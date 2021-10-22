import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Lemmas.DerivedFunctors

import Lean



set_option autoBoundImplicitLocal false



-- By treating the primite and derived functors as combinators (see
-- https://en.wikipedia.org/wiki/Combinatory_logic), we obtain an algorithm to construct a functor
-- for a given lambda term, i.e. to prove functoriality automatically.
--
-- Below, `t` and `T` denote arbitrary terms of the correct type (which is a functor type in case
-- of `T`).
-- We write `Λ a => b` for the functor obtained for `λ a => b` using this algorithm recursively.
--
--  Functor               | Condition      | Definition
-- -----------------------+----------------+-------------------------------------------------------
--  `Λ a => t`            | `a` not in `t` | `constFun _ t`
--  `Λ a => a`            |                | `idFun _`
--  `Λ a => T a`          | `a` not in `T` | `T`
--  `Λ a => T t`          | `a` not in `T` | `compFun (Λ a => t) T`
--  `Λ F => F t`          | `F` not in `t` | `appFun t _`
--  `Λ a => T t`          | `a` not in `t` | `swapFun (Λ a => T) t`
--  `Λ a => T a`          |                | `dupFun (Λ a => T)`
--  `Λ a => T t`          |                | `substFun (Λ a => t) (Λ a => T)`
--  `Λ a => ?Fun t₁...tₙ` |                | `Λ a => (?FunFun t₁...tₙ₋₁) tₙ`
--                        |                | (optimization: use `rev` if it makes `?FunFun` term
--                        |                | constant)
--
-- Although all cases of functor application inside the lambda body can be handled generically by
-- `substFun` (matching SKI combinator calculus), `substFun` requires `FullFunOp`, whereas
-- `compFun`, `appFun`, and `swapFun` only require `LinearFunOp` (corresponding to linear logic,
-- where each variable is used exactly once). So the special cases are not merely optimizations.



namespace Lean

  open Meta Elab Tactic

  -- Some helper code so that we can work with a `(U : Universe) [h : HasInternalFunctors U]` more
  -- easily in meta code.

  def mkHasInstancesInst (u v : Level) (U h A : Expr) : Expr :=
    mkApp3 (mkConst ``HasInstances.Inst [u, v]) U h A

  def mkUniverseInst (u : Level) (U : Expr) : Expr :=
    mkHasInstancesInst (mkLevelSucc u) (mkLevelSucc (mkLevelSucc u)) (mkConst ``Universe [u]) (mkConst ``Universe.hasInstances [u]) U

  def mkUniverseInstInst (u : Level) (U U' A : Expr) : Expr :=
    mkHasInstancesInst u (mkLevelSucc u) U' (mkApp (mkConst ``Universe.instInst [u]) U) A

  structure FunUniv where
  (mvarId   : MVarId)
  (u iu     : Level)
  (U U'     : Expr)
  (hId hFun : Expr)

  namespace FunUniv

    def getDecl (φ : FunUniv) (n : Name) : Expr :=
      mkApp3 (mkConst n [φ.u, φ.iu]) φ.U φ.hId φ.hFun

    def mkTypeInst (φ : FunUniv) (A : Expr) : Expr :=
      mkUniverseInstInst φ.u φ.U φ.U' A

    def mkFunType (φ : FunUniv) (A B : Expr) : Expr :=
      mkApp2 (φ.getDecl ``HasInternalFunctors.Helpers.Fun) A B

    def mkFreshTypeMVar (φ : FunUniv): MetaM Expr :=
      mkFreshExprMVar φ.U'

    def mkFreshInstMVar (φ : FunUniv) (A : Expr) : MetaM Expr :=
      mkFreshExprMVar (φ.mkTypeInst A)

    def mkFreshDeclMVar (φ : FunUniv) (n : Name) : MetaM Expr :=
      mkFreshExprMVar (φ.getDecl n)

  end FunUniv

  -- A function that has been transformed into a lambda abstraction that we can work with more
  -- easily. In particular, the lambda variable `a` is an `FVar`, so that `t` does not contain any
  -- loose bound variables. This is required for Lean algorithms such as `isDefEq` to work.

  structure LambdaAbstr where
  (A B a t : Expr)

  namespace LambdaAbstr

    def exprAsConstant (f : LambdaAbstr) (t : Expr) : MetaM (Option Expr) := do
      if !(t.containsFVar f.a.fvarId!) then
        return t
      let t' ← reduce t
      if !(t'.containsFVar f.a.fvarId!) then
        return t'
      none

    def asConstant (f : LambdaAbstr) : MetaM (Option Expr) := f.exprAsConstant f.t

    def isId (f : LambdaAbstr) : MetaM Bool := isDefEq f.t f.a

  end LambdaAbstr

  -- The actual algorithm is implemented as a set of mutually recursive functions.
  -- Of these, `constructLambdaFunctor` is the main entry point (called by `constructFunctor`
  -- below); it returns a functor for the lambda expression given by `f`. If the body of `f`
  -- is a functor application, it is analyzed and handled by `constructLambdaAppFunctor`. If it is
  -- an application of `fromDefFun`, `constructLambdaDefFunFunctor` handles that; in most cases we
  -- are dealing with some primitive or derived `...Fun` (the last case in the algorithm).

  mutual

    -- The main entry point, which handles `constFun` and `idFun` directly, and calls either
    -- `constructLambdaAppFunctor` or `constructLambdaDefFunFunctor` otherwise.

    partial def constructLambdaFunctor (φ : FunUniv) (f : LambdaAbstr) : MetaM Expr := do
      match ← f.asConstant with
      | some t => do
        let hHasSubLinearFunOp ← synthInstance (φ.getDecl ``HasSubLinearFunOp)
        mkApp4 (φ.getDecl ``HasSubLinearFunOp.constFun) hHasSubLinearFunOp f.A f.B t
      | none => do
        if ← f.isId then
          let hHasLinearFunOp ← synthInstance (φ.getDecl ``HasLinearFunOp)
          return mkApp2 (φ.getDecl ``HasLinearFunOp.idFun) hHasLinearFunOp f.A
        let B_b ← φ.mkFreshTypeMVar
        let G ← φ.mkFreshInstMVar (φ.mkFunType B_b f.B)
        let b ← φ.mkFreshInstMVar B_b
        if ← isDefEq f.t (mkApp4 (φ.getDecl ``HasInternalFunctors.Helpers.apply) B_b f.B G b) then
          let G ← instantiateMVars G
          let b ← instantiateMVars b
          return ← constructLambdaAppFunctor φ f B_b G b
        let A_G ← φ.mkFreshTypeMVar
        let B_G ← φ.mkFreshTypeMVar
        let g ← mkFreshExprMVar (← mkArrow (φ.mkTypeInst A_G) (φ.mkTypeInst B_G))
        let G' ← mkFreshExprMVar (mkApp3 (φ.getDecl ``HasInternalFunctors.Helpers.DefFun) A_G B_G g)
        if ← isDefEq f.t (mkApp4 (φ.getDecl ``HasInternalFunctors.Helpers.fromDefFun) A_G B_G g G') then
          let g ← instantiateMVars g
          let G' ← instantiateMVars G'
          return ← constructLambdaDefFunFunctor φ f A_G B_G g G'
        throwTacticEx `makeFunctor φ.mvarId m!"unsupported lambda body '{f.t}'"

    -- This function handles the different cases of functor application in the lambda body,
    -- depending on which parts are either equal to the lambda variable or constant with respect
    -- to it. (Note that we do not optimize the case where both parts are constant, since that
    -- should have been handled already.)

    partial def constructLambdaAppFunctor (φ : FunUniv) (f : LambdaAbstr) (B_b G b : Expr) : MetaM Expr :=
      withDefault do
        let B_G := φ.mkFunType B_b f.B
        let f_G : LambdaAbstr := ⟨f.A, B_G, f.a, G⟩
        let f_b : LambdaAbstr := ⟨f.A, B_b, f.a, b⟩
        let hHasLinearFunOp ← synthInstance (φ.getDecl ``HasLinearFunOp)
        match ← f_G.asConstant with
        | some G => do
          if ← f_b.isId then
            return G
          let F_b ← constructLambdaFunctor φ f_b
          -- TODO: Write as `trans` to enable notation.
          return mkApp6 (φ.getDecl ``HasLinearFunOp.compFun) hHasLinearFunOp f.A B_b f.B F_b G
        | none => do
          match ← f_b.asConstant with
          | some b => do
            if ← f_G.isId then
              return mkApp4 (φ.getDecl ``HasLinearFunOp.appFun) hHasLinearFunOp B_b b f.B
            let F_G ← constructLambdaFunctor φ f_G
            return mkApp6 (φ.getDecl ``HasLinearFunOp.swapFun) hHasLinearFunOp f.A B_b f.B F_G b
          | none => do
            let F_G ← constructLambdaFunctor φ f_G
            if ← f_b.isId then
              let hHasNonLinearFunOp ← synthInstance (φ.getDecl ``HasNonLinearFunOp)
              return mkApp4 (φ.getDecl ``HasNonLinearFunOp.dupFun) hHasNonLinearFunOp f.A f.B F_G
            let F_b ← constructLambdaFunctor φ f_b
            let hHasFullFunOp ← synthInstance (φ.getDecl ``HasFullFunOp)
            return mkApp6 (φ.getDecl ``HasFullFunOp.substFun) hHasFullFunOp f.A B_b f.B F_b F_G

    -- This function performs the simple but tedious task of converting applications of `def...Fun`
    -- to a functor application of the corresponding `...FunFun`, which is then handled by
    -- `constructLambdaAppFunctor`.
    --
    -- Normally in combinator calculus, there is no such transformation, because combinators only
    -- come in a single variant. But since we have e.g. `compFun`, `compFunFun`, and
    -- `compFunFunFun`, we would like to work with all of them in the best possible way.
    --
    -- The sequence of `isDefEq` is a bit slow in cases where we have a late match. There is
    -- probably a way to improve this; e.g. we could work with fully reduced terms and match
    -- expressions exactly, assigning metavariables in the process. The catch is that the
    -- expressions we match against are not actually fully reduced: Lean can further reduce them to
    -- `Expr.proj` -- but apparently not if they contain metavariables, so a naive matching
    -- algorithm fails. Also, we would need to make sure that the derived functors that we use as
    -- building blocks are not reduced.

    partial def constructLambdaDefFunFunctor (φ : FunUniv) (f : LambdaAbstr) (A_G B_G g G' : Expr) : MetaM Expr := do
      let G ← φ.mkFreshInstMVar (φ.mkFunType A_G B_G)
      if ← isDefEq G' (mkApp3 (φ.getDecl ``HasInternalFunctors.Helpers.toDefFun) A_G B_G G) then
        let G ← instantiateMVars G
        return ← constructLambdaFunctor φ ⟨f.A, f.B, f.a, G⟩
      withReducible do
        let hHasSubLinearFunOp ← φ.mkFreshDeclMVar ``HasSubLinearFunOp
        let b ← φ.mkFreshInstMVar B_G
        if ← isDefEq G' (mkApp4 (φ.getDecl ``HasSubLinearFunOp.defConstFun) hHasSubLinearFunOp A_G B_G b) then
          let b ← instantiateMVars b
          let const := mkApp3 (φ.getDecl ``HasSubLinearFunOp.constFunFun) hHasSubLinearFunOp A_G B_G
          return ← constructLambdaAppFunctor φ f B_G const b
        let hHasLinearFunOp ← φ.mkFreshDeclMVar ``HasLinearFunOp
        let A₁ ← φ.mkFreshTypeMVar
        let a₁ ← φ.mkFreshInstMVar A₁
        if ← isDefEq G' (mkApp4 (φ.getDecl ``HasLinearFunOp.defAppFun) hHasLinearFunOp A₁ a₁ B_G) then
          let a₁ ← instantiateMVars a₁
          let app := mkApp3 (φ.getDecl ``HasLinearFunOp.appFunFun) hHasLinearFunOp A₁ B_G
          return ← constructLambdaAppFunctor φ f A₁ app a₁
        let A_F₁ := φ.mkFunType A_G A₁
        let A_F₂ := φ.mkFunType A₁ B_G
        let F₁ ← φ.mkFreshInstMVar A_F₁
        let F₂ ← φ.mkFreshInstMVar A_F₂
        if ← isDefEq G' (mkApp6 (φ.getDecl ``HasLinearFunOp.defCompFun) hHasLinearFunOp A_G A₁ B_G F₁ F₂) then
          let F₁ ← instantiateMVars F₁
          let F₂ ← instantiateMVars F₂
          let comp := mkApp5 (φ.getDecl ``HasLinearFunOp.compFunFun) hHasLinearFunOp A_G A₁ F₁ B_G
          return ← match ← f.exprAsConstant comp with
          | some comp =>
            constructLambdaAppFunctor φ f A_F₂ comp F₂
          | none =>
            let revComp := mkApp5 (φ.getDecl ``HasLinearFunOp.revCompFunFun) hHasLinearFunOp A_G A₁ B_G F₂
            constructLambdaAppFunctor φ f A_F₁ revComp F₁
        let A₂ ← φ.mkFreshTypeMVar
        let A₃ ← φ.mkFreshTypeMVar
        let A_F₃ := φ.mkFunType A₁ A₂
        let F₃ ← φ.mkFreshInstMVar A_F₃
        if ← isDefEq G' (mkApp5 (φ.getDecl ``HasLinearFunOp.defCompFunFun) hHasLinearFunOp A₁ A₂ F₃ A₃) then
          let F₃ ← instantiateMVars F₃
          let comp := mkApp4 (φ.getDecl ``HasLinearFunOp.compFunFunFun) hHasLinearFunOp A₁ A₂ A₃
          return ← constructLambdaAppFunctor φ f A_F₃ comp F₃
        let A_F₄ := φ.mkFunType A₂ A₃
        let F₄ ← φ.mkFreshInstMVar A_F₄
        if ← isDefEq G' (mkApp5 (φ.getDecl ``HasLinearFunOp.defRevCompFunFun) hHasLinearFunOp A₁ A₂ A₃ F₄) then
          let F₄ ← instantiateMVars F₄
          let revComp := mkApp4 (φ.getDecl ``HasLinearFunOp.revCompFunFunFun) hHasLinearFunOp A₁ A₂ A₃
          return ← constructLambdaAppFunctor φ f A_F₄ revComp F₄
        let A_F₅ := φ.mkFunType A_G (φ.mkFunType A₁ B_G)
        let F₅ ← φ.mkFreshInstMVar A_F₅
        if ← isDefEq G' (mkApp6 (φ.getDecl ``HasLinearFunOp.defSwapFun) hHasLinearFunOp A_G A₁ B_G F₅ a₁) then
          let F₅ ← instantiateMVars F₅
          let a₁ ← instantiateMVars a₁
          let swap := mkApp5 (φ.getDecl ``HasLinearFunOp.swapFunFun) hHasLinearFunOp A_G A₁ B_G F₅
          return ← match ← f.exprAsConstant swap with
          | some swap =>
            constructLambdaAppFunctor φ f A₁ swap a₁
          | none =>
            let revSwap := mkApp5 (φ.getDecl ``HasLinearFunOp.revSwapFunFun) hHasLinearFunOp A_G A₁ a₁ B_G
            constructLambdaAppFunctor φ f A_F₅ revSwap F₅
        let A_F₆ := φ.mkFunType A₁ (φ.mkFunType A_G A₂)
        let F₆ ← φ.mkFreshInstMVar A_F₆
        if ← isDefEq G' (mkApp5 (φ.getDecl ``HasLinearFunOp.defSwapFunFun) hHasLinearFunOp A₁ A_G A₂ F₆) then
          let F₆ ← instantiateMVars F₆
          let swap := mkApp4 (φ.getDecl ``HasLinearFunOp.swapFunFunFun) hHasLinearFunOp A₁ A_G A₂
          return ← constructLambdaAppFunctor φ f A_F₆ swap F₆
        let a₂ ← φ.mkFreshInstMVar A₂
        if ← isDefEq G' (mkApp5 (φ.getDecl ``HasLinearFunOp.defRevSwapFunFun) hHasLinearFunOp A₁ A₂ a₂ A₃) then
          let a₂ ← instantiateMVars a₂
          let revSwap := mkApp4 (φ.getDecl ``HasLinearFunOp.revSwapFunFunFun) hHasLinearFunOp A₁ A₂ A₃
          return ← constructLambdaAppFunctor φ f A₂ revSwap a₂
        let hHasNonLinearFunOp ← φ.mkFreshDeclMVar ``HasNonLinearFunOp
        let A_F₇ := φ.mkFunType A_G (φ.mkFunType A_G B_G)
        let F₇ ← φ.mkFreshInstMVar A_F₇
        if ← isDefEq G' (mkApp4 (φ.getDecl ``HasNonLinearFunOp.defDupFun) hHasNonLinearFunOp A_G B_G F₇) then
          let F₇ ← instantiateMVars F₇
          let dup := mkApp3 (φ.getDecl ``HasNonLinearFunOp.dupFunFun) hHasNonLinearFunOp A_G B_G
          return ← constructLambdaAppFunctor φ f A_F₇ dup F₇
        let hHasFullFunOp ← φ.mkFreshDeclMVar ``HasFullFunOp
        let A_F₈ := φ.mkFunType A_G (φ.mkFunType A₁ B_G)
        let F₈ ← φ.mkFreshInstMVar A_F₈
        if ← isDefEq G' (mkApp6 (φ.getDecl ``HasFullFunOp.defSubstFun) hHasFullFunOp A_G A₁ B_G F₁ F₈) then
          let F₁ ← instantiateMVars F₁
          let F₈ ← instantiateMVars F₈
          let subst := mkApp5 (φ.getDecl ``HasFullFunOp.substFunFun) hHasFullFunOp A_G A₁ F₁ B_G
          return ← match ← f.exprAsConstant subst with
          | some subst =>
            constructLambdaAppFunctor φ f A_F₈ subst F₈
          | none =>
            let revSubst := mkApp5 (φ.getDecl ``HasFullFunOp.revSubstFunFun) hHasFullFunOp A_G A₁ B_G F₈
            constructLambdaAppFunctor φ f A_F₁ revSubst F₁
        if ← isDefEq G' (mkApp5 (φ.getDecl ``HasFullFunOp.defSubstFunFun) hHasFullFunOp A₁ A₂ F₃ A₃) then
          let F₃ ← instantiateMVars F₃
          let subst := mkApp4 (φ.getDecl ``HasFullFunOp.substFunFunFun) hHasFullFunOp A₁ A₂ A₃
          return ← constructLambdaAppFunctor φ f A_F₃ subst F₃
        let A_F₉ := φ.mkFunType A₁ (φ.mkFunType A₂ A₃)
        let F₉ ← φ.mkFreshInstMVar A_F₉
        if ← isDefEq G' (mkApp5 (φ.getDecl ``HasFullFunOp.defRevSubstFunFun) hHasFullFunOp A₁ A₂ A₃ F₉) then
          let F₉ ← instantiateMVars F₉
          let revSubst := mkApp4 (φ.getDecl ``HasFullFunOp.revSubstFunFunFun) hHasFullFunOp A₁ A₂ A₃
          return ← constructLambdaAppFunctor φ f A_F₉ revSubst F₉
        throwTacticEx `makeFunctor φ.mvarId m!"unsupported fromDefFun argument '{G'}'"

  end

  -- Construct a functor for a given function expression.
  -- If the expression is a lambda abstraction, we use its components directly; otherwise we
  -- convert it to a lambda abstraction with a lambda application in its body (which can hopefully
  -- be unfolded).

  def constructFunctor (φ : FunUniv) (A B A' B' : Expr) : Expr → MetaM Expr
    | Expr.lam n d b c => withLocalDecl n c.binderInfo d fun a =>
      let t := b.instantiate1 a
      constructLambdaFunctor φ ⟨A, B, a, t⟩
    | f => do
      let F ← φ.mkFreshInstMVar (φ.mkFunType A B)
      if ← isDefEq f (mkApp3 (φ.getDecl ``HasInternalFunctors.Helpers.apply) A B F) then
        return F
      let a := mkFVar (← mkFreshFVarId)
      withLocalDecl `a BinderInfo.default A' fun a =>
        let t := mkApp f a
        constructLambdaFunctor φ ⟨A, B, a, t⟩

  -- The `makeFunctor` tactic, which calls `constructFunctor` based on the target type and given
  -- term. Note that the target type determines how to elaborate the term, which enables us to omit
  -- the variable type in `Λ` expressions.

  def makeFunctor (mvarId : MVarId) (hf : Syntax) : TacticM Expr := do
    let type ← getMVarType mvarId
    let u ← mkFreshLevelMVar
    let iu ← mkFreshLevelMVar
    let U ← mkFreshExprMVar (mkConst ``Universe [u])
    let hId ← mkFreshExprMVar (mkApp (mkConst ``HasIdentity [u, iu]) U)
    let hFun ← mkFreshExprMVar (mkApp2 (mkConst ``HasInternalFunctors [u, iu]) U hId)
    let U' := mkUniverseInst u U
    let φ' : FunUniv := ⟨mvarId, u, iu, U, U', hId, hFun⟩
    let A ← φ'.mkFreshTypeMVar
    let B ← φ'.mkFreshTypeMVar
    if ← isDefEq type (φ'.mkTypeInst (φ'.mkFunType A B)) then
      let u ← instantiateLevelMVars u
      let iu ← instantiateLevelMVars iu
      let U ← instantiateMVars U
      let U' ← instantiateMVars U'
      let hId ← instantiateMVars hId
      let hFun ← instantiateMVars hFun
      let A ← instantiateMVars A
      let B ← instantiateMVars B
      let φ : FunUniv := ⟨mvarId, u, iu, U, U', hId, hFun⟩
      let A' := φ.mkTypeInst A
      let B' := φ.mkTypeInst B
      let f ← elabTerm hf (← mkArrow A' B')
      return ← constructFunctor φ A B A' B' f
    throwTacticEx `makeFunctor mvarId m!"type '{type}' is not an application of 'HasInternalFunctors.Fun'"

  elab "makeFunctor " hf:term : tactic => do
    let mvarId ← getMainGoal
    withMVarContext mvarId do
      let e ← makeFunctor mvarId hf
      assignExprMVar mvarId e

  -- Implementation of the `Λ` notation.
  -- We want `Λ a b ... => t` to be a shortcut for:
  -- `by makeFunctor (λ a => by makeFunctor (λ b => ... t))`.
  -- However, `expandExplicitBinders` only accepts a name, so as a hack, we currently give it a
  -- dummy name `__mkFun` and then recursively replace the corresponding syntax nodes in the
  -- result.

  partial def replaceMkFun : Syntax → MacroM Syntax
    | `(__mkFun $f) => do
      let f ← replaceMkFun f
      `(by makeFunctor $f)
    | f => match f with
           | Syntax.node kind args => do
             let args ← args.sequenceMap replaceMkFun
             Syntax.node kind args
           | _ => f

  macro "Λ" xs:explicitBinders " => " b:term : term => do
    let f ← expandExplicitBinders `__mkFun xs b
    replaceMkFun f

  -- The `functoriality` tactic, which constructs instances of `DefFun`.
  -- Essentially, when asked to construct an instance of `A ⟶{f} B`, it outputs
  -- `(by makeFunctor f) ◄ λ _ => by simp`.

  def functoriality (mvarId : MVarId) : TacticM Expr := do
    let type ← getMVarType mvarId
    let u ← mkFreshLevelMVar
    let iu ← mkFreshLevelMVar
    let U ← mkFreshExprMVar (mkConst ``Universe [u])
    let hId ← mkFreshExprMVar (mkApp (mkConst ``HasIdentity [u, iu]) U)
    let hFun ← mkFreshExprMVar (mkApp2 (mkConst ``HasInternalFunctors [u, iu]) U hId)
    let U' := mkUniverseInst u U
    let φ' : FunUniv := ⟨mvarId, u, iu, U, U', hId, hFun⟩
    let A ← φ'.mkFreshTypeMVar
    let B ← φ'.mkFreshTypeMVar
    let A' := φ'.mkTypeInst A
    let B' := φ'.mkTypeInst B
    let f ← mkFreshExprMVar (← mkArrow A' B')
    if ← isDefEq type (mkApp3 (φ'.getDecl ``HasInternalFunctors.Helpers.DefFun) A B f) then
      let u ← instantiateLevelMVars u
      let iu ← instantiateLevelMVars iu
      let U ← instantiateMVars U
      let U' ← instantiateMVars U'
      let hId ← instantiateMVars hId
      let hFun ← instantiateMVars hFun
      let A ← instantiateMVars A
      let B ← instantiateMVars B
      let A' ← instantiateMVars A'
      let B' ← instantiateMVars B'
      let f ← instantiateMVars f
      let φ : FunUniv := ⟨mvarId, u, iu, U, U', hId, hFun⟩
      let F ← constructFunctor φ A B A' B' f
      let hDefTypeBody := mkApp3 (mkConst ``Eq [u]) B' (mkApp4 (φ.getDecl ``HasInternalFunctors.Helpers.apply) A B F (mkBVar 0)) (mkApp f (mkBVar 0))
      let hDefType := mkForall `a BinderInfo.default A' hDefTypeBody
      let hDef ← elabTerm (← `(λ _ => by simp [HasInternalFunctors.Helpers.apply])) hDefType
      return mkApp5 (φ'.getDecl ``HasInternalFunctors.Helpers.toDefFun') A B F f hDef
    throwTacticEx `makeFunctor mvarId m!"type '{type}' is not an application of 'HasInternalFunctors.DefFun'"

  elab "functoriality" : tactic => do
    let mvarId ← getMainGoal
    withMVarContext mvarId do
      let e ← functoriality mvarId
      assignExprMVar mvarId e

end Lean
