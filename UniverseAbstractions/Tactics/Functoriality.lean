import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Lemmas.DerivedFunctors

import Lean



set_option autoBoundImplicitLocal false



-- By treating the primite and derived functors as combinators (see
-- https://en.wikipedia.org/wiki/Combinatory_logic), we obtain an algorithm to construct a functor
-- for a given lambda term, i.e. to prove functoriality automatically.
--
-- Below, `F`, `G`, etc. denote functors, whereas `a`, `b`, etc. denote arbitrary terms.
-- We write `Λ a => b` for the functor obtained for `λ a => b` using this algorithm recursively.
--
--  Term                  | Condition      | Functor
-- -----------------------+----------------+-------------------------------------------------------
--  `λ a => c`            | `a` not in `c` | `constFun _ c`
--  `λ a => a`            |                | `idFun _`
--  `λ a => F a`          | `a` not in `F` | `F`
--  `λ a => F b`          | `a` not in `F` | `compFun (Λ a => b) F`
--  `λ F => F c`          | `F` not in `c` | `appFun c _`
--  `λ a => F c`          | `a` not in `c` | `swapFun (Λ a => F) c`
--  `λ a => F a`          |                | `dupFun (Λ a => F)`
--  `λ a => F b`          |                | `substFun (Λ a => b) (Λ a => F)`
--  `λ a => ?Fun b₁...bₙ` |                | `Λ a => (?FunFun b₁...bₙ₋₁) bₙ`
--                        |                | (optimization: use `rev` if it makes `?FunFun` term
--                        |                | constant)
--
-- Although all cases of functor application inside the lambda body can be handled generically by
-- `substFun` (matching SKI combinator calculus), `substFun` requires `FullFunOp`, whereas
-- `compFun`, `appFun`, and `swapFun` only require `LinearFunOp` (corresponding to linear logic,
-- where each variable is used exactly once). So the special cases are not merely optimizations.



namespace Lean

  open Meta Elab Tactic

  -- Some helper code so that we can work with a `(U : Universe) [h : HasEmbeddedFunctors U]` more
  -- easily in meta code.

  def mkHasInstancesInst (u v : Level) (U h α : Expr) : Expr :=
    mkApp3 (mkConst ``HasInstances.Inst [u, v]) U h α

  def mkUniverseInst (u : Level) (U : Expr) : Expr :=
    mkHasInstancesInst (mkLevelSucc u) (mkLevelSucc (mkLevelSucc u)) (mkConst ``Universe [u]) (mkConst ``Universe.hasInstances [u]) U

  def mkUniverseInstInst (u : Level) (U U' α : Expr) : Expr :=
    mkHasInstancesInst u (mkLevelSucc u) U' (mkApp (mkConst ``Universe.instInst [u]) U) α

  structure FunUniv where
  (mvarId : MVarId)
  (u w    : Level)
  (U U' h : Expr)

  namespace FunUniv

    def getDecl (φ : FunUniv) (n : Name) : Expr :=
      mkApp2 (mkConst n [φ.u, φ.w]) φ.U φ.h

    def mkTypeInst (φ : FunUniv) (α : Expr) : Expr :=
      mkUniverseInstInst φ.u φ.U φ.U' α

    def mkFunType (φ : FunUniv) (α β : Expr) : Expr :=
      mkApp2 (φ.getDecl ``HasEmbeddedFunctors.Fun) α β

    def mkFreshTypeMVar (φ : FunUniv): MetaM Expr :=
      mkFreshExprMVar φ.U'

    def mkFreshInstMVar (φ : FunUniv) (α : Expr) : MetaM Expr :=
      mkFreshExprMVar (φ.mkTypeInst α)

    def mkFreshDeclMVar (φ : FunUniv) (n : Name) : MetaM Expr :=
      mkFreshExprMVar (φ.getDecl n)

  end FunUniv

  -- A function that has been transformed into a lambda abstraction that we can work with more
  -- easily. In particular, the lambda variable `a` is an `FVar`, so that `t` does not contain any
  -- loose bound variables. This is required for Lean algorithms such as `isDefEq` to work.

  structure LambdaAbstr where
  (α β a t : Expr)

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
        mkApp4 (φ.getDecl ``HasSubLinearFunOp.constFun) hHasSubLinearFunOp f.α f.β t
      | none => do
        if ← f.isId then
          let hHasLinearFunOp ← synthInstance (φ.getDecl ``HasLinearFunOp)
          return mkApp2 (φ.getDecl ``HasLinearFunOp.idFun) hHasLinearFunOp f.α
        let β_b ← φ.mkFreshTypeMVar
        let G ← φ.mkFreshInstMVar (φ.mkFunType β_b f.β)
        let b ← φ.mkFreshInstMVar β_b
        if ← isDefEq f.t (mkApp4 (φ.getDecl ``HasEmbeddedFunctors.funCoe) β_b f.β G b) then
          let G ← instantiateMVars G
          let b ← instantiateMVars b
          return ← constructLambdaAppFunctor φ f β_b G b
        let α_G ← φ.mkFreshTypeMVar
        let β_G ← φ.mkFreshTypeMVar
        let g ← mkFreshExprMVar (← mkArrow (φ.mkTypeInst α_G) (φ.mkTypeInst β_G))
        let G' ← mkFreshExprMVar (mkApp3 (φ.getDecl ``HasEmbeddedFunctors.DefFun) α_G β_G g)
        if ← isDefEq f.t (mkApp4 (φ.getDecl ``HasEmbeddedFunctors.fromDefFun) α_G β_G g G') then
          let g ← instantiateMVars g
          let G' ← instantiateMVars G'
          return ← constructLambdaDefFunFunctor φ f α_G β_G g G'
        throwTacticEx `makeFunctor φ.mvarId m!"unsupported lambda body '{f.t}'"

    -- This function handles the different cases of functor application in the lambda body,
    -- depending on which parts are either equal to the lambda variable or constant with respect
    -- to it. (Note that we do not optimize the case where both parts are constant, since that
    -- should have been handled already.)

    partial def constructLambdaAppFunctor (φ : FunUniv) (f : LambdaAbstr) (β_b G b : Expr) : MetaM Expr :=
      withDefault do
        let β_G := φ.mkFunType β_b f.β
        let f_G : LambdaAbstr := ⟨f.α, β_G, f.a, G⟩
        let f_b : LambdaAbstr := ⟨f.α, β_b, f.a, b⟩
        let hHasLinearFunOp ← synthInstance (φ.getDecl ``HasLinearFunOp)
        match ← f_G.asConstant with
        | some G => do
          if ← f_b.isId then
            return G
          let F_b ← constructLambdaFunctor φ f_b
          return mkApp6 (φ.getDecl ``HasLinearFunOp.revCompFun) hHasLinearFunOp f.α β_b f.β G F_b
        | none => do
          match ← f_b.asConstant with
          | some b => do
            if ← f_G.isId then
              return mkApp4 (φ.getDecl ``HasLinearFunOp.appFun) hHasLinearFunOp β_b b f.β
            let F_G ← constructLambdaFunctor φ f_G
            return mkApp6 (φ.getDecl ``HasLinearFunOp.swapFun) hHasLinearFunOp f.α β_b f.β F_G b
          | none => do
            let F_G ← constructLambdaFunctor φ f_G
            if ← f_b.isId then
              let hHasNonLinearFunOp ← synthInstance (φ.getDecl ``HasNonLinearFunOp)
              return mkApp4 (φ.getDecl ``HasNonLinearFunOp.dupFun) hHasNonLinearFunOp f.α f.β F_G
            let F_b ← constructLambdaFunctor φ f_b
            let hHasFullFunOp ← synthInstance (φ.getDecl ``HasFullFunOp)
            return mkApp6 (φ.getDecl ``HasFullFunOp.substFun) hHasFullFunOp f.α β_b f.β F_b F_G

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

    partial def constructLambdaDefFunFunctor (φ : FunUniv) (f : LambdaAbstr) (α_G β_G g G' : Expr) : MetaM Expr := do
      let G ← φ.mkFreshInstMVar (φ.mkFunType α_G β_G)
      if ← isDefEq G' (mkApp3 (φ.getDecl ``HasEmbeddedFunctors.toDefFun) α_G β_G G) then
        let G ← instantiateMVars G
        return ← constructLambdaFunctor φ ⟨f.α, f.β, f.a, G⟩
      withReducible do
        let hHasSubLinearFunOp ← φ.mkFreshDeclMVar ``HasSubLinearFunOp
        let b ← φ.mkFreshInstMVar β_G
        if ← isDefEq G' (mkApp4 (φ.getDecl ``HasSubLinearFunOp.defConstFun) hHasSubLinearFunOp α_G β_G b) then
          let b ← instantiateMVars b
          let const := mkApp3 (φ.getDecl ``HasSubLinearFunOp.constFunFun) hHasSubLinearFunOp α_G β_G
          return ← constructLambdaAppFunctor φ f β_G const b
        let hHasLinearFunOp ← φ.mkFreshDeclMVar ``HasLinearFunOp
        let α₁ ← φ.mkFreshTypeMVar
        let a₁ ← φ.mkFreshInstMVar α₁
        if ← isDefEq G' (mkApp4 (φ.getDecl ``HasLinearFunOp.defAppFun) hHasLinearFunOp α₁ a₁ β_G) then
          let a₁ ← instantiateMVars a₁
          let app := mkApp3 (φ.getDecl ``HasLinearFunOp.appFunFun) hHasLinearFunOp α₁ β_G
          return ← constructLambdaAppFunctor φ f α₁ app a₁
        let α_F₁ := φ.mkFunType α_G α₁
        let α_F₂ := φ.mkFunType α₁ β_G
        let F₁ ← φ.mkFreshInstMVar α_F₁
        let F₂ ← φ.mkFreshInstMVar α_F₂
        if ← isDefEq G' (mkApp6 (φ.getDecl ``HasLinearFunOp.defCompFun) hHasLinearFunOp α_G α₁ β_G F₁ F₂) then
          let F₁ ← instantiateMVars F₁
          let F₂ ← instantiateMVars F₂
          let revComp := mkApp5 (φ.getDecl ``HasLinearFunOp.revCompFunFun) hHasLinearFunOp α_G α₁ β_G F₂
          return ← match ← f.exprAsConstant revComp with
          | some revComp =>
            constructLambdaAppFunctor φ f α_F₁ revComp F₁
          | none =>
            let comp := mkApp5 (φ.getDecl ``HasLinearFunOp.compFunFun) hHasLinearFunOp α_G α₁ F₁ β_G
            constructLambdaAppFunctor φ f α_F₂ comp F₂
        let α₂ ← φ.mkFreshTypeMVar
        let α₃ ← φ.mkFreshTypeMVar
        let α_F₃ := φ.mkFunType α₁ α₂
        let F₃ ← φ.mkFreshInstMVar α_F₃
        if ← isDefEq G' (mkApp5 (φ.getDecl ``HasLinearFunOp.defCompFunFun) hHasLinearFunOp α₁ α₂ F₃ α₃) then
          let F₃ ← instantiateMVars F₃
          let comp := mkApp4 (φ.getDecl ``HasLinearFunOp.compFunFunFun) hHasLinearFunOp α₁ α₂ α₃
          return ← constructLambdaAppFunctor φ f α_F₃ comp F₃
        let α_F₄ := φ.mkFunType α₂ α₃
        let F₄ ← φ.mkFreshInstMVar α_F₄
        if ← isDefEq G' (mkApp5 (φ.getDecl ``HasLinearFunOp.defRevCompFunFun) hHasLinearFunOp α₁ α₂ α₃ F₄) then
          let F₄ ← instantiateMVars F₄
          let revComp := mkApp4 (φ.getDecl ``HasLinearFunOp.revCompFunFunFun) hHasLinearFunOp α₁ α₂ α₃
          return ← constructLambdaAppFunctor φ f α_F₄ revComp F₄
        let α_F₅ := φ.mkFunType α_G (φ.mkFunType α₁ β_G)
        let F₅ ← φ.mkFreshInstMVar α_F₅
        if ← isDefEq G' (mkApp6 (φ.getDecl ``HasLinearFunOp.defSwapFun) hHasLinearFunOp α_G α₁ β_G F₅ a₁) then
          let F₅ ← instantiateMVars F₅
          let a₁ ← instantiateMVars a₁
          let revSwap := mkApp5 (φ.getDecl ``HasLinearFunOp.revSwapFunFun) hHasLinearFunOp α_G α₁ a₁ β_G
          return ← match ← f.exprAsConstant revSwap with
          | some revSwap =>
            constructLambdaAppFunctor φ f α_F₅ revSwap F₅
          | none =>
            let swap := mkApp5 (φ.getDecl ``HasLinearFunOp.swapFunFun) hHasLinearFunOp α_G α₁ β_G F₅
            constructLambdaAppFunctor φ f α₁ swap a₁
        let α_F₆ := φ.mkFunType α₁ (φ.mkFunType α_G α₂)
        let F₆ ← φ.mkFreshInstMVar α_F₆
        if ← isDefEq G' (mkApp5 (φ.getDecl ``HasLinearFunOp.defSwapFunFun) hHasLinearFunOp α₁ α_G α₂ F₆) then
          let F₆ ← instantiateMVars F₆
          let swap := mkApp4 (φ.getDecl ``HasLinearFunOp.swapFunFunFun) hHasLinearFunOp α₁ α_G α₂
          return ← constructLambdaAppFunctor φ f α_F₆ swap F₆
        let a₂ ← φ.mkFreshInstMVar α₂
        if ← isDefEq G' (mkApp5 (φ.getDecl ``HasLinearFunOp.defRevSwapFunFun) hHasLinearFunOp α₁ α₂ a₂ α₃) then
          let a₂ ← instantiateMVars a₂
          let revSwap := mkApp4 (φ.getDecl ``HasLinearFunOp.revSwapFunFunFun) hHasLinearFunOp α₁ α₂ α₃
          return ← constructLambdaAppFunctor φ f α₂ revSwap a₂
        let hHasNonLinearFunOp ← φ.mkFreshDeclMVar ``HasNonLinearFunOp
        let α_F₇ := φ.mkFunType α_G (φ.mkFunType α_G β_G)
        let F₇ ← φ.mkFreshInstMVar α_F₇
        if ← isDefEq G' (mkApp4 (φ.getDecl ``HasNonLinearFunOp.defDupFun) hHasNonLinearFunOp α_G β_G F₇) then
          let F₇ ← instantiateMVars F₇
          let dup := mkApp3 (φ.getDecl ``HasNonLinearFunOp.dupFunFun) hHasNonLinearFunOp α_G β_G
          return ← constructLambdaAppFunctor φ f α_F₇ dup F₇
        let hHasFullFunOp ← φ.mkFreshDeclMVar ``HasFullFunOp
        let α_F₈ := φ.mkFunType α_G (φ.mkFunType α₁ β_G)
        let F₈ ← φ.mkFreshInstMVar α_F₈
        if ← isDefEq G' (mkApp6 (φ.getDecl ``HasFullFunOp.defSubstFun) hHasFullFunOp α_G α₁ β_G F₁ F₈) then
          let F₁ ← instantiateMVars F₁
          let F₈ ← instantiateMVars F₈
          let revSubst := mkApp5 (φ.getDecl ``HasFullFunOp.revSubstFunFun) hHasFullFunOp α_G α₁ β_G F₈
          return ← match ← f.exprAsConstant revSubst with
          | some revSubst =>
            constructLambdaAppFunctor φ f α_F₁ revSubst F₁
          | none =>
            let subst := mkApp5 (φ.getDecl ``HasFullFunOp.substFunFun) hHasFullFunOp α_G α₁ F₁ β_G
            constructLambdaAppFunctor φ f α_F₈ subst F₈
        if ← isDefEq G' (mkApp5 (φ.getDecl ``HasFullFunOp.defSubstFunFun) hHasFullFunOp α₁ α₂ F₃ α₃) then
          let F₃ ← instantiateMVars F₃
          let subst := mkApp4 (φ.getDecl ``HasFullFunOp.substFunFunFun) hHasFullFunOp α₁ α₂ α₃
          return ← constructLambdaAppFunctor φ f α_F₃ subst F₃
        let α_F₉ := φ.mkFunType α₁ (φ.mkFunType α₂ α₃)
        let F₉ ← φ.mkFreshInstMVar α_F₉
        if ← isDefEq G' (mkApp5 (φ.getDecl ``HasFullFunOp.defRevSubstFunFun) hHasFullFunOp α₁ α₂ α₃ F₉) then
          let F₉ ← instantiateMVars F₉
          let revSubst := mkApp4 (φ.getDecl ``HasFullFunOp.revSubstFunFunFun) hHasFullFunOp α₁ α₂ α₃
          return ← constructLambdaAppFunctor φ f α_F₉ revSubst F₉
        throwTacticEx `makeFunctor φ.mvarId m!"unsupported fromDefFun argument '{G'}'"

  end

  -- Construct a functor for a given function expression.
  -- If the expression is a lambda abstraction, we use its components directly; otherwise we
  -- convert it to a lambda abstraction with a lambda application in its body (which can hopefully
  -- be unfolded).

  def constructFunctor (φ : FunUniv) (α β α' β' : Expr) : Expr → MetaM Expr
    | Expr.lam n d b c => withLocalDecl n c.binderInfo d fun a =>
      let t := b.instantiate1 a
      constructLambdaFunctor φ ⟨α, β, a, t⟩
    | f => do
      let F ← φ.mkFreshInstMVar (φ.mkFunType α β)
      if ← isDefEq f (mkApp3 (φ.getDecl ``HasEmbeddedFunctors.funCoe) α β F) then
        return F
      let a := mkFVar (← mkFreshFVarId)
      withLocalDecl `a BinderInfo.default α' fun a =>
        let t := mkApp f a
        constructLambdaFunctor φ ⟨α, β, a, t⟩

  -- The `makeFunctor` tactic, which calls `constructFunctor` based on the target type and given
  -- term. Note that the target type determines how to elaborate the term, which enables us to omit
  -- the variable type in `Λ` expressions.

  def makeFunctor (mvarId : MVarId) (hf : Syntax) : TacticM Expr := do
    let type ← getMVarType mvarId
    let u ← mkFreshLevelMVar
    let w ← mkFreshLevelMVar
    let U ← mkFreshExprMVar (mkConst ``Universe [u])
    let h ← mkFreshExprMVar (mkApp (mkConst ``HasEmbeddedFunctors [u, w]) U)
    let U' := mkUniverseInst u U
    let φ' : FunUniv := ⟨mvarId, u, w, U, U', h⟩
    let α ← φ'.mkFreshTypeMVar
    let β ← φ'.mkFreshTypeMVar
    if ← isDefEq type (φ'.mkTypeInst (φ'.mkFunType α β)) then
      let u ← instantiateLevelMVars u
      let w ← instantiateLevelMVars w
      let U ← instantiateMVars U
      let U' ← instantiateMVars U'
      let h ← instantiateMVars h
      let α ← instantiateMVars α
      let β ← instantiateMVars β
      let φ : FunUniv := ⟨mvarId, u, w, U, U', h⟩
      let α' := φ.mkTypeInst α
      let β' := φ.mkTypeInst β
      let f ← elabTerm hf (← mkArrow α' β')
      return ← constructFunctor φ α β α' β' f
    throwTacticEx `makeFunctor mvarId m!"type '{type}' is not an application of 'HasEmbeddedFunctors.Fun'"

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
  -- Essentially, when asked to construct an instance of `α ⟶[f] β`, it outputs
  -- `(by makeFunctor f) ◄ λ _ => by simp`.

  def functoriality (mvarId : MVarId) : TacticM Expr := do
    let type ← getMVarType mvarId
    let u ← mkFreshLevelMVar
    let w ← mkFreshLevelMVar
    let U ← mkFreshExprMVar (mkConst ``Universe [u])
    let h ← mkFreshExprMVar (mkApp (mkConst ``HasEmbeddedFunctors [u, w]) U)
    let U' := mkUniverseInst u U
    let φ' : FunUniv := ⟨mvarId, u, w, U, U', h⟩
    let α ← φ'.mkFreshTypeMVar
    let β ← φ'.mkFreshTypeMVar
    let α' := φ'.mkTypeInst α
    let β' := φ'.mkTypeInst β
    let f ← mkFreshExprMVar (← mkArrow α' β')
    if ← isDefEq type (mkApp3 (φ'.getDecl ``HasEmbeddedFunctors.DefFun) α β f) then
      let u ← instantiateLevelMVars u
      let w ← instantiateLevelMVars w
      let U ← instantiateMVars U
      let U' ← instantiateMVars U'
      let h ← instantiateMVars h
      let α ← instantiateMVars α
      let β ← instantiateMVars β
      let α' ← instantiateMVars α'
      let β' ← instantiateMVars β'
      let f ← instantiateMVars f
      let φ : FunUniv := ⟨mvarId, u, w, U, U', h⟩
      let F ← constructFunctor φ α β α' β' f
      let hDefTypeBody := mkApp3 (mkConst ``Eq [u]) β' (mkApp4 (φ.getDecl ``HasEmbeddedFunctors.funCoe) α β F (mkBVar 0)) (mkApp f (mkBVar 0))
      let hDefType := mkForall `a BinderInfo.default α' hDefTypeBody
      let hDef ← elabTerm (← `(λ _ => by simp)) hDefType
      return mkApp5 (φ'.getDecl ``HasEmbeddedFunctors.toDefFun') α β F f hDef
    throwTacticEx `makeFunctor mvarId m!"type '{type}' is not an application of 'HasEmbeddedFunctors.DefFun'"

  elab "functoriality" : tactic => do
    let mvarId ← getMainGoal
    withMVarContext mvarId do
      let e ← functoriality mvarId
      assignExprMVar mvarId e

end Lean
