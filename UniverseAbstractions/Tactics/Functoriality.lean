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
--  `Λ a => T a`          | `a` not in `T` | `appFun T`, i.e. just `T`
--  `Λ a => T t`          | `a` not in `T` | `compFun (Λ a => t) T`
--  `Λ F => F t`          | `F` not in `t` | `revAppFun t _`
--  `Λ a => T t`          | `a` not in `t` | `swapFun (Λ a => T) t`
--  `Λ a => T a`          |                | `dupFun (Λ a => T)`
--  `Λ a => T t`          |                | `substFun (Λ a => t) (Λ a => T)`
--  `Λ a => ?Fun t₁...tₙ` |                | `Λ a => (?FunFun t₁...tₙ₋₁) tₙ`
--                        |                | (optimization: use `rev` if it makes `?FunFun` term
--                        |                | constant)
--
-- Although all cases of functor application inside the lambda body can be handled generically by
-- `substFun` (matching SKI combinator calculus), `substFun` requires `FullFunOp`, whereas
-- `compFun`, `revAppFun`, and `swapFun` only require `LinearFunOp` (corresponding to linear logic,
-- where each variable is used exactly once). So the special cases are not merely optimizations.



namespace Lean

  open Meta Elab Tactic

  -- Some helper code so that we can work with a `(U : Universe) [h : HasInternalFunctors U]` more
  -- easily in meta code.

  def mkHasInstancesInst (u v : Level) (U h A : Expr) : Expr :=
    mkApp3 (mkConst ``HasInstances.Inst [u, v]) U h A

  structure Univ where
  (u : Level)
  (U : Expr)

  namespace Univ

    def mkFreshUnivMVar : MetaM Univ := do
      let u ← mkFreshLevelMVar
      let U ← mkFreshExprMVar (mkConst ``Universe [u])
      return ⟨u, U⟩

    variable (U : Univ)

    def mkUniverseInst : Expr :=
      mkHasInstancesInst (mkLevelSucc U.u) (mkLevelSucc (mkLevelSucc U.u)) (mkConst ``Universe [U.u]) (mkConst ``Universe.hasInstances [U.u]) U.U

    def mkTypeInst (A : Expr) : Expr :=
      mkHasInstancesInst U.u (mkLevelSucc U.u) (mkUniverseInst U) (mkApp (mkConst ``Universe.instInst [U.u]) U.U) A

    def mkFreshTypeMVar: MetaM Expr :=
      mkFreshExprMVar U.mkUniverseInst

    def mkFreshInstMVar (A : Expr) : MetaM Expr :=
      mkFreshExprMVar (U.mkTypeInst A)

    def instantiateVars : MetaM Univ := do
      let u ← instantiateLevelMVars U.u
      let U ← instantiateMVars U.U
      return ⟨u, U⟩

  end Univ

  structure FunUniv where
  (U        : Univ)
  (iu       : Level)
  (hId hFun : Expr)

  namespace FunUniv

    def mkFreshFunUnivMVar : MetaM FunUniv := do
      let U ← Univ.mkFreshUnivMVar
      let iu ← mkFreshLevelMVar
      let hId ← mkFreshExprMVar (mkApp (mkConst ``HasIdentity [U.u, iu]) U.U)
      let hFun ← mkFreshExprMVar (mkApp2 (mkConst ``HasInternalFunctors [U.u, iu]) U.U hId)
      return ⟨U, iu, hId, hFun⟩

    variable (φ : FunUniv)

    def getDecl (n : Name) : Expr :=
      mkApp3 (mkConst n [φ.U.u, φ.iu]) φ.U.U φ.hId φ.hFun

    def mkFunType (A B : Expr) : Expr :=
      mkApp2 (φ.getDecl ``HasInternalFunctors.Helpers.Fun) A B

    def mkFreshDeclMVar (n : Name) : MetaM Expr :=
      mkFreshExprMVar (φ.getDecl n)

    def instantiateVars : MetaM FunUniv := do
      let U ← φ.U.instantiateVars
      let iu ← instantiateLevelMVars φ.iu
      let hId ← instantiateMVars φ.hId
      let hFun ← instantiateMVars φ.hFun
      return ⟨U, iu, hId, hFun⟩

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

  structure FunctorialityData where
  (mvarId : MVarId)
  (φ      : FunUniv)
  (f      : LambdaAbstr)

  -- The actual algorithm is implemented as a set of mutually recursive functions.
  -- Of these, `constructLambdaFunctor` is the main entry point (called by `constructFunctor`
  -- below); it returns a functor for the lambda expression given by `f`. If the body of `f`
  -- is a functor application, it is analyzed and handled by `constructLambdaAppFunctor`. If it is
  -- an application of `fromDefFun`, `constructLambdaDefFunFunctor` handles that; in most cases we
  -- are dealing with some primitive or derived `...Fun` (the last case in the algorithm).

  mutual

    -- The main entry point, which handles `constFun` and `idFun` directly, and calls either
    -- `constructLambdaAppFunctor` or `constructLambdaDefFunFunctor` otherwise.

    partial def constructLambdaFunctor (φ : FunctorialityData) : MetaM Expr := do
      match ← φ.f.asConstant with
      | some t => do
        let hHasSubLinearFunOp ← synthInstance (φ.φ.getDecl ``HasSubLinearFunOp)
        mkApp4 (φ.φ.getDecl ``HasSubLinearFunOp.constFun) hHasSubLinearFunOp φ.f.A φ.f.B t
      | none => do
        if ← φ.f.isId then
          let hHasLinearFunOp ← synthInstance (φ.φ.getDecl ``HasLinearFunOp)
          return mkApp2 (φ.φ.getDecl ``HasLinearFunOp.idFun) hHasLinearFunOp φ.f.A
        let B_b ← φ.φ.U.mkFreshTypeMVar
        let G ← φ.φ.U.mkFreshInstMVar (φ.φ.mkFunType B_b φ.f.B)
        let b ← φ.φ.U.mkFreshInstMVar B_b
        if ← isDefEq φ.f.t (mkApp4 (φ.φ.getDecl ``HasInternalFunctors.Helpers.apply) B_b φ.f.B G b) then
          let G ← instantiateMVars G
          let b ← instantiateMVars b
          return ← constructLambdaAppFunctor φ B_b G b
        let A_G ← φ.φ.U.mkFreshTypeMVar
        let B_G ← φ.φ.U.mkFreshTypeMVar
        let g ← mkFreshExprMVar (← mkArrow (φ.φ.U.mkTypeInst A_G) (φ.φ.U.mkTypeInst B_G))
        let G' ← mkFreshExprMVar (mkApp3 (φ.φ.getDecl ``HasInternalFunctors.Helpers.DefFun) A_G B_G g)
        if ← isDefEq φ.f.t (mkApp4 (φ.φ.getDecl ``HasInternalFunctors.Helpers.fromDefFun) A_G B_G g G') then
          let g ← instantiateMVars g
          let G' ← instantiateMVars G'
          return ← constructLambdaDefFunFunctor φ A_G B_G g G'
        throwTacticEx `makeFunctor φ.mvarId m!"unsupported lambda body '{φ.f.t}'"

    -- This function handles the different cases of functor application in the lambda body,
    -- depending on which parts are either equal to the lambda variable or constant with respect
    -- to it. (Note that we do not optimize the case where both parts are constant, since that
    -- should have been handled already.)

    partial def constructLambdaAppFunctor (φ : FunctorialityData) (B_b G b : Expr) : MetaM Expr :=
      withDefault do
        let B_G := φ.φ.mkFunType B_b φ.f.B
        let f_G : LambdaAbstr := ⟨φ.f.A, B_G, φ.f.a, G⟩
        let f_b : LambdaAbstr := ⟨φ.f.A, B_b, φ.f.a, b⟩
        let hHasLinearFunOp ← synthInstance (φ.φ.getDecl ``HasLinearFunOp)
        match ← f_G.asConstant with
        | some G => do
          if ← f_b.isId then
            return G
          let F_b ← constructLambdaFunctor ⟨φ.mvarId, φ.φ, f_b⟩
          -- TODO: Write as `trans` to enable notation.
          return mkApp6 (φ.φ.getDecl ``HasLinearFunOp.compFun) hHasLinearFunOp φ.f.A B_b φ.f.B F_b G
        | none => do
          match ← f_b.asConstant with
          | some b => do
            if ← f_G.isId then
              return mkApp4 (φ.φ.getDecl ``HasLinearFunOp.revAppFun) hHasLinearFunOp B_b b φ.f.B
            let F_G ← constructLambdaFunctor ⟨φ.mvarId, φ.φ, f_G⟩
            return mkApp6 (φ.φ.getDecl ``HasLinearFunOp.swapFun) hHasLinearFunOp φ.f.A B_b φ.f.B F_G b
          | none => do
            let F_G ← constructLambdaFunctor ⟨φ.mvarId, φ.φ, f_G⟩
            if ← f_b.isId then
              let hHasNonLinearFunOp ← synthInstance (φ.φ.getDecl ``HasNonLinearFunOp)
              return mkApp4 (φ.φ.getDecl ``HasNonLinearFunOp.dupFun) hHasNonLinearFunOp φ.f.A φ.f.B F_G
            let F_b ← constructLambdaFunctor ⟨φ.mvarId, φ.φ, f_b⟩
            let hHasFullFunOp ← synthInstance (φ.φ.getDecl ``HasFullFunOp)
            return mkApp6 (φ.φ.getDecl ``HasFullFunOp.substFun) hHasFullFunOp φ.f.A B_b φ.f.B F_b F_G

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

    -- TODO: Use `IsFunApp` type class instead, or a variant thereof.

    partial def constructLambdaDefFunFunctor (φ : FunctorialityData) (A_G B_G g G' : Expr) : MetaM Expr := do
      let G ← φ.φ.U.mkFreshInstMVar (φ.φ.mkFunType A_G B_G)
      if ← isDefEq G' (mkApp3 (φ.φ.getDecl ``HasInternalFunctors.Helpers.toDefFun) A_G B_G G) then
        let G ← instantiateMVars G
        return ← constructLambdaFunctor ⟨φ.mvarId, φ.φ, ⟨φ.f.A, φ.f.B, φ.f.a, G⟩⟩
      withReducible do
        let hHasSubLinearFunOp ← φ.φ.mkFreshDeclMVar ``HasSubLinearFunOp
        let b ← φ.φ.U.mkFreshInstMVar B_G
        if ← isDefEq G' (mkApp4 (φ.φ.getDecl ``HasSubLinearFunOp.defConstFun) hHasSubLinearFunOp A_G B_G b) then
          let b ← instantiateMVars b
          let const := mkApp3 (φ.φ.getDecl ``HasSubLinearFunOp.constFunFun) hHasSubLinearFunOp A_G B_G
          return ← constructLambdaAppFunctor φ B_G const b
        let hHasLinearFunOp ← φ.φ.mkFreshDeclMVar ``HasLinearFunOp
        let A₁ ← φ.φ.U.mkFreshTypeMVar
        let a₁ ← φ.φ.U.mkFreshInstMVar A₁
        if ← isDefEq G' (mkApp4 (φ.φ.getDecl ``HasLinearFunOp.defRevAppFun) hHasLinearFunOp A₁ a₁ B_G) then
          let a₁ ← instantiateMVars a₁
          let app := mkApp3 (φ.φ.getDecl ``HasLinearFunOp.revAppFunFun) hHasLinearFunOp A₁ B_G
          return ← constructLambdaAppFunctor φ A₁ app a₁
        let A_F₁ := φ.φ.mkFunType A_G A₁
        let A_F₂ := φ.φ.mkFunType A₁ B_G
        let F₁ ← φ.φ.U.mkFreshInstMVar A_F₁
        let F₂ ← φ.φ.U.mkFreshInstMVar A_F₂
        if ← isDefEq G' (mkApp6 (φ.φ.getDecl ``HasLinearFunOp.defCompFun) hHasLinearFunOp A_G A₁ B_G F₁ F₂) then
          let F₁ ← instantiateMVars F₁
          let F₂ ← instantiateMVars F₂
          let comp := mkApp5 (φ.φ.getDecl ``HasLinearFunOp.compFunFun) hHasLinearFunOp A_G A₁ F₁ B_G
          return ← match ← φ.f.exprAsConstant comp with
          | some comp =>
            constructLambdaAppFunctor φ A_F₂ comp F₂
          | none =>
            let revComp := mkApp5 (φ.φ.getDecl ``HasLinearFunOp.revCompFunFun) hHasLinearFunOp A_G A₁ B_G F₂
            constructLambdaAppFunctor φ A_F₁ revComp F₁
        let A₂ ← φ.φ.U.mkFreshTypeMVar
        let A₃ ← φ.φ.U.mkFreshTypeMVar
        let A_F₃ := φ.φ.mkFunType A₁ A₂
        let F₃ ← φ.φ.U.mkFreshInstMVar A_F₃
        if ← isDefEq G' (mkApp5 (φ.φ.getDecl ``HasLinearFunOp.defCompFunFun) hHasLinearFunOp A₁ A₂ F₃ A₃) then
          let F₃ ← instantiateMVars F₃
          let comp := mkApp4 (φ.φ.getDecl ``HasLinearFunOp.compFunFunFun) hHasLinearFunOp A₁ A₂ A₃
          return ← constructLambdaAppFunctor φ A_F₃ comp F₃
        let A_F₄ := φ.φ.mkFunType A₂ A₃
        let F₄ ← φ.φ.U.mkFreshInstMVar A_F₄
        if ← isDefEq G' (mkApp5 (φ.φ.getDecl ``HasLinearFunOp.defRevCompFunFun) hHasLinearFunOp A₁ A₂ A₃ F₄) then
          let F₄ ← instantiateMVars F₄
          let revComp := mkApp4 (φ.φ.getDecl ``HasLinearFunOp.revCompFunFunFun) hHasLinearFunOp A₁ A₂ A₃
          return ← constructLambdaAppFunctor φ A_F₄ revComp F₄
        let A_F₅ := φ.φ.mkFunType A_G (φ.φ.mkFunType A₁ B_G)
        let F₅ ← φ.φ.U.mkFreshInstMVar A_F₅
        if ← isDefEq G' (mkApp6 (φ.φ.getDecl ``HasLinearFunOp.defSwapFun) hHasLinearFunOp A_G A₁ B_G F₅ a₁) then
          let F₅ ← instantiateMVars F₅
          let a₁ ← instantiateMVars a₁
          let swap := mkApp5 (φ.φ.getDecl ``HasLinearFunOp.swapFunFun) hHasLinearFunOp A_G A₁ B_G F₅
          return ← match ← φ.f.exprAsConstant swap with
          | some swap =>
            constructLambdaAppFunctor φ A₁ swap a₁
          | none =>
            let revSwap := mkApp5 (φ.φ.getDecl ``HasLinearFunOp.revSwapFunFun) hHasLinearFunOp A_G A₁ a₁ B_G
            constructLambdaAppFunctor φ A_F₅ revSwap F₅
        let A_F₆ := φ.φ.mkFunType A₁ (φ.φ.mkFunType A_G A₂)
        let F₆ ← φ.φ.U.mkFreshInstMVar A_F₆
        if ← isDefEq G' (mkApp5 (φ.φ.getDecl ``HasLinearFunOp.defSwapFunFun) hHasLinearFunOp A₁ A_G A₂ F₆) then
          let F₆ ← instantiateMVars F₆
          let swap := mkApp4 (φ.φ.getDecl ``HasLinearFunOp.swapFunFunFun) hHasLinearFunOp A₁ A_G A₂
          return ← constructLambdaAppFunctor φ A_F₆ swap F₆
        let a₂ ← φ.φ.U.mkFreshInstMVar A₂
        if ← isDefEq G' (mkApp5 (φ.φ.getDecl ``HasLinearFunOp.defRevSwapFunFun) hHasLinearFunOp A₁ A₂ a₂ A₃) then
          let a₂ ← instantiateMVars a₂
          let revSwap := mkApp4 (φ.φ.getDecl ``HasLinearFunOp.revSwapFunFunFun) hHasLinearFunOp A₁ A₂ A₃
          return ← constructLambdaAppFunctor φ A₂ revSwap a₂
        let hHasNonLinearFunOp ← φ.φ.mkFreshDeclMVar ``HasNonLinearFunOp
        let A_F₇ := φ.φ.mkFunType A_G (φ.φ.mkFunType A_G B_G)
        let F₇ ← φ.φ.U.mkFreshInstMVar A_F₇
        if ← isDefEq G' (mkApp4 (φ.φ.getDecl ``HasNonLinearFunOp.defDupFun) hHasNonLinearFunOp A_G B_G F₇) then
          let F₇ ← instantiateMVars F₇
          let dup := mkApp3 (φ.φ.getDecl ``HasNonLinearFunOp.dupFunFun) hHasNonLinearFunOp A_G B_G
          return ← constructLambdaAppFunctor φ A_F₇ dup F₇
        let hHasFullFunOp ← φ.φ.mkFreshDeclMVar ``HasFullFunOp
        let A_F₈ := φ.φ.mkFunType A_G (φ.φ.mkFunType A₁ B_G)
        let F₈ ← φ.φ.U.mkFreshInstMVar A_F₈
        if ← isDefEq G' (mkApp6 (φ.φ.getDecl ``HasFullFunOp.defSubstFun) hHasFullFunOp A_G A₁ B_G F₁ F₈) then
          let F₁ ← instantiateMVars F₁
          let F₈ ← instantiateMVars F₈
          let subst := mkApp5 (φ.φ.getDecl ``HasFullFunOp.substFunFun) hHasFullFunOp A_G A₁ F₁ B_G
          return ← match ← φ.f.exprAsConstant subst with
          | some subst =>
            constructLambdaAppFunctor φ A_F₈ subst F₈
          | none =>
            let revSubst := mkApp5 (φ.φ.getDecl ``HasFullFunOp.revSubstFunFun) hHasFullFunOp A_G A₁ B_G F₈
            constructLambdaAppFunctor φ A_F₁ revSubst F₁
        if ← isDefEq G' (mkApp5 (φ.φ.getDecl ``HasFullFunOp.defSubstFunFun) hHasFullFunOp A₁ A₂ F₃ A₃) then
          let F₃ ← instantiateMVars F₃
          let subst := mkApp4 (φ.φ.getDecl ``HasFullFunOp.substFunFunFun) hHasFullFunOp A₁ A₂ A₃
          return ← constructLambdaAppFunctor φ A_F₃ subst F₃
        let A_F₉ := φ.φ.mkFunType A₁ (φ.φ.mkFunType A₂ A₃)
        let F₉ ← φ.φ.U.mkFreshInstMVar A_F₉
        if ← isDefEq G' (mkApp5 (φ.φ.getDecl ``HasFullFunOp.defRevSubstFunFun) hHasFullFunOp A₁ A₂ A₃ F₉) then
          let F₉ ← instantiateMVars F₉
          let revSubst := mkApp4 (φ.φ.getDecl ``HasFullFunOp.revSubstFunFunFun) hHasFullFunOp A₁ A₂ A₃
          return ← constructLambdaAppFunctor φ A_F₉ revSubst F₉
        throwTacticEx `makeFunctor φ.mvarId m!"unsupported fromDefFun argument '{G'}'"

  end

  -- Construct a functor for a given function expression.
  -- If the expression is a lambda abstraction, we use its components directly; otherwise we
  -- convert it to a lambda abstraction with a lambda application in its body (which can hopefully
  -- be unfolded).

  def constructFunctor (mvarId : MVarId) (φ : FunUniv) (A B A' B' : Expr) : Expr → MetaM Expr
    | Expr.lam n d b c => withLocalDecl n c.binderInfo d fun a =>
      let t := b.instantiate1 a
      constructLambdaFunctor ⟨mvarId, φ, ⟨A, B, a, t⟩⟩
    | f => do
      let F ← φ.U.mkFreshInstMVar (φ.mkFunType A B)
      if ← isDefEq f (mkApp3 (φ.getDecl ``HasInternalFunctors.Helpers.apply) A B F) then
        return F
      let a := mkFVar (← mkFreshFVarId)
      withLocalDecl `a BinderInfo.default A' fun a =>
        let t := mkApp f a
        constructLambdaFunctor ⟨mvarId, φ, ⟨A, B, a, t⟩⟩

  -- The `makeFunctor` tactic, which calls `constructFunctor` based on the target type and given
  -- term. Note that the target type determines how to elaborate the term, which enables us to omit
  -- the variable type in `Λ` expressions.

  def makeFunctor (mvarId : MVarId) (hf : Syntax) : TacticM Expr := do
    let type ← getMVarType mvarId
    let φ ← FunUniv.mkFreshFunUnivMVar
    let A ← φ.U.mkFreshTypeMVar
    let B ← φ.U.mkFreshTypeMVar
    if ← isDefEq type (φ.U.mkTypeInst (φ.mkFunType A B)) then
      let φ ← φ.instantiateVars
      let A ← instantiateMVars A
      let B ← instantiateMVars B
      let A' := φ.U.mkTypeInst A
      let B' := φ.U.mkTypeInst B
      let f ← elabTerm hf (← mkArrow A' B')
      return ← constructFunctor mvarId φ A B A' B' f
    throwTacticEx `makeFunctor mvarId m!"type '{type}' is not an application of 'HasInternalFunctors.Helpers.Fun'"

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
           | Syntax.node info kind args => do
             let args ← args.sequenceMap replaceMkFun
             Syntax.node info kind args
           | _ => f

  macro "Λ" xs:explicitBinders " => " b:term : term => do
    let f ← expandExplicitBinders `__mkFun xs b
    replaceMkFun f

  -- The `functoriality` tactic, which constructs instances of `DefFun`.
  -- Essentially, when asked to construct an instance of `A ⟶{f} B`, it outputs
  -- `(by makeFunctor f) ◄ λ _ => by simp`.

  def functoriality (mvarId : MVarId) : TacticM Expr := do
    let type ← getMVarType mvarId
    let φ ← FunUniv.mkFreshFunUnivMVar
    let A ← φ.U.mkFreshTypeMVar
    let B ← φ.U.mkFreshTypeMVar
    let A' := φ.U.mkTypeInst A
    let B' := φ.U.mkTypeInst B
    let f ← mkFreshExprMVar (← mkArrow A' B')
    if ← isDefEq type (mkApp3 (φ.getDecl ``HasInternalFunctors.Helpers.DefFun) A B f) then
      let φ ← φ.instantiateVars
      let A ← instantiateMVars A
      let B ← instantiateMVars B
      let A' ← instantiateMVars A'
      let B' ← instantiateMVars B'
      let f ← instantiateMVars f
      let F ← constructFunctor mvarId φ A B A' B' f
      let hDefTypeBody := mkApp3 (mkConst ``Eq [φ.U.u]) B' (mkApp4 (φ.getDecl ``HasInternalFunctors.Helpers.apply) A B F (mkBVar 0)) (mkApp f (mkBVar 0))
      let hDefType := mkForall `a BinderInfo.default A' hDefTypeBody
      let hDef ← elabTerm (← `(λ _ => by simp [HasInternalFunctors.Helpers.apply])) hDefType
      return mkApp5 (φ.getDecl ``HasInternalFunctors.Helpers.toDefFun') A B F f hDef
    throwTacticEx `makeFunctor mvarId m!"type '{type}' is not an application of 'HasInternalFunctors.Helpers.DefFun'"

  elab "functoriality" : tactic => do
    let mvarId ← getMainGoal
    withMVarContext mvarId do
      let e ← functoriality mvarId
      assignExprMVar mvarId e

end Lean
