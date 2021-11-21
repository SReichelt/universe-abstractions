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

  -- Some helper code so that we can work with universes more easily in meta code.

  @[reducible] def TypedExpr (type : Expr) := Expr

  namespace TypedExpr

    instance : CoeSort Expr Type := ⟨TypedExpr⟩

    def mkFreshMVar {type : Expr} : MetaM type :=
      mkFreshExprMVar type

    def instantiate {type : Expr} (e : type) : MetaM type :=
      instantiateMVars e

    def elaborate {type : Expr} (stx : Syntax) : TacticM type :=
      elabTerm stx type

  end TypedExpr

  def mkHasInstancesInst {u v : Level} {I : mkSort v} (h : mkApp (mkConst ``HasInstances [u, v]) I)
                         (A : I) :
      mkSort u :=
    mkApp3 (mkConst ``HasInstances.Inst [u, v]) I h A

  def universeHasInstances (u : Level) :
      mkApp (mkConst ``HasInstances [mkLevelSucc u, mkLevelSucc (mkLevelSucc u)]) (mkConst ``Universe [u]) :=
    mkConst ``Universe.hasInstances [u]

  structure MetaUniverse where
  {u : Level}
  (U : mkConst ``Universe [u])

  namespace MetaUniverse

    def mkFreshMVar : MetaM MetaUniverse := do
      let u ← mkFreshLevelMVar
      let U : mkConst ``Universe [u] ← TypedExpr.mkFreshMVar
      return ⟨U⟩

    def instantiate (U : MetaUniverse) : MetaM MetaUniverse := do
      let u ← instantiateLevelMVars U.u
      let U : mkConst ``Universe [u] ← U.U.instantiate
      return ⟨U⟩

    def mkUniverseInst (U : MetaUniverse) : mkSort (mkLevelSucc U.u) :=
      mkHasInstancesInst (universeHasInstances U.u) U.U

    instance : CoeSort MetaUniverse Type := ⟨λ U => TypedExpr U.mkUniverseInst⟩

    def mkFreshTypeMVar (U : MetaUniverse) : MetaM U :=
      TypedExpr.mkFreshMVar

    def mkTypeInst {U : MetaUniverse} (A : U) : mkSort U.u :=
      mkHasInstancesInst (mkApp (mkConst ``Universe.instInst [U.u]) U.U) A

    instance (U : MetaUniverse) : CoeSort U Type := ⟨λ A => TypedExpr (U.mkTypeInst A)⟩

    def mkFreshInstMVar {U : MetaUniverse} (A : U) : MetaM A :=
      TypedExpr.mkFreshMVar

  end MetaUniverse

  structure MetaInternalFunctors where
  (U    : MetaUniverse)
  {iu   : Level}
  (hId  : mkApp (mkConst ``HasIdentity [U.u, iu]) U.U)
  (hFun : mkApp2 (mkConst ``HasInternalFunctors [U.u, iu]) U.U hId)

  namespace MetaInternalFunctors

    def mkFreshMVar : MetaM MetaInternalFunctors := do
      let U ← MetaUniverse.mkFreshMVar
      let iu ← mkFreshLevelMVar
      let hId : mkApp (mkConst ``HasIdentity [U.u, iu]) U.U ← TypedExpr.mkFreshMVar
      let hFun : mkApp2 (mkConst ``HasInternalFunctors [U.u, iu]) U.U hId ← TypedExpr.mkFreshMVar
      return ⟨U, hId, hFun⟩

    def instantiate (φ : MetaInternalFunctors) : MetaM MetaInternalFunctors := do
      let U ← φ.U.instantiate
      let iu ← instantiateLevelMVars φ.iu
      let hId : mkApp (mkConst ``HasIdentity [U.u, iu]) U.U ← φ.hId.instantiate
      let hFun : mkApp2 (mkConst ``HasInternalFunctors [U.u, iu]) U.U hId ← φ.hFun.instantiate
      return ⟨U, hId, hFun⟩

    def getDecl (φ : MetaInternalFunctors) (n : Name) : Expr :=
      mkApp3 (mkConst n [φ.U.u, φ.iu]) φ.U.U φ.hId φ.hFun

    def mkFreshDeclMVar (φ : MetaInternalFunctors) (n : Name) : MetaM (φ.getDecl n) :=
      TypedExpr.mkFreshMVar

    def mkFunType {φ : MetaInternalFunctors} (A B : φ.U) : φ.U :=
      mkApp2 (φ.getDecl ``HasInternalFunctors.Helpers.Fun) A B

    def mkFunArrow {φ : MetaInternalFunctors} (A B : φ.U) : Expr :=
      mkForall `_ BinderInfo.default (φ.U.mkTypeInst A) (φ.U.mkTypeInst B)

    def mkDefFunType {φ : MetaInternalFunctors} (A B : φ.U) (f : mkFunArrow A B) : Expr :=
      mkApp3 (φ.getDecl ``HasInternalFunctors.Helpers.DefFun) A B f

  end MetaInternalFunctors

  -- A function that has been transformed into a lambda abstraction that we can work with more
  -- easily. In particular, the lambda variable `a` is an `FVar`, so that `t` does not contain any
  -- loose bound variables. This is required for Lean algorithms such as `isDefEq` to work.

  structure LambdaAbstr (φ : MetaInternalFunctors) where
  {A B : φ.U}
  (a   : A)
  (t   : B)

  namespace LambdaAbstr

    variable {φ : MetaInternalFunctors}

    def mkFunType (f : LambdaAbstr φ) : φ.U :=
      φ.mkFunType f.A f.B

    def exprAsConstant (f : LambdaAbstr φ) (t : f.B) : MetaM (Option f.B) := do
      if !(t.containsFVar f.a.fvarId!) then
        return t
      let t' : f.B ← reduce t
      if !(t'.containsFVar f.a.fvarId!) then
        return t'
      none

    def asConstant (f : LambdaAbstr φ) : MetaM (Option f.B) := f.exprAsConstant f.t

    def isId (f : LambdaAbstr φ) : MetaM Bool := isDefEq f.t f.a

  end LambdaAbstr

  structure FunctorialityData where
  (mvarId : MVarId)
  (φ      : MetaInternalFunctors)
  (f      : LambdaAbstr φ)

  -- The actual algorithm is implemented as a set of mutually recursive functions.
  -- Of these, `constructLambdaFunctor` is the main entry point (called by `constructFunctor`
  -- below); it returns a functor for the lambda expression given by `f`. If the body of `f`
  -- is a functor application, it is analyzed and handled by `constructLambdaAppFunctor`. If it is
  -- an application of `fromDefFun`, `constructLambdaDefFunFunctor` handles that; in most cases we
  -- are dealing with some primitive or derived `...Fun` (the last case in the algorithm).

  mutual

    -- The main entry point, which handles `constFun` and `idFun` directly, and calls either
    -- `constructLambdaAppFunctor` or `constructLambdaDefFunFunctor` otherwise.

    partial def constructLambdaFunctor (φ : FunctorialityData) : MetaM φ.f.mkFunType := do
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
          let G ← G.instantiate
          let b ← b.instantiate
          return ← constructLambdaAppFunctor φ G b
        let A_G ← φ.φ.U.mkFreshTypeMVar
        let B_G ← φ.φ.U.mkFreshTypeMVar
        let g : φ.φ.mkFunArrow A_G B_G ← TypedExpr.mkFreshMVar
        let G' : φ.φ.mkDefFunType A_G B_G g ← TypedExpr.mkFreshMVar
        if ← isDefEq φ.f.t (mkApp4 (φ.φ.getDecl ``HasInternalFunctors.Helpers.fromDefFun) A_G B_G g G') then
          let g ← g.instantiate
          let G' ← G'.instantiate
          return ← constructLambdaDefFunFunctor φ g G'
        throwTacticEx `makeFunctor φ.mvarId m!"unsupported lambda body '{φ.f.t}'"

    -- This function handles the different cases of functor application in the lambda body,
    -- depending on which parts are either equal to the lambda variable or constant with respect
    -- to it. (Note that we do not optimize the case where both parts are constant, since that
    -- should have been handled already.)

    partial def constructLambdaAppFunctor (φ : FunctorialityData) {B_b : φ.φ.U}
                                          (G : φ.φ.mkFunType B_b φ.f.B) (b : B_b) :
                MetaM φ.f.mkFunType :=
      withDefault do
        let f_G : LambdaAbstr φ.φ := ⟨φ.f.a, G⟩
        let f_b : LambdaAbstr φ.φ := ⟨φ.f.a, b⟩
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

    partial def constructLambdaDefFunFunctor (φ : FunctorialityData) {A_G B_G : φ.φ.U}
                                             (g : φ.φ.mkFunArrow A_G B_G)
                                             (G' : φ.φ.mkDefFunType A_G B_G g) :
                MetaM Expr := do
      let G ← φ.φ.U.mkFreshInstMVar (φ.φ.mkFunType A_G B_G)
      if ← isDefEq G' (mkApp3 (φ.φ.getDecl ``HasInternalFunctors.Helpers.toDefFun) A_G B_G G) then
        let G ← G.instantiate
        return ← constructLambdaFunctor ⟨φ.mvarId, φ.φ, ⟨φ.f.a, G⟩⟩
      withReducible do
        let hHasSubLinearFunOp ← φ.φ.mkFreshDeclMVar ``HasSubLinearFunOp
        let b ← φ.φ.U.mkFreshInstMVar B_G
        if ← isDefEq G' (mkApp4 (φ.φ.getDecl ``HasSubLinearFunOp.defConstFun) hHasSubLinearFunOp A_G B_G b) then
          let b ← b.instantiate
          let const := mkApp3 (φ.φ.getDecl ``HasSubLinearFunOp.constFunFun) hHasSubLinearFunOp A_G B_G
          return ← constructLambdaAppFunctor φ const b
        let hHasLinearFunOp ← φ.φ.mkFreshDeclMVar ``HasLinearFunOp
        let A₁ ← φ.φ.U.mkFreshTypeMVar
        let a₁ ← φ.φ.U.mkFreshInstMVar A₁
        if ← isDefEq G' (mkApp4 (φ.φ.getDecl ``HasLinearFunOp.defRevAppFun) hHasLinearFunOp A₁ a₁ B_G) then
          let a₁ ← a₁.instantiate
          let app := mkApp3 (φ.φ.getDecl ``HasLinearFunOp.revAppFunFun) hHasLinearFunOp A₁ B_G
          return ← constructLambdaAppFunctor φ app a₁
        let A_F₁ := φ.φ.mkFunType A_G A₁
        let A_F₂ := φ.φ.mkFunType A₁ B_G
        let F₁ ← φ.φ.U.mkFreshInstMVar A_F₁
        let F₂ ← φ.φ.U.mkFreshInstMVar A_F₂
        if ← isDefEq G' (mkApp6 (φ.φ.getDecl ``HasLinearFunOp.defCompFun) hHasLinearFunOp A_G A₁ B_G F₁ F₂) then
          let F₁ ← F₁.instantiate
          let F₂ ← F₂.instantiate
          let comp := mkApp5 (φ.φ.getDecl ``HasLinearFunOp.compFunFun) hHasLinearFunOp A_G A₁ F₁ B_G
          return ← match ← φ.f.exprAsConstant comp with
          | some comp =>
            constructLambdaAppFunctor φ comp F₂
          | none =>
            let revComp := mkApp5 (φ.φ.getDecl ``HasLinearFunOp.revCompFunFun) hHasLinearFunOp A_G A₁ B_G F₂
            constructLambdaAppFunctor φ revComp F₁
        let A₂ ← φ.φ.U.mkFreshTypeMVar
        let A₃ ← φ.φ.U.mkFreshTypeMVar
        let A_F₃ := φ.φ.mkFunType A₁ A₂
        let F₃ ← φ.φ.U.mkFreshInstMVar A_F₃
        if ← isDefEq G' (mkApp5 (φ.φ.getDecl ``HasLinearFunOp.defCompFunFun) hHasLinearFunOp A₁ A₂ F₃ A₃) then
          let F₃ ← F₃.instantiate
          let comp := mkApp4 (φ.φ.getDecl ``HasLinearFunOp.compFunFunFun) hHasLinearFunOp A₁ A₂ A₃
          return ← constructLambdaAppFunctor φ comp F₃
        let A_F₄ := φ.φ.mkFunType A₂ A₃
        let F₄ ← φ.φ.U.mkFreshInstMVar A_F₄
        if ← isDefEq G' (mkApp5 (φ.φ.getDecl ``HasLinearFunOp.defRevCompFunFun) hHasLinearFunOp A₁ A₂ A₃ F₄) then
          let F₄ ← F₄.instantiate
          let revComp := mkApp4 (φ.φ.getDecl ``HasLinearFunOp.revCompFunFunFun) hHasLinearFunOp A₁ A₂ A₃
          return ← constructLambdaAppFunctor φ revComp F₄
        let A_F₅ := φ.φ.mkFunType A_G (φ.φ.mkFunType A₁ B_G)
        let F₅ ← φ.φ.U.mkFreshInstMVar A_F₅
        if ← isDefEq G' (mkApp6 (φ.φ.getDecl ``HasLinearFunOp.defSwapFun) hHasLinearFunOp A_G A₁ B_G F₅ a₁) then
          let F₅ ← F₅.instantiate
          let a₁ ← a₁.instantiate
          let swap := mkApp5 (φ.φ.getDecl ``HasLinearFunOp.swapFunFun) hHasLinearFunOp A_G A₁ B_G F₅
          return ← match ← φ.f.exprAsConstant swap with
          | some swap =>
            constructLambdaAppFunctor φ swap a₁
          | none =>
            let revSwap := mkApp5 (φ.φ.getDecl ``HasLinearFunOp.revSwapFunFun) hHasLinearFunOp A_G A₁ a₁ B_G
            constructLambdaAppFunctor φ revSwap F₅
        let A_F₆ := φ.φ.mkFunType A₁ (φ.φ.mkFunType A_G A₂)
        let F₆ ← φ.φ.U.mkFreshInstMVar A_F₆
        if ← isDefEq G' (mkApp5 (φ.φ.getDecl ``HasLinearFunOp.defSwapFunFun) hHasLinearFunOp A₁ A_G A₂ F₆) then
          let F₆ ← F₆.instantiate
          let swap := mkApp4 (φ.φ.getDecl ``HasLinearFunOp.swapFunFunFun) hHasLinearFunOp A₁ A_G A₂
          return ← constructLambdaAppFunctor φ swap F₆
        let a₂ ← φ.φ.U.mkFreshInstMVar A₂
        if ← isDefEq G' (mkApp5 (φ.φ.getDecl ``HasLinearFunOp.defRevSwapFunFun) hHasLinearFunOp A₁ A₂ a₂ A₃) then
          let a₂ ← a₂.instantiate
          let revSwap := mkApp4 (φ.φ.getDecl ``HasLinearFunOp.revSwapFunFunFun) hHasLinearFunOp A₁ A₂ A₃
          return ← constructLambdaAppFunctor φ revSwap a₂
        let hHasNonLinearFunOp ← φ.φ.mkFreshDeclMVar ``HasNonLinearFunOp
        let A_F₇ := φ.φ.mkFunType A_G (φ.φ.mkFunType A_G B_G)
        let F₇ ← φ.φ.U.mkFreshInstMVar A_F₇
        if ← isDefEq G' (mkApp4 (φ.φ.getDecl ``HasNonLinearFunOp.defDupFun) hHasNonLinearFunOp A_G B_G F₇) then
          let F₇ ← F₇.instantiate
          let dup := mkApp3 (φ.φ.getDecl ``HasNonLinearFunOp.dupFunFun) hHasNonLinearFunOp A_G B_G
          return ← constructLambdaAppFunctor φ dup F₇
        let hHasFullFunOp ← φ.φ.mkFreshDeclMVar ``HasFullFunOp
        let A_F₈ := φ.φ.mkFunType A_G (φ.φ.mkFunType A₁ B_G)
        let F₈ ← φ.φ.U.mkFreshInstMVar A_F₈
        if ← isDefEq G' (mkApp6 (φ.φ.getDecl ``HasFullFunOp.defSubstFun) hHasFullFunOp A_G A₁ B_G F₁ F₈) then
          let F₁ ← F₁.instantiate
          let F₈ ← F₈.instantiate
          let subst := mkApp5 (φ.φ.getDecl ``HasFullFunOp.substFunFun) hHasFullFunOp A_G A₁ F₁ B_G
          return ← match ← φ.f.exprAsConstant subst with
          | some subst =>
            constructLambdaAppFunctor φ subst F₈
          | none =>
            let revSubst := mkApp5 (φ.φ.getDecl ``HasFullFunOp.revSubstFunFun) hHasFullFunOp A_G A₁ B_G F₈
            constructLambdaAppFunctor φ revSubst F₁
        if ← isDefEq G' (mkApp5 (φ.φ.getDecl ``HasFullFunOp.defSubstFunFun) hHasFullFunOp A₁ A₂ F₃ A₃) then
          let F₃ ← F₃.instantiate
          let subst := mkApp4 (φ.φ.getDecl ``HasFullFunOp.substFunFunFun) hHasFullFunOp A₁ A₂ A₃
          return ← constructLambdaAppFunctor φ subst F₃
        let A_F₉ := φ.φ.mkFunType A₁ (φ.φ.mkFunType A₂ A₃)
        let F₉ ← φ.φ.U.mkFreshInstMVar A_F₉
        if ← isDefEq G' (mkApp5 (φ.φ.getDecl ``HasFullFunOp.defRevSubstFunFun) hHasFullFunOp A₁ A₂ A₃ F₉) then
          let F₉ ← F₉.instantiate
          let revSubst := mkApp4 (φ.φ.getDecl ``HasFullFunOp.revSubstFunFunFun) hHasFullFunOp A₁ A₂ A₃
          return ← constructLambdaAppFunctor φ revSubst F₉
        throwTacticEx `makeFunctor φ.mvarId m!"unsupported fromDefFun argument '{G'}'"

  end

  -- Construct a functor for a given function expression.
  -- If the expression is a lambda abstraction, we use its components directly; otherwise we
  -- convert it to a lambda abstraction with a lambda application in its body (which can hopefully
  -- be unfolded).

  def constructFunctor (mvarId : MVarId) (φ : MetaInternalFunctors) (A B : φ.U) :
    φ.mkFunArrow A B → MetaM (φ.mkFunType A B)
    | Expr.lam n d b c => withLocalDecl n c.binderInfo d fun a : A =>
      let t : B := b.instantiate1 a
      constructLambdaFunctor ⟨mvarId, φ, ⟨a, t⟩⟩
    | f => do
      let F ← φ.U.mkFreshInstMVar (φ.mkFunType A B)
      if ← isDefEq f (mkApp3 (φ.getDecl ``HasInternalFunctors.Helpers.apply) A B F) then
        return F
      let a := mkFVar (← mkFreshFVarId)
      withLocalDecl `a BinderInfo.default (φ.U.mkTypeInst A) fun a : A =>
        let t : B := mkApp f a
        constructLambdaFunctor ⟨mvarId, φ, ⟨a, t⟩⟩

  -- The `makeFunctor` tactic, which calls `constructFunctor` based on the target type and given
  -- term. Note that the target type determines how to elaborate the term, which enables us to omit
  -- the variable type in `Λ` expressions.

  def makeFunctor (mvarId : MVarId) (hf : Syntax) : TacticM Expr := do
    let type ← getMVarType mvarId
    let φ ← MetaInternalFunctors.mkFreshMVar
    let A ← φ.U.mkFreshTypeMVar
    let B ← φ.U.mkFreshTypeMVar
    if ← isDefEq type (φ.U.mkTypeInst (φ.mkFunType A B)) then
      let φ ← φ.instantiate
      let A : φ.U ← A.instantiate
      let B : φ.U ← B.instantiate
      let f : φ.mkFunArrow A B ← TypedExpr.elaborate hf
      return ← constructFunctor mvarId φ A B f
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

--  def functoriality (mvarId : MVarId) : TacticM Expr := do
--    let type ← getMVarType mvarId
--    let φ ← MetaInternalFunctors.mkFreshMVar
--    let A ← φ.U.mkFreshTypeMVar
--    let B ← φ.U.mkFreshTypeMVar
--    let A' := φ.U.mkTypeInst A
--    let B' := φ.U.mkTypeInst B
--    let f ← mkFreshExprMVar (← mkArrow A' B')
--    if ← isDefEq type (mkApp3 (φ.getDecl ``HasInternalFunctors.Helpers.DefFun) A B f) then
--      let φ ← φ.instantiate
--      let A ← A.instantiate
--      let B ← B.instantiate
--      let A' ← A'.instantiate
--      let B' ← B'.instantiate
--      let f ← f.instantiate
--      let F ← constructFunctor mvarId φ A B A' B' f
--      let hDefTypeBody := mkApp3 (mkConst ``Eq [φ.U.u]) B' (mkApp4 (φ.getDecl ``HasInternalFunctors.Helpers.apply) A B F (mkBVar 0)) (mkApp f (mkBVar 0))
--      let hDefType := mkForall `a BinderInfo.default A' hDefTypeBody
--      let hDef ← elabTerm (← `(λ _ => by simp [HasInternalFunctors.Helpers.apply])) hDefType
--      return mkApp5 (φ.getDecl ``HasInternalFunctors.Helpers.toDefFun') A B F f hDef
--    throwTacticEx `makeFunctor mvarId m!"type '{type}' is not an application of 'HasInternalFunctors.Helpers.DefFun'"
--
--  elab "functoriality" : tactic => do
--    let mvarId ← getMainGoal
--    withMVarContext mvarId do
--      let e ← functoriality mvarId
--      assignExprMVar mvarId e

end Lean
