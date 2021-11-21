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



  -- We reflect quite a bit of the type system on the meta level, as a kind of annotation on
  -- `Expr`. Of course, this does not provide any type safety, but it allows us to leave a lot of
  -- arguments implicit. Using `CoeSort`, we can directly use any instance of `Expr` as a type.

  @[reducible] def TypeExpr := Expr
  @[reducible] def TypedExpr (type : TypeExpr) := Expr

  namespace TypedExpr

    instance : CoeSort TypeExpr Type := ⟨TypedExpr⟩

    def mkFreshMVar {type : TypeExpr} : MetaM type :=
      mkFreshExprMVar type

    def instantiate {type : TypeExpr} (e : type) : MetaM type :=
      instantiateMVars e

    def elaborate {type : TypeExpr} (stx : Syntax) : TacticM type :=
      elabTerm stx type

  end TypedExpr



  class _HasInstances (u : outParam Level) {v : Level} (I : mkSort v) where
  (h : mkApp (mkConst ``HasInstances [u, v]) I)

  namespace _HasInstances

    instance (u : outParam Level) {v : Level} (I : mkSort v) :
             Coe (_HasInstances u I) Expr :=
    ⟨λ h => h.h⟩

    variable {u v : Level} {I : mkSort v} [h : _HasInstances u I]

    def mkInst (A : I) : mkSort u :=
      mkApp3 (mkConst ``HasInstances.Inst [u, v]) I h A
    notation "_⌈" A:0 "⌉" => _HasInstances.mkInst A

  end _HasInstances



  def mkUniverse (u : Level) : mkSort (mkLevelSucc (mkLevelSucc u)) := mkConst ``Universe [u]

  instance (u : Level) : _HasInstances (mkLevelSucc u) (mkUniverse u) :=
    ⟨mkConst ``Universe.hasInstances [u]⟩



  structure _Universe where
  {u : Level}
  (U : mkUniverse u)

  namespace _Universe

    instance : Coe _Universe Expr := ⟨_Universe.U⟩

    def mkFreshMVar : MetaM _Universe := do
      let u ← mkFreshLevelMVar
      let U : mkUniverse u ← TypedExpr.mkFreshMVar
      return ⟨U⟩

    def instantiate (U : _Universe) : MetaM _Universe := do
      let u ← instantiateLevelMVars U.u
      let U : mkUniverse u ← U.U.instantiate
      return ⟨U⟩

    instance : CoeSort _Universe Type := ⟨λ U => _⌈U.U⌉⟩

    def mkFreshTypeMVar (U : _Universe) : MetaM U :=
      TypedExpr.mkFreshMVar

    instance (U : _Universe) : _HasInstances U.u (_⌈U.U⌉) :=
      ⟨mkApp (mkConst ``Universe.instInst [U.u]) U⟩

    instance (U : _Universe) : CoeSort U Type := ⟨λ A => _⌈A⌉⟩

    def mkFreshInstMVar {U : _Universe} (A : U) : MetaM A :=
      TypedExpr.mkFreshMVar

  end _Universe



  class _HasIdentity (U : _Universe) (iu : outParam Level) where
  (h : mkApp (mkConst ``HasIdentity [U.u, iu]) U)

  namespace _HasIdentity

    instance (U : _Universe) (iu : Level) : Coe (_HasIdentity U iu) Expr :=
      ⟨λ h => h.h⟩

  end _HasIdentity



  class _HasFunctors (U V : _Universe) (UV : outParam _Universe) where
  (h : mkApp3 (mkConst ``HasFunctors [U.u, V.u, UV.u]) U V UV)

  namespace _HasFunctors

    instance (U V UV : _Universe) : Coe (_HasFunctors U V UV) Expr :=
      ⟨λ h => h.h⟩

    def getDecl (U V : _Universe) {UV : _Universe} [h : _HasFunctors U V UV]
                (n : Name) : Expr :=
      mkApp4 (mkConst n [U.u, V.u, UV.u]) U V UV h

    def getDeclWithId (U V : _Universe) {UV : _Universe} {iv : Level}
                      [h : _HasFunctors U V UV] [hId : _HasIdentity V iv]
                      (n : Name) : Expr :=
      mkApp5 (mkConst n [U.u, V.u, UV.u, iv]) U V UV h hId

    def mkFreshDeclMVar (U V : _Universe) {UV : _Universe} [_HasFunctors U V UV]
                        (n : Name) : MetaM (getDecl U V n) :=
      TypedExpr.mkFreshMVar

    variable {U V UV : _Universe} [_HasFunctors U V UV]

    def mkFun (A : U) (B : V) : UV := mkApp2 (getDecl U V ``HasFunctors.Fun) A B
    infixr:20 " _⟶ " => _HasFunctors.mkFun

    def mkFunArrow (A : U) (B : V) : TypeExpr := mkForall `_ BinderInfo.default _⌈A⌉ _⌈B⌉
    infixr:20 " _→ " => _HasFunctors.mkFunArrow

    def mkApplyFn {A : U} {B : V} (F : A _⟶ B) : A _→ B :=
      mkApp3 (getDecl U V ``HasFunctors.apply) A B F

    def mkApply {A : U} {B : V} (F : A _⟶ B) (a : A) : B := mkApp (mkApplyFn F) a
    instance (A : U) (B : V) : CoeFun (A _⟶ B) (λ _ => A → B) := ⟨mkApply⟩

    variable {iv : Level} [_HasIdentity V iv]

    def mkDefFun (A : U) (B : V) (f : A _→ B) : TypeExpr :=
      mkApp3 (getDeclWithId U V ``HasFunctors.DefFun) A B f
    notation:20 A:21 " _⟶{" f:0 "} " B:21 => _HasFunctors.mkDefFun A B f

    def mkFromDefFun {A : U} {B : V} {f : A _→ B} (F : A _⟶{f} B) : A _⟶ B :=
      mkApp4 (getDeclWithId U V ``HasFunctors.fromDefFun) A B f F

    def mkToDefFun {A : U} {B : V} (F : A _⟶ B) : A _⟶{mkApplyFn F} B :=
      mkApp3 (getDeclWithId U V ``HasFunctors.toDefFun) A B F

  end _HasFunctors



  class _HasInternalFunctors (U : _Universe) {iu : Level} [hId : _HasIdentity U iu] where
  (h : mkApp2 (mkConst ``HasInternalFunctors [U.u, iu]) U hId)

  namespace _HasInternalFunctors

    instance (U : _Universe) {iu : Level} [_HasIdentity U iu] :
             Coe (_HasInternalFunctors U) Expr :=
      ⟨λ h => h.h⟩

    instance (U : _Universe) {iu : Level} [hId : _HasIdentity U iu] [h : _HasInternalFunctors U] :
             _HasFunctors U U U :=
      ⟨mkApp3 (mkConst ``HasInternalFunctors.toHasFunctors [U.u, iu]) U hId h⟩

    def getDecl (U : _Universe) {iu : Level} [hId : _HasIdentity U iu] [h : _HasInternalFunctors U]
                (n : Name) : Expr :=
      mkApp3 (mkConst n [U.u, iu]) U hId h

    def mkFreshDeclMVar (U : _Universe) {iu : Level} [hId : _HasIdentity U iu]
                        [h : _HasInternalFunctors U] (n : Name) : MetaM (getDecl U n) :=
      TypedExpr.mkFreshMVar

  end _HasInternalFunctors



  -- A function that has been transformed into a lambda abstraction that we can work with more
  -- easily. In particular, the lambda variable `a` is an `FVar`, so that `t` does not contain any
  -- loose bound variables. This is required for Lean algorithms such as `isDefEq` to work.

  structure LambdaAbstraction {U V UV : _Universe} [_HasFunctors U V UV] (A : U) (B : V) where
  (a : A)
  (t : B)

  namespace LambdaAbstraction

    variable {U V UV : _Universe} [_HasFunctors U V UV] {A : U} {B : V} (f : LambdaAbstraction A B)

    def exprAsConstant (t : B) : MetaM (Option B) := do
      if !(t.containsFVar f.a.fvarId!) then
        return t
      let t' : B ← reduce t
      if !(t'.containsFVar f.a.fvarId!) then
        return t'
      none

    def asConstant : MetaM (Option B) := f.exprAsConstant f.t

    def isId : MetaM Bool := isDefEq f.t f.a

  end LambdaAbstraction



  structure FunctorialityData where
  (mvarId : MVarId)
  (U      : _Universe)
  {iu     : Level}
  [hId    : _HasIdentity U iu]
  [hFun   : _HasInternalFunctors U]
  {A B    : U}
  (f      : LambdaAbstraction A B)

  namespace FunctorialityData

    variable (φ : FunctorialityData)

    instance : _HasIdentity φ.U φ.iu := φ.hId
    instance : _HasInternalFunctors φ.U := φ.hFun

  end FunctorialityData



  -- The actual algorithm is implemented as a set of mutually recursive functions.
  -- Of these, `constructLambdaFunctor` is the main entry point (called by `constructFunctor`
  -- below); it returns a functor for the lambda expression given by `f`. If the body of `f`
  -- is a functor application, it is analyzed and handled by `constructLambdaAppFunctor`. If it is
  -- an application of `fromDefFun`, `constructLambdaDefFunFunctor` handles that; in most cases we
  -- are dealing with some primitive or derived `...Fun` (the last case in the algorithm).

  mutual

    -- The main entry point, which handles `constFun` and `idFun` directly, and calls either
    -- `constructLambdaAppFunctor` or `constructLambdaDefFunFunctor` otherwise.

    partial def constructLambdaFunctor (φ : FunctorialityData) : MetaM (φ.A _⟶ φ.B) := do
      match ← φ.f.asConstant with
      | some t => do
        let hHasSubLinearFunOp ← synthInstance (_HasInternalFunctors.getDecl φ.U ``HasSubLinearFunOp)
        mkApp4 (_HasInternalFunctors.getDecl φ.U ``HasSubLinearFunOp.constFun) hHasSubLinearFunOp φ.A φ.B t
      | none => do
        if ← φ.f.isId then
          let hHasLinearFunOp ← synthInstance (_HasInternalFunctors.getDecl φ.U ``HasLinearFunOp)
          return mkApp2 (_HasInternalFunctors.getDecl φ.U ``HasLinearFunOp.idFun) hHasLinearFunOp φ.A
        let B_b ← φ.U.mkFreshTypeMVar
        let G ← φ.U.mkFreshInstMVar (B_b _⟶ φ.B)
        let b ← φ.U.mkFreshInstMVar B_b
        if ← isDefEq φ.f.t (G b) then
          let G ← G.instantiate
          let b ← b.instantiate
          return ← constructLambdaAppFunctor φ G b
        let A_G ← φ.U.mkFreshTypeMVar
        let B_G ← φ.U.mkFreshTypeMVar
        let g : (A_G _→ B_G) ← TypedExpr.mkFreshMVar
        let G' : (A_G _⟶{g} B_G) ← TypedExpr.mkFreshMVar
        if ← isDefEq φ.f.t (_HasFunctors.mkFromDefFun G') then
          let g ← g.instantiate
          let G' ← G'.instantiate
          return ← constructLambdaDefFunFunctor φ g G'
        throwTacticEx `makeFunctor φ.mvarId m!"unsupported lambda body '{φ.f.t}'"

    -- This function handles the different cases of functor application in the lambda body,
    -- depending on which parts are either equal to the lambda variable or constant with respect
    -- to it. (Note that we do not optimize the case where both parts are constant, since that
    -- should have been handled already.)

    partial def constructLambdaAppFunctor (φ : FunctorialityData) {B_b : φ.U}
                                          (G : B_b _⟶ φ.B) (b : B_b) :
                MetaM (φ.A _⟶ φ.B) :=
      withDefault do
        let f_G : LambdaAbstraction φ.A (B_b _⟶ φ.B) := ⟨φ.f.a, G⟩
        let f_b : LambdaAbstraction φ.A B_b := ⟨φ.f.a, b⟩
        let hHasLinearFunOp ← synthInstance (_HasInternalFunctors.getDecl φ.U ``HasLinearFunOp)
        match ← f_G.asConstant with
        | some G => do
          if ← f_b.isId then
            return G
          let F_b ← constructLambdaFunctor ⟨φ.mvarId, φ.U, f_b⟩
          -- TODO: Write as `trans` to enable notation.
          return mkApp6 (_HasInternalFunctors.getDecl φ.U ``HasLinearFunOp.compFun) hHasLinearFunOp φ.A B_b φ.B F_b G
        | none => do
          match ← f_b.asConstant with
          | some b => do
            if ← f_G.isId then
              return mkApp4 (_HasInternalFunctors.getDecl φ.U ``HasLinearFunOp.revAppFun) hHasLinearFunOp B_b b φ.B
            let F_G ← constructLambdaFunctor ⟨φ.mvarId, φ.U, f_G⟩
            return mkApp6 (_HasInternalFunctors.getDecl φ.U ``HasLinearFunOp.swapFun) hHasLinearFunOp φ.A B_b φ.B F_G b
          | none => do
            let F_G ← constructLambdaFunctor ⟨φ.mvarId, φ.U, f_G⟩
            if ← f_b.isId then
              let hHasNonLinearFunOp ← synthInstance (_HasInternalFunctors.getDecl φ.U ``HasNonLinearFunOp)
              return mkApp4 (_HasInternalFunctors.getDecl φ.U ``HasNonLinearFunOp.dupFun) hHasNonLinearFunOp φ.A φ.B F_G
            let F_b ← constructLambdaFunctor ⟨φ.mvarId, φ.U, f_b⟩
            let hHasFullFunOp ← synthInstance (_HasInternalFunctors.getDecl φ.U ``HasFullFunOp)
            return mkApp6 (_HasInternalFunctors.getDecl φ.U ``HasFullFunOp.substFun) hHasFullFunOp φ.A B_b φ.B F_b F_G

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

    partial def constructLambdaDefFunFunctor (φ : FunctorialityData) {A_G B_G : φ.U}
                                             (g : A_G _→ B_G) (G' : A_G _⟶{g} B_G) :
                MetaM (A_G _⟶ B_G) := do
      let G ← φ.U.mkFreshInstMVar (A_G _⟶ B_G)
      if ← isDefEq G' (_HasFunctors.mkToDefFun G) then
        let G ← G.instantiate
        return ← constructLambdaFunctor ⟨φ.mvarId, φ.U, ⟨φ.f.a, G⟩⟩
      withReducible do
        let hHasSubLinearFunOp ← _HasInternalFunctors.mkFreshDeclMVar φ.U ``HasSubLinearFunOp
        let b ← φ.U.mkFreshInstMVar B_G
        if ← isDefEq G' (mkApp4 (_HasInternalFunctors.getDecl φ.U ``HasSubLinearFunOp.defConstFun) hHasSubLinearFunOp A_G B_G b) then
          let b ← b.instantiate
          let const := mkApp3 (_HasInternalFunctors.getDecl φ.U ``HasSubLinearFunOp.constFunFun) hHasSubLinearFunOp A_G B_G
          return ← constructLambdaAppFunctor φ const b
        let hHasLinearFunOp ← _HasInternalFunctors.mkFreshDeclMVar φ.U ``HasLinearFunOp
        let A₁ ← φ.U.mkFreshTypeMVar
        let a₁ ← φ.U.mkFreshInstMVar A₁
        if ← isDefEq G' (mkApp4 (_HasInternalFunctors.getDecl φ.U ``HasLinearFunOp.defRevAppFun) hHasLinearFunOp A₁ a₁ B_G) then
          let a₁ ← a₁.instantiate
          let app := mkApp3 (_HasInternalFunctors.getDecl φ.U ``HasLinearFunOp.revAppFunFun) hHasLinearFunOp A₁ B_G
          return ← constructLambdaAppFunctor φ app a₁
        let A_F₁ := A_G _⟶ A₁
        let A_F₂ := A₁ _⟶ B_G
        let F₁ ← φ.U.mkFreshInstMVar A_F₁
        let F₂ ← φ.U.mkFreshInstMVar A_F₂
        if ← isDefEq G' (mkApp6 (_HasInternalFunctors.getDecl φ.U ``HasLinearFunOp.defCompFun) hHasLinearFunOp A_G A₁ B_G F₁ F₂) then
          let F₁ ← F₁.instantiate
          let F₂ ← F₂.instantiate
          let comp := mkApp5 (_HasInternalFunctors.getDecl φ.U ``HasLinearFunOp.compFunFun) hHasLinearFunOp A_G A₁ F₁ B_G
          return ← match ← φ.f.exprAsConstant comp with
          | some comp =>
            constructLambdaAppFunctor φ comp F₂
          | none =>
            let revComp := mkApp5 (_HasInternalFunctors.getDecl φ.U ``HasLinearFunOp.revCompFunFun) hHasLinearFunOp A_G A₁ B_G F₂
            constructLambdaAppFunctor φ revComp F₁
        let A₂ ← φ.U.mkFreshTypeMVar
        let A₃ ← φ.U.mkFreshTypeMVar
        let A_F₃ := A₁ _⟶ A₂
        let F₃ ← φ.U.mkFreshInstMVar A_F₃
        if ← isDefEq G' (mkApp5 (_HasInternalFunctors.getDecl φ.U ``HasLinearFunOp.defCompFunFun) hHasLinearFunOp A₁ A₂ F₃ A₃) then
          let F₃ ← F₃.instantiate
          let comp := mkApp4 (_HasInternalFunctors.getDecl φ.U ``HasLinearFunOp.compFunFunFun) hHasLinearFunOp A₁ A₂ A₃
          return ← constructLambdaAppFunctor φ comp F₃
        let A_F₄ := A₂ _⟶ A₃
        let F₄ ← φ.U.mkFreshInstMVar A_F₄
        if ← isDefEq G' (mkApp5 (_HasInternalFunctors.getDecl φ.U ``HasLinearFunOp.defRevCompFunFun) hHasLinearFunOp A₁ A₂ A₃ F₄) then
          let F₄ ← F₄.instantiate
          let revComp := mkApp4 (_HasInternalFunctors.getDecl φ.U ``HasLinearFunOp.revCompFunFunFun) hHasLinearFunOp A₁ A₂ A₃
          return ← constructLambdaAppFunctor φ revComp F₄
        let A_F₅ := A_G _⟶ (A₁ _⟶ B_G)
        let F₅ ← φ.U.mkFreshInstMVar A_F₅
        if ← isDefEq G' (mkApp6 (_HasInternalFunctors.getDecl φ.U ``HasLinearFunOp.defSwapFun) hHasLinearFunOp A_G A₁ B_G F₅ a₁) then
          let F₅ ← F₅.instantiate
          let a₁ ← a₁.instantiate
          let swap := mkApp5 (_HasInternalFunctors.getDecl φ.U ``HasLinearFunOp.swapFunFun) hHasLinearFunOp A_G A₁ B_G F₅
          return ← match ← φ.f.exprAsConstant swap with
          | some swap =>
            constructLambdaAppFunctor φ swap a₁
          | none =>
            let revSwap := mkApp5 (_HasInternalFunctors.getDecl φ.U ``HasLinearFunOp.revSwapFunFun) hHasLinearFunOp A_G A₁ a₁ B_G
            constructLambdaAppFunctor φ revSwap F₅
        let A_F₆ := A₁ _⟶ (A_G _⟶ A₂)
        let F₆ ← φ.U.mkFreshInstMVar A_F₆
        if ← isDefEq G' (mkApp5 (_HasInternalFunctors.getDecl φ.U ``HasLinearFunOp.defSwapFunFun) hHasLinearFunOp A₁ A_G A₂ F₆) then
          let F₆ ← F₆.instantiate
          let swap := mkApp4 (_HasInternalFunctors.getDecl φ.U ``HasLinearFunOp.swapFunFunFun) hHasLinearFunOp A₁ A_G A₂
          return ← constructLambdaAppFunctor φ swap F₆
        let a₂ ← φ.U.mkFreshInstMVar A₂
        if ← isDefEq G' (mkApp5 (_HasInternalFunctors.getDecl φ.U ``HasLinearFunOp.defRevSwapFunFun) hHasLinearFunOp A₁ A₂ a₂ A₃) then
          let a₂ ← a₂.instantiate
          let revSwap := mkApp4 (_HasInternalFunctors.getDecl φ.U ``HasLinearFunOp.revSwapFunFunFun) hHasLinearFunOp A₁ A₂ A₃
          return ← constructLambdaAppFunctor φ revSwap a₂
        let hHasNonLinearFunOp ← _HasInternalFunctors.mkFreshDeclMVar φ.U ``HasNonLinearFunOp
        let A_F₇ := A_G _⟶ (A_G _⟶ B_G)
        let F₇ ← φ.U.mkFreshInstMVar A_F₇
        if ← isDefEq G' (mkApp4 (_HasInternalFunctors.getDecl φ.U ``HasNonLinearFunOp.defDupFun) hHasNonLinearFunOp A_G B_G F₇) then
          let F₇ ← F₇.instantiate
          let dup := mkApp3 (_HasInternalFunctors.getDecl φ.U ``HasNonLinearFunOp.dupFunFun) hHasNonLinearFunOp A_G B_G
          return ← constructLambdaAppFunctor φ dup F₇
        let hHasFullFunOp ← _HasInternalFunctors.mkFreshDeclMVar φ.U ``HasFullFunOp
        let A_F₈ := A_G _⟶ (A₁ _⟶ B_G)
        let F₈ ← φ.U.mkFreshInstMVar A_F₈
        if ← isDefEq G' (mkApp6 (_HasInternalFunctors.getDecl φ.U ``HasFullFunOp.defSubstFun) hHasFullFunOp A_G A₁ B_G F₁ F₈) then
          let F₁ ← F₁.instantiate
          let F₈ ← F₈.instantiate
          let subst := mkApp5 (_HasInternalFunctors.getDecl φ.U ``HasFullFunOp.substFunFun) hHasFullFunOp A_G A₁ F₁ B_G
          return ← match ← φ.f.exprAsConstant subst with
          | some subst =>
            constructLambdaAppFunctor φ subst F₈
          | none =>
            let revSubst := mkApp5 (_HasInternalFunctors.getDecl φ.U ``HasFullFunOp.revSubstFunFun) hHasFullFunOp A_G A₁ B_G F₈
            constructLambdaAppFunctor φ revSubst F₁
        if ← isDefEq G' (mkApp5 (_HasInternalFunctors.getDecl φ.U ``HasFullFunOp.defSubstFunFun) hHasFullFunOp A₁ A₂ F₃ A₃) then
          let F₃ ← F₃.instantiate
          let subst := mkApp4 (_HasInternalFunctors.getDecl φ.U ``HasFullFunOp.substFunFunFun) hHasFullFunOp A₁ A₂ A₃
          return ← constructLambdaAppFunctor φ subst F₃
        let A_F₉ := A₁ _⟶ (A₂ _⟶ A₃)
        let F₉ ← φ.U.mkFreshInstMVar A_F₉
        if ← isDefEq G' (mkApp5 (_HasInternalFunctors.getDecl φ.U ``HasFullFunOp.defRevSubstFunFun) hHasFullFunOp A₁ A₂ A₃ F₉) then
          let F₉ ← F₉.instantiate
          let revSubst := mkApp4 (_HasInternalFunctors.getDecl φ.U ``HasFullFunOp.revSubstFunFunFun) hHasFullFunOp A₁ A₂ A₃
          return ← constructLambdaAppFunctor φ revSubst F₉
        throwTacticEx `makeFunctor φ.mvarId m!"unsupported fromDefFun argument '{G'}'"

  end

  -- Construct a functor for a given function expression.
  -- If the expression is a lambda abstraction, we use its components directly; otherwise we
  -- convert it to a lambda abstraction with a lambda application in its body (which can hopefully
  -- be unfolded).

  def constructFunctor (mvarId : MVarId) {U : _Universe} {iu : Level} [_HasIdentity U iu]
                       [hFun : _HasInternalFunctors U] (A B : U) :
    (A _→ B) → MetaM (A _⟶ B)
    | Expr.lam n d b c => withLocalDecl n c.binderInfo d fun a : A =>
      let t : B := b.instantiate1 a
      constructLambdaFunctor ⟨mvarId, U, ⟨a, t⟩⟩
    | f => do
      let F ← U.mkFreshInstMVar (A _⟶ B)
      if ← isDefEq f (_HasFunctors.mkApplyFn F) then
        return F
      let a := mkFVar (← mkFreshFVarId)
      withLocalDecl `a BinderInfo.default _⌈A⌉ fun a : A =>
        let t : B := mkApp f a
        constructLambdaFunctor ⟨mvarId, U, ⟨a, t⟩⟩

  -- The `makeFunctor` tactic, which calls `constructFunctor` based on the target type and given
  -- term. Note that the target type determines how to elaborate the term, which enables us to omit
  -- the variable type in `Λ` expressions.

  def makeFunctor (mvarId : MVarId) (hf : Syntax) : TacticM Expr := do
    let type ← getMVarType mvarId
    let U ← _Universe.mkFreshMVar
    let A ← U.mkFreshTypeMVar
    let B ← U.mkFreshTypeMVar
    let iu ← mkFreshLevelMVar
    let hId : _HasIdentity U iu := ⟨← TypedExpr.mkFreshMVar⟩
    let hFun : _HasInternalFunctors U := ⟨← TypedExpr.mkFreshMVar⟩
    if ← isDefEq type _⌈A _⟶ B⌉ then
      let U ← U.instantiate
      let A : U ← A.instantiate
      let B : U ← B.instantiate
      let iu ← instantiateLevelMVars iu
      let hId : _HasIdentity U iu := ⟨← hId.h.instantiate⟩
      let hFun : _HasInternalFunctors U := ⟨← hFun.h.instantiate⟩
      let f : (A _→ B) ← TypedExpr.elaborate hf
      return ← constructFunctor mvarId A B f
    throwTacticEx `makeFunctor mvarId m!"type '{type}' is not an application of 'HasFunctors.Fun'"

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
--    let f : (A _→ B) ← TypedExpr.mkFreshMVar
--    if ← isDefEq type (φ.mkDefFunType A B f) then
--      let φ ← φ.instantiate
--      let A ← A.instantiate
--      let B ← B.instantiate
--      let f ← f.instantiate
--      let F ← constructFunctor mvarId φ A B f
--      let hDefTypeBody := mkApp3 (mkConst ``Eq [φ.U.u]) B' (mkApp4 (φ.getDecl ``HasInternalFunctors.Helpers.apply) A B F (mkBVar 0)) (mkApp f (mkBVar 0))
--      let hDefType := mkForall `a BinderInfo.default A' hDefTypeBody
--      let hDef ← elabTerm (← `(λ _ => by simp [HasInternalFunctors.Helpers.apply])) hDefType
--      return mkApp5 (φ.getDecl ``HasInternalFunctors.Helpers.toDefFun') A B F f hDef
--    throwTacticEx `makeFunctor mvarId m!"type '{type}' is not an application of 'HasFunctors.DefFun'"
--
--  elab "functoriality" : tactic => do
--    let mvarId ← getMainGoal
--    withMVarContext mvarId do
--      let e ← functoriality mvarId
--      assignExprMVar mvarId e

end Lean
