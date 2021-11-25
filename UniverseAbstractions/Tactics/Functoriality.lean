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
  @[reducible] def TypedExpr (α : TypeExpr) := Expr

  scoped instance : CoeSort TypeExpr Type := ⟨TypedExpr⟩

  namespace TypedExpr

    def mkFreshMVar {α : TypeExpr} : MetaM α :=
      mkFreshExprMVar α

    def instantiate {α : TypeExpr} : α → MetaM α :=
      instantiateMVars

    def synthesize {α : TypeExpr} : MetaM α :=
      synthInstance α

    def synthesize? {α : TypeExpr} : MetaM (Option α) :=
      synthInstance? α

    def elaborate {α : TypeExpr} (a : Syntax) : TacticM α :=
      elabTerm a α

  end TypedExpr



  def mkFunction (α β : TypeExpr) : TypeExpr := mkForall `_ BinderInfo.default α β
  infixr:20 " _→ " => mkFunction



  -- A function `f : α → β` that has been transformed into a lambda abstraction `λ a : α => t` that
  -- we can work with more easily. In particular, the lambda variable `a` is an `FVar`, so that `t`
  -- does not contain any loose bound variables. This is required for Lean algorithms such as
  -- `isDefEq` to work.

  structure LambdaAbstraction (α β : TypeExpr) where
  (a : α)
  (t : β)

  namespace LambdaAbstraction

    variable {α β : TypeExpr} (f : LambdaAbstraction α β)

    def exprAsConstant {γ : TypeExpr} (t : γ) : MetaM (Option γ) := do
      if !(t.containsFVar f.a.fvarId!) then
        return t
      let t' ← reduce t
      if !(t'.containsFVar f.a.fvarId!) then
        return t'
      none

    def asConstant : MetaM (Option β) := f.exprAsConstant f.t

    def exprIsId {γ : TypeExpr} (t : γ) : MetaM Bool := isDefEq t f.a

    def isId : MetaM Bool := f.exprIsId f.t

  end LambdaAbstraction



  def getSynthInstanceDecl (nTC nDecl : Name) (lvls : List Level) (args : List Expr) :
      MetaM Expr := do
    let args' : Array Expr := ⟨args⟩
    let h : mkAppN (mkConst nTC lvls) args' ← TypedExpr.synthesize
    mkAppN (mkConst nDecl lvls) (args'.push h)



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

    instance (priority := high) : CoeSort _Universe Type := ⟨λ U => _⌈U.U⌉⟩

    instance (U : _Universe) : _HasInstances U.u (_⌈U.U⌉) :=
      ⟨mkApp (mkConst ``Universe.instInst [U.u]) U⟩

    instance (priority := high) (U : _Universe) : CoeSort U Type := ⟨λ A => _⌈A⌉⟩

  end _Universe



  class _HasIdentity (U : _Universe) (iu : outParam Level) where
  (h : mkApp (mkConst ``HasIdentity [U.u, iu]) U)

  namespace _HasIdentity

    instance (U : _Universe) (iu : Level) : Coe (_HasIdentity U iu) Expr := ⟨λ h => h.h⟩

    def getDecl (U : _Universe) {iu : Level} [h : _HasIdentity U iu] (n : Name) : Expr :=
      mkApp2 (mkConst n [U.u, iu]) U h

    def mkUniv (U : _Universe) {iu : Level} [h : _HasIdentity U iu] : mkUniverse iu :=
      getDecl U ``HasIdentity.univ

    def mkHasInstanceEquivalences (U : _Universe) {iu : Level} [h : _HasIdentity U iu] : Expr :=
      getDecl U ``HasIdentity.hasInstanceEquivalences

    variable {U : _Universe} {iu : Level} [_HasIdentity U iu]

    def mkRel (A : U) : _⌈A⌉ _→ _⌈A⌉ _→ _⌈mkUniv U⌉ :=
      mkApp4 (mkConst ``HasInstanceEquivalences.Rel [U.u, iu]) U (mkUniv U) (mkHasInstanceEquivalences U) A

    def mkEquiv {A : U} (a b : A) : mkUniv U := mkApp2 (mkRel A) a b

  end _HasIdentity



  class _HasFunctors (U V : _Universe) (UV : outParam _Universe) where
  (h : mkApp3 (mkConst ``HasFunctors [U.u, V.u, UV.u]) U V UV)

  namespace _HasFunctors

    instance (U V UV : _Universe) : Coe (_HasFunctors U V UV) Expr := ⟨λ h => h.h⟩

    def getDecl (U V : _Universe) {UV : _Universe} [h : _HasFunctors U V UV]
                (n : Name) : Expr :=
      mkApp4 (mkConst n [U.u, V.u, UV.u]) U V UV h

    def getDeclWithId (U V : _Universe) {UV : _Universe} {iv : Level}
                      [h : _HasFunctors U V UV] [hId : _HasIdentity V iv]
                      (n : Name) : Expr :=
      mkApp5 (mkConst n [U.u, V.u, UV.u, iv]) U V UV h hId

    variable {U V UV : _Universe} [_HasFunctors U V UV]

    def mkFun (A : U) (B : V) : UV := mkApp2 (getDecl U V ``HasFunctors.Fun) A B
    infixr:20 " _⟶ " => _HasFunctors.mkFun

    def mkApplyFn {A : U} {B : V} (F : A _⟶ B) : _⌈A⌉ _→ _⌈B⌉ :=
      mkApp3 (getDecl U V ``HasFunctors.apply) A B F

    def mkApply {A : U} {B : V} (F : A _⟶ B) (a : A) : B := mkApp (mkApplyFn F) a
    instance (A : U) (B : V) : CoeFun (A _⟶ B) (λ _ => A → B) := ⟨mkApply⟩

    variable {iv : Level} [_HasIdentity V iv]

    def mkDefFun (A : U) (B : V) (f : _⌈A⌉ _→ _⌈B⌉) : TypeExpr :=
      mkApp3 (getDeclWithId U V ``HasFunctors.DefFun) A B f
    notation:20 A:21 " _⟶{" f:0 "} " B:21 => _HasFunctors.mkDefFun A B f

    def mkFromDefFun {A : U} {B : V} {f : _⌈A⌉ _→ _⌈B⌉} (F : A _⟶{f} B) : A _⟶ B :=
      mkApp4 (getDeclWithId U V ``HasFunctors.fromDefFun) A B f F

    def mkToDefFun {A : U} {B : V} (F : A _⟶ B) : A _⟶{mkApplyFn F} B :=
      mkApp3 (getDeclWithId U V ``HasFunctors.toDefFun) A B F

    structure FunctorDefinition (A : U) (B : V) where
    {f  : _⌈A⌉ _→ _⌈B⌉}
    (F' : A _⟶{f} B)
    (F  : A _⟶ B)  -- Should be defeq to `fromDefFun F'` in transparency mode "reducible".

    def getFunctorDefinition {A : U} {B : V} (F : A _⟶ B) :
        MetaM (Option (FunctorDefinition A B)) := do
      let f : (_⌈A⌉ _→ _⌈B⌉) ← TypedExpr.mkFreshMVar
      let F' : (A _⟶{f} B) ← TypedExpr.mkFreshMVar
      let F'' := mkFromDefFun F'
      if ← isDefEq F F'' then
        -- If `F` is defeq to `fromDefFun F'` in reducible transparancy mode, then store
        -- `F` in the result instead of `F''`, as terms involving `fromDefFun` are usually
        -- hard to read.
        if ← withReducible (isDefEq F F'') then
          return some ⟨F', F⟩
        -- TODO: It would be nice if we could somehow unfold one by one until we reach
        -- a suitable term.
        return some ⟨F', F''⟩
      return none

    class _IsFunApp (A : outParam U) {B : V} (b : B) where
    (h : mkApp3 (getDeclWithId U V ``HasFunctors.IsFunApp) A B b)

    namespace _IsFunApp

      instance (A : U) {B : V} (b : B) : Coe (_IsFunApp A b) Expr := ⟨λ h => h.h⟩

      def mkRefl' {A : U} {B : V} (F : A _⟶ B) (a : A) {b : B} : _IsFunApp A b :=
        ⟨mkApp4 (_HasFunctors.getDeclWithId U V ``HasFunctors.IsFunApp.refl) A B F a⟩

      def mkRefl {A : U} {B : V} (F : A _⟶ B) (a : A) : _IsFunApp A (F a) :=
        mkRefl' F a

      def synthesize' {A : U} {B : V} {b : B} : MetaM (_IsFunApp A b) := do
        -- TODO: Multiple alternatives.
        return ⟨← TypedExpr.synthesize⟩

      def synthesize {A : U} {B : V} {b : B} : MetaM (_IsFunApp A b) := do
        -- First check whether `b` is literally a function application.
        -- This sees through some definitions that are opaque to type class synthesization.
        let F : (A _⟶ B) ← TypedExpr.mkFreshMVar
        let a : A ← TypedExpr.mkFreshMVar
        if ← isDefEq b (F a) then
          return mkRefl' F a
        -- Next, check if `b` is an application of `fromDefFun`. If it is, pass that to
        -- `IsFunApp` instead of the original value of `b`, as `IsFunApp` is usually
        -- defined on such terms.
        let U' ← _Universe.mkFreshMVar
        let V' ← _Universe.mkFreshMVar
        let hFun_UV' : _HasFunctors U' V' V := ⟨← TypedExpr.mkFreshMVar⟩
        let iv' ← mkFreshLevelMVar
        let hId_V' : _HasIdentity V' iv' := ⟨← TypedExpr.mkFreshMVar⟩
        let A' : U' ← TypedExpr.mkFreshMVar
        let B' : V' ← TypedExpr.mkFreshMVar
        match ← getFunctorDefinition (A := A') (B := B') b with
        | some b' =>
          let h : _IsFunApp A (B := B) b'.F ← synthesize'
          return ⟨h⟩
        | none =>
          -- Finally, try to synthesize an instance of `IsFunApp` normally.
          synthesize'

      variable (A : U) {B : V} (b : B) [h : _IsFunApp A b]

      def getDecl (n : Name) : Expr :=
        mkApp4 (_HasFunctors.getDeclWithId U V n) A B b h

      def getFun : MetaM (A _⟶ B) := whnfI (getDecl A b ``HasFunctors.IsFunApp.F)
      def getArg : MetaM A        := whnfI (getDecl A b ``HasFunctors.IsFunApp.a)

    end _IsFunApp

  end _HasFunctors



  -- TODO: Remove? Or maybe use it to improve readability?
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

  end _HasInternalFunctors



  structure FunData where
  {U V UV : _Universe}
  [hFun   : _HasFunctors U V UV]
  (A      : U)
  (B      : V)

  namespace FunData

    def mkFreshMVar : MetaM FunData := do
      let U ← _Universe.mkFreshMVar
      let V ← _Universe.mkFreshMVar
      let UV ← _Universe.mkFreshMVar
      let hFun : _HasFunctors U V UV := ⟨← TypedExpr.mkFreshMVar⟩
      let A : U ← TypedExpr.mkFreshMVar
      let B : V ← TypedExpr.mkFreshMVar
      return ⟨A, B⟩

    def instantiate (φ : FunData) : MetaM FunData := do
      let U ← φ.U.instantiate
      let V ← φ.V.instantiate
      let UV ← φ.UV.instantiate
      let hFun : _HasFunctors U V UV := ⟨← φ.hFun.h.instantiate⟩
      let A : U ← φ.A.instantiate
      let B : V ← φ.B.instantiate
      return ⟨A, B⟩

    variable (φ : FunData)

    instance : _HasFunctors φ.U φ.V φ.UV := φ.hFun

    def mkFun      : φ.UV     := φ.A _⟶ φ.B
    def mkFunArrow : TypeExpr := _⌈φ.A⌉ _→ _⌈φ.B⌉

  end FunData

  structure DefFunData extends FunData where
  {iv  : Level}
  [hId : _HasIdentity V iv]

  namespace DefFunData

    variable (φ : DefFunData)

    instance : _HasIdentity φ.V φ.iv := φ.hId

  end DefFunData

  def FunctorLambdaAbstraction (φ : DefFunData) := LambdaAbstraction _⌈φ.A⌉ _⌈φ.B⌉



  mutual

    -- The main entry point, which handles `constFun` and `idFun` directly, and calls
    -- `constructLambdaAppFunctor` to deal with a lambda application.

    partial def constructLambdaFunctor (φ : DefFunData) (f : FunctorLambdaAbstraction φ) : MetaM φ.mkFun := do
      match ← f.asConstant with
      | some t => do
        let constFun ← getSynthInstanceDecl ``HasConstFun ``HasConstFun.constFun 
                                            [φ.U.u, φ.V.u, φ.UV.u,         φ.iv]
                                            [φ.U,   φ.V,   φ.UV,   φ.hFun, φ.hId]
        mkApp3 constFun φ.A φ.B t
      | none => do
        if ← f.isId then
          let idFun ← getSynthInstanceDecl ``HasIdFun ``HasIdFun.idFun
                                           [φ.U.u, φ.UV.u,         φ.iv]
                                           [φ.U,   φ.UV,   φ.hFun, φ.hId]
          return mkApp idFun φ.A
        let W ← _Universe.mkFreshMVar
        let WV ← _Universe.mkFreshMVar
        let hFun_WV : _HasFunctors W φ.V WV := ⟨← TypedExpr.mkFreshMVar⟩
        let C : W ← TypedExpr.mkFreshMVar
        let hFunApp : _HasFunctors._IsFunApp C f.t ← _HasFunctors._IsFunApp.synthesize
        return ← constructLambdaAppFunctor φ f C

    -- This function handles the different cases of functor application in the lambda body,
    -- depending on which parts are either equal to the lambda variable or constant with respect
    -- to it. (Note that we do not optimize the case where both parts are constant, since that
    -- should have been handled already.)

    -- TODO instance equivalence

    partial def constructLambdaAppFunctor (φ : DefFunData) (f : FunctorLambdaAbstraction φ)
                                          {W WV : _Universe} [hFun_WV : _HasFunctors W φ.V WV]
                                          (C : W) [hFunApp : _HasFunctors._IsFunApp C f.t] :
                MetaM φ.mkFun := do
      let G ← _HasFunctors._IsFunApp.getFun C f.t
      let c ← _HasFunctors._IsFunApp.getArg C f.t
      match ← f.exprAsConstant G with
      | some G => do
        if ← f.exprIsId c then
          return mkApp3 (_HasFunctors.getDeclWithId φ.U φ.V ``HasFunctors.appFun) φ.A φ.B G
        let UW ← _Universe.mkFreshMVar
        let hFun_UW : _HasFunctors φ.U W UW := ⟨← TypedExpr.synthesize⟩
        let iw ← mkFreshLevelMVar
        let hId_W : _HasIdentity W iw := ⟨← TypedExpr.synthesize⟩
        let F_c ← constructLambdaFunctor ⟨φ.A, C⟩ ⟨f.a, c⟩
        let compFun ← getSynthInstanceDecl ``HasCompFun ``HasCompFun.compFun
                                           [φ.U.u, W.u, φ.V.u, UW.u, WV.u, φ.UV.u,                           φ.iv]
                                           [φ.U,   W,   φ.V,   UW,   WV,   φ.UV,   hFun_UW, hFun_WV, φ.hFun, φ.hId]
        return mkApp5 compFun φ.A C φ.B F_c G
      | none => do
        match ← f.exprAsConstant c with
        | some c => do
          if ← f.exprIsId G then
            let revAppFun ← getSynthInstanceDecl ``HasRevAppFun ``HasRevAppFun.revAppFun
                                                 [φ.V.u,         φ.iv]
                                                 [φ.V,   φ.hFun, φ.hId]
            return mkApp3 revAppFun C c φ.B
          let UWV ← _Universe.mkFreshMVar
          let hFun_UWV : _HasFunctors φ.U WV UWV := ⟨← TypedExpr.synthesize⟩
          let iwv ← mkFreshLevelMVar
          let hId_WV : _HasIdentity WV iwv := ⟨← TypedExpr.synthesize⟩
          let F_G ← constructLambdaFunctor ⟨φ.A, C _⟶ φ.B⟩ ⟨f.a, G⟩
          let swapFun ← getSynthInstanceDecl ``HasSwapFun ``HasSwapFun.swapFun
                                             [φ.U.u, W.u, φ.V.u, WV.u, UWV.u, φ.UV.u,                            φ.iv]
                                             [φ.U,   W,   φ.V,   WV,   UWV,   φ.UV,   hFun_WV, hFun_UWV, φ.hFun, φ.hId]
          return mkApp5 swapFun φ.A C φ.B F_G c
        | none => do
          if ← f.exprIsId c then
            let UUV ← _Universe.mkFreshMVar
            let hFun_UUV : _HasFunctors φ.U φ.UV UUV := ⟨← TypedExpr.synthesize⟩
            let iuv ← mkFreshLevelMVar
            let hId_UV : _HasIdentity φ.UV iuv := ⟨← TypedExpr.synthesize⟩
            let F_G ← constructLambdaFunctor ⟨φ.A, φ.A _⟶ φ.B⟩ ⟨f.a, G⟩
            let dupFun ← getSynthInstanceDecl ``HasDupFun ``HasDupFun.dupFun
                                              [φ.U.u, φ.V.u, φ.UV.u, UUV.u,                   φ.iv]
                                              [φ.U,   φ.V,   φ.UV,   UUV,   φ.hFun, hFun_UUV, φ.hId]
            return mkApp3 dupFun φ.A φ.B F_G
          let UW ← _Universe.mkFreshMVar
          let hFun_UW : _HasFunctors φ.U W UW := ⟨← TypedExpr.synthesize⟩
          let iw ← mkFreshLevelMVar
          let hId_W : _HasIdentity W iw := ⟨← TypedExpr.synthesize⟩
          let F_c ← constructLambdaFunctor ⟨φ.A, C⟩ ⟨f.a, c⟩
          let UWV ← _Universe.mkFreshMVar
          let hFun_UWV : _HasFunctors φ.U WV UWV := ⟨← TypedExpr.synthesize⟩
          let iwv ← mkFreshLevelMVar
          let hId_WV : _HasIdentity WV iwv := ⟨← TypedExpr.synthesize⟩
          let F_G ← constructLambdaFunctor ⟨φ.A, C _⟶ φ.B⟩ ⟨f.a, G⟩
          let substFun ← getSynthInstanceDecl ``HasSubstFun ``HasSubstFun.substFun
                                              [φ.U.u, W.u, φ.V.u, UW.u, WV.u, UWV.u, φ.UV.u,                                     φ.iv]
                                              [φ.U,   W,   φ.V,   UW,   WV,   UWV,   φ.UV,   hFun_UW, hFun_WV, hFun_UWV, φ.hFun, φ.hId]
          return mkApp5 substFun φ.A C φ.B F_c F_G

  end

  -- Construct a functor for a given function expression.
  -- If the expression is a lambda abstraction, we use its components directly; otherwise we
  -- convert it to a lambda abstraction with a lambda application in its body (which can hopefully
  -- be unfolded).

  def constructFunctor (φ : DefFunData) : φ.mkFunArrow → MetaM φ.mkFun
    | Expr.lam n d b c => withLocalDecl n c.binderInfo d fun a : φ.A =>
      let t : φ.B := b.instantiate1 a
      constructLambdaFunctor φ ⟨a, t⟩
    | f => do
      let a := mkFVar (← mkFreshFVarId)
      withLocalDecl `a BinderInfo.default _⌈φ.A⌉ fun a : φ.A =>
        let t : φ.B := mkApp f a
        constructLambdaFunctor φ ⟨a, t⟩

  def constructDefFun (φ : DefFunData) (f : φ.mkFunArrow) : MetaM (φ.A _⟶{f} φ.B) := do
    let F ← constructFunctor φ f
    match ← _HasFunctors.getFunctorDefinition F with
    | some F' => return F'.F'
    | none => throwError m!"unable to extract definition from functor '{F}'"

  -- The `makeFunctor` tactic, which calls `constructFunctor` based on the target type and given
  -- term. Note that the target type determines how to elaborate the term, which enables us to omit
  -- the variable type in `Λ` expressions.

  def makeFunctor (mvarId : MVarId) (hf : Syntax) : TacticM Expr := do
    let type ← getMVarType mvarId
    let φ ← FunData.mkFreshMVar
    if ← isDefEq type _⌈φ.mkFun⌉ then
      let φ ← φ.instantiate
      let iv ← mkFreshLevelMVar
      let hId : _HasIdentity φ.V iv := ⟨← TypedExpr.synthesize⟩
      let f : φ.mkFunArrow ← TypedExpr.elaborate hf
      return ← constructFunctor ⟨φ⟩ f
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
  -- `(by makeFunctor f) ◄ byDef`.

  def functoriality (mvarId : MVarId) : TacticM Expr := do
    let type ← getMVarType mvarId
    let φ ← FunData.mkFreshMVar
    let iv ← mkFreshLevelMVar
    let hId : _HasIdentity φ.V iv := ⟨← TypedExpr.mkFreshMVar⟩
    let f : φ.mkFunArrow ← TypedExpr.mkFreshMVar
    if ← isDefEq type (φ.A _⟶{f} φ.B) then
      let φ ← φ.instantiate
      let iv ← instantiateLevelMVars iv
      let hId : _HasIdentity φ.V iv := ⟨← hId.h.instantiate⟩
      let f : φ.mkFunArrow ← f.instantiate
      return ← constructDefFun ⟨φ⟩ f
    throwTacticEx `functoriality mvarId m!"type '{type}' is not an application of 'HasFunctors.DefFun'"

  elab "functoriality" : tactic => do
    let mvarId ← getMainGoal
    withMVarContext mvarId do
      let e ← functoriality mvarId
      assignExprMVar mvarId e

end Lean
