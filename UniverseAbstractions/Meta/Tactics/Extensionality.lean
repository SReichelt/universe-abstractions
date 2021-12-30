import UniverseAbstractions.Meta.TypedExpr
import UniverseAbstractions.Meta.Helpers
import UniverseAbstractions.Meta.Reflect
import UniverseAbstractions.Meta.Tactics.Functoriality
import UniverseAbstractions.Meta.Tactics.Extensionality.CombinatorExtensionality



set_option autoBoundImplicitLocal false
set_option maxHeartbeats 100000



-- The extensionality algorithm is conceptually similar to the functoriality algorithm. Given an
-- instance equivalence `e : b ≃ c` depending on `a : A`, i.e. `λ a => e`, it constructs an
-- equivalence of type `(Λ a => b) ≃{▻ λ a => e ◅} (Λ a => c)`, which we will write as
-- `Λ a => e` in this description (although we do not introduce any Lean notation for it).
--
-- The algorithm handles the following cases (and cases symmetrical to those, where applicable).
--
--  Input                 | Condition                   | Type                                                              | Output
-- -----------------------+-----------------------------+-------------------------------------------------------------------+------------------------------------------------------------------------------
--  `Λ a => f`            | `a` not in `f`              |                                                                   | `defCongrArg (defConstFunFun _ _) f`
--  `Λ a => congrFun h a` | `a` not in `h`              |                                                                   | `h` (optimization)
--  `Λ a => congrFun h t` | `a` not in `h`              |                                                                   | `defCongrArg (defCompFunFun (Λ a => t) _) h` (optimization)
--  `Λ a => refl b`       |                             |                                                                   | `refl (Λ a => b)`
--  `Λ a => f⁻¹`          |                             |                                                                   | `(Λ a => f)⁻¹`
--  `Λ a => g • f`        |                             |                                                                   | `(Λ a => g) • (Λ a => f)`
--  `Λ a => F.eff t`      | `F` is a combinator         |                                                                   | appropriate def from `CombinatorExtensionality.lean`
--  `Λ a => congrArg T f` | `a` not in `T`, `f : a ≃ a` | `T ≃ T`                                                           | `refl T`
--  `Λ a => congrArg T f` | `a` not in `T`, `f : s ≃ a` | `compFun (Λ a => s) T ≃ T`                                        | `rightId T • defCongrArg (defRevCompFunFun _ T) (Λ a => f)`
--  `Λ a => congrArg T f` | `a` not in `T`, `f : s ≃ t` | `compFun (Λ a => s) T ≃ compFun (Λ a => t) T`                     | `defCongrArg (defRevCompFunFun _ T) (Λ a => f)`
--  `Λ F => congrArg F f` | `F` not in `f`, `f : s ≃ t` | `revAppFun s _ ≃ revAppFun t _`                                   | `defCongrArg (defRevAppFunFun _ _) f`
--  `Λ a => congrArg T f` | `a` not in `f`, `f : s ≃ t` | `swapFun (Λ a => T) s ≃ swapFun (Λ a => T) t`                     | `defCongrArg (defSwapFunFun (Λ a => T)) f`
--  `Λ a => congrArg T f` |                 `f : a ≃ a` | `dupFun (Λ a => T) ≃ dupFun (Λ a => T)`                           | `refl (dupFun (Λ a => T))`
--  `Λ a => congrArg T f` |                 `f : s ≃ a` | `substFun (Λ a => s) (Λ a => T) ≃ dupFun (Λ a => T)`              | `substId (Λ a => T) • defCongrArg (defRevSubstFunFun (Λ a => T)) (Λ a => f)`
--  `Λ a => congrArg T f` |                 `f : s ≃ t` | `substFun (Λ a => s) (Λ a => T) ≃ substFun (Λ a => t) (Λ a => T)` | `defCongrArg (defRevSubstFunFun (Λ a => T)) (Λ a => f)`
--  `Λ a => ? f₁...fₙ`    |                             |                                                                   | `Λ a => (?Ext f₁...fₙ₋₁) fₙ` (with possible optimizations)



namespace Lean.Extensionality

  open Meta Elab Tactic Qq

  def constructPrimitiveFunctor {φ : DefFunData} (f : FunctorLambdaAbstraction φ) :
      MetaM f.FunDef :=
  Functoriality.constructLambdaFunctor f true

  -- Matches an application of `optionalRelation` without specifying the arguments.
  @[reducible] def UntypedEquiv := Option Expr

  def mkIdFunDefExt {φ : FunEquivData} [hFunOp : mkHasLinearFunOp φ.U] {X A : _⌈φ.U⌉_}
                    (a : FunctorLambdaAbstraction ⟨X, A⟩) :
      MetaM UntypedEquiv := do
    if ← a.term.isId then
      return none
    let hFunExt : mkHasLinearFunOp.mkHasLinearFunExt φ.U ← InstanceExpr.synthesize
    let _ := hFunExt.h
    let F_fun ← constructPrimitiveFunctor a
    let F : Q($X ⟶ $A) := F_fun.F.F
    ⌜HasLinearFunOp.HasLinearFunExt.idFunDefExt_a_fun $F⌝

  def mkRevAppFunDefExt {φ : FunEquivData} [hFunOp : mkHasLinearFunOp φ.U] {X A B : _⌈φ.U⌉_}
                        (a : FunctorLambdaAbstraction ⟨X, A⟩)
                        (F : FunctorLambdaAbstraction ⟨X, A _⟶ B⟩) :
      MetaM UntypedEquiv := do
    let _ := hFunOp.h
    match ← a.term.asConstant? with
    | some a' => none
    | none    =>
      match ← F.term.asConstant? with
      | some (F' : Q($A ⟶ $B)) =>
        let hFunExt : mkHasLinearFunOp.mkHasLinearFunExt φ.U ← InstanceExpr.synthesize
        let _ := hFunExt.h
        if ← a.term.isId then
          ⌜HasLinearFunOp.HasLinearFunExt.revAppFunDefExt_a_id $F'⌝
        else
          let H_fun ← constructPrimitiveFunctor a
          let H : Q($X ⟶ $A) := H_fun.F.F
          ⌜HasLinearFunOp.HasLinearFunExt.revAppFunDefExt_a_fun $H $F'⌝
      | none => throwError "TODO1"

  def mkCompFunDefExt {φ : FunEquivData} [hFunOp : mkHasLinearFunOp φ.U] {X A B C : _⌈φ.U⌉_}
                      (F : FunctorLambdaAbstraction ⟨X, A _⟶ B⟩)
                      (G : FunctorLambdaAbstraction ⟨X, B _⟶ C⟩)
                      (a : FunctorLambdaAbstraction ⟨X, A⟩) :
      MetaM UntypedEquiv := do
    let _ := hFunOp.h
    match ← F.term.asConstant? with
    | some (F' : Q($A ⟶ $B)) =>
      match ← G.term.asConstant? with
      | some (G' : Q($B ⟶ $C)) =>
        if ← a.term.isId then
          none
        else
          let hFunExt : mkHasLinearFunOp.mkHasLinearFunExt φ.U ← InstanceExpr.synthesize
          let _ := hFunExt.h
          let H_fun ← constructPrimitiveFunctor a
          let H : Q($X ⟶ $A) := H_fun.F.F
          ⌜HasLinearFunOp.HasLinearFunExt.compFunDefExt_a_fun $F' $G' $H⌝
      | none =>
        match ← a.term.asConstant? with
        | some (a' : Q($A)) =>
          let hFunExt : mkHasLinearFunOp.mkHasLinearFunExt φ.U ← InstanceExpr.synthesize
          let _ := hFunExt.h
          if ← G.term.isId then
            ⌜HasLinearFunOp.HasLinearFunExt.compFunDefExt_G_id $F' $C $a'⌝
          else
            let G_fun ← constructPrimitiveFunctor G
            let G' : Q($X ⟶ $B ⟶ $C) := G_fun.F.F
            ⌜HasLinearFunOp.HasLinearFunExt.compFunDefExt_G_fun $F' $G' $a'⌝
        | none => throwError "TODO2"
    | none =>
      match ← G.term.asConstant? with
      | some (G' : Q($B ⟶ $C)) =>
        match ← a.term.asConstant? with
        | some (a' : Q($A)) =>
          let hFunExt : mkHasLinearFunOp.mkHasLinearFunExt φ.U ← InstanceExpr.synthesize
          let _ := hFunExt.h
          if ← F.term.isId then
            ⌜HasLinearFunOp.HasLinearFunExt.compFunDefExt_F_id $G' $a'⌝
          else
            let F_fun ← constructPrimitiveFunctor F
            let F' : Q($X ⟶ $A ⟶ $B) := F_fun.F.F
            ⌜HasLinearFunOp.HasLinearFunExt.compFunDefExt_F_fun $F' $G' $a'⌝
        | none => throwError "TODO3"
      | none => throwError "TODO4"

  def mkCompFunFunDefExt {φ : FunEquivData} [hFunOp : mkHasLinearFunOp φ.U] {X A B C : _⌈φ.U⌉_}
                         (F : FunctorLambdaAbstraction ⟨X, A _⟶ B⟩)
                         (G : FunctorLambdaAbstraction ⟨X, B _⟶ C⟩) :
      MetaM UntypedEquiv := do
    let _ := hFunOp.h
    match ← F.term.asConstant? with
    | some (F' : Q($A ⟶ $B)) => none
    | none =>
      match ← G.term.asConstant? with
      | some (G' : Q($B ⟶ $C)) =>
        if ← F.term.isId then
          none
        else
          let hFunExt : mkHasLinearFunOp.mkHasLinearFunExt φ.U ← InstanceExpr.synthesize
          let _ := hFunExt.h
          let F_fun ← constructPrimitiveFunctor F
          let F' : Q($X ⟶ $A ⟶ $B) := F_fun.F.F
          ⌜HasLinearFunOp.HasLinearFunExt.compFunFunDefExt_F_fun $F' $G'⌝
      | none => throwError "TODO5"

  def getSourceToDisplay {φ : FunEquivData} (h : FunEquivLambdaAbstraction φ) : MetaM Expr := do
    let C : _⌈φ.U⌉_ ← _Universe.mkFreshTypeMVar
    let g : ⌜$C → $φ.B⌝ ← TypedExpr.mkFreshMVar
    let G : C _⟶{g} φ.B ← TypedExpr.mkFreshMVar
    let c : C ← _Universe.mkFreshInstMVar
    if ← isDefEq h.e (mkHasFunctors.mkByDef G c) then
      mkHasFunctors.mkByDef' G c
    else
      h.e

  def constructCombinatorDefEquiv {φ : FunEquivData} (h : FunEquivLambdaAbstraction φ)
                                  (F₁ F₂ : φ.mkFun) :
      MetaM ⌈F₁ _≃_ F₂⌉ := do
    let hFunOp : mkHasLinearFunOp φ.U ← InstanceExpr.mkFreshMVar
    let idFun_A : _⌈φ.U⌉_ ← _Universe.mkFreshTypeMVar
    let idFun_a : idFun_A ← _Universe.mkFreshInstMVar
    if ← isDefEq h.e (mkHasFunctors.mkByDef (mkHasLinearFunOp.mkDefIdFun idFun_A) idFun_a) then
      let hFunOp : mkHasLinearFunOp φ.U ← hFunOp.instantiate
      let idFun_A : _⌈φ.U⌉_ ← _Universe.instantiateTypeMVars idFun_A
      let idFun_a : idFun_A ← _Universe.instantiateInstMVars idFun_a
      return ← mkIdFunDefExt ⟨h.n, h.a, idFun_a⟩
    let revAppFun_A : _⌈φ.U⌉_ ← _Universe.mkFreshTypeMVar
    let revAppFun_B : _⌈φ.U⌉_ ← _Universe.mkFreshTypeMVar
    let revAppFun_a : revAppFun_A ← _Universe.mkFreshInstMVar
    let revAppFun_F : revAppFun_A _⟶ revAppFun_B ← _Universe.mkFreshInstMVar
    if ← isDefEq h.e (mkHasFunctors.mkByDef (mkHasLinearFunOp.mkDefRevAppFun revAppFun_a revAppFun_B) revAppFun_F) then
      let hFunOp : mkHasLinearFunOp φ.U ← hFunOp.instantiate
      let revAppFun_A : _⌈φ.U⌉_ ← _Universe.instantiateTypeMVars revAppFun_A
      let revAppFun_B : _⌈φ.U⌉_ ← _Universe.instantiateTypeMVars revAppFun_B
      let revAppFun_a : revAppFun_A ← _Universe.instantiateInstMVars revAppFun_a
      let revAppFun_F : revAppFun_A _⟶ revAppFun_B ← _Universe.instantiateInstMVars revAppFun_F
      return ← mkRevAppFunDefExt ⟨h.n, h.a, revAppFun_a⟩ ⟨h.n, h.a, revAppFun_F⟩
    if ← isDefEq h.e (mkHasFunctors.mkByDef (mkHasLinearFunOp.mkDefRevAppFunFun revAppFun_A revAppFun_B) revAppFun_a) then
      return none
    let compFun_A : _⌈φ.U⌉_ ← _Universe.mkFreshTypeMVar
    let compFun_B : _⌈φ.U⌉_ ← _Universe.mkFreshTypeMVar
    let compFun_C : _⌈φ.U⌉_ ← _Universe.mkFreshTypeMVar
    let compFun_F : compFun_A _⟶ compFun_B ← _Universe.mkFreshInstMVar
    let compFun_G : compFun_B _⟶ compFun_C ← _Universe.mkFreshInstMVar
    let compFun_a : compFun_A ← _Universe.mkFreshInstMVar
    if ← isDefEq h.e (mkHasFunctors.mkByDef (mkHasLinearFunOp.mkDefCompFun compFun_F compFun_G) compFun_a) then
      let hFunOp : mkHasLinearFunOp φ.U ← hFunOp.instantiate
      let compFun_A : _⌈φ.U⌉_ ← _Universe.instantiateTypeMVars compFun_A
      let compFun_B : _⌈φ.U⌉_ ← _Universe.instantiateTypeMVars compFun_B
      let compFun_C : _⌈φ.U⌉_ ← _Universe.instantiateTypeMVars compFun_C
      let compFun_F : compFun_A _⟶ compFun_B ← _Universe.instantiateInstMVars compFun_F
      let compFun_G : compFun_B _⟶ compFun_C ← _Universe.instantiateInstMVars compFun_G
      let compFun_a : compFun_A ← _Universe.instantiateInstMVars compFun_a
      return ← mkCompFunDefExt ⟨h.n, h.a, compFun_F⟩ ⟨h.n, h.a, compFun_G⟩ ⟨h.n, h.a, compFun_a⟩
    if ← isDefEq h.e (mkHasFunctors.mkByDef (mkHasLinearFunOp.mkDefCompFunFun compFun_F compFun_C) compFun_G) then
      let hFunOp : mkHasLinearFunOp φ.U ← hFunOp.instantiate
      let compFun_A : _⌈φ.U⌉_ ← _Universe.instantiateTypeMVars compFun_A
      let compFun_B : _⌈φ.U⌉_ ← _Universe.instantiateTypeMVars compFun_B
      let compFun_C : _⌈φ.U⌉_ ← _Universe.instantiateTypeMVars compFun_C
      let compFun_F : compFun_A _⟶ compFun_B ← _Universe.instantiateInstMVars compFun_F
      let compFun_G : compFun_B _⟶ compFun_C ← _Universe.instantiateInstMVars compFun_G
      return ← mkCompFunFunDefExt ⟨h.n, h.a, compFun_F⟩ ⟨h.n, h.a, compFun_G⟩
    if ← isDefEq h.e (mkHasFunctors.mkByDef (mkHasLinearFunOp.mkDefCompFunFunFun compFun_A compFun_B compFun_C) compFun_F) then
      return none
    -- TODO: const, dup
    let F₁' : Expr := F₁
    let F₂' : Expr := F₂
    let h' : Expr ← getSourceToDisplay h
    let b₁' : Expr := h.b₁
    let b₂' : Expr := h.b₂
    throwError "unable to solve{indentD m!"{F₁'} ≃ {F₂'}"}\nusing{indentD m!"{h'} : {b₁'} ≃ {b₂'}"}"

  def constructCongrFunEquiv {φ : FunEquivData} (h : FunEquivLambdaAbstraction φ)
                             (F₁ F₂ : φ.mkFun) {C : _⌈φ.U⌉_} (G₁ G₂ : C _⟶ φ.B) (f : G₁ _≃ G₂)
                             (c : C) :
      MetaM ⌈F₁ _≃_ F₂⌉ := do
  let h_c : FunctorLambdaAbstraction ⟨⟨φ.A, C⟩⟩ := ⟨h.n, h.a, c⟩
  if ← h_c.term.isId then
    return (some f)
  else
    let F_fun ← constructPrimitiveFunctor h_c
    let F : φ.A _⟶ C := F_fun.rawFunctor
    let hFunOp : mkHasLinearFunOp φ.U ← InstanceExpr.synthesize
    let defCompFunFun := mkHasLinearFunOp.mkDefCompFunFun F φ.B
    let e : ⌈G₁ ⊙ F _≃ G₂ ⊙ F⌉ := mkHasCongrArg.mkDefCongrArg' defCompFunFun f
    return (some e)

  def printFunctorialityResults {φ : FunEquivData} (h : FunEquivLambdaAbstraction φ) :
      MetaM Unit := do
    let h_e_type ← inferType h.e
    let h_e_type_expected := _⌈h.b₁ __≃ h.b₂⌉
    -- TODO: For some reason, this check doesn't fail reliably.
    unless ← isDefEq h_e_type h_e_type_expected do
      throwError "internal extensionality error:{indentExpr h.e}\n{← mkHasTypeButIsExpectedMsg h_e_type h_e_type_expected}"
    let F₁_fun ← constructPrimitiveFunctor (φ := φ.toDefFunData) h.f₁
    let F₁' : Expr := F₁_fun.rawFunctor
    let F₂_fun ← constructPrimitiveFunctor (φ := φ.toDefFunData) h.f₂
    let F₂' : Expr := F₂_fun.rawFunctor
    trace[Meta.Tactic] "expected type by functoriality:{indentD m!"{F₁'} ≃ {F₂'}"}"

  mutual

    partial def constructFunEquiv {φ : FunEquivData} (h : FunEquivLambdaAbstraction φ)
                                  (F₁ F₂ : φ.mkFun) :
                MetaM ⌈F₁ _≃_ F₂⌉ := do
      -- TODO: custom trace class; does that only work with compilation?
      let F₁' : Expr := F₁
      let F₂' : Expr := F₂
      let h' : Expr ← getSourceToDisplay h
      let b₁' : Expr := h.b₁
      let b₂' : Expr := h.b₂
      trace[Meta.Tactic] "solving{indentD m!"{F₁'} ≃ {F₂'}"}\nusing{indentD m!"{h'} : {b₁'} ≃ {b₂'}"}"
      --let h_e_type ← inferType h.e
      --let h_e_type_expected := _⌈h.b₁ __≃ h.b₂⌉
      --trace[Meta.Tactic] "debug:{indentExpr h'}\n{← mkHasTypeButIsExpectedMsg h_e_type h_e_type_expected}"
      let e ← constructFunEquiv' h F₁ F₂
      match e with
      | some (e' : Expr) =>
        trace[Meta.Tactic] "result:{indentD m!"{e'} : {F₁'} ≃ {F₂'}"}\nusing{indentD m!"{h'} : {b₁'} ≃ {b₂'}"}"
        -- TODO: disable this debug check
        let e_type ← inferType e'
        let e_type_expected := _⌈F₁ __≃ F₂⌉
        unless ← isDefEq e_type e_type_expected do
          printFunctorialityResults h
          throwError "internal extensionality error:{indentExpr e'}\n{← mkHasTypeButIsExpectedMsg e_type e_type_expected}"
      | none =>
        trace[Meta.Tactic] "result:{indentD m!"refl _ : {F₁'} ≃ {F₂'}"}\nusing{indentD m!"{h'} : {b₁'} ≃ {b₂'}"}"
        -- TODO: disable this debug check
        unless ← isDefEq F₁ F₂ do
          printFunctorialityResults h
          throwError "internal extensionality error: got refl result, but {F₁'} ≠ {F₂'}"
      e

    partial def constructFunEquiv' {φ : FunEquivData} (h : FunEquivLambdaAbstraction φ)
                                   (F₁ F₂ : φ.mkFun) :
                MetaM ⌈F₁ _≃_ F₂⌉ := do
      -- TODO: const
      let C : _⌈φ.U⌉_ ← _Universe.mkFreshTypeMVar
      let G₁ : C _⟶ φ.B ← _Universe.mkFreshInstMVar
      let G₂ : C _⟶ φ.B ← _Universe.mkFreshInstMVar
      let f : G₁ _≃ G₂ ← _Universe.mkFreshInstMVar
      let c : C ← _Universe.mkFreshInstMVar
      let hCongrFun : mkHasCongrFun φ.U φ.U ← InstanceExpr.mkFreshMVar
      if ← isDefEq h.e (mkHasCongrFun.mkCongrFun' f c) then
        let C : _⌈φ.U⌉_ ← _Universe.instantiateTypeMVars C
        let G₁ : C _⟶ φ.B ← _Universe.instantiateInstMVars G₁
        let G₂ : C _⟶ φ.B ← _Universe.instantiateInstMVars G₂
        let f : G₁ _≃ G₂ ← _Universe.instantiateInstMVars f
        let h_f : FunEquivLambdaAbstraction φ := ⟨h.n, h.a, G₁, G₂, f⟩
        match ← h_f.term.asConstant? with
        | some (f' : G₁ _≃ G₂) =>
          let c : C ← _Universe.instantiateInstMVars c
          return ← constructCongrFunEquiv h F₁ F₂ G₁ G₂ f' c
        | none => ()
      let refl : h.b₁ _≃ h.b₁ := MetaRelation.HasRefl.refl h.b₁
      if ← isDefEq h.e refl then
        return none
      let f : h.b₂ _≃ h.b₁ ← _Universe.mkFreshInstMVar
      if ← isDefEq h.e f⁻¹ then
        let f : h.b₂ _≃ h.b₁ ← _Universe.instantiateInstMVars f
        let h_f : FunEquivLambdaAbstraction φ := ⟨h.n, h.a, h.b₂, h.b₁, f⟩
        let e_f ← constructFunEquiv h_f F₂ F₁
        return e_f⁻¹
      let b₀ : φ.B ← _Universe.mkFreshInstMVar
      let f : h.b₁ _≃ b₀ ← _Universe.mkFreshInstMVar
      let g : b₀ _≃ h.b₂ ← _Universe.mkFreshInstMVar
      if ← isDefEq h.e (g • f) then
        let b₀ : φ.B ← _Universe.instantiateInstMVars b₀
        let f : h.b₁ _≃ b₀ ← _Universe.instantiateInstMVars f
        let g : b₀ _≃ h.b₂ ← _Universe.instantiateInstMVars g
        -- TODO: Can we use a metavariable for `F₀` instead?
        let F₀_fun ← constructPrimitiveFunctor (φ := φ.toDefFunData) ⟨h.n, h.a, b₀⟩
        let F₀ : φ.mkFun := F₀_fun.rawFunctor
        let e_f ← constructFunEquiv ⟨h.n, h.a, h.b₁, b₀, f⟩ F₁ F₀
        let e_g ← constructFunEquiv ⟨h.n, h.a, b₀, h.b₂, g⟩ F₀ F₂
        return e_g • e_f
      let C : _⌈φ.U⌉_ ← _Universe.mkFreshTypeMVar
      let G : C _⟶ φ.B ← _Universe.mkFreshInstMVar
      let c₁ : C ← _Universe.mkFreshInstMVar
      let c₂ : C ← _Universe.mkFreshInstMVar
      let f : c₁ _≃ c₂ ← _Universe.mkFreshInstMVar
      if ← isDefEq h.e (mkHasCongrArg.mkCongrArg' G f) then
        let C : _⌈φ.U⌉_ ← _Universe.instantiateTypeMVars C
        let G : C _⟶ φ.B ← _Universe.instantiateInstMVars G
        let c₁ : C ← _Universe.instantiateInstMVars c₁
        let c₂ : C ← _Universe.instantiateInstMVars c₂
        let f : c₁ _≃ c₂ ← _Universe.instantiateInstMVars f
        return ← constructCongrArgEquiv h F₁ F₂ ⟨h.n, h.a, G⟩ ⟨h.n, h.a, c₁, c₂, f⟩
      -- TODO: Optimization: If `h.e` is `defCongrArg _ f` with `f : a₁ ≃ a₂`, and
      -- `F₁` is functorial in `a₁`, and `F₂` is functorial in `a₂` in the same way,
      -- use `defCongrArg` with that functor.
      match ← constructCombinatorDefEquiv h F₁ F₂ with
      | some (e : _⌈F₁ __≃ F₂⌉) => some (← TypedExpr.unfold_once e)
      | none                    => none

    partial def constructCongrArgEquiv {φ : FunEquivData} (h : FunEquivLambdaAbstraction φ)
                                       (F₁ F₂ : φ.mkFun) {C : _⌈φ.U⌉_}
                                       (G : FunctorLambdaAbstraction ⟨φ.A, C _⟶ φ.B⟩)
                                       (f : FunEquivLambdaAbstraction ⟨φ.A, C⟩) :
                MetaM ⌈F₁ _≃_ F₂⌉ := do
      match ← G.term.asConstant? with
      | some (G' : C _⟶ φ.B) =>
        let c₁_id ← f.f₁.term.isId
        let c₂_id ← f.f₂.term.isId
        if c₁_id && c₂_id then
          return none
        let c₁_fun ← constructPrimitiveFunctor f.f₁
        let c₂_fun ← constructPrimitiveFunctor f.f₂
        let F_c₁ : φ.A _⟶ C := c₁_fun.rawFunctor
        let F_c₂ : φ.A _⟶ C := c₂_fun.rawFunctor
        let e_f : F_c₁ _≃_ F_c₂ ← constructFunEquiv f F_c₁ F_c₂
        let hFunOp : mkHasLinearFunOp φ.U ← InstanceExpr.synthesize
        let defRevCompFunFun := mkHasLinearFunOp.mkDefRevCompFunFun φ.A G'
        let e : ⌈G' ⊙ F_c₁ _≃_ G' ⊙ F_c₂⌉ := mkHasCongrArg.mkDefCongrArg defRevCompFunFun e_f
        let e₁ : ⌈G' ⊙ F_c₁ _≃_ F₁⌉ ←
            if c₁_id then
              let hFunExt : mkHasLinearFunOp.mkHasLinearFunExt φ.U ← InstanceExpr.synthesize
              some (mkHasLinearFunOp.mkHasLinearFunExt.mkRightId G')
            else
              none
        let e₂ : ⌈G' ⊙ F_c₂ _≃_ F₂⌉ ←
            if c₂_id then
              let hFunExt : mkHasLinearFunOp.mkHasLinearFunExt φ.U ← InstanceExpr.synthesize
              some (mkHasLinearFunOp.mkHasLinearFunExt.mkRightId G')
            else
              none
        pure (e₂ • e • e₁⁻¹)
      | none =>
        match ← f.term.asConstant? with
        | some (f' : ⌈f.b₁ _≃ f.b₂⌉) =>
          let hFunOp : mkHasLinearFunOp φ.U ← InstanceExpr.synthesize
          if ← G.term.isId then
            let defRevAppFunFun := mkHasLinearFunOp.mkDefRevAppFunFun C φ.B
            let e := mkHasCongrArg.mkDefCongrArg' defRevAppFunFun f'
            pure (some e)
          else
            let G_fun ← constructPrimitiveFunctor G
            let F_G : φ.A _⟶ C _⟶ φ.B := G_fun.rawFunctor
            let defSwapFunFun := mkHasLinearFunOp.mkDefSwapFunFun F_G
            let e := mkHasCongrArg.mkDefCongrArg' defSwapFunFun f'
            pure (some e)
        | none => throwError "TODO6"

  end

  def proveExtensionality {φ : FunEquivData} (F₁ F₂ : φ.mkFun)
                          (h : mkHasCongrFun.mkFunEquiv F₁ F₂) :
      MetaM (F₁ ≃ F₂) :=
  DependentlyTypedTerm.fromFunction (v := mkHasIdentity.iu φ.U) (α := _⌈φ.A⌉)
                                    (β := mkHasCongrFun.mkFunEquivTypeFun F₁ F₂) h
                                    (fun {a} {T} t => do
    let t₁ : DependentTerm a _⌈φ.B⌉ := ⟨t.b.n, HasFunctors.apply F₁ a⟩
    let t₂ : DependentTerm a _⌈φ.B⌉ := ⟨t.b.n, HasFunctors.apply F₂ a⟩
    let h' : FunEquivLambdaAbstraction φ := FunEquivLambdaAbstraction.construct t₁ t₂ ⟨⟨t.b.n, t.b.b⟩⟩
    constructFunEquiv h' F₁ F₂)

  def extensionality (mvarId : MVarId) : TacticM Expr := do
    let type ← getMVarType mvarId
    let φ ← FunEquivData.mkFreshMVar
    let F₁ : φ.mkFun ← _Universe.mkFreshInstMVar
    let F₂ : φ.mkFun ← _Universe.mkFreshInstMVar
    unless ← isDefEq type _⌈F₁ __≃ F₂⌉ do
      throwTacticEx `extensionality mvarId m!"type '{type}' is not an equivalence of functors"
    let φ ← φ.instantiate
    let F₁ : φ.mkFun ← _Universe.instantiateInstMVars F₁
    let F₂ : φ.mkFun ← _Universe.instantiateInstMVars F₂
    let h : mkHasCongrFun.mkFunEquiv F₁ F₂ ← TypedExpr.mkFreshMVar
    unless ← isDefEq type _⌈mkHasCongrFun.mkIsExtensional F₁ F₂ h⌉ do
      throwTacticEx `extensionality mvarId m!"type '{type}' is not an instance of `HasCongrFun.IsExtensional`"
    let h : mkHasCongrFun.mkFunEquiv F₁ F₂ ← h.instantiate
    let e ← proveExtensionality F₁ F₂ h
    mkHasInstanceEquivalences.materialize e

  elab "extensionality" : tactic => do
    let mvarId ← getMainGoal
    withMVarContext mvarId do
      let e ← extensionality mvarId
      assignExprMVar mvarId e

end Lean.Extensionality
