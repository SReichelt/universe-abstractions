import UniverseAbstractions.Lemmas.CombinatorExtensionality
import UniverseAbstractions.Meta.TypedExpr
import UniverseAbstractions.Meta.Helpers
import UniverseAbstractions.Meta.Reflect
import UniverseAbstractions.Meta.Tactics.Functoriality

-- TODO: Move to test file
import UniverseAbstractions.Lemmas.DerivedFunctorExtensionality


set_option autoBoundImplicitLocal false



-- The extensionality algorithm is conceptually similar to the functoriality algorithm. Given an
-- instance equivalence `e : b ≃ c` depending on `a : A`, i.e. `λ a => e`, it constructs an
-- equivalence of type `(Λ a => b) ≃{▻ λ a => e ◅} (Λ a => c)`, which we will write as
-- `Λ a => e` in this description (although we do not introduce any Lean notation for it).
--
-- The algorithm handles the following cases (and cases symmetrical to those, where applicable).
--
--  Input                 | Condition                   | Type                                                              | Output
-- -----------------------+-----------------------------+-------------------------------------------------------------------+------------------------------------------------------------------------------
--  `Λ a => congrFun h a` | `a` not in `h`              |                                                                   | `h` (optimization)
--  `Λ a => f`            | `a` not in `f`              |                                                                   | `defCongrArg (defConstFunFun _ _) f`
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



namespace Lean

  open Meta Elab Tactic Qq

  def constructCombinatorDefEquiv {φ : FunEquivData} (h : FunEquivLambdaAbstraction φ)
                                  (F₁ : h.f₁.FunDef) (F₂ : h.f₂.FunDef) :
      MetaM (h.EquivDef F₁ F₂) := do
    -- We (currently) only have single-universe versions of the extensionality axioms.
    -- So assume that `U` and `V` are the same universe.
    let hFun : mkHasFunctors φ.U φ.U φ.U := { h := φ.hFun.h }
    let hId : mkHasIdentity φ.U := { iu := φ.hId.iu, iuv := φ.hId.iuv, h := { h := φ.hId.h.h }}
    let hIdFun : mkHasIdFun φ.U ← InstanceExpr.mkFreshMVar
    let idFun_A : _⌈φ.U⌉_ ← _Universe.mkFreshTypeMVar
    let idFun_a : idFun_A ← _Universe.mkFreshInstMVar
    if ← isDefEq h.e (mkHasFunctors.mkByDef (mkHasIdFun.mkDefIdFun idFun_A) idFun_a) then
      let hIdFun : mkHasIdFun φ.U ← hIdFun.instantiate
      let idFun_A : _⌈φ.U⌉_ ← _Universe.instantiateTypeMVars idFun_A
      let idFun_a : idFun_A ← _Universe.instantiateInstMVars idFun_a
      let idFun_a_f : FunctorLambdaAbstraction ⟨φ.A, idFun_A⟩ := ⟨h.n, h.a, idFun_a⟩
      let idFun_a_F : idFun_a_f.FunDef ← constructLambdaFunctor idFun_a_f
      let _ := hFun.h
      let idFun_a_F' : Q($φ.A ⟶ $idFun_A) := idFun_a_F.F.F
      --let r := ⌜HasLinearFunOp.HasLinearFunExt.idFunDefExt₂ $idFun_a_F'⌝
      let b : Expr := idFun_a_f.b
      throwError "test: {b}, {idFun_a_F'}"
    let F₁'' : Expr ← F₁.functor
    let F₂'' : Expr ← F₂.functor
    let a' : Expr := h.a
    let e' : Expr := h.appliedEquiv F₁ F₂
    let h' : Expr := h.e
    let b₁' : Expr := h.b₁
    let b₂' : Expr := h.b₂
    throwError "unable to solve\n{F₁''} ≃⦃λ {a'} => {e'}⦄ {F₂''}\nusing\n{h'} : {b₁'} ≃ {b₂'}"

  -- `Fₓ` must match the result of `constructLambdaFunctor h.fₓ`.
  -- TODO: How exactly do we need to incorporate `Fₓ.F.eff`?
  partial def constructFunEquiv {φ : FunEquivData} (h : FunEquivLambdaAbstraction φ)
                                (F₁ : h.f₁.FunDef) (F₂ : h.f₂.FunDef) :
              MetaM (h.EquivDef F₁ F₂) := do
    if ← isDefEq F₁.F.F F₂.F.F then
      return ⟨none⟩
    let f : h.b₂ _≃ h.b₁ ← _Universe.mkFreshInstMVar
    if ← isDefEq h.e f⁻¹ then
      let f : h.b₂ _≃ h.b₁ ← _Universe.instantiateInstMVars f
      let h_f : FunEquivLambdaAbstraction φ := ⟨h.n, h.a, h.b₂, h.b₁, f⟩
      let e_f ← constructFunEquiv h_f F₂ F₁
      let e_f' : ⌈F₂.F.F ≃ F₁.F.F⌉ := e_f.e
      return ⟨HasInstanceEquivalences.symm e_f'⟩
    let b₀ : φ.B ← _Universe.mkFreshInstMVar
    let f : h.b₁ _≃ b₀ ← _Universe.mkFreshInstMVar
    let g : b₀ _≃ h.b₂ ← _Universe.mkFreshInstMVar
    if ← isDefEq h.e (g • f) then
      let b₀ : φ.B ← _Universe.instantiateInstMVars b₀
      let f : h.b₁ _≃ b₀ ← _Universe.instantiateInstMVars f
      let g : b₀ _≃ h.b₂ ← _Universe.instantiateInstMVars g
      let f₀ : FunctorLambdaAbstraction φ.toDefFunData := ⟨h.n, h.a, b₀⟩
      let F₀ : f₀.FunDef ← constructLambdaFunctor f₀
      let h_f : FunEquivLambdaAbstraction φ := ⟨h.n, h.a, h.b₁, b₀, f⟩
      let h_g : FunEquivLambdaAbstraction φ := ⟨h.n, h.a, b₀, h.b₂, g⟩
      let e_f ← constructFunEquiv h_f F₁ F₀
      let e_g ← constructFunEquiv h_g F₀ F₂
      let e_f' : ⌈F₁.F.F ≃ F₀.F.F⌉ := e_f.e
      let e_g' : ⌈F₀.F.F ≃ F₂.F.F⌉ := e_g.e
      return ⟨HasInstanceEquivalences.trans e_f' e_g'⟩
    constructCombinatorDefEquiv h F₁ F₂

  def proveExtensionality {φ : FunEquivData} (F₁ F₂ : φ.mkFun)
                          (h : mkHasCongrFun.mkFunEquiv F₁ F₂) :
      MetaM (F₁ ≃ F₂) :=
  DependentlyTypedTerm.fromFunction (v := mkHasIdentity.iu φ.V) (α := _⌈φ.A⌉)
                                    (β := mkHasCongrFun.mkFunEquivTypeFun F₁ F₂) h
                                    (fun {a} {T} t => do
    let t₁ : DependentTerm a _⌈φ.B⌉ := ⟨t.b.n, HasFunctors.apply F₁ a⟩
    let t₂ : DependentTerm a _⌈φ.B⌉ := ⟨t.b.n, HasFunctors.apply F₂ a⟩
    let h' : FunEquivLambdaAbstraction φ := FunEquivLambdaAbstraction.construct t₁ t₂ ⟨⟨t.b.n, t.b.b⟩⟩
    let F₁' : h'.f₁.FunDef := ⟨{ F   := F₁,
                                 eff := λ _ => none }⟩
    let F₂' : h'.f₂.FunDef := ⟨{ F   := F₂,
                                 eff := λ _ => none }⟩
    let e ← constructFunEquiv h' F₁' F₂'
    e.e)

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

end Lean



namespace Test

  variable {U : Universe} [HasIdentity U] [HasStandardFunctors U] (A B C D : U)

  def testRefl (F : A ⟶ B) : F ≃{λ a => MetaRelation.HasRefl.refl (F a)} F := by extensionality
  #print testRefl

  def testRightId (F : A ⟶ B) : F • HasIdFun.idFun A ≃{HasCongrArg.byArgDef ▻|} F := by extensionality

  def testLeftId (F : A ⟶ B) : HasIdFun.idFun B • F ≃{HasFunctors.byDef ▻|} F := by extensionality

  def testLeftIdRev (F : A ⟶ B) : F ≃{λ a => (HasFunctors.byDef • HasFunctors.byDef)⁻¹} HasIdFun.idFun B • F := by extensionality

  def testAssoc (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) :
    (H • G) • F ≃{HasFunctors.byDef ▻-◅ HasCongrArg.byArgDef} H • (G • F) :=
  by extensionality

end Test
