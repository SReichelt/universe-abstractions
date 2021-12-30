import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.FunctorExtensionality
import UniverseAbstractions.Lemmas.DerivedFunctors
import UniverseAbstractions.Lemmas.DerivedFunctorExtensionality
import UniverseAbstractions.Meta.Tactics.Extensionality



set_option autoBoundImplicitLocal false
--set_option pp.universes true
--set_option pp.all true

universe u v iu iuv



namespace Test

  open MetaRelation HasFunctors HasCongrArg HasCongrFun HasLinearFunOp

  set_option trace.Meta.Tactic true

  variable {U : Universe.{u, v}} [HasIdentity.{u, iu, v, iuv} U] [HasStandardFunctors U] (A B C D E : U)

  def testRefl (F : A ⟶ B) : F ≃{λ a => HasRefl.refl (F a)} F := by extensionality
  #print testRefl

  def testCongrFun (F₁ F₂ : A ⟶ B) (h : F₁ ≃ F₂) : F₁ ≃{λ a => congrFun h a} F₂ := by extensionality
  #print testCongrFun

  def testRightId (F : A ⟶ B) : F • idFun A ≃{byArgDef ▻|} F := by extensionality
  #print testRightId

  def testRightIdSymm (F : A ⟶ B) : F ≃{λ _ => (byArgDef • byDef)⁻¹} F • idFun A := by extensionality
  #print testRightIdSymm

  def testLeftId (F : A ⟶ B) : idFun B • F ≃{byDef ▻|} F := by extensionality
  #print testLeftId

  def testLeftIdSymm (F : A ⟶ B) : F ≃{λ _ => (byDef • byDef)⁻¹} idFun B • F := by extensionality
  #print testLeftIdSymm

  def testTestLeftId :  revCompFunFun A (idFun B) ≃{▻ λ F => testLeftId A B F ◅} idFun (A ⟶ B) := by extensionality
  #print testTestLeftId

  def testAssoc (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) :
    (H • G) • F ≃{byDef ▻-◅ byArgDef} H • (G • F) :=
  by extensionality
  #print testAssoc

  def testAssoc₄ (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) (I : D ⟶ E) :
    ((I • H) • G) • F ≃{byDef • byDef ▻-◅ congrArg I (byArgDef • byDef)} I • (H • (G • F)) :=
  by extensionality
  #print testAssoc₄

  def testRevAppFunFun (a₁ a₂ : A) (h : a₁ ≃ a₂) :
    revAppFun a₁ B ≃{▻ λ F => congrArg F h ◅} revAppFun a₂ B :=
  by extensionality
  #print testRevAppFunFun

  def testCompFunFun (F : A ⟶ B) (G₁ G₂ : B ⟶ C) (h : G₁ ≃ G₂) :
    G₁ • F ≃{▻ λ a => congrFun h (F a) ◅} G₂ • F :=
  by extensionality
  #print testCompFunFun

  def testRevCompFunFun (F₁ F₂ : A ⟶ B) (h : F₁ ≃ F₂) (G : B ⟶ C) :
    G • F₁ ≃{▻ λ a => congrArg G (congrFun h a) ◅} G • F₂ :=
  by extensionality
  #print testRevCompFunFun

  -- TODO: optimize (using IsFunApp)
  def testCompFunFunFun (F₁ F₂ : A ⟶ B) (h : F₁ ≃ F₂) :
    compFunFun F₁ C ≃{▻ λ G => testRevCompFunFun A B C F₁ F₂ h G ◅} compFunFun F₂ C :=
  by extensionality
  #print testCompFunFunFun

  -- TODO: optimize
  def testRevCompFunFunFun (G₁ G₂ : B ⟶ C) (h : G₁ ≃ G₂) :
    revCompFunFun A G₁ ≃{▻ λ F => testCompFunFun A B C F G₁ G₂ h ◅} revCompFunFun A G₂ :=
  by extensionality
  #print testRevCompFunFunFun

  def testSwapFunFun (F : A ⟶ B ⟶ C) (b₁ b₂ : B) (h : b₁ ≃ b₂) :
    swapFun F b₁ ≃{▻ λ a => congrArg (F a) h ◅} swapFun F b₂ :=
  by extensionality
  #print testSwapFunFun

  -- TODO: optimize
  def testRevSwapFunFun (F₁ F₂ : A ⟶ B ⟶ C) (h : F₁ ≃ F₂) (b : B) :
    swapFun F₁ b ≃{▻ λ a => congrFun (congrFun h a) b ◅} swapFun F₂ b :=
  by extensionality
  #print testRevSwapFunFun

  -- TODO: optimize
  def testSwapFunFunFun (F₁ F₂ : A ⟶ B ⟶ C) (h : F₁ ≃ F₂) :
    swapFunFun F₁ ≃{▻ λ b => testRevSwapFunFun A B C F₁ F₂ h b ◅} swapFunFun F₂ :=
  by extensionality
  #print testSwapFunFunFun

  -- TODO: optimize
  def testRevSwapFunFunFun (b₁ b₂ : B) (h : b₁ ≃ b₂) :
    revSwapFunFun A b₁ C ≃{▻ λ F => testSwapFunFun A B C F b₁ b₂ h ◅} revSwapFunFun A b₂ C :=
  by extensionality
  #print testSwapFunFunFun

end Test
