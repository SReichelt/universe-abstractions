import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.DependentTypes.Properties
import UniverseAbstractions.Axioms.Universe.DependentTypes.DependentFunctors
import UniverseAbstractions.Axioms.Universe.DependentTypes.DependentProducts
import UniverseAbstractions.Axioms.Universe.FunctorialIdentities.IdentityQuantification
import UniverseAbstractions.Lemmas.DerivedProductFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true



namespace FunctorProperties

  open HasSubLinearFunOp HasInternalProducts HasTypeIdentity

  variable {U UI : Universe} [HasInstanceEquivalences U UI] [HasInternalFunctors U]
           [HasAffineFunOp U] [HasInternalProducts U] [hUI : HasTypeIdentity UI]
           [HasInternalProducts UI] [HasFunctors U {UI} {UI}] [HasDependentFunctors U UI UI]
           [HasInternalFunctors {UI}] [HasTypeBiFun hUI.hasInternalFunctors.Fun]
           [HasCongrFun {UI} {UI}] [HasBiCompFun U {UI} {UI} {UI}] [HasFunEqProp U U]
           {A B : U} (F : A ⟶ B)

  def InjectiveAt (a₁ a₂ : A) : UI := F a₁ ≃ F a₂ ⟶ a₁ ≃ a₂

  def injectiveProp : A ⊓ A ⟶ ⌊UI⌋ :=
  F • fstFun A A {≃} F • sndFun A A {⟶} fstFun A A {≃} sndFun A A

  @[reducible] def Injective : UI := Π (injectiveProp F)

  variable [hSigma : HasDependentProducts U UI UI] [HasDependentTypeFun hSigma.Sigma]
           [HasCompFun U {UI} {UI}]

  def SurjectiveAt (b : B) : UI := Σ (F {≃} constFun A b)

  @[reducible] def surjectiveProp : B ⟶ A ⟶ ⌊UI⌋ := constFun B F {≃} constFunFun A B

  @[reducible] def Surjective : UI := Π ({Σ} (surjectiveProp F))

  def preimage (h : Surjective F) (b : B) : A :=
  HasDependentProducts.fst (castToDef (h b) : _)

  -- TODO: preimage functor ...

  @[reducible] def Bijective : UI := Injective F ⊓ Surjective F

  -- TODO: construct equivalence

end FunctorProperties
