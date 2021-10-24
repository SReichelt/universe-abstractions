import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences
import UniverseAbstractions.Axioms.Universe.DependentTypes.Properties
import UniverseAbstractions.Axioms.Universe.DependentTypes.DependentFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true



class HasFunEqProp (U V : Universe) {UV VI UpVI : Universe}
                   [HasInstanceEquivalences V VI] [HasIdentity {VI}]
                   [HasFunctors U V UV] [HasFunctors U {VI} UpVI] where
(defEqProp {A : U} {B : V} (F₁ F₂ : A ⟶ B) : A ⟶{λ a => F₁ a ≃ F₂ a} ⌊VI⌋)

namespace HasFunEqProp

  variable {U V UV VI UpVI : Universe} [HasInstanceEquivalences V VI] [HasIdentity {VI}]
           [HasFunctors U V UV] [HasFunctors U {VI} UpVI] [HasFunEqProp U V]

  @[reducible] def eqProp {A : U} {B : V} (F₁ F₂ : A ⟶ B) : A ⟶ ⌊VI⌋ := defEqProp F₁ F₂
  infixr:25 " {≃} " => HasFunEqProp.eqProp

end HasFunEqProp



class HasPiEqProp (U V : Universe) {UpV UV VI UpVI : Universe}
                  [HasInstanceEquivalences V VI] [HasIdentity {VI}] [HasFunctors U {V} UpV]
                  [HasDependentFunctors U V UV] [HasFunctors U {VI} UpVI] where
(defEqProp {A : U} {φ : A ⟶ ⌊V⌋} (F₁ F₂ : Π φ) : A ⟶{λ a => F₁ a ≃ F₂ a} ⌊VI⌋)

namespace HasPiEqProp

  variable {U V UpV UV VI UpVI : Universe} [HasInstanceEquivalences V VI] [HasIdentity {VI}]
           [HasFunctors U {V} UpV] [HasDependentFunctors U V UV] [HasFunctors U {VI} UpVI]
           [HasPiEqProp U V]

  @[reducible] def eqProp {A : U} {φ : A ⟶ ⌊V⌋} (F₁ F₂ : Π φ) : A ⟶ ⌊VI⌋ := defEqProp F₁ F₂
  infixr:25 " {Π≃} " => HasPiEqProp.eqProp

end HasPiEqProp
