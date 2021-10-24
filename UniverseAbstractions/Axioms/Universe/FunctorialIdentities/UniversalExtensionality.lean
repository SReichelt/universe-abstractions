import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.DependentTypes.Properties
import UniverseAbstractions.Axioms.Universe.DependentTypes.DependentFunctors
import UniverseAbstractions.Axioms.Universe.FunctorialIdentities.IdentityQuantification



set_option autoBoundImplicitLocal false
--set_option pp.universes true



-- TODO: We probably also want to state the reverse direction, i.e. a (dependently) functorial
--       version of `congrFun`.



class HasUniversalFunctorExtensionality (U V : Universe) {UV VI UpVI UVI : Universe}
                                        [HasInstanceEquivalences V VI] [HasIdentity {VI}]
                                        [HasIdentity UV] [HasFunctors U V UV]
                                        [HasFunctors U {VI} UpVI] [HasFunEqProp U V]
                                        [HasDependentFunctors U VI UVI] where
(funExt {A : U} {B : V} {F₁ F₂ : A ⟶ B} : (Π (F₁ {≃} F₂)) → F₁ ≃ F₂)



class HasUniversalDependentFunctorExtensionality (U V : Universe) {UV VI UpV UpVI UVI : Universe}
                                                 [HasInstanceEquivalences V VI] [HasIdentity {VI}]
                                                 [HasIdentity UV] [HasFunctors U {V} UpV]
                                                 [HasDependentFunctors U V UV]
                                                 [HasFunctors U {VI} UpVI] [HasPiEqProp U V]
                                                 [HasDependentFunctors U VI UVI] where
(piExt {A : U} {φ : A ⟶ ⌊V⌋} {F₁ F₂ : Π φ} : (Π (F₁ {Π≃} F₂)) → F₁ ≃ F₂)
