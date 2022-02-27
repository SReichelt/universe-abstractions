import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.DependentTypes.DependentFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v iu upv



-- We can define functors to any universe with propositional identities, i.e. a universe where
-- identities of identities are trivial (such as `sort`). Such functors just need to map equivalent
-- values to equivalent values. In general this captures isomorphism invariance.

structure PropositionalFunctor {U : Universe.{u}} {V : Universe.{v}}
                               [HasIdentity.{u, iu} U] [HasIdentity.{v, 0} V]
                               (A : U) (B : V) :
  Sort (max 1 u v) where
(f                    : A → B)
(congrArg {a₁ a₂ : A} : a₁ ≃ a₂ → f a₁ ≃ f a₂)

namespace PropositionalFunctor

  variable (U : Universe.{u}) (V : Universe.{v}) [HasIdentity.{u, iu} U]
           [HasIdentity.{v, 0} V]

  instance (priority := low) hasPropositionalFunctors : HasFunctors U V sort.{max 1 u v} :=
  { Fun   := PropositionalFunctor,
    apply := PropositionalFunctor.f }

  instance (priority := low) hasPropositionalCongrArg : HasCongrArg U V :=
  ⟨PropositionalFunctor.congrArg⟩

end PropositionalFunctor

structure PropositionalDependentFunctor {U : Universe.{u}} {V : Universe.{v}}
                                        [HasIdentity.{u, iu} U] [HasTypeIdentity.{v, 0} V]
                                        {UpV : Universe.{upv}} [HasFunctors U {V} UpV]
                                        [HasCongrArg U {V}] {A : U} (φ : A ⟶ ⌊V⌋) :
  Sort (max 1 u v) where
(f                                    : HasFunctors.Pi φ)
(piCongrArg {a₁ a₂ : A} (e : a₁ ≃ a₂) : f a₁ ≃[HasCongrArg.propCongrArg φ e] f a₂)

namespace PropositionalDependentFunctor

  variable (U : Universe.{u}) (V : Universe.{v}) [HasIdentity.{u, iu} U] [HasTypeIdentity.{v, 0} V]
           {UpV : Universe.{upv}} [HasFunctors U {V} UpV] [HasCongrArg U {V}]

  instance (priority := low) hasPropositionalDependentFunctors : HasDependentFunctors U V sort.{max 1 u v} :=
  { Pi    := PropositionalDependentFunctor,
    apply := PropositionalDependentFunctor.f }

  instance (priority := low) hasPropositionalDependentCongrArg : HasDependentCongrArg U V :=
  ⟨PropositionalDependentFunctor.piCongrArg⟩

end PropositionalDependentFunctor
