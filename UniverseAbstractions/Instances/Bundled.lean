import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors

import mathlib4_experiments.Data.Equiv.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w



def bundledUniverse {U : Universe.{u}} (C : GeneralizedTypeClass.{u, u + 1, u} U) : Universe.{u} := ⟨Bundled C⟩
instance bundledInstance {U : Universe.{u}} (C : GeneralizedTypeClass.{u, u + 1, u} U) (S : bundledUniverse C) : C S.α := S.inst

def SimpleTypeClass := GeneralizedTypeClass.{u + 1, u + 2, u + 1} sort.{u + 1}
def simpleBundledUniverse (C : SimpleTypeClass.{u}) : Universe.{u + 1} := bundledUniverse C
instance simpleBundledInstance (C : SimpleTypeClass.{u}) (S : simpleBundledUniverse C) : C ⌈S⌉ := bundledInstance C S



namespace Bundled

  class HasInstanceFunctoriality (C : SimpleTypeClass.{u}) (D : SimpleTypeClass.{v}) : Type ((max u v) + 1) where
  (IsFun {S : simpleBundledUniverse C} {T : simpleBundledUniverse D} : (S → T) → Type (max u v))

  instance hasFunctoriality (C : SimpleTypeClass.{u}) (D : SimpleTypeClass.{v}) [h : HasInstanceFunctoriality C D] :
    HasFunctoriality.{u + 1, v + 1, (max u v) + 1} (simpleBundledUniverse C) (simpleBundledUniverse D) :=
  ⟨h.IsFun⟩

  class HasFunctorInstances (C : SimpleTypeClass.{u}) [h : HasInstanceFunctoriality C C] : Type (u + 1) where
  (funInst (S T : simpleBundledUniverse C) : C (S ⟶' T))

  instance hasEmbeddedFunctorType {C : SimpleTypeClass.{u}} [HasInstanceFunctoriality C C] [h : HasFunctorInstances C]
                                  (S T : simpleBundledUniverse C) :
    HasEmbeddedType (simpleBundledUniverse C) (S ⟶' T) :=
  { α := { α    := S ⟶' T,
           inst := h.funInst S T },
    h := Equiv.refl (S ⟶' T) }

  instance hasFunctors (C : SimpleTypeClass.{u}) [HasInstanceFunctoriality C C] [HasFunctorInstances C] :
    HasFunctors.{u + 1, u + 1, u + 1, u + 1} (simpleBundledUniverse C) (simpleBundledUniverse C)
                                             (simpleBundledUniverse C) :=
  ⟨⟩

  instance hasEmbeddedFunctors (C : SimpleTypeClass.{u}) [HasInstanceFunctoriality C C] [HasFunctorInstances C] :
    HasEmbeddedFunctors.{u + 1} (simpleBundledUniverse C) :=
  ⟨⟩

end Bundled
