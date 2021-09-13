import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors

import mathlib4_experiments.Data.Equiv.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w



def bundledUniverse {U : Universe.{u}} (φ : GeneralizedTypeClass.{u, u + 1, u} U) : Universe.{u} := ⟨Bundled φ⟩
instance bundledInstance {U : Universe.{u}} (φ : GeneralizedTypeClass.{u, u + 1, u} U) (A : bundledUniverse φ) : φ A.A := A.inst

def SimpleTypeClass := GeneralizedTypeClass.{u + 1, u + 2, u + 1} sort.{u + 1}
def simpleBundledUniverse (φ : SimpleTypeClass.{u}) : Universe.{u + 1} := bundledUniverse φ
instance simpleBundledInstance (φ : SimpleTypeClass.{u}) (A : simpleBundledUniverse φ) : φ ⌈A⌉ := bundledInstance φ A



namespace Bundled

  class HasInstanceFunctoriality (φ : SimpleTypeClass.{u}) (ψ : SimpleTypeClass.{v}) : Type ((max u v) + 1) where
  (IsFun {A : simpleBundledUniverse φ} {B : simpleBundledUniverse ψ} : (A → B) → Type (max u v))

  instance hasFunctoriality (φ : SimpleTypeClass.{u}) (ψ : SimpleTypeClass.{v}) [h : HasInstanceFunctoriality φ ψ] :
    HasFunctoriality.{u + 1, v + 1, (max u v) + 1} (simpleBundledUniverse φ) (simpleBundledUniverse ψ) :=
  ⟨h.IsFun⟩

  class HasFunctorInstances (φ : SimpleTypeClass.{u}) [h : HasInstanceFunctoriality φ φ] : Type (u + 1) where
  (funInst (A B : simpleBundledUniverse φ) : φ (A ⟶' B))

  instance hasEmbeddedFunctorType {φ : SimpleTypeClass.{u}} [HasInstanceFunctoriality φ φ] [h : HasFunctorInstances φ]
                                  (A B : simpleBundledUniverse φ) :
    HasEmbeddedType (simpleBundledUniverse φ) (A ⟶' B) :=
  { A := { A    := A ⟶' B,
           inst := h.funInst A B },
    h := Equiv.refl (A ⟶' B) }

  instance hasFunctors (φ : SimpleTypeClass.{u}) [HasInstanceFunctoriality φ φ] [HasFunctorInstances φ] :
    HasFunctors.{u + 1, u + 1, u + 1, u + 1} (simpleBundledUniverse φ) (simpleBundledUniverse φ)
                                             (simpleBundledUniverse φ) :=
  ⟨⟩

  instance hasEmbeddedFunctors (φ : SimpleTypeClass.{u}) [HasInstanceFunctoriality φ φ] [HasFunctorInstances φ] :
    HasEmbeddedFunctors.{u + 1} (simpleBundledUniverse φ) :=
  ⟨⟩

end Bundled
