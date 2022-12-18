import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Axioms.Singletons
import UniverseAbstractions.Universes.Layer1.Axioms.Products
import UniverseAbstractions.Universes.Layer1.Axioms.Coproducts
import UniverseAbstractions.Universes.Layer1.Axioms.Equivalences
import UniverseAbstractions.Universes.Layer1.Instances.Utils.Trivial



namespace UniverseAbstractions.Layer1

set_option autoImplicit false

universe u

open HasPreorderRelation



def unit : Universe.{0, 0} where
  I := True
  h := ⟨λ _ => True⟩

namespace unit

  def Inst : unit := trivial
  def inst : Inst := trivial

  def hasType {α : Sort u} (a : α) : HasTypeWithIntro unit α where
    A      := Inst
    hElim  := ⟨λ _ => a⟩
    hIntro := ⟨λ _ => inst⟩

  instance hasPiType {α : Sort u} (P : α → unit) : HasTypeWithIntro unit (∀ a, P a) :=
    hasType (λ _ => inst)

  instance hasFunctors (p : Prop) : HasFunctorsWithIntro p unit := ⟨⟩

  instance hasUnivFunctors : HasUnivFunctorsWithIntro unit unit := ⟨⟩

  instance hasExternalFullLogic (p : Prop) : HasExternalFullLogic p unit := inferInstance

  instance hasFullLogic : HasFullLogic unit := inferInstance

  instance hasTopType : HasTypeWithIntro unit PUnit.{0} := hasType PUnit.unit

  instance hasProductType (A B : unit) : HasTypeWithIntro unit (PProd A B) := hasType ⟨inst, inst⟩

  instance hasProducts : HasProducts unit := inferInstance

  instance hasCoproductType (A B : unit) : HasTypeWithIntro unit (PSum A B) :=
    hasType (PSum.inl inst)

  instance hasCoproducts : HasCoproducts unit := inferInstance

  instance hasIsomorphisms (α : Sort u) [HasPreorderRelation unit α] :
      HasIsomorphismsWithIntro α :=
    HasProducts.hasIsomorphismsWithIntro α

  instance hasEquivalences : HasEquivalences unit := inferInstance

  instance hasFullPositiveEquivalences : HasFullPositiveEquivalences unit := inferInstance
  instance hasPropEquivalences : HasPropEquivalences unit := inferInstance

  instance isPositiveUniverse : IsPositiveUniverse unit := ⟨⟩

end unit
