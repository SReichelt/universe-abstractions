import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Axioms.Singletons
import UniverseAbstractions.Universes.Layer1.Axioms.Products
import UniverseAbstractions.Universes.Layer1.Axioms.Coproducts
import UniverseAbstractions.Universes.Layer1.Axioms.Equivalences
import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations
import UniverseAbstractions.Universes.Layer1.Instances.Utils.Trivial

import UniverseAbstractions.MathlibFragments.Init.CoreExt



namespace UniverseAbstractions.Layer1

set_option autoImplicit false

universe u

open HasPreorderRelation



def prop : Universe.{0, 1} := ⟨Prop⟩

namespace prop

  instance hasPiType {α : Sort u} (P : α → prop) : HasTypeWithIntro prop (∀ a, P a) :=
    HasTypeWithIntro.native _

  instance hasFunctors (α : Sort u) : HasFunctorsWithIntro α prop := ⟨⟩

  instance hasUnivFunctors : HasUnivFunctorsWithIntro prop prop := ⟨⟩

  instance hasExternalFullLogic (α : Sort u) : HasExternalFullLogic α prop := inferInstance

  instance hasFullLogic : HasFullLogic prop := inferInstance

  instance hasTopType : HasTypeWithIntro prop PUnit.{0} where
    T      := True
    hElim  := ⟨λ _ => PUnit.unit⟩
    hIntro := ⟨λ _ => trivial⟩

  instance hasTop : HasTop prop := inferInstance

  instance hasBotType : HasType prop PEmpty.{0} where
    T     := False
    hElim := ⟨False.elim⟩

  instance hasBot : HasBot prop := inferInstance

  instance hasClassicalLogic : HasClassicalLogic prop := ⟨@Classical.byContradiction⟩

  noncomputable instance hasSigmaType {α : Sort u} (β : α → Prop) :
      HasTypeWithIntro prop (PSigma β) where
    T      := ∃ a, β a
    hElim  := ⟨λ h => Classical.choice (let ⟨i, j⟩ := h; ⟨⟨i, j⟩⟩)⟩
    hIntro := ⟨λ ⟨i, j⟩ => ⟨i, j⟩⟩

  noncomputable instance hasExternalSigmaType {α : Sort u} (β : α → Prop) :
      HasExternalSigmaType prop β :=
    inferInstance

  instance hasProductType (p q : prop) : HasTypeWithIntro prop (PProd p q) where
    T      := p ∧ q
    hElim  := ⟨λ ⟨l, r⟩ => ⟨l, r⟩⟩
    hIntro := ⟨λ ⟨l, r⟩ => ⟨l, r⟩⟩

  instance hasProducts : HasProducts prop := inferInstance

  noncomputable instance hasCoproductType (p q : prop) : HasTypeWithIntro prop (PSum p q) where
    T      := p ∨ q
    hElim  := ⟨λ h => Classical.choice (match h with
                                        | Or.inl l => ⟨PSum.inl l⟩
                                        | Or.inr r => ⟨PSum.inr r⟩)⟩
    hIntro := ⟨λ s => match s with
                      | PSum.inl l => Or.inl l
                      | PSum.inr r => Or.inr r⟩

  noncomputable instance hasCoproducts : HasCoproducts prop := inferInstance

  instance hasIsomorphisms (α : Sort u) [HasPreorderRelation prop α] : HasIsomorphismsWithIntro α :=
    HasProducts.hasIsomorphismsWithIntro α

  -- Specialization of `hasIsomorphisms` that uses `Iff` instead of `And`, for nicer results.
  instance (priority := high) hasEquivalenceIsoType (p q : prop) :
      HasTypeWithIntro prop (DefIso p q) where
    T      := p ↔ q
    hElim  := ⟨λ ⟨mp, mpr⟩ => ⟨mp, mpr⟩⟩
    hIntro := ⟨λ ⟨toHom, invHom⟩ => ⟨toHom, invHom⟩⟩

  instance (priority := high) hasEquivalenceIsos : HasIsomorphismsWithIntro prop where
    hIsoType := hasEquivalenceIsoType

  instance hasEquivalences : HasEquivalences prop := inferInstance

  instance hasFullPositiveEquivalences : HasFullPositiveEquivalences prop := inferInstance
  noncomputable instance hasFullEquivalences : HasFullEquivalences prop := inferInstance
  noncomputable instance hasPropEquivalences : HasPropEquivalences prop := inferInstance
  instance hasClassicalEquivalences : HasClassicalEquivalences prop := inferInstance

  instance isPositiveUniverse : IsPositiveUniverse prop := ⟨⟩
  noncomputable instance isNegativeUniverse : IsNegativeUniverse prop := ⟨⟩
  noncomputable instance isStandardUniverse : IsStandardUniverse prop := ⟨⟩

end prop



namespace Prerelation

  def nativePreorder {α : Sort u} {r : Prerelation α prop} (p : Preorder r) :
      IsPreorder r where
    refl         a     := p.refl a
    revTransFun₂ _ _ _ := λ h i => p.trans i h

  def nativeEquivalence {α : Sort u} {r : Prerelation α prop} (e : Equivalence r) :
      IsEquivalence r where
    refl         a     := e.refl a
    symmFun      _ _   := e.symm
    revTransFun₂ _ _ _ := λ h i => e.trans i h

  instance Iff.isEquivalence : IsEquivalence (V := prop) Iff := nativeEquivalence Iff.equivalence

  instance Eq.isEquivalence (α : Sort u) : IsEquivalence (V := prop) (@Eq α) :=
    nativeEquivalence (Eq.equivalence α)

  instance Setoid.isEquivalence (α : Sort u) [s : Setoid α] : IsEquivalence (V := prop) s.r :=
    nativeEquivalence s.iseqv

end Prerelation
