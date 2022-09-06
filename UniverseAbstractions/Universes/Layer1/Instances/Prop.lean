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

open Universe HasPreorderRelation HasTrivialDefInst HasTrivialDefPi



def prop : Universe.{0, 1} := ⟨Prop⟩

namespace prop

  instance hasPiType {α : Sort u} (P : α → prop) : HasPiType P where
    defPiType := DefType.native _

  instance hasTrivialDefPi {α : Sort u} (P : α → prop) : HasTrivialDefPi P where
    toHasTrivialDefInst := HasTrivialDefInst.native _

  instance hasFunctors (p : Prop) (Y : prop) : HasFunctors p Y := ⟨⟩

  instance hasTrivialDefFun (p : Prop) (Y : prop) : HasTrivialDefFun p Y := ⟨⟩

  instance hasUnivFunctors : HasUnivFunctors prop prop := ⟨⟩

  instance hasTrivialFunctoriality : HasTrivialFunctoriality prop prop := ⟨⟩

  instance hasFullLogic : HasFullLogic prop := inferInstance

  instance hasTop : HasTop prop where
    defTopType   := ⟨⟨True, λ _ => PUnit.unit⟩, λ _ => ⟨trivial⟩⟩
    defElimFun _ := defFun

  instance hasBot : HasBot prop where
    defBotType   := ⟨False, False.elim⟩
    defElimFun _ := defFun

  instance hasClassicalLogic : HasClassicalLogic prop := ⟨@Classical.byContradiction⟩

  instance hasProducts (p q : prop) : HasProducts p q where
    defProdType    := ⟨⟨p ∧ q, λ ⟨l, r⟩ => ⟨l, r⟩⟩, λ ⟨l, r⟩ => ⟨⟨l, r⟩⟩⟩
    defIntroFun₂   := defFun₂
    defElimFun₂  _ := defFun₂

  instance hasInnerProducts : HasInnerProducts prop := ⟨⟩

  noncomputable instance hasCoproducts (p q : prop) : HasCoproducts p q where
    defCoprodType      := ⟨⟨p ∨ q, λ h => Classical.choice (match h with
                                                            | Or.inl l => ⟨PSum.inl l⟩
                                                            | Or.inr r => ⟨PSum.inr r⟩)⟩,
                           λ s => ⟨match s with
                                   | PSum.inl l => Or.inl l
                                   | PSum.inr r => Or.inr r⟩⟩
    defLeftIntroFun    := defFun
    defRightIntroFun   := defFun
    defElimFun₃      _ := defFun₃

  noncomputable instance hasInnerCoproducts : HasInnerCoproducts prop := ⟨⟩

  instance hasIsomorphismsBase (α : Sort u) [HasPreorderRelation prop α] : HasIsomorphismsBase α :=
    HasInnerProducts.hasIsomorphismsBase α

  instance hasTrivialIsomorphismCondition (α : Sort u) [HasPreorderRelation prop α] :
      HasTrivialIsomorphismCondition α := ⟨⟩

  instance hasIsomorphisms (α : Sort u) [HasPreorderRelation prop α] : HasIsomorphisms α :=
    inferInstance

  -- Specialization of `hasIsomorphismsBase` that uses `Iff` instead of `And`, for nicer results.
  instance (priority := high) hasEquivalencesBase : HasIsomorphismsBase prop where
    defIsoType  p q := ⟨p ↔ q, λ h => ⟨h.mp, h.mpr⟩⟩
    defToHomFun _ _ := defFun

  instance hasTrivialEquivalenceCondition : HasTrivialIsomorphismCondition prop where
    hDefIso _ _ := ⟨λ ⟨toHom, invHom⟩ => ⟨toHom, invHom⟩⟩

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
