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

set_option autoBoundImplicitLocal false

universe u

open Prerelation



def prop : Universe.{0, 1} := ⟨Prop⟩

namespace prop

  instance hasFunctors : HasFunctors prop :=
  { Fun   := λ p q => p → q,
    apply := id }

  instance hasTrivialFunctoriality : HasTrivialFunctoriality prop := ⟨λ f => ⟨f⟩⟩

  instance hasFullLogic : HasFullLogic prop := inferInstance

  instance hasTop : HasTop prop :=
  { T          := True,
    t          := trivial,
    defElimFun := λ _ => HasTrivialFunctoriality.defFun }

  instance hasBot : HasBot prop :=
  { B       := False,
    elimFun := @False.elim }

  instance hasClassicalLogic : HasClassicalLogic prop := ⟨@Classical.byContradiction⟩

  instance isLogicallyConsistent : IsLogicallyConsistent prop := ⟨id⟩

  instance hasProducts : HasProducts prop :=
  { Prod      := And,
    introFun₂ := @And.intro,
    elimFun₂  := λ p q r f h => f h.left h.right }

  instance hasCoproducts : HasCoproducts prop :=
  { Coprod        := Or,
    leftIntroFun  := @Or.inl,
    rightIntroFun := @Or.inr,
    elimFun₃      := λ p q r f g h => Or.elim h f g }

  instance hasEquivalences : HasEquivalences prop :=
  { Equiv   := Iff,
    toFun₂  := @Iff.mp,
    invFun₂ := @Iff.mpr }

  instance hasTrivialEquivalenceCondition : HasTrivialEquivalenceCondition prop :=
  ⟨λ to inv => ⟨⟨to, inv⟩⟩⟩

  instance hasEquivOp : HasEquivOp prop := inferInstance
  instance hasFullEquivalences : HasFullEquivalences prop := inferInstance
  instance hasPropEquivalences : HasPropEquivalences prop := inferInstance
  instance hasClassicalEquivalences : HasClassicalEquivalences prop := inferInstance

end prop



namespace Prerelation

  def nativePreorder {α : Sort u} {r : Prerelation α prop} (p : Preorder r) :
    IsPreorder r :=
  { refl      := p.refl,
    transFun₂ := λ _ _ _ => p.trans }

  def nativeEquivalence {α : Sort u} {r : Prerelation α prop} (e : Equivalence r) :
    IsEquivalence r :=
  { refl      := e.refl,
    symmFun   := λ _ _ => e.symm,
    transFun₂ := λ _ _ _ => e.trans }

  instance Iff.isEquivalence : IsEquivalence (V := prop) Iff := nativeEquivalence Iff.equivalence

  instance Eq.isEquivalence (α : Sort u) : IsEquivalence (V := prop) (@Eq α) :=
  nativeEquivalence (Eq.equivalence α)

  instance Setoid.isEquivalence (α : Sort u) [s : Setoid α] : IsEquivalence (V := prop) s.r :=
  nativeEquivalence s.iseqv

end Prerelation
