import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Relations

import mathlib4_experiments.Data.Notation



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v iu iv



class HasIdentity' (U : Universe.{u}) (IU : outParam Universe.{iu}) : Type (max u iu) where
(Eq (A : U) : EquivalenceRelation ⌈A⌉ IU)

namespace HasIdentity'

  variable {U IU : Universe} [h : HasIdentity' U IU]

  instance hasEquivalence (A : U) : HasEquivalence ⌈A⌉ ⌈A⌉ := ⟨(h.Eq A).R⟩
  instance hasInstances (A : U) : HasInstances (HasEquivalence.γ ⌈A⌉ ⌈A⌉) := Universe.instInst IU

  instance isEquivalence (A : U) : MetaRelation.IsEquivalence (HasEquivalence.Equiv (α := ⌈A⌉) (β := ⌈A⌉)) :=
  EquivalenceRelation.isEquivalence (h.Eq A)

  class IsSubsingleton (A : U) where
  (eq (a b : A) : a ≃ b)

end HasIdentity'

class HasIdentity (U : Universe.{u}) : Type (max u (iu + 1)) where
(IU : Universe.{iu})
[h  : HasIdentity' U IU]

namespace HasIdentity

  variable (U : Universe) [h : HasIdentity U]

  @[reducible] def univ := h.IU
  notation "⌊" U:0 "⌋" => HasIdentity.univ U

  instance hasIdentity' : HasIdentity' U ⌊U⌋ := h.h

end HasIdentity

instance HasIdentity'.hasIdentity (U IU : Universe) [HasIdentity' U IU] : HasIdentity U := ⟨IU⟩
