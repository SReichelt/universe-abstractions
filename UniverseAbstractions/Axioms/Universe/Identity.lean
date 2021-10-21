import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Relations

import mathlib4_experiments.Data.Notation



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v iu iv



class HasInstanceEquivalences (U : Universe.{u}) (IU : outParam Universe.{iu}) : Type (max u iu) where
(Eq (A : U) : EquivalenceRelation ⌈A⌉ IU)

namespace HasInstanceEquivalences

  variable {U IU : Universe} [h : HasInstanceEquivalences U IU]

  instance hasEquivalence (A : U) : HasEquivalence ⌈A⌉ ⌈A⌉ := ⟨(h.Eq A).R⟩
  instance hasInstances (A : U) : HasInstances (HasEquivalence.γ ⌈A⌉ ⌈A⌉) := Universe.instInst IU

  instance isEquivalence (A : U) : MetaRelation.IsEquivalence (HasEquivalence.Equiv (α := ⌈A⌉) (β := ⌈A⌉)) :=
  EquivalenceRelation.isEquivalence (h.Eq A)

  class IsSubsingleton (A : U) where
  (eq (a b : A) : a ≃ b)

end HasInstanceEquivalences

class HasIdentity (U : Universe.{u}) : Type (max u (iu + 1)) where
(IU : Universe.{iu})
[h  : HasInstanceEquivalences U IU]

namespace HasIdentity

  variable (U : Universe) [h : HasIdentity U]

  @[reducible] def univ := h.IU

  instance hasInstanceEquivalences : HasInstanceEquivalences U (univ U) := h.h

end HasIdentity

instance HasInstanceEquivalences.hasIdentity (U IU : Universe) [HasInstanceEquivalences U IU] : HasIdentity U := ⟨IU⟩
