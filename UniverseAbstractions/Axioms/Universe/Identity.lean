import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Relations

import UniverseAbstractions.MathlibFragments.Data.Notation



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v iu iv



class HasInstanceEquivalences (U : Universe.{u}) (IU : outParam Universe.{iu}) : Type (max u iu) where
(Eq (A : U) : EquivalenceRelation ⌈A⌉ IU)

namespace HasInstanceEquivalences

  variable {U IU : Universe} [h : HasInstanceEquivalences U IU]

  @[reducible] def Rel (A : U) : MetaRelation ⌈A⌉ IU := (h.Eq A).R

  instance hasEquivalence (A : U) : HasEquivalence ⌈A⌉ ⌈A⌉ := ⟨Rel A⟩
  instance hasInstances (A : U) : HasInstances (HasEquivalence.γ ⌈A⌉ ⌈A⌉) := Universe.instInst IU

  instance isEquivalence (A : U) : MetaRelation.IsEquivalence (HasEquivalence.Equiv (α := ⌈A⌉) (β := ⌈A⌉)) :=
  EquivalenceRelation.isEquivalence (h.Eq A)

  @[reducible] def refl  {A : U} (a : A) : a ≃ a := MetaRelation.HasRefl.refl a
  @[reducible] def symm  {A : U} {a b : A} (e : a ≃ b) : b ≃ a := e⁻¹
  @[reducible] def trans {A : U} {a b c : A} (e : a ≃ b) (f : b ≃ c) : a ≃ c := f • e

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
