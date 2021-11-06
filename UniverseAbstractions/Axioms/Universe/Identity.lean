import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.MetaRelations



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v iu iv



class HasInstanceEquivalences (U : Universe.{u}) (IU : outParam Universe.{iu}) : Type (max u iu) where
(hasEq (A : U) : HasEquivalenceRelation ⌈A⌉ IU)

namespace HasInstanceEquivalences

  open MetaRelation

  variable {U IU : Universe} [h : HasInstanceEquivalences U IU]

  instance hasEquivalenceRelation (A : U) : HasEquivalenceRelation ⌈A⌉ IU := h.hasEq A

  @[reducible] def Rel (A : U) : MetaRelation ⌈A⌉ IU := (hasEquivalenceRelation A).R

  instance isEquivalence (A : U) : IsEquivalence (Rel A) := HasEquivalenceRelation.isEquivalence

  @[reducible] def refl  {A : U} (a     : A)                         : a ≃ a := HasEquivalenceRelation.refl a
  @[reducible] def symm  {A : U} {a b   : A} (e : a ≃ b)             : b ≃ a := HasEquivalenceRelation.symm e
  @[reducible] def trans {A : U} {a b c : A} (e : a ≃ b) (f : b ≃ c) : a ≃ c := HasEquivalenceRelation.trans e f

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
