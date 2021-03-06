import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.MetaRelations



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u iu uu iuu



class HasInstanceEquivalences (U : Universe.{u}) (IU : outParam Universe.{iu}) where
(hasEq (A : U) : HasEquivalenceRelation A IU)

namespace HasInstanceEquivalences

  open MetaRelation

  variable {U IU : Universe} [h : HasInstanceEquivalences U IU]

  instance hasEquivalenceRelation (A : U) : HasEquivalenceRelation A IU := h.hasEq A

  -- Some redundant definitions to avoid problems related to definitional equality.

  @[reducible] def Rel (A : U) : MetaRelation A IU := λ a b => a ≃ b
  infix:25 " ≃' " => HasInstanceEquivalences.Rel _
  notation:25 a:26 " ≃'{" A:0 "} " b:26 => HasInstanceEquivalences.Rel A a b

  instance isEquivalence (A : U) : IsEquivalence (Rel A) := HasEquivalenceRelation.isEquivalence

  @[reducible] def refl  {A : U} (a     : A)                         : a ≃ a := HasRefl.refl a
  @[reducible] def symm  {A : U} {a b   : A} (e : a ≃ b)             : b ≃ a := e⁻¹
  @[reducible] def trans {A : U} {a b c : A} (e : a ≃ b) (f : b ≃ c) : a ≃ c := f • e
  @[reducible] def indir {A : U} {a b c : A} (e : a ≃ c) (f : b ≃ c) : a ≃ b := f⁻¹ • e

  notation:90 g:91 " •' " f:90 => HasInstanceEquivalences.trans f g
  postfix:max "⁻¹'" => HasInstanceEquivalences.symm
  notation:80 e:81 " ⑅ " f:81 => HasInstanceEquivalences.indir e f
  notation:80 e:81 " ▹{" x:0 "}◃ " f:81 => HasInstanceEquivalences.indir (c := x) e f

  class IsSubsingleton (A : U) where
  (eq (a b : A) : a ≃ b)

end HasInstanceEquivalences

class HasIdentity (U : Universe.{u, uu}) where
{IU : Universe.{iu, iuu}}
[h  : HasInstanceEquivalences U IU]

namespace HasIdentity

  variable (U : Universe) [h : HasIdentity U]

  @[reducible] def univ := h.IU

  instance hasInstanceEquivalences : HasInstanceEquivalences U (univ U) := h.h

end HasIdentity

-- Although this is an obvious instance loop, it doesn't seem to cause any problems.
-- It is difficult to avoid while keeping the two options of either specifying `IU`
-- explicitly or omitting it.
instance HasInstanceEquivalences.hasIdentity (U IU : Universe) [HasInstanceEquivalences U IU] : HasIdentity U := ⟨⟩
