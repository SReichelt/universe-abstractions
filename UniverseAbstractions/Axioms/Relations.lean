import UniverseAbstractions.Axioms.Universes



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v



def MetaRelation (α : Sort u) (V : Universe.{v}) : Sort (max u (v + 1)) := α → α → V

namespace MetaRelation

  variable {α : Sort u} {V : Universe} (R : MetaRelation α V)

  class HasRefl where
  (refl (a : α) : R a a)

  class HasSymm where
  (symm {a b : α} : R a b → R b a)

  class HasTrans where
  (trans {a b c : α} : R a b → R b c → R a c)

  class IsPreorder extends HasRefl R, HasTrans R
  class IsEquivalence extends IsPreorder R, HasSymm R

  notation:90 g:91 " • " f:90 => MetaRelation.HasTrans.trans f g
  postfix:max "⁻¹" => MetaRelation.HasSymm.symm

end MetaRelation

def MetaRelation.nativeRelation {α : Sort u} (r : α → α → Prop) : MetaRelation α prop := r

def MetaRelation.nativeEquivalence {α : Sort u} {r : α → α → Prop} (e : Equivalence r) :
  IsEquivalence (nativeRelation r) :=
{ refl  := e.refl,
  symm  := e.symm
  trans := e.trans }

def MetaRelation.unitRelation (α : Sort u) {V : Universe.{v}} (B : V) :
  MetaRelation α V :=
λ _ _ => B

def MetaRelation.unitEquivalence (α : Sort u) {V : Universe.{v}} {B : V} (b : B) :
  IsEquivalence (MetaRelation.unitRelation α B) :=
{ refl  := λ _   => b,
  symm  := λ _   => b,
  trans := λ _ _ => b }



structure EquivalenceRelation (α : Sort u) (V : Universe.{v}) : Sort (max u (v + 1)) where
(R : MetaRelation α V)
[h : MetaRelation.IsEquivalence R]

namespace EquivalenceRelation

  variable {α : Sort u} {V : Universe} (E : EquivalenceRelation α V)

  instance isEquivalence : MetaRelation.IsEquivalence E.R := E.h

end EquivalenceRelation

instance EquivalenceRelation.coeNativeEquivalence {α : Sort u} {r : α → α → Prop} :
  Coe (Equivalence r) (EquivalenceRelation α prop) :=
⟨λ e => { R := r,
          h := MetaRelation.nativeEquivalence e }⟩
