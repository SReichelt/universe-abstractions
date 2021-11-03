import UniverseAbstractions.Axioms.Universes

import UniverseAbstractions.MathlibFragments.Data.Notation



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w



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

  @[reducible] def lift {ω : Sort w} (l : ω → α) : MetaRelation ω V := λ a b => R (l a) (l b)

  namespace lift

    variable {ω : Sort w} (l : ω → α)

    instance hasRefl  [h : HasRefl  R] : HasRefl  (lift R l) := ⟨λ a => h.refl (l a)⟩
    instance hasSymm  [h : HasSymm  R] : HasSymm  (lift R l) := ⟨h.symm⟩
    instance hasTrans [h : HasTrans R] : HasTrans (lift R l) := ⟨h.trans⟩

    instance isPreorder    [IsPreorder    R] : IsPreorder    (lift R l) := ⟨⟩
    instance isEquivalence [IsEquivalence R] : IsEquivalence (lift R l) := ⟨⟩

  end lift

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



class HasEquivalenceRelation (α : Sort u) (V : outParam Universe.{v}) :
  Sort (max u (v + 1)) where
(R : MetaRelation α V)
[h : MetaRelation.IsEquivalence R]

namespace HasEquivalenceRelation

  open MetaRelation

  variable {α : Sort u} {V : Universe} [h : HasEquivalenceRelation α V]

  instance isEquivalence : IsEquivalence h.R := h.h

  instance hasEquivalence : HasEquivalence α α := ⟨h.R⟩
  instance : IsEquivalence (HasEquivalence.Equiv (α := α) (β := α)) := isEquivalence
  instance : HasInstances (HasEquivalence.γ α α) := Universe.instInst V

  @[reducible] def refl  (a     : α)                         : a ≃ a := HasRefl.refl a
  @[reducible] def symm  {a b   : α} (e : a ≃ b)             : b ≃ a := e⁻¹
  @[reducible] def trans {a b c : α} (e : a ≃ b) (f : b ≃ c) : a ≃ c := f • e

end HasEquivalenceRelation

instance HasEquivalenceRelation.coeNativeEquivalence {α : Sort u} {r : α → α → Prop} :
  Coe (Equivalence r) (HasEquivalenceRelation α prop) :=
⟨λ e => { R := r,
          h := MetaRelation.nativeEquivalence e }⟩



def DependentMetaRelation {U : Universe.{u}} {V : Universe.{v}} (R : MetaRelation ⌈U⌉ V)
                          (W : Universe.{w}) :=
∀ {A B}, R A B → (A → B → W)

namespace DependentMetaRelation

  open MetaRelation

  variable {U V W : Universe} {R : MetaRelation ⌈U⌉ V} (S : DependentMetaRelation R W)

  class HasDependentRefl [h : HasRefl R] where
  (refl {A : U} (a : A) : S (h.refl A) a a)

  def reflRel [h : HasRefl R] (A : U) : MetaRelation ⌈A⌉ W := S (h.refl A)
  instance [HasRefl R] [h : HasDependentRefl S] (A : U) : HasRefl (reflRel S A) := ⟨h.refl⟩

  class HasDependentSymm [h : HasSymm R] where
  (symm {A B : U} {F : R A B} {a : A} {b : B} : S F a b → S F⁻¹ b a)

  class HasDependentTrans [h : HasTrans R] where
  (trans {A B C : U} {F : R A B} {G : R B C} {a : A} {b : B} {c : C} : S F a b → S G b c → S (G • F) a c)

  class IsDependentPreorder [h : IsPreorder R] extends HasDependentRefl S, HasDependentTrans S
  class IsDependentEquivalence [h : IsEquivalence R] extends IsDependentPreorder S, HasDependentSymm S

end DependentMetaRelation
