import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Axioms.Singletons
import UniverseAbstractions.Universes.Layer1.Axioms.Products
import UniverseAbstractions.Universes.Layer1.Axioms.Coproducts
import UniverseAbstractions.Universes.Layer1.Axioms.Equivalences

import UniverseAbstractions.MathlibFragments.Init.CoreExt



namespace UniverseAbstractions.Layer1

set_option autoBoundImplicitLocal false

universe u v w



def NativeTypeClass := Sort (max 1 u w) → Sort v

structure Bundled (Φ : NativeTypeClass.{u, v, w}) : Sort (max ((max 1 u w) + 1) v) where
(α : Sort (max 1 u w))
[h : Φ α]

namespace Bundled

  variable (Φ : NativeTypeClass.{u, v, w})

  instance hasInstances : HasInstances (Bundled Φ) := ⟨Bundled.α⟩

  def univ : Universe.{max 1 u w, max ((max 1 u w) + 1) v} := ⟨Bundled Φ⟩

  def type {α : Sort (max 1 u w)} (h : Φ α) : univ Φ :=
  { α := α,
    h := h }

  structure Functor (A B : univ Φ) (IsFun : (A → B) → Sort w) : Sort (max 1 u w) where
  (f     : A → B)
  [isFun : IsFun f]

  class HasFunctorInstances where
  (IsFun   {A B : univ Φ} : (A → B) → Sort w)
  (funInst (A B : univ Φ) : Φ (Functor Φ A B IsFun))

  variable [hFunInst : HasFunctorInstances Φ]

  instance hasFunctors : HasFunctors (univ Φ) :=
  { Fun   := λ A B => type Φ (hFunInst.funInst A B),
    apply := Functor.f }

  def mkFun {A B : univ Φ} {f : A → B} (isFun : hFunInst.IsFun f) : A ⟶ B :=
  { f     := f,
    isFun := isFun }

  def mkDefFun {A B : univ Φ} {f : A → B} (isFun : hFunInst.IsFun f) : A ⟶{f} B := ⟨mkFun Φ isFun⟩

  class HasTopInstance where
  (topInst : Φ PUnit)
  (elimIsFun {A : univ Φ} (a : A) : hFunInst.IsFun (λ _ : type Φ topInst => a))

  instance hasTop [h : HasTopInstance Φ] : HasTop (univ Φ) :=
  { T          := type Φ h.topInst,
    t          := PUnit.unit,
    defElimFun := λ a => mkDefFun Φ (h.elimIsFun a) }

  class HasBotInstance where
  (botInst : Φ PEmpty)
  (elimIsFun (A : univ Φ) : hFunInst.IsFun (λ b : type Φ botInst => @PEmpty.elim A b))

  instance hasBot [h : HasBotInstance Φ] : HasBot (univ Φ) :=
  { B       := type Φ h.botInst,
    elimFun := λ A => mkFun Φ (h.elimIsFun A) }

  class HasProductInstances where
  (prodInst (A B : univ Φ) : Φ (PProd A B))
  (introIsFun {A : univ Φ} (a : A) (B : univ Φ) :
     hFunInst.IsFun (B := type Φ (prodInst A B)) (λ b : B => ⟨a, b⟩))
  (introIsFun₂ (A B : univ Φ) : hFunInst.IsFun (λ a : A => mkFun Φ (introIsFun a B)))
  (elimIsFun {A B C : univ Φ} (F : A ⟶ B ⟶ C) :
     hFunInst.IsFun (λ P : type Φ (prodInst A B) => F P.fst P.snd))
  (elimIsFun₂ (A B C : univ Φ) : hFunInst.IsFun (λ F : A ⟶ B ⟶ C => mkFun Φ (elimIsFun F)))

  instance hasProducts [h : HasProductInstances Φ] : HasProducts (univ Φ) :=
  { Prod      := λ A B => type Φ (h.prodInst A B),
    introFun₂ := λ A B => mkFun Φ (h.introIsFun₂ A B),
    elimFun₂  := λ A B C => mkFun Φ (h.elimIsFun₂ A B C) }

  class HasCoproductInstances where
  (coprodInst (A B : univ Φ) : Φ (PSum A B))
  (leftIntroIsFun (A B : univ Φ) :
     hFunInst.IsFun (B := type Φ (coprodInst A B)) (λ a : A => PSum.inl a))
  (rightIntroIsFun (A B : univ Φ) :
     hFunInst.IsFun (B := type Φ (coprodInst A B)) (λ b : B => PSum.inr b))
  (elimIsFun {A B C : univ Φ} (F : A ⟶ C) (G : B ⟶ C) :
     hFunInst.IsFun (λ P : type Φ (coprodInst A B) => match P with
                                                      | PSum.inl a => F a
                                                      | PSum.inr b => G b))
  (elimIsFun₂ (A B C : univ Φ) (F : A ⟶ C) :
     hFunInst.IsFun (λ G : B ⟶ C => mkFun Φ (elimIsFun F G)))
  (elimIsFun₃ (A B C : univ Φ) : hFunInst.IsFun (λ F : A ⟶ C => mkFun Φ (elimIsFun₂ A B C F)))

  instance hasCoproducts [h : HasCoproductInstances Φ] : HasCoproducts (univ Φ) :=
  { Coprod        := λ A B => type Φ (h.coprodInst A B),
    leftIntroFun  := λ A B => mkFun Φ (h.leftIntroIsFun A B),
    rightIntroFun := λ A B => mkFun Φ (h.rightIntroIsFun A B),
    elimFun₃      := λ A B C => mkFun Φ (h.elimIsFun₃ A B C) }

  structure Equivalence (A B : univ Φ) (IsEquiv : (A ⟶ B) → (B ⟶ A) → Sort w) :
    Sort (max 1 u w) where
  (toFun   : A ⟶ B)
  (invFun  : B ⟶ A)
  [isEquiv : IsEquiv toFun invFun]

  class HasEquivalenceInstances where
  (IsEquiv {A B : univ Φ} : (A ⟶ B) → (B ⟶ A) → Sort w)
  (equivInst (A B : univ Φ) : Φ (Equivalence Φ A B IsEquiv))
  (toFunIsFun (A B : univ Φ) : hFunInst.IsFun (λ E : type Φ (equivInst A B) => E.toFun))
  (invFunIsFun (A B : univ Φ) : hFunInst.IsFun (λ E : type Φ (equivInst A B) => E.invFun))

  instance hasEquivalences [h : HasEquivalenceInstances Φ] : HasEquivalences (univ Φ) :=
  { Equiv   := λ A B => type Φ (h.equivInst A B),
    toFun₂  := λ A B => mkFun Φ (h.toFunIsFun A B),
    invFun₂ := λ A B => mkFun Φ (h.invFunIsFun A B) }

end Bundled
