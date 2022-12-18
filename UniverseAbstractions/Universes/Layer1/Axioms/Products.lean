import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors



namespace UniverseAbstractions.Layer1

set_option autoImplicit false

universe u

open HasFunctors



class HasExternalProducts (U : Universe.{u}) [HasUnivFunctors U U] (α β : Sort u) [HasFunctors α U]
                          [HasFunctors β U] extends
    HasTypeWithIntro U (PProd α β) where
  defIntroFun₂ : [α ⥤ β ⥤ A]__{λ a b => hIntro.intro ⟨a, b⟩}
  defElimFun₂ (C : U) :
    [(α ⥤ β ⥤ C) ⥤ A ⥤ C]__{λ F P => F (hElim.elim P).fst (hElim.elim P).snd}

namespace HasExternalProducts

  section

    variable (U : Universe.{u}) [HasUnivFunctors U U] (α β : Sort u) [HasFunctors α U]
             [HasFunctors β U] [h : HasExternalProducts U α β]

    @[reducible] def Prod : U := h.A

  end

  section

    variable (U : Universe.{u}) [HasUnivFunctors U U] {α β : Sort u} [HasFunctors α U]
             [HasFunctors β U] [h : HasExternalProducts U α β]

    @[reducible] def intro (a : α) (b : β) : Prod U α β := h.hIntro.intro ⟨a, b⟩

  end

  section

    variable (U : Universe.{u}) [HasUnivFunctors U U] (α β : Sort u) [HasFunctors α U]
             [HasFunctors β U] [h : HasExternalProducts U α β]

    @[reducible] def introFun₂ : α ⥤ β ⥤ Prod U α β := h.defIntroFun₂

    instance intro.isFunApp₂ {a : α} {b : β} : IsFunApp₂ (intro U a b) := ⟨introFun₂ U α β, a, b⟩

  end

  section

    variable {U : Universe.{u}} [HasUnivFunctors U U] {α β : Sort u} [HasFunctors α U]
             [HasFunctors β U] [h : HasExternalProducts U α β]

    @[reducible] def fst (P : Prod U α β) : α := (h.hElim.elim P).fst
    @[reducible] def snd (P : Prod U α β) : β := (h.hElim.elim P).snd

    @[reducible] def elimFun {C : U} (F : α ⥤ β ⥤ C) : Prod U α β ⥤ C := (h.defElimFun₂ C) F

  end

  section

    variable {U : Universe.{u}} [HasUnivFunctors U U] (α β : Sort u) [HasFunctors α U]
             [HasFunctors β U] [h : HasExternalProducts U α β]

    @[reducible] def elimFun₂ (C : U) : (α ⥤ β ⥤ C) ⥤ (Prod U α β ⥤ C) := h.defElimFun₂ C

    instance elimFun.isFunApp {C : U} {F : α ⥤ β ⥤ C} : IsFunApp (elimFun F) := ⟨elimFun₂ α β C, F⟩

  end

end HasExternalProducts


class HasProducts (U : Universe) [HasUnivFunctors U U] where
  [hProd (A B : U) : HasExternalProducts U A B]

namespace HasProducts

  variable {U : Universe} [HasUnivFunctors U U] [h : HasProducts U]

  instance (A B : U) : HasExternalProducts U A B := h.hProd A B

  @[reducible] def Prod (A B : U) : U := HasExternalProducts.Prod U A B
  infix:35 " ⊓ " => HasProducts.Prod

  @[reducible] def intro {A B : U} (a : A) (b : B) : A ⊓ B := HasExternalProducts.intro U a b
  @[reducible] def introFun₂ (A B : U) : A ⥤ B ⥤ A ⊓ B := HasExternalProducts.introFun₂ U A B

  @[reducible] def fst {A B : U} (P : A ⊓ B) : A := HasExternalProducts.fst P
  @[reducible] def snd {A B : U} (P : A ⊓ B) : B := HasExternalProducts.snd P

  @[reducible] def elimFun {A B C : U} (F : A ⥤ B ⥤ C) : A ⊓ B ⥤ C := HasExternalProducts.elimFun F
  @[reducible] def elimFun₂ (A B C : U) : (A ⥤ B ⥤ C) ⥤ (A ⊓ B ⥤ C) :=
    HasExternalProducts.elimFun₂ A B C

end HasProducts
