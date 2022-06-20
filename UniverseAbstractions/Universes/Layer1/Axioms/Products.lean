import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors



namespace UniverseAbstractions.Layer1

set_option autoImplicit false

universe u u'

open Universe HasFunctors



class HasProducts (α : Sort u) (β : Sort u') (V : Universe) [HasFunctors α V] [HasFunctors β V]
                  [HasLinearLogic V] where
  defProdType : DefType V (PProd α β)
  defIntro (a : α) (b : β) : DefType.DefInst defProdType ⟨a, b⟩
  defIntroFun₂ : α ⥤ β ⥤{λ a b => defIntro a b} defProdType.A
  defElimFun₂ (C : V) :
    (α ⥤ β ⥤ C) ⥤ defProdType.A ⥤{λ F P => F (defProdType.elim P).fst (defProdType.elim P).snd} C

namespace HasProducts

  @[reducible] def Prod (α : Sort u) (β : Sort u') (V : Universe) [HasFunctors α V]
                        [HasFunctors β V] [HasLinearLogic V] [h : HasProducts α β V] : V :=
    h.defProdType
  notation:35 α:36 " ⊓_" V:max β:36 => HasProducts.Prod α β V

  section

    variable {α : Sort u} {β : Sort u'} (a : α) (b : β) (V : Universe) [HasFunctors α V]
             [HasFunctors β V] [HasLinearLogic V] [h : HasProducts α β V]

    @[reducible] def intro : α ⊓_V β := h.defIntro a b

  end

  section

    variable (α : Sort u) (β : Sort u') (V : Universe) [HasFunctors α V] [HasFunctors β V]
             [HasLinearLogic V] [h : HasProducts α β V]

    @[reducible] def introFun₂ : α ⥤ β ⥤ α ⊓_V β := h.defIntroFun₂

    instance intro.isFunApp₂ {a : α} {b : β} : IsFunApp₂ α β (intro a b V) :=
      ⟨introFun₂ α β V, a, b⟩

  end

  section

    variable {α : Sort u} {β : Sort u'} {V : Universe} [HasFunctors α V] [HasFunctors β V]
             [HasLinearLogic V] [h : HasProducts α β V]

    @[reducible] def fst (P : α ⊓_V β) : α := (h.defProdType.elim P).fst
    @[reducible] def snd (P : α ⊓_V β) : β := (h.defProdType.elim P).snd

    @[reducible] def elimFun {C : V} (F : α ⥤ β ⥤ C) : α ⊓_V β ⥤ C := (h.defElimFun₂ C).app F

  end

  section

    variable (α : Sort u) (β : Sort u') {V : Universe} [HasFunctors α V] [HasFunctors β V]
             [HasLinearLogic V] [h : HasProducts α β V]

    @[reducible] def elimFun₂ (C : V) : (α ⥤ β ⥤ C) ⥤ (α ⊓_V β ⥤ C) := h.defElimFun₂ C

    instance elimFun.isFunApp {C : V} {F : α ⥤ β ⥤ C} : IsFunApp (α ⥤ β ⥤ C) (elimFun F) :=
      ⟨elimFun₂ α β C, F⟩

  end

end HasProducts


class HasInnerProducts (U : Universe) [HasLinearLogic U] where
  [hProd (A B : U) : HasProducts A B U]

namespace HasInnerProducts

  variable {U : Universe} [HasLinearLogic U] [h : HasInnerProducts U]

  instance (A B : U) : HasProducts A B U := h.hProd A B

  @[reducible] def Prod (A B : U) := A ⊓_U B
  infix:35 " ⊓ " => HasInnerProducts.Prod

  @[reducible] def intro {A B : U} (a : A) (b : B) : A ⊓ B := HasProducts.intro a b U
  @[reducible] def introFun₂ (A B : U) : A ⥤ B ⥤ A ⊓ B := HasProducts.introFun₂ A B U

end HasInnerProducts
