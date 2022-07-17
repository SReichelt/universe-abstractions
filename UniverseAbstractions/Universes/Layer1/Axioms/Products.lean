import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors



namespace UniverseAbstractions.Layer1

set_option autoImplicit false

open Universe HasFunctors



class HasProducts {U : Universe} [HasLinearLogic U] (A B : U) where
  defProdType : DefType U (PProd A B)
  defIntro (a : A) (b : B) : DefType.DefInst defProdType ⟨a, b⟩
  defIntroFun₂ : A ⥤ B ⥤{λ a b => defIntro a b} defProdType.A
  defElimFun₂ (C : U) :
    (A ⥤ B ⥤ C) ⥤ defProdType.A ⥤{λ F P => F (defProdType.elim P).fst (defProdType.elim P).snd} C

namespace HasProducts

  variable {U : Universe} [HasLinearLogic U]

  @[reducible] def Prod (A B : U) [h : HasProducts A B] : U := h.defProdType
  infix:35 " ⊓ " => HasProducts.Prod

  section

    variable {A B : U} [h : HasProducts A B] (a : A) (b : B)

    @[reducible] def intro : A ⊓ B := h.defIntro a b

  end

  section

    variable (A B : U) [h : HasProducts A B]

    @[reducible] def introFun₂ : A ⥤ B ⥤ A ⊓ B := h.defIntroFun₂

    instance intro.isFunApp₂ {a : A} {b : B} : IsFunApp₂ (intro a b) := ⟨introFun₂ A B, a, b⟩

  end

  section

    variable {A B : U} [h : HasProducts A B]

    @[reducible] def fst (P : A ⊓ B) : A := (h.defProdType.elim P).fst
    @[reducible] def snd (P : A ⊓ B) : B := (h.defProdType.elim P).snd

    @[reducible] def elimFun {C : U} (F : A ⥤ B ⥤ C) : A ⊓ B ⥤ C := (h.defElimFun₂ C).app F

  end

  section

    variable (A B : U) [h : HasProducts A B]

    @[reducible] def elimFun₂ (C : U) : (A ⥤ B ⥤ C) ⥤ (A ⊓ B ⥤ C) := h.defElimFun₂ C

    instance elimFun.isFunApp {C : U} {F : A ⥤ B ⥤ C} : IsFunApp (elimFun F) := ⟨elimFun₂ A B C, F⟩

  end

end HasProducts


class HasInnerProducts (U : Universe) [HasLinearLogic U] where
  [hProd (A B : U) : HasProducts A B]

namespace HasInnerProducts

  variable {U : Universe} [HasLinearLogic U] [h : HasInnerProducts U]

  instance (A B : U) : HasProducts A B := h.hProd A B

end HasInnerProducts
