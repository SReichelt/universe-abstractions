import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors



namespace UniverseAbstractions.Layer1

set_option autoImplicit false

open Universe HasFunctors



class HasCoproducts {U : Universe} [HasLinearLogic U] (A B : U) where
  defCoprodType : DefTypeWithIntro U (PSum A B)
  defLeftIntroFun  : A ⥤{λ a => DefTypeWithIntro.inst defCoprodType (PSum.inl a)} defCoprodType.A
  defRightIntroFun : B ⥤{λ b => DefTypeWithIntro.inst defCoprodType (PSum.inr b)} defCoprodType.A
  defElimFun₃ (C : U) :
    (A ⥤ C) ⥤ (B ⥤ C) ⥤ defCoprodType.A ⥤{λ F G S => match defCoprodType.elim S with
                                                       | PSum.inl a => F a
                                                       | PSum.inr b => G b} C

namespace HasCoproducts

  variable {U : Universe} [HasLinearLogic U]

  @[reducible] def Coprod (A B : U) [h : HasCoproducts A B] : U := h.defCoprodType
  infix:34 " ⊔ " => HasCoproducts.Coprod

  @[reducible] def leftIntro  {A : U} (a : A) (B : U) [HasCoproducts A B] : A ⊔ B :=
    DefTypeWithIntro.inst defCoprodType (PSum.inl a)
  @[reducible] def rightIntro (A : U) {B : U} (b : B) [HasCoproducts A B] : A ⊔ B :=
    DefTypeWithIntro.inst defCoprodType (PSum.inr b)

  section

    variable (A B : U) [h : HasCoproducts A B]

    @[reducible] def leftIntroFun  : A ⥤ A ⊔ B := h.defLeftIntroFun
    @[reducible] def rightIntroFun : B ⥤ A ⊔ B := h.defRightIntroFun

    instance leftIntro.isFunApp  {a : A} : IsFunApp (leftIntro  a B) := ⟨leftIntroFun  A B, a⟩
    instance rightIntro.isFunApp {b : B} : IsFunApp (rightIntro A b) := ⟨rightIntroFun A B, b⟩

  end

  section

    variable {A B : U} [h : HasCoproducts A B]

    @[reducible] def elim {C : U} (F : A ⥤ C) (G : B ⥤ C) (S : A ⊔ B) : C :=
      match defCoprodType.elim S with
      | PSum.inl a => F a
      | PSum.inr b => G b

    @[reducible] def elimFun {C : U} (F : A ⥤ C) (G : B ⥤ C) : A ⊔ B ⥤ C :=
      ((h.defElimFun₃ C).app F).app G

    instance elim.isFunApp {C : U} {F : A ⥤ C} {G : B ⥤ C} {S : A ⊔ B} : IsFunApp (elim F G S) :=
      ⟨elimFun F G, S⟩

  end

  section

    variable (A B : U) [h : HasCoproducts A B]

    @[reducible] def elimFun₃ (C : U) : (A ⥤ C) ⥤ (B ⥤ C) ⥤ (A ⊔ B ⥤ C) := h.defElimFun₃ C

    instance elimFun.isFunApp₂ {C : U} {F : A ⥤ C} {G : B ⥤ C} : IsFunApp₂ (elimFun F G) :=
      ⟨elimFun₃ A B C, F, G⟩

  end

end HasCoproducts


class HasInnerCoproducts (U : Universe) [HasLinearLogic U] where
  [hCoprod (A B : U) : HasCoproducts A B]

namespace HasInnerCoproducts

  variable {U : Universe} [HasLinearLogic U] [h : HasInnerCoproducts U]

  instance (A B : U) : HasCoproducts A B := h.hCoprod A B

end HasInnerCoproducts
