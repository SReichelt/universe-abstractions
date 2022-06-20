import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors



namespace UniverseAbstractions.Layer1

set_option autoImplicit false

universe u u'

open Universe HasFunctors



class HasCoproducts (α : Sort u) (β : Sort u') (V : Universe.{u}) [HasFunctors α V]
                    [HasFunctors β V] [HasLinearLogic V] where
  defCoprodType : DefType V (PSum α β)
  defLeftIntro  (a : α) : DefType.DefInst defCoprodType (PSum.inl a)
  defRightIntro (b : β) : DefType.DefInst defCoprodType (PSum.inr b)
  defLeftIntroFun  : α ⥤{λ a => defLeftIntro  a} defCoprodType.A
  defRightIntroFun : β ⥤{λ b => defRightIntro b} defCoprodType.A
  defElimFun₃ (C : V) :
    (α ⥤ C) ⥤ (β ⥤ C) ⥤ defCoprodType.A ⥤{λ F G S => match defCoprodType.elim S with
                                                       | PSum.inl a => F a
                                                       | PSum.inr b => G b} C

namespace HasCoproducts

  @[reducible] def Coprod (α : Sort u) (β : Sort u') (V : Universe.{u}) [HasFunctors α V]
                          [HasFunctors β V] [HasLinearLogic V] [h : HasCoproducts α β V] : V :=
    h.defCoprodType
  notation:34 α:35 " ⊔_" V:max β:35 => HasCoproducts.Coprod α β V

  section

    variable (α : Sort u) (β : Sort u') (V : Universe.{u}) [HasFunctors α V] [HasFunctors β V]
             [HasLinearLogic V] [h : HasCoproducts α β V]

    @[reducible] def leftIntro  (a : α) : α ⊔_V β := h.defLeftIntro  a
    @[reducible] def rightIntro (b : β) : α ⊔_V β := h.defRightIntro b

    @[reducible] def leftIntroFun  : α ⥤ α ⊔_V β := h.defLeftIntroFun
    @[reducible] def rightIntroFun : β ⥤ α ⊔_V β := h.defRightIntroFun

    instance leftIntro.isFunApp  {a : α} : IsFunApp α (leftIntro  α β V a) := ⟨leftIntroFun  α β V, a⟩
    instance rightIntro.isFunApp {b : β} : IsFunApp β (rightIntro α β V b) := ⟨rightIntroFun α β V, b⟩

  end

  section

    variable {α : Sort u} {β : Sort u'} {V : Universe.{u}} [HasFunctors α V] [HasFunctors β V]
             [HasLinearLogic V] [h : HasCoproducts α β V]

    @[reducible] def elim {C : V} (F : α ⥤ C) (G : β ⥤ C) (S : α ⊔_V β) : C :=
      match defCoprodType.elim S with
      | PSum.inl a => F a
      | PSum.inr b => G b

    @[reducible] def elimFun {C : V} (F : α ⥤ C) (G : β ⥤ C) : α ⊔_V β ⥤ C :=
      ((h.defElimFun₃ C).app F).app G

    instance elim.isFunApp {C : V} {F : α ⥤ C} {G : β ⥤ C} {S : α ⊔_V β} :
        IsFunApp (α ⊔_V β) (elim F G S) :=
      ⟨elimFun F G, S⟩

  end

  section

    variable (α : Sort u) (β : Sort u') {V : Universe.{u}} [HasFunctors α V] [HasFunctors β V]
             [HasLinearLogic V] [h : HasCoproducts α β V]

    @[reducible] def elimFun₃ (C : V) : (α ⥤ C) ⥤ (β ⥤ C) ⥤ (α ⊔_V β ⥤ C) :=
      h.defElimFun₃ C

    instance elimFun.isFunApp₂ {C : V} {F : α ⥤ C} {G : β ⥤ C} :
        IsFunApp₂ (α ⥤ C) (β ⥤ C) (elimFun F G) :=
      ⟨elimFun₃ α β C, F, G⟩

  end

end HasCoproducts


class HasInnerCoproducts (U : Universe.{u}) [HasLinearLogic U] where
  [hCoprod (A B : U) : HasCoproducts A B U]

namespace HasInnerCoproducts

  variable {U : Universe.{u}} [HasLinearLogic U] [h : HasInnerCoproducts U]

  instance (A B : U) : HasCoproducts A B U := h.hCoprod A B

  @[reducible] def Coprod (A B : U) := A ⊔_U B
  infix:34 " ⊔ " => HasInnerCoproducts.Coprod

  @[reducible] def leftIntro  {A : U} (a : A) (B : U) : A ⊔ B := HasCoproducts.leftIntro  A B U a
  @[reducible] def rightIntro (A : U) {B : U} (b : B) : A ⊔ B := HasCoproducts.rightIntro A B U b

  @[reducible] def leftIntroFun  (A B : U) : A ⥤ A ⊔ B := HasCoproducts.leftIntroFun  A B U
  @[reducible] def rightIntroFun (A B : U) : B ⥤ A ⊔ B := HasCoproducts.rightIntroFun A B U

end HasInnerCoproducts
