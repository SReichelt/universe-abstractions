import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors



namespace UniverseAbstractions.Layer1

set_option autoImplicit false

universe u v

open HasFunctors



class HasExternalCoproducts (U : Universe) [HasUnivFunctors U U] (α : Sort u) (β : Sort v)
                            [HasFunctors α U] [HasFunctors β U] extends
    HasTypeWithIntro U (PSum α β) where
  defLeftIntroFun  : [α ⥤ T]_{λ a => hIntro.intro (PSum.inl a)}
  defRightIntroFun : [β ⥤ T]_{λ b => hIntro.intro (PSum.inr b)}
  defElimFun₃ (Y : U) :
    [(α ⥤ Y) ⥤ (β ⥤ Y) ⥤ T ⥤ Y]___{λ F G S => match hElim.elim S with
                                                | PSum.inl a => F a
                                                | PSum.inr b => G b}

namespace HasExternalCoproducts

  section

    variable (U : Universe) [HasUnivFunctors U U] (α : Sort u) (β : Sort v) [HasFunctors α U]
             [HasFunctors β U] [h : HasExternalCoproducts U α β]

    @[reducible] def Coprod : U := h.T

  end

  section

    variable (U : Universe) [HasUnivFunctors U U]

    @[reducible] def leftIntro  {α : Sort u} (a : α) (β : Sort v) [HasFunctors α U]
                                [HasFunctors β U] [HasExternalCoproducts U α β] :
        Coprod U α β :=
      PSum.inl (β := β) a

    @[reducible] def rightIntro (α : Sort u) {β : Sort v} (b : β) [HasFunctors α U]
                                [HasFunctors β U] [HasExternalCoproducts U α β] :
        Coprod U α β :=
      PSum.inr (α := α) b

  end

  section

    variable (U : Universe) [HasUnivFunctors U U] (α : Sort u) (β : Sort v) [HasFunctors α U]
             [HasFunctors β U] [h : HasExternalCoproducts U α β]

    @[reducible] def leftIntroFun  : α ⥤ Coprod U α β := h.defLeftIntroFun
    @[reducible] def rightIntroFun : β ⥤ Coprod U α β := h.defRightIntroFun

    instance leftIntro.isFunApp  {a : α} : IsFunApp (leftIntro  U a β) := ⟨leftIntroFun  U α β, a⟩
    instance rightIntro.isFunApp {b : β} : IsFunApp (rightIntro U α b) := ⟨rightIntroFun U α β, b⟩

  end

  section

    variable {U : Universe} [HasUnivFunctors U U] {α : Sort u} {β : Sort v} [HasFunctors α U]
             [HasFunctors β U] [h : HasExternalCoproducts U α β]

    @[reducible] def elim {Y : U} (F : α ⥤ Y) (G : β ⥤ Y) (S : Coprod U α β) : Y :=
      match h.hElim.elim S with
      | PSum.inl a => F a
      | PSum.inr b => G b

    @[reducible] def elimFun {Y : U} (F : α ⥤ Y) (G : β ⥤ Y) : Coprod U α β ⥤ Y :=
      (h.defElimFun₃ Y) F G

    instance elim.isFunApp {Y : U} {F : α ⥤ Y} {G : β ⥤ Y} {S : Coprod U α β} :
        IsFunApp (elim F G S) :=
      ⟨elimFun F G, S⟩

  end

  section

    variable {U : Universe} [HasUnivFunctors U U] (α : Sort u) (β : Sort v) [HasFunctors α U]
             [HasFunctors β U] [h : HasExternalCoproducts U α β]

    @[reducible] def elimFun₃ (Y : U) : (α ⥤ Y) ⥤ (β ⥤ Y) ⥤ (Coprod U α β ⥤ Y) := h.defElimFun₃ Y

    instance elimFun.isFunApp₂ {Y : U} {F : α ⥤ Y} {G : β ⥤ Y} : IsFunApp₂ (elimFun F G) :=
      ⟨elimFun₃ α β Y, F, G⟩

  end

end HasExternalCoproducts


class HasCoproducts (U : Universe) [HasUnivFunctors U U] where
  [hCoprod (A B : U) : HasExternalCoproducts U A B]

namespace HasCoproducts

  variable {U : Universe} [HasUnivFunctors U U] [h : HasCoproducts U]

  instance (A B : U) : HasExternalCoproducts U A B := h.hCoprod A B

  @[reducible] def Coprod (A B : U) : U := HasExternalCoproducts.Coprod U A B
  infix:34 " ⊔ " => HasCoproducts.Coprod

  @[reducible] def leftIntro  {A : U} (a : A) (B : U) : A ⊔ B :=
    HasExternalCoproducts.leftIntro  U a B
  @[reducible] def rightIntro (A : U) {B : U} (b : B) : A ⊔ B :=
    HasExternalCoproducts.rightIntro U A b

  @[reducible] def leftIntroFun  (A B : U) : A ⥤ A ⊔ B := HasExternalCoproducts.leftIntroFun  U A B
  @[reducible] def rightIntroFun (A B : U) : B ⥤ A ⊔ B := HasExternalCoproducts.rightIntroFun U A B

  @[reducible] def elim {A B Y : U} (F : A ⥤ Y) (G : B ⥤ Y) (S : A ⊔ B) : Y :=
    HasExternalCoproducts.elim F G S
  @[reducible] def elimFun {A B Y : U} (F : A ⥤ Y) (G : B ⥤ Y) : A ⊔ B ⥤ Y :=
    HasExternalCoproducts.elimFun F G
  @[reducible] def elimFun₃ (A B Y : U) : (A ⥤ Y) ⥤ (B ⥤ Y) ⥤ (A ⊔ B ⥤ Y) :=
    HasExternalCoproducts.elimFun₃ A B Y

end HasCoproducts
