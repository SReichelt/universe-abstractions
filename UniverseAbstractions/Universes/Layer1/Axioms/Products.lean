import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors



namespace UniverseAbstractions.Layer1

set_option autoImplicit false

universe u v

open HasPiType HasFunctors



namespace HasSigmaType

  section

    variable (U : Universe) {α : Sort u} (β : α → Sort v) [h : HasType U (PSigma β)]

    @[reducible] def Sigma : U := h.T

  end

  section

    variable (U : Universe) {α : Sort u} {β : α → Sort v} [h : HasTypeWithIntro U (PSigma β)]

    @[reducible] def intro (a : α) (b : β a) : Sigma U β := h.hIntro.intro ⟨a, b⟩

  end

  section

    variable {U : Universe} {α : Sort u} {β : α → Sort v} [h : HasType U (PSigma β)]

    @[reducible] def fst (P : Sigma U β) : α         := (h.hElim.elim P).fst
    @[reducible] def snd (P : Sigma U β) : β (fst P) := (h.hElim.elim P).snd

  end

end HasSigmaType



class HasExternalSigmaType (U : Universe) [HasUnivFunctors U U] {α : Sort u} (β : α → Sort v)
                           [∀ a, HasFunctors (β a) U] [∀ Y : U, HasType U (∀ a, β a ⥤ Y)] extends
    HasTypeWithIntro U (PSigma β) where
  defIntroFun (a : α) : [β a ⥤ T]_{λ b => hIntro.intro ⟨a, b⟩}
  defIntroFunPi : [∀ a, β a ⥤ T | U]_{defIntroFun}
  defElimFun₂ (Y : U) :
    [[∀ a, β a ⥤ Y | U] ⥤ T ⥤ Y]__{λ F P => F (hElim.elim P).fst (hElim.elim P).snd}

namespace HasExternalSigmaType

  open HasSigmaType

  section

    variable (U : Universe) [HasUnivFunctors U U] {α : Sort u} (β : α → Sort v)
             [∀ a, HasFunctors (β a) U] [∀ Y : U, HasType U (∀ a, β a ⥤ Y)]
             [h : HasExternalSigmaType U β]

    @[reducible] def introFun (a : α) : β a ⥤ Sigma U β := h.defIntroFun a
    @[reducible] def introFunPi : [∀ a, β a ⥤ Sigma U β | U] := h.defIntroFunPi

    instance intro.isFunApp {a : α} {b : β a} : IsFunApp (intro U a b) := ⟨introFun U β a, b⟩
    instance introFun.isPiApp {a : α} : IsPiApp (introFun U β a) := ⟨introFunPi U β, a, rfl⟩

  end

  section

    variable {U : Universe} [HasUnivFunctors U U] {α : Sort u} {β : α → Sort v}
             [∀ a, HasFunctors (β a) U] [∀ Y : U, HasType U (∀ a, β a ⥤ Y)]
             [h : HasExternalSigmaType U β]

    @[reducible] def elimFun {Y : U} (F : [∀ a, β a ⥤ Y | U]) : Sigma U β ⥤ Y :=
      (h.defElimFun₂ Y) F

  end

  section

    variable {U : Universe} [HasUnivFunctors U U] {α : Sort u} (β : α → Sort v)
             [∀ a, HasFunctors (β a) U] [∀ Y : U, HasType U (∀ a, β a ⥤ Y)]
             [h : HasExternalSigmaType U β]

    @[reducible] def elimFun₂ (Y : U) : [∀ a, β a ⥤ Y | U] ⥤ (Sigma U β ⥤ Y) := h.defElimFun₂ Y

    instance elimFun.isFunApp {Y : U} {F : [∀ a, β a ⥤ Y | U]} : IsFunApp (elimFun F) :=
      ⟨elimFun₂ β Y, F⟩

  end

end HasExternalSigmaType



class HasExternalProducts (U : Universe) [HasUnivFunctors U U] (α : Sort u) (β : Sort v)
                          [HasFunctors α U] [HasFunctors β U] extends
    HasTypeWithIntro U (PProd α β) where
  defIntroFun₂ : [α ⥤ β ⥤ T]__{λ a b => hIntro.intro ⟨a, b⟩}
  defElimFun₂ (Y : U) :
    [(α ⥤ β ⥤ Y) ⥤ T ⥤ Y]__{λ F P => F (hElim.elim P).fst (hElim.elim P).snd}

namespace HasExternalProducts

  section

    variable (U : Universe) [HasUnivFunctors U U] (α : Sort u) (β : Sort v) [hαU : HasFunctors α U]
             [HasFunctors β U] [h : HasExternalProducts U α β]

    @[reducible] def Prod : U := h.T

  end

  section

    variable (U : Universe) [HasUnivFunctors U U] {α : Sort u} {β : Sort v} [HasFunctors α U]
             [HasFunctors β U] [h : HasExternalProducts U α β]

    @[reducible] def intro (a : α) (b : β) : Prod U α β := h.hIntro.intro ⟨a, b⟩

  end

  section

    variable (U : Universe) [HasUnivFunctors U U] (α : Sort u) (β : Sort v) [HasFunctors α U]
             [HasFunctors β U] [h : HasExternalProducts U α β]

    @[reducible] def introFun₂ : α ⥤ β ⥤ Prod U α β := h.defIntroFun₂

    instance intro.isFunApp₂ {a : α} {b : β} : IsFunApp₂ (intro U a b) := ⟨introFun₂ U α β, a, b⟩

  end

  section

    variable {U : Universe} [HasUnivFunctors U U] {α : Sort u} {β : Sort v} [HasFunctors α U]
             [HasFunctors β U] [h : HasExternalProducts U α β]

    @[reducible] def fst (P : Prod U α β) : α := (h.hElim.elim P).fst
    @[reducible] def snd (P : Prod U α β) : β := (h.hElim.elim P).snd

    @[reducible] def elimFun {Y : U} (F : α ⥤ β ⥤ Y) : Prod U α β ⥤ Y := (h.defElimFun₂ Y) F

  end

  section

    variable {U : Universe} [HasUnivFunctors U U] (α : Sort u) (β : Sort v) [HasFunctors α U]
             [HasFunctors β U] [h : HasExternalProducts U α β]

    @[reducible] def elimFun₂ (Y : U) : (α ⥤ β ⥤ Y) ⥤ (Prod U α β ⥤ Y) := h.defElimFun₂ Y

    instance elimFun.isFunApp {Y : U} {F : α ⥤ β ⥤ Y} : IsFunApp (elimFun F) := ⟨elimFun₂ α β Y, F⟩

  end

  section

    variable (U : Universe) [HasUnivFunctors U U] (α : Sort u) (β : Sort v) [hαU : HasFunctors α U]
             [HasFunctors β U] [h : HasExternalProducts U α β]

    local instance (Y : U) : HasType U (∀ a : α, (λ _ => β) a ⥤ Y) := hαU.hFun (β ⥤ Y)

    instance hasSigmaType : HasTypeWithIntro U (Σ' _ : α, β) where
      T      := Prod U α β
      hElim  := ⟨λ P => ⟨fst P, snd P⟩⟩
      hIntro := ⟨λ ⟨l, r⟩ => intro U l r⟩

    instance hasExternalSigmaType : HasExternalSigmaType U (λ _ : α => β) where
      defIntroFun   a := (introFun₂ U α β) a
      defIntroFunPi   := introFun₂ U α β
      defElimFun₂   Y := h.defElimFun₂ Y

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

  @[reducible] def elimFun {A B Y : U} (F : A ⥤ B ⥤ Y) : A ⊓ B ⥤ Y := HasExternalProducts.elimFun F
  @[reducible] def elimFun₂ (A B Y : U) : (A ⥤ B ⥤ Y) ⥤ (A ⊓ B ⥤ Y) :=
    HasExternalProducts.elimFun₂ A B Y

end HasProducts
