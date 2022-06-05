import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations
import UniverseAbstractions.Universes.Layer1.Meta.Tactics.Functoriality

import UniverseAbstractions.Universes.Helpers



namespace UniverseAbstractions.Layer1

set_option autoBoundImplicitLocal false

open Universe HasFunctors HasIdFun HasRevCompFun₃ Prerelation Helpers

universe u u' u''



class HasPreorderRelation (V : outParam Universe) [outParam (HasLinearLogic V)] (α : Sort u) where
  Hom : Prerelation α V
  [h : IsPreorder Hom]

namespace HasPreorderRelation

  variable {V : Universe} [HasLinearLogic V]

  instance (α : Sort u) [h : HasPreorderRelation V α] : IsPreorder h.Hom := h.h

  section

    variable {α : Sort u} [h : HasPreorderRelation V α]

    infixr:20 " ⟶ " => HasPreorderRelation.Hom

    @[reducible] def idHom (a : α) : a ⟶ a := h.h.refl a
    @[reducible] def compHom {a b c : α} (f : a ⟶ b) (g : b ⟶ c) : a ⟶ c := g • f

  end

  def opposite (α : Sort u) [h : HasPreorderRelation V α] := α

  instance opposite.hasPreorderRelation (α : Sort u) [h : HasPreorderRelation V α] :
      HasPreorderRelation V (opposite α) :=
    ⟨Prerelation.opposite h.Hom⟩

  @[reducible] def PreorderFunctor {α : Sort u} {β : Sort u'} [hα : HasPreorderRelation V α]
                                   [hβ : HasPreorderRelation V β] (φ : α → β) :=
    Implication hα.Hom (lift hβ.Hom φ)

  namespace PreorderFunctor

    @[reducible] def idFun (α : Sort u) [hα : HasPreorderRelation V α] : PreorderFunctor (@id α) :=
      Implication.idImpl hα.Hom

    @[reducible] def constFun [HasSubLinearLogic V] (α : Sort u) {β : Sort u'}
                              [hα : HasPreorderRelation V α] [hβ : HasPreorderRelation V β] (b : β) :
        PreorderFunctor (Function.const α b) :=
      Implication.constImpl hα.Hom (idHom b)

    @[reducible] def compFun {α : Sort u} {β : Sort u'} {γ : Sort u''}
                             [hα : HasPreorderRelation V α] [hβ : HasPreorderRelation V β]
                             [hγ : HasPreorderRelation V γ] {φ : α → β} {ψ : β → γ}
                             (F : PreorderFunctor φ) (G : PreorderFunctor ψ) :
        PreorderFunctor (ψ ∘ φ) :=
      Implication.compImpl F (Implication.lift G φ)

  end PreorderFunctor

  def PreorderFunctor₂ {α : Sort u} {β : Sort u'} {γ : Sort u''} [hα : HasPreorderRelation V α]
                       [hβ : HasPreorderRelation V β] [hγ : HasPreorderRelation V γ]
                       (φ : α → β → γ) :=
    AbstractBiFun PreorderFunctor PreorderFunctor φ

  namespace PreorderFunctor₂

    section

      variable {α : Sort u} {β : Sort u'} {γ : Sort u''} [hα : HasPreorderRelation V α]
               [hβ : HasPreorderRelation V β] [hγ : HasPreorderRelation V γ] {φ : α → β → γ}
               (F : PreorderFunctor₂ φ)

      @[reducible] def apply {a₁ a₂ : α} {b₁ b₂ : β} (f : a₁ ⟶ a₂) (g : b₁ ⟶ b₂) :
          φ a₁ b₁ ⟶ φ a₂ b₂ :=
        (F.app a₂) g • (F.app₂ b₁) f

      @[reducible] def apply' {a₁ a₂ : α} {b₁ b₂ : β} (f : a₁ ⟶ a₂) (g : b₁ ⟶ b₂) :
          φ a₁ b₁ ⟶ φ a₂ b₂ :=
        (F.app₂ b₂) f • (F.app a₁) g

      @[reducible] def applyFun₂ (a₁ a₂ : α) (b₁ b₂ : β) :
          (a₁ ⟶ a₂) ⥤ (b₁ ⟶ b₂) ⥤ (φ a₁ b₁ ⟶ φ a₂ b₂) :=
        Λ f g => apply F f g

      @[reducible] def applyFun₂' (a₁ a₂ : α) (b₁ b₂ : β) :
          (a₁ ⟶ a₂) ⥤ (b₁ ⟶ b₂) ⥤ (φ a₁ b₁ ⟶ φ a₂ b₂) :=
        Λ f g => apply' F f g

      instance apply.isFunApp₂ {a₁ a₂ : α} {b₁ b₂ : β} {f : a₁ ⟶ a₂} {g : b₁ ⟶ b₂} :
          IsFunApp₂ (a₁ ⟶ a₂) (b₁ ⟶ b₂) (apply F f g) :=
        ⟨applyFun₂ F a₁ a₂ b₁ b₂, f, g⟩

      instance apply'.isFunApp₂ {a₁ a₂ : α} {b₁ b₂ : β} {f : a₁ ⟶ a₂} {g : b₁ ⟶ b₂} :
          IsFunApp₂ (a₁ ⟶ a₂) (b₁ ⟶ b₂) (apply' F f g) :=
        ⟨applyFun₂' F a₁ a₂ b₁ b₂, f, g⟩

    end

    @[reducible] def swapFun₂ {α : Sort u} {β : Sort u'} {γ : Sort u''}
                              [hα : HasPreorderRelation V α] [hβ : HasPreorderRelation V β]
                              [hγ : HasPreorderRelation V γ] {φ : α → β → γ}
                              (F : PreorderFunctor₂ φ) :
        PreorderFunctor₂ (λ b a => φ a b) :=
      AbstractBiFun.swap F

    @[reducible] def dupFun [HasNonLinearLogic V] {α : Sort u} {β : Sort u'}
                            [hα : HasPreorderRelation V α] [hβ : HasPreorderRelation V β]
                            {φ : α → α → β} (F : PreorderFunctor₂ φ) :
        PreorderFunctor (λ a => φ a a) :=
      Implication₂.dupImpl ⟨λ a b => applyFun₂ F a b a b⟩

    @[reducible] def substFun [HasNonLinearLogic V] {α : Sort u} {β : Sort u'} {γ : Sort u''}
                              [hα : HasPreorderRelation V α] [hβ : HasPreorderRelation V β]
                              [hγ : HasPreorderRelation V γ] {φ : α → β} {ψ : α → β → γ}
                              (F : PreorderFunctor φ) (G : PreorderFunctor₂ ψ) :
        PreorderFunctor (λ a => ψ a (φ a)) :=
      Implication₂.substImpl F ⟨λ a b => applyFun₂ G a b (φ a) (φ b)⟩

  end PreorderFunctor₂

end HasPreorderRelation

open HasPreorderRelation


class HasEquivalenceRelationBase (V : outParam Universe) [outParam (HasLinearLogic V)] (α : Sort u)
                                 where
  Iso : Prerelation α V
  [h : IsEquivalence Iso]

namespace HasEquivalenceRelationBase

  variable {V : Universe} [HasLinearLogic V]

  instance (α : Sort u) [h : HasEquivalenceRelationBase V α] : IsEquivalence h.Iso := h.h

  section

    variable {α : Sort u} [h : HasEquivalenceRelationBase V α]

    infix:25 " ≃ " => HasEquivalenceRelationBase.Iso

    @[reducible] def idIso (a : α) : a ≃ a := h.h.refl a
    @[reducible] def invIso {a b : α} (e : a ≃ b) : b ≃ a := e⁻¹
    @[reducible] def compIso {a b c : α} (f : a ≃ b) (g : b ≃ c) : a ≃ c := g • f

  end

  def asPreorder (α : Sort u) [h : HasEquivalenceRelationBase V α] := α

  instance asPreorder.hasPreorderRelation (α : Sort u) [h : HasEquivalenceRelationBase V α] :
      HasPreorderRelation V (asPreorder α) :=
    ⟨h.Iso⟩

  def opposite (α : Sort u) [h : HasEquivalenceRelationBase V α] := α

  instance opposite.hasEquivalenceRelation (α : Sort u) [h : HasEquivalenceRelationBase V α] :
      HasEquivalenceRelationBase V (opposite α) :=
    ⟨Prerelation.opposite h.Iso⟩

  @[reducible] def EquivalenceFunctor {α : Sort u} {β : Sort u'}
                                      [hα : HasEquivalenceRelationBase V α]
                                      [hβ : HasEquivalenceRelationBase V β] (φ : α → β) :=
    PreorderFunctor (α := asPreorder α) (β := asPreorder β) φ

  namespace EquivalenceFunctor

    def symmFun (α : Sort u) [hα : HasEquivalenceRelationBase V α] :
        EquivalenceFunctor (β := opposite α) (@id α) :=
      Implication.symmImpl hα.Iso

  end EquivalenceFunctor

  @[reducible] def EquivalenceFunctor₂ {α : Sort u} {β : Sort u'} {γ : Sort u''}
                                       [hα : HasEquivalenceRelationBase V α]
                                       [hβ : HasEquivalenceRelationBase V β]
                                       [hγ : HasEquivalenceRelationBase V γ] (φ : α → β → γ) :=
    PreorderFunctor₂ (α := asPreorder α) (β := asPreorder β) (γ := asPreorder γ) φ

  namespace EquivalenceFunctor₂

    section

      variable {α : Sort u} {β : Sort u'} {γ : Sort u''} [hα : HasEquivalenceRelationBase V α]
               [hβ : HasEquivalenceRelationBase V β] [hγ : HasEquivalenceRelationBase V γ]
               {φ : α → β → γ} (F : EquivalenceFunctor₂ φ)

      @[reducible] def apply {a₁ a₂ : α} {b₁ b₂ : β} (f : a₁ ≃ a₂) (g : b₁ ≃ b₂) :
          φ a₁ b₁ ≃ φ a₂ b₂ :=
        (F.app a₂) g • (F.app₂ b₁) f

      @[reducible] def apply' {a₁ a₂ : α} {b₁ b₂ : β} (f : a₁ ≃ a₂) (g : b₁ ≃ b₂) :
          φ a₁ b₁ ≃ φ a₂ b₂ :=
        (F.app₂ b₂) f • (F.app a₁) g

      @[reducible] def applyFun₂ (a₁ a₂ : α) (b₁ b₂ : β) :
          (a₁ ≃ a₂) ⥤ (b₁ ≃ b₂) ⥤ (φ a₁ b₁ ≃ φ a₂ b₂) :=
        Λ f g => apply F f g

      @[reducible] def applyFun₂' (a₁ a₂ : α) (b₁ b₂ : β) :
          (a₁ ≃ a₂) ⥤ (b₁ ≃ b₂) ⥤ (φ a₁ b₁ ≃ φ a₂ b₂) :=
        Λ f g => apply' F f g

      instance apply.isFunApp₂ {a₁ a₂ : α} {b₁ b₂ : β} {f : a₁ ≃ a₂} {g : b₁ ≃ b₂} :
          IsFunApp₂ (a₁ ≃ a₂) (b₁ ≃ b₂) (apply F f g) :=
        ⟨applyFun₂ F a₁ a₂ b₁ b₂, f, g⟩

      instance apply'.isFunApp₂ {a₁ a₂ : α} {b₁ b₂ : β} {f : a₁ ≃ a₂} {g : b₁ ≃ b₂} :
          IsFunApp₂ (a₁ ≃ a₂) (b₁ ≃ b₂) (apply' F f g) :=
        ⟨applyFun₂' F a₁ a₂ b₁ b₂, f, g⟩

    end

  end EquivalenceFunctor₂

end HasEquivalenceRelationBase



namespace HasLinearLogic

  section

    variable (U : Universe) [HasLinearLogic U]

    def funRel : Prerelation U U := λ A B => A ⥤ B

    instance funRel.isPreorder : IsPreorder (funRel U) where
      refl         A := idFun       A
      revTransFun₂ A := revCompFun₃ A

    instance hasPreorderRelation : HasPreorderRelation U U := ⟨funRel U⟩

  end

  section

    variable {U : Universe} [HasLinearLogic U]

    @[reducible] def asHom {A B : U} (F : A ⥤ B) : A ⟶ B := F

    instance (A B : U) : CoeFun (A ⟶ B) (λ _ => A → B) := HasFunctors.coeFun A B

    -- The hom-bifunctor is covariant in one argument and contravariant in the other.
    def homFun₂ (α : Sort u) [hα : HasPreorderRelation U α] :
        PreorderFunctor₂ (α := opposite α) (β := α) (γ := U) hα.Hom where
      app  a := ⟨λ b₁ b₂ => HasTrans.revTransFun₂ a b₁ b₂⟩
      app₂ b := ⟨λ a₁ a₂ => HasTrans.transFun₂ (R := hα.Hom) a₂ a₁ b⟩

    @[reducible] def idFun (A : U) : A ⟶ A := idHom A

    @[reducible] def revAppFun {A : U} (a : A) (B : U) : (A ⟶ B) ⟶ B := HasRevAppFun.revAppFun a B
    @[reducible] def revAppFun₂ (A B : U) : A ⟶ (A ⟶ B) ⟶ B := HasRevAppFun.revAppFun₂ A B

    @[reducible] def swapFun {A B C : U} (F : A ⟶ B ⟶ C) (b : B) : A ⟶ C := HasSwapFun.swapFun F b
    @[reducible] def swapFun₂ {A B C : U} (F : A ⟶ B ⟶ C) : B ⟶ A ⟶ C := HasSwapFun.swapFun₂ F
    @[reducible] def swapFun₃ (A B C : U) : (A ⟶ B ⟶ C) ⟶ (B ⟶ A ⟶ C) := HasSwapFun₃.swapFun₃ A B C

  end

end HasLinearLogic


namespace HasSubLinearLogic

  variable {U : Universe} [HasLinearLogic U] [HasSubLinearLogic U]

  @[reducible] def constFun (A : U) {B : U} (b : B) : A ⟶ B := HasConstFun.constFun A b
  @[reducible] def constFun₂ (A B : U) : B ⟶ (A ⟶ B) := HasConstFun₂.constFun₂ A B

end HasSubLinearLogic


namespace HasNonLinearLogic

  variable {U : Universe} [HasLinearLogic U] [HasNonLinearLogic U]

  @[reducible] def dupFun {A B : U} (F : A ⟶ A ⟶ B) : A ⟶ B := HasDupFun.dupFun F
  @[reducible] def dupFun₂ (A B : U) : (A ⟶ A ⟶ B) ⟶ (A ⟶ B) := HasDupFun₂.dupFun₂ A B

  @[reducible] def revSubstFun {A B C : U} (G : A ⟶ B ⟶ C) (F : A ⟶ B) : A ⟶ C :=
    HasSubstFun.revSubstFun G F

end HasNonLinearLogic



namespace HasPreorderRelation

  variable {V : Universe} [HasLinearLogic V] {α : Sort u} [h : HasPreorderRelation V α]

  @[reducible] def revTransFun₂ (a b c : α) : (b ⟶ c) ⟶ (a ⟶ b) ⟶ (a ⟶ c) :=
    HasTrans.revTransFun₂ a b c

end HasPreorderRelation


namespace HasEquivalenceRelationBase

  variable {V : Universe} [HasLinearLogic V] {α : Sort u} [h : HasEquivalenceRelationBase V α]

  @[reducible] def symmFun (a b : α) : a ≃ b ⟶ b ≃ a := HasSymm.symmFun a b

  @[reducible] def revTransFun₂ (a b c : α) : b ≃ c ⟶ a ≃ b ⟶ a ≃ c :=
    HasTrans.revTransFun₂ a b c

end HasEquivalenceRelationBase
