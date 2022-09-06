import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations
import UniverseAbstractions.Universes.Layer1.Meta.Tactics.Functoriality

import UniverseAbstractions.Universes.Helpers



namespace UniverseAbstractions.Layer1

set_option autoImplicit false
set_option linter.unusedVariables false

open Universe HasFunctors HasIdFun HasRevCompFunPiFun Prerelation Helpers

universe u u' u'' u''' u''''



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

  def opposite (α : Sort u) [HasPreorderRelation V α] := α

  instance opposite.hasPreorderRelation (α : Sort u) [h : HasPreorderRelation V α] :
      HasPreorderRelation V (opposite α) :=
    ⟨Prerelation.opposite h.Hom⟩

  class IsPreorderFunctor {α : Sort u} {β : Sort u'} [hα : HasPreorderRelation V α]
                          [hβ : HasPreorderRelation V β] (φ : α → β) extends
    HasImplication hα.Hom (lift hβ.Hom φ)

  namespace IsPreorderFunctor

    def construct {α : Sort u} {β : Sort u'} [hα : HasPreorderRelation V α]
                  [hβ : HasPreorderRelation V β] {φ : α → β}
                  (hφ : ∀ a₁ a₂, (a₁ ⟶ a₂) ⥤ (φ a₁ ⟶ φ a₂)) :
        IsPreorderFunctor φ where
      inst := hφ

    section

      variable {α : Sort u} {β : Sort u'} [hα : HasPreorderRelation V α]
               [hβ : HasPreorderRelation V β] (φ : α → β) [hφ : IsPreorderFunctor φ]

      @[reducible] def apply {a₁ a₂ : α} (f : a₁ ⟶ a₂) : φ a₁ ⟶ φ a₂ := hφ.toHasImplication f

    end

    instance coeFun {α : Sort u} {β : Sort u'} [hα : HasPreorderRelation V α]
                    [hβ : HasPreorderRelation V β] (φ : α → β) :
        CoeFun (IsPreorderFunctor φ) (λ _ => ∀ {a₁ a₂}, (a₁ ⟶ a₂) → (φ a₁ ⟶ φ a₂)) :=
      ⟨λ _ => apply φ⟩

    instance idFun (α : Sort u) [hα : HasPreorderRelation V α] : IsPreorderFunctor (@id α) where
      toHasImplication := HasImplication.idImpl hα.Hom

    instance constFun [HasSubLinearLogic V] (α : Sort u) {β : Sort u'}
                      [hα : HasPreorderRelation V α] [hβ : HasPreorderRelation V β] (b : β) :
        IsPreorderFunctor (Function.const α b) where
      toHasImplication := HasImplication.constImpl hα.Hom (idHom b)

    instance compFun {α : Sort u} {β : Sort u'} {γ : Sort u''} [hα : HasPreorderRelation V α]
                     [hβ : HasPreorderRelation V β] [hγ : HasPreorderRelation V γ] (φ : α → β)
                     (ψ : β → γ) [hφ : IsPreorderFunctor φ] [hψ : IsPreorderFunctor ψ] :
        IsPreorderFunctor (ψ ∘ φ) where
      toHasImplication := HasImplication.compImpl hα.Hom (lift hβ.Hom φ) (lift hγ.Hom (ψ ∘ φ))
                            (hST := HasImplication.lift hβ.Hom (lift hγ.Hom ψ) φ)

  end IsPreorderFunctor

  class IsPreorderFunctor₂ {α : Sort u} {β : Sort u'} {γ : Sort u''} [hα : HasPreorderRelation V α]
                           [hβ : HasPreorderRelation V β] [hγ : HasPreorderRelation V γ]
                           (φ : α → β → γ) extends
    AbstractMultiFun₂ IsPreorderFunctor IsPreorderFunctor φ

  namespace IsPreorderFunctor₂

    def construct {α : Sort u} {β : Sort u'} {γ : Sort u''} [hα : HasPreorderRelation V α]
               [hβ : HasPreorderRelation V β] [hγ : HasPreorderRelation V γ] {φ : α → β → γ}
               (hφa : ∀ a b₁ b₂, (b₁ ⟶ b₂) ⥤ (φ a b₁ ⟶ φ a b₂))
               (hφb : ∀ a₁ a₂ b, (a₁ ⟶ a₂) ⥤ (φ a₁ b ⟶ φ a₂ b)) :
        IsPreorderFunctor₂ φ where
      app  a := IsPreorderFunctor.construct (hφa a)
      app₂ b := IsPreorderFunctor.construct (λ a₁ a₂ => hφb a₁ a₂ b)

    section

      variable {α : Sort u} {β : Sort u'} {γ : Sort u''} [hα : HasPreorderRelation V α]
               [hβ : HasPreorderRelation V β] [hγ : HasPreorderRelation V γ] (φ : α → β → γ)
               [hφ : IsPreorderFunctor₂ φ]

      def apply {a₁ a₂ : α} {b₁ b₂ : β} (f : a₁ ⟶ a₂) (g : b₁ ⟶ b₂) : φ a₁ b₁ ⟶ φ a₂ b₂ :=
        (hφ.app a₂) g • (hφ.app₂ b₁) f

      def apply' {a₁ a₂ : α} {b₁ b₂ : β} (f : a₁ ⟶ a₂) (g : b₁ ⟶ b₂) : φ a₁ b₁ ⟶ φ a₂ b₂ :=
        (hφ.app₂ b₂) f • (hφ.app a₁) g

      def applyFun₂ (a₁ a₂ : α) (b₁ b₂ : β) : (a₁ ⟶ a₂) ⥤ (b₁ ⟶ b₂) ⥤ (φ a₁ b₁ ⟶ φ a₂ b₂) :=
        Λ f g => apply φ f g

      def applyFun₂' (a₁ a₂ : α) (b₁ b₂ : β) : (a₁ ⟶ a₂) ⥤ (b₁ ⟶ b₂) ⥤ (φ a₁ b₁ ⟶ φ a₂ b₂) :=
        Λ f g => apply' φ f g

      instance apply.isFunApp₂ {a₁ a₂ : α} {b₁ b₂ : β} {f : a₁ ⟶ a₂} {g : b₁ ⟶ b₂} :
          IsFunApp₂ (apply φ f g) :=
        ⟨applyFun₂ φ a₁ a₂ b₁ b₂, f, g⟩

      instance apply'.isFunApp₂ {a₁ a₂ : α} {b₁ b₂ : β} {f : a₁ ⟶ a₂} {g : b₁ ⟶ b₂} :
          IsFunApp₂ (apply' φ f g) :=
        ⟨applyFun₂' φ a₁ a₂ b₁ b₂, f, g⟩

    end

    instance coeFun {α : Sort u} {β : Sort u'} {γ : Sort u''} [hα : HasPreorderRelation V α]
                    [hβ : HasPreorderRelation V β] [hγ : HasPreorderRelation V γ] (φ : α → β → γ) :
        CoeFun (IsPreorderFunctor₂ φ)
               (λ _ => ∀ {a₁ a₂ b₁ b₂}, (a₁ ⟶ a₂) → (b₁ ⟶ b₂) → (φ a₁ b₁ ⟶ φ a₂ b₂)) :=
      ⟨λ _ => apply φ⟩

    instance swapFun₂ {α : Sort u} {β : Sort u'} {γ : Sort u''} [hα : HasPreorderRelation V α]
                      [hβ : HasPreorderRelation V β] [hγ : HasPreorderRelation V γ] (φ : α → β → γ)
                      [hφ : IsPreorderFunctor₂ φ] :
        IsPreorderFunctor₂ (λ b a => φ a b) where
      toAbstractMultiFun₂ := AbstractMultiFun₂.swap hφ.toAbstractMultiFun₂

    instance dupFun [HasNonLinearLogic V] {α : Sort u} {β : Sort u'} [hα : HasPreorderRelation V α]
                    [hβ : HasPreorderRelation V β] (φ : α → α → β) [hφ : IsPreorderFunctor₂ φ] :
        IsPreorderFunctor (λ a => φ a a) where
      toHasImplication := HasImplication₂.dupImpl hα.Hom (lift hβ.Hom (λ a => φ a a))
                            (h := { inst := λ a b => applyFun₂ φ a b a b })

    instance substFun [HasNonLinearLogic V] {α : Sort u} {β : Sort u'} {γ : Sort u''}
                      [hα : HasPreorderRelation V α] [hβ : HasPreorderRelation V β]
                      [hγ : HasPreorderRelation V γ] (φ : α → β) (ψ : α → β → γ)
                      [hφ : IsPreorderFunctor φ] [hψ : IsPreorderFunctor₂ ψ] :
        IsPreorderFunctor (λ a => ψ a (φ a)) where
      toHasImplication := HasImplication₂.substImpl hα.Hom (lift hβ.Hom φ)
                                                    (lift hγ.Hom (λ a => ψ a (φ a)))
                            (hRST := { inst := λ a b => applyFun₂ ψ a b (φ a) (φ b) })

  end IsPreorderFunctor₂

  class IsPreorderFunctor₃ {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''}
                           [hα : HasPreorderRelation V α] [hβ : HasPreorderRelation V β]
                           [hγ : HasPreorderRelation V γ] [hδ : HasPreorderRelation V δ]
                           (φ : α → β → γ → δ) extends
    AbstractMultiFun₃ IsPreorderFunctor IsPreorderFunctor IsPreorderFunctor φ

  namespace IsPreorderFunctor₃

    def construct {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''}
                  [hα : HasPreorderRelation V α] [hβ : HasPreorderRelation V β]
                  [hγ : HasPreorderRelation V γ] [hδ : HasPreorderRelation V δ] {φ : α → β → γ → δ}
                  (hφab : ∀ a b c₁ c₂, (c₁ ⟶ c₂) ⥤ (φ a b c₁ ⟶ φ a b c₂))
                  (hφac : ∀ a b₁ b₂ c, (b₁ ⟶ b₂) ⥤ (φ a b₁ c ⟶ φ a b₂ c))
                  (hφbc : ∀ a₁ a₂ b c, (a₁ ⟶ a₂) ⥤ (φ a₁ b c ⟶ φ a₂ b c)) :
        IsPreorderFunctor₃ φ where
      app   a   := (IsPreorderFunctor₂.construct (hφab a) (hφac a)).toAbstractMultiFun₂
      app₂₃ b c := IsPreorderFunctor.construct (λ a₁ a₂ => hφbc a₁ a₂ b c)

    section

      variable {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''}
               [hα : HasPreorderRelation V α] [hβ : HasPreorderRelation V β]
               [hγ : HasPreorderRelation V γ] [hδ : HasPreorderRelation V δ] (φ : α → β → γ → δ)
               [hφ : IsPreorderFunctor₃ φ]

      def apply {a₁ a₂ : α} {b₁ b₂ : β} {c₁ c₂ : γ} (f : a₁ ⟶ a₂) (g : b₁ ⟶ b₂) (h : c₁ ⟶ c₂) :
          φ a₁ b₁ c₁ ⟶ φ a₂ b₂ c₂ :=
        IsPreorderFunctor₂.apply (φ a₂) (hφ := ⟨hφ.app a₂⟩) g h • (hφ.app₂₃ b₁ c₁) f

      def applyFun₃ (a₁ a₂ : α) (b₁ b₂ : β) (c₁ c₂ : γ) :
          (a₁ ⟶ a₂) ⥤ (b₁ ⟶ b₂) ⥤ (c₁ ⟶ c₂) ⥤ (φ a₁ b₁ c₁ ⟶ φ a₂ b₂ c₂) :=
        Λ f g h => apply φ f g h

      instance apply.isFunApp₃ {a₁ a₂ : α} {b₁ b₂ : β} {c₁ c₂ : γ} {f : a₁ ⟶ a₂} {g : b₁ ⟶ b₂}
                               {h : c₁ ⟶ c₂} :
          IsFunApp₃ (apply φ f g h) :=
        ⟨applyFun₃ φ a₁ a₂ b₁ b₂ c₁ c₂, f, g, h⟩

    end

  end IsPreorderFunctor₃

  class IsPreorderFunctor₄ {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''} {ε : Sort u''''}
                           [hα : HasPreorderRelation V α] [hβ : HasPreorderRelation V β]
                           [hγ : HasPreorderRelation V γ] [hδ : HasPreorderRelation V δ]
                           [hε : HasPreorderRelation V ε] (φ : α → β → γ → δ → ε) extends
    AbstractMultiFun₄ IsPreorderFunctor IsPreorderFunctor IsPreorderFunctor IsPreorderFunctor φ

  namespace IsPreorderFunctor₄

    def construct {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''} {ε : Sort u''''}
                  [hα : HasPreorderRelation V α] [hβ : HasPreorderRelation V β]
                  [hγ : HasPreorderRelation V γ] [hδ : HasPreorderRelation V δ]
                  [hε : HasPreorderRelation V ε] {φ : α → β → γ → δ → ε}
                  (hφabc : ∀ a b c d₁ d₂, (d₁ ⟶ d₂) ⥤ (φ a b c d₁ ⟶ φ a b c d₂))
                  (hφabd : ∀ a b c₁ c₂ d, (c₁ ⟶ c₂) ⥤ (φ a b c₁ d ⟶ φ a b c₂ d))
                  (hφacd : ∀ a b₁ b₂ c d, (b₁ ⟶ b₂) ⥤ (φ a b₁ c d ⟶ φ a b₂ c d))
                  (hφbcd : ∀ a₁ a₂ b c d, (a₁ ⟶ a₂) ⥤ (φ a₁ b c d ⟶ φ a₂ b c d)) :
        IsPreorderFunctor₄ φ where
      app    a     := (IsPreorderFunctor₃.construct (hφabc a) (hφabd a) (hφacd a)).toAbstractMultiFun₃
      app₂₃₄ b c d := IsPreorderFunctor.construct (λ a₁ a₂ => hφbcd a₁ a₂ b c d)

    section

      variable {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''} {ε : Sort u''''}
               [hα : HasPreorderRelation V α] [hβ : HasPreorderRelation V β]
               [hγ : HasPreorderRelation V γ] [hδ : HasPreorderRelation V δ]
               [hε : HasPreorderRelation V ε] (φ : α → β → γ → δ → ε) [hφ : IsPreorderFunctor₄ φ]

      def apply {a₁ a₂ : α} {b₁ b₂ : β} {c₁ c₂ : γ} {d₁ d₂ : δ} (f : a₁ ⟶ a₂) (g : b₁ ⟶ b₂)
                (h : c₁ ⟶ c₂) (i : d₁ ⟶ d₂) :
          φ a₁ b₁ c₁ d₁ ⟶ φ a₂ b₂ c₂ d₂ :=
        IsPreorderFunctor₃.apply (φ a₂) (hφ := ⟨hφ.app a₂⟩) g h i • (hφ.app₂₃₄ b₁ c₁ d₁) f

      def applyFun₄ (a₁ a₂ : α) (b₁ b₂ : β) (c₁ c₂ : γ) (d₁ d₂ : δ) :
          (a₁ ⟶ a₂) ⥤ (b₁ ⟶ b₂) ⥤ (c₁ ⟶ c₂) ⥤ (d₁ ⟶ d₂) ⥤ (φ a₁ b₁ c₁ d₁ ⟶ φ a₂ b₂ c₂ d₂) :=
        Λ f g h i => apply φ f g h i

      instance apply.isFunApp₄ {a₁ a₂ : α} {b₁ b₂ : β} {c₁ c₂ : γ} {d₁ d₂ : δ} {f : a₁ ⟶ a₂}
                               {g : b₁ ⟶ b₂} {h : c₁ ⟶ c₂} {i : d₁ ⟶ d₂} :
          IsFunApp₄ (apply φ f g h i) :=
        ⟨applyFun₄ φ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂, f, g, h, i⟩

    end

  end IsPreorderFunctor₄

  structure PreorderFunctor (α : Sort u) (β : Sort u') [hα : HasPreorderRelation V α]
                            [hβ : HasPreorderRelation V β] where
    φ : α → β
    [hφ : IsPreorderFunctor φ]

  namespace PreorderFunctor

    instance {α : Sort u} {β : Sort u'} [hα : HasPreorderRelation V α]
             [hβ : HasPreorderRelation V β] (F : PreorderFunctor α β) :
        IsPreorderFunctor F.φ :=
      F.hφ

    instance coeFun (α : Sort u) (β : Sort u') [hα : HasPreorderRelation V α]
                    [hβ : HasPreorderRelation V β] :
        CoeFun (PreorderFunctor α β) (λ _ => α → β) :=
      ⟨PreorderFunctor.φ⟩

    def idFun (α : Sort u) [hα : HasPreorderRelation V α] : PreorderFunctor α α := ⟨id⟩

    def constFun [HasSubLinearLogic V] (α : Sort u) {β : Sort u'} [hα : HasPreorderRelation V α]
                 [hβ : HasPreorderRelation V β] (b : β) :
        PreorderFunctor α β :=
      ⟨Function.const α b⟩

    def compFun {α : Sort u} {β : Sort u'} {γ : Sort u''} [hα : HasPreorderRelation V α]
                [hβ : HasPreorderRelation V β] [hγ : HasPreorderRelation V γ]
                (F : PreorderFunctor α β) (G : PreorderFunctor β γ) :
        PreorderFunctor α γ :=
      ⟨G.φ ∘ F.φ⟩

  end PreorderFunctor

  structure PreorderFunctor₂ (α : Sort u) (β : Sort u') (γ : Sort u'')
                             [hα : HasPreorderRelation V α] [hβ : HasPreorderRelation V β]
                             [hγ : HasPreorderRelation V γ] where
    φ : α → β → γ
    [hφ : IsPreorderFunctor₂ φ]

  namespace PreorderFunctor₂

    section

      variable {α : Sort u} {β : Sort u'} {γ : Sort u''} [hα : HasPreorderRelation V α]
               [hβ : HasPreorderRelation V β] [hγ : HasPreorderRelation V γ]
               (F : PreorderFunctor₂ α β γ)

      instance : IsPreorderFunctor₂ F.φ := F.hφ

      instance (a : α) : IsPreorderFunctor (F.φ a)          := F.hφ.app  a
      instance (b : β) : IsPreorderFunctor (λ a => F.φ a b) := F.hφ.app₂ b

      def app  (a : α) : PreorderFunctor β γ := ⟨F.φ a⟩
      def app₂ (b : β) : PreorderFunctor α γ := ⟨λ a => F.φ a b⟩

    end

    instance coeFun (α : Sort u) (β : Sort u') (γ : Sort u'') [hα : HasPreorderRelation V α]
                    [hβ : HasPreorderRelation V β] [hγ : HasPreorderRelation V γ] :
        CoeFun (PreorderFunctor₂ α β γ) (λ _ => α → β → γ) :=
      ⟨PreorderFunctor₂.φ⟩

    def swapFun₂ {α : Sort u} {β : Sort u'} {γ : Sort u''} [hα : HasPreorderRelation V α]
                 [hβ : HasPreorderRelation V β] [hγ : HasPreorderRelation V γ]
                 (F : PreorderFunctor₂ α β γ) :
        PreorderFunctor₂ β α γ :=
      ⟨λ b a => F.φ a b⟩

    def dupFun [HasNonLinearLogic V] {α : Sort u} {β : Sort u'} [hα : HasPreorderRelation V α]
               [hβ : HasPreorderRelation V β] (F : PreorderFunctor₂ α α β) :
        PreorderFunctor α β :=
      ⟨λ a => F.φ a a⟩

    def substFun [HasNonLinearLogic V] {α : Sort u} {β : Sort u'} {γ : Sort u''}
                 [hα : HasPreorderRelation V α] [hβ : HasPreorderRelation V β]
                 [hγ : HasPreorderRelation V γ] (F : PreorderFunctor α β)
                 (G : PreorderFunctor₂ α β γ) :
        PreorderFunctor α γ :=
      ⟨λ a => G.φ a (F.φ a)⟩

  end PreorderFunctor₂

  structure PreorderFunctor₃ (α : Sort u) (β : Sort u') (γ : Sort u'') (δ : Sort u''')
                             [hα : HasPreorderRelation V α] [hβ : HasPreorderRelation V β]
                             [hγ : HasPreorderRelation V γ] [hδ : HasPreorderRelation V δ] where
    φ : α → β → γ → δ
    [hφ : IsPreorderFunctor₃ φ]

  namespace PreorderFunctor₃

    section

      variable {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''}
               [hα : HasPreorderRelation V α] [hβ : HasPreorderRelation V β]
               [hγ : HasPreorderRelation V γ] [hδ : HasPreorderRelation V δ]
               (F : PreorderFunctor₃ α β γ δ)

      instance : IsPreorderFunctor₃ F.φ := F.hφ

      instance (a : α) : IsPreorderFunctor₂ (F.φ a) := { toAbstractMultiFun₂ := F.hφ.app a }
      instance (b : β) (c : γ) : IsPreorderFunctor (λ a => F.φ a b c) := F.hφ.app₂₃ b c

      def app   (a : α)         : PreorderFunctor₂ β γ δ := ⟨F.φ a⟩
      def app₂₃ (b : β) (c : γ) : PreorderFunctor α δ    := ⟨λ a => F.φ a b c⟩

    end

    instance coeFun (α : Sort u) (β : Sort u') (γ : Sort u'') (δ : Sort u''')
                    [hα : HasPreorderRelation V α] [hβ : HasPreorderRelation V β]
                    [hγ : HasPreorderRelation V γ] [hδ : HasPreorderRelation V δ] :
        CoeFun (PreorderFunctor₃ α β γ δ) (λ _ => α → β → γ → δ) :=
      ⟨PreorderFunctor₃.φ⟩

  end PreorderFunctor₃

  structure PreorderFunctor₄ (α : Sort u) (β : Sort u') (γ : Sort u'') (δ : Sort u''') (ε : Sort u'''')
                             [hα : HasPreorderRelation V α] [hβ : HasPreorderRelation V β]
                             [hγ : HasPreorderRelation V γ] [hδ : HasPreorderRelation V δ]
                             [hε : HasPreorderRelation V ε] where
    φ : α → β → γ → δ → ε
    [hφ : IsPreorderFunctor₄ φ]

  namespace PreorderFunctor₄

    section

      variable {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''} {ε : Sort u''''}
               [hα : HasPreorderRelation V α] [hβ : HasPreorderRelation V β]
               [hγ : HasPreorderRelation V γ] [hδ : HasPreorderRelation V δ]
               [hε : HasPreorderRelation V ε] (F : PreorderFunctor₄ α β γ δ ε)

      instance : IsPreorderFunctor₄ F.φ := F.hφ

      instance (a : α) : IsPreorderFunctor₃ (F.φ a) := { toAbstractMultiFun₃ := F.hφ.app a }
      instance (b : β) (c : γ) (d : δ) : IsPreorderFunctor (λ a => F.φ a b c d) := F.hφ.app₂₃₄ b c d

      def app    (a : α)                 : PreorderFunctor₃ β γ δ ε := ⟨F.φ a⟩
      def app₂₃₄ (b : β) (c : γ) (d : δ) : PreorderFunctor α ε      := ⟨λ a => F.φ a b c d⟩

    end

    instance coeFun (α : Sort u) (β : Sort u') (γ : Sort u'') (δ : Sort u''') (ε : Sort u'''')
                    [hα : HasPreorderRelation V α] [hβ : HasPreorderRelation V β]
                    [hγ : HasPreorderRelation V γ] [hδ : HasPreorderRelation V δ]
                    [hε : HasPreorderRelation V ε] :
        CoeFun (PreorderFunctor₄ α β γ δ ε) (λ _ => α → β → γ → δ → ε) :=
      ⟨PreorderFunctor₄.φ⟩

  end PreorderFunctor₄

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

  @[reducible] def EquivalenceFunctor (α : Sort u) (β : Sort u')
                                      [hα : HasEquivalenceRelationBase V α]
                                      [hβ : HasEquivalenceRelationBase V β] :=
    PreorderFunctor (asPreorder α) (asPreorder β)

  namespace EquivalenceFunctor

    @[reducible] def mk {α : Sort u} {β : Sort u'} [hα : HasEquivalenceRelationBase V α]
                        [hβ : HasEquivalenceRelationBase V β] (φ : α → β)
                        [hφ : IsPreorderFunctor (α := asPreorder α) (β := asPreorder β) φ] :
        EquivalenceFunctor α β :=
      PreorderFunctor.mk φ

    -- We need this to be a separate definition in order to remove `asPreorder` from the return
    -- type.
    def φ {α : Sort u} {β : Sort u'} [hα : HasEquivalenceRelationBase V α]
          [hβ : HasEquivalenceRelationBase V β] (F : EquivalenceFunctor α β) :
        α → β :=
      PreorderFunctor.φ (α := asPreorder α) (β := asPreorder β) F

    instance coeFun (α : Sort u) (β : Sort u') [hα : HasEquivalenceRelationBase V α]
                    [hβ : HasEquivalenceRelationBase V β] :
        CoeFun (EquivalenceFunctor α β) (λ _ => α → β) :=
      ⟨EquivalenceFunctor.φ⟩

    @[reducible] def idFun (α : Sort u) [hα : HasEquivalenceRelationBase V α] :
        EquivalenceFunctor α α :=
      PreorderFunctor.idFun (asPreorder α)

    @[reducible] def constFun [HasSubLinearLogic V] (α : Sort u) {β : Sort u'}
                              [hα : HasEquivalenceRelationBase V α]
                              [hβ : HasEquivalenceRelationBase V β] (b : β) :
        EquivalenceFunctor α β :=
      PreorderFunctor.constFun (asPreorder α) b

    @[reducible] def compFun {α : Sort u} {β : Sort u'} {γ : Sort u''}
                             [hα : HasEquivalenceRelationBase V α]
                             [hβ : HasEquivalenceRelationBase V β]
                             [hγ : HasEquivalenceRelationBase V γ] (F : EquivalenceFunctor α β)
                             (G : EquivalenceFunctor β γ) :
        EquivalenceFunctor α γ :=
      PreorderFunctor.compFun F G

    def symmFun (α : Sort u) [hα : HasEquivalenceRelationBase V α] :
        EquivalenceFunctor α (opposite α) where
      φ  := id
      hφ := { toHasImplication := HasImplication.symmImpl hα.Iso }

  end EquivalenceFunctor

  @[reducible] def EquivalenceFunctor₂ (α : Sort u) (β : Sort u') (γ : Sort u'')
                                       [hα : HasEquivalenceRelationBase V α]
                                       [hβ : HasEquivalenceRelationBase V β]
                                       [hγ : HasEquivalenceRelationBase V γ] :=
    PreorderFunctor₂ (asPreorder α) (asPreorder β) (asPreorder γ)

  namespace EquivalenceFunctor₂

    @[reducible] def mk {α : Sort u} {β : Sort u'} {γ : Sort u''}
                        [hα : HasEquivalenceRelationBase V α] [hβ : HasEquivalenceRelationBase V β]
                        [hγ : HasEquivalenceRelationBase V γ] (φ : α → β → γ)
                        [hφ : IsPreorderFunctor₂ (α := asPreorder α) (β := asPreorder β)
                                                 (γ := asPreorder γ) φ] :
        EquivalenceFunctor₂ α β γ :=
      PreorderFunctor₂.mk φ

    def φ {α : Sort u} {β : Sort u'} {γ : Sort u''} [hα : HasEquivalenceRelationBase V α]
          [hβ : HasEquivalenceRelationBase V β] [hγ : HasEquivalenceRelationBase V γ]
          (F : EquivalenceFunctor₂ α β γ) :
        α → β → γ :=
      PreorderFunctor₂.φ (α := asPreorder α) (β := asPreorder β) (γ := asPreorder γ) F

    instance coeFun (α : Sort u) (β : Sort u') (γ : Sort u'') [hα : HasEquivalenceRelationBase V α]
                    [hβ : HasEquivalenceRelationBase V β] [hγ : HasEquivalenceRelationBase V γ] :
        CoeFun (EquivalenceFunctor₂ α β γ) (λ _ => α → β → γ) :=
      ⟨EquivalenceFunctor₂.φ⟩

    @[reducible] def swapFun₂ {α : Sort u} {β : Sort u'} {γ : Sort u''}
                 [hα : HasEquivalenceRelationBase V α] [hβ : HasEquivalenceRelationBase V β]
                 [hγ : HasEquivalenceRelationBase V γ] (F : EquivalenceFunctor₂ α β γ) :
        EquivalenceFunctor₂ β α γ :=
      PreorderFunctor₂.swapFun₂ F

    @[reducible] def dupFun [HasNonLinearLogic V] {α : Sort u} {β : Sort u'}
                            [hα : HasEquivalenceRelationBase V α]
                            [hβ : HasEquivalenceRelationBase V β] (F : EquivalenceFunctor₂ α α β) :
        EquivalenceFunctor α β :=
      PreorderFunctor₂.dupFun F

    @[reducible] def substFun [HasNonLinearLogic V] {α : Sort u} {β : Sort u'} {γ : Sort u''}
                              [hα : HasEquivalenceRelationBase V α]
                              [hβ : HasEquivalenceRelationBase V β]
                              [hγ : HasEquivalenceRelationBase V γ] (F : EquivalenceFunctor α β)
                              (G : EquivalenceFunctor₂ α β γ) :
        EquivalenceFunctor α γ :=
      PreorderFunctor₂.substFun F G

  end EquivalenceFunctor₂

  @[reducible] def EquivalenceFunctor₃ (α : Sort u) (β : Sort u') (γ : Sort u'') (δ : Sort u''')
                                       [hα : HasEquivalenceRelationBase V α]
                                       [hβ : HasEquivalenceRelationBase V β]
                                       [hγ : HasEquivalenceRelationBase V γ]
                                       [hδ : HasEquivalenceRelationBase V δ] :=
    PreorderFunctor₃ (asPreorder α) (asPreorder β) (asPreorder γ) (asPreorder δ)

  namespace EquivalenceFunctor₃

    @[reducible] def mk {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''}
                        [hα : HasEquivalenceRelationBase V α] [hβ : HasEquivalenceRelationBase V β]
                        [hγ : HasEquivalenceRelationBase V γ] [hδ : HasEquivalenceRelationBase V δ]
                        (φ : α → β → γ → δ)
                        [hφ : IsPreorderFunctor₃ (α := asPreorder α) (β := asPreorder β)
                                                 (γ := asPreorder γ) (δ := asPreorder δ) φ] :
        EquivalenceFunctor₃ α β γ δ :=
      PreorderFunctor₃.mk φ

    def φ {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''}
          [hα : HasEquivalenceRelationBase V α] [hβ : HasEquivalenceRelationBase V β]
          [hγ : HasEquivalenceRelationBase V γ] [hδ : HasEquivalenceRelationBase V δ]
          (F : EquivalenceFunctor₃ α β γ δ) :
        α → β → γ → δ :=
      PreorderFunctor₃.φ (α := asPreorder α) (β := asPreorder β) (γ := asPreorder γ)
                         (δ := asPreorder δ) F

    instance coeFun (α : Sort u) (β : Sort u') (γ : Sort u'') (δ : Sort u''')
                    [hα : HasEquivalenceRelationBase V α] [hβ : HasEquivalenceRelationBase V β]
                    [hγ : HasEquivalenceRelationBase V γ] [hδ : HasEquivalenceRelationBase V δ] :
        CoeFun (EquivalenceFunctor₃ α β γ δ) (λ _ => α → β → γ → δ) :=
      ⟨EquivalenceFunctor₃.φ⟩

  end EquivalenceFunctor₃

  @[reducible] def EquivalenceFunctor₄ (α : Sort u) (β : Sort u') (γ : Sort u'') (δ : Sort u''')
                                       (ε : Sort u'''') [hα : HasEquivalenceRelationBase V α]
                                       [hβ : HasEquivalenceRelationBase V β]
                                       [hγ : HasEquivalenceRelationBase V γ]
                                       [hδ : HasEquivalenceRelationBase V δ]
                                       [hε : HasEquivalenceRelationBase V ε] :=
    PreorderFunctor₄ (asPreorder α) (asPreorder β) (asPreorder γ) (asPreorder δ) (asPreorder ε)

  namespace EquivalenceFunctor₄

    @[reducible] def mk {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''} {ε : Sort u''''}
                        [hα : HasEquivalenceRelationBase V α] [hβ : HasEquivalenceRelationBase V β]
                        [hγ : HasEquivalenceRelationBase V γ] [hδ : HasEquivalenceRelationBase V δ]
                        [hε : HasEquivalenceRelationBase V ε] (φ : α → β → γ → δ → ε)
                        [hφ : IsPreorderFunctor₄ (α := asPreorder α) (β := asPreorder β)
                                                 (γ := asPreorder γ) (δ := asPreorder δ)
                                                 (ε := asPreorder ε) φ] :
        EquivalenceFunctor₄ α β γ δ ε :=
      PreorderFunctor₄.mk φ

    def φ {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''} {ε : Sort u''''}
          [hα : HasEquivalenceRelationBase V α] [hβ : HasEquivalenceRelationBase V β]
          [hγ : HasEquivalenceRelationBase V γ] [hδ : HasEquivalenceRelationBase V δ]
          [hε : HasEquivalenceRelationBase V ε] (F : EquivalenceFunctor₄ α β γ δ ε) :
        α → β → γ → δ → ε :=
      PreorderFunctor₄.φ (α := asPreorder α) (β := asPreorder β) (γ := asPreorder γ)
                         (δ := asPreorder δ) (ε := asPreorder ε) F

    instance coeFun (α : Sort u) (β : Sort u') (γ : Sort u'') (δ : Sort u''') (ε : Sort u'''')
                    [hα : HasEquivalenceRelationBase V α] [hβ : HasEquivalenceRelationBase V β]
                    [hγ : HasEquivalenceRelationBase V γ] [hδ : HasEquivalenceRelationBase V δ]
                    [hε : HasEquivalenceRelationBase V ε] :
        CoeFun (EquivalenceFunctor₄ α β γ δ ε) (λ _ => α → β → γ → δ → ε) :=
      ⟨EquivalenceFunctor₄.φ⟩

  end EquivalenceFunctor₄

end HasEquivalenceRelationBase



namespace HasLinearLogic

  section

    variable (U : Universe) [HasLinearLogic U]

    def funRel : Prerelation U U := λ A B => A ⥤ B

    instance funRel.isPreorder : IsPreorder (funRel U) where
      refl         A     := idFun       A
      revTransFun₂ A B C := revCompFun₃ A B C

    instance hasPreorderRelation : HasPreorderRelation U U := ⟨funRel U⟩

  end

  section

    variable {U : Universe} [HasLinearLogic U]

    @[reducible] def asHom {A B : U} (F : A ⥤ B) : A ⟶ B := F

    instance (A B : U) : CoeFun (A ⟶ B) (λ _ => A → B) := HasFunctors.coeFun A B

    -- The hom-bifunctor is covariant in one argument and contravariant in the other.
    def homFun₂ (α : Sort u) [hα : HasPreorderRelation U α] :
        PreorderFunctor₂ (opposite α) α U where
      φ  := hα.Hom
      hφ := IsPreorderFunctor₂.construct (HasTrans.revTransFun₂ (R := hα.Hom))
                                         (λ a₁ a₂ => HasTrans.transFun₂ (R := hα.Hom) a₂ a₁)

  end

end HasLinearLogic
