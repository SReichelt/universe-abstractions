import UniverseAbstractions.Universes.Layer1.Axioms.Universes



namespace UniverseAbstractions.Layer1

set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 2500

universe u u' u'' u'''



-- Π types have a bit of a chicken-and-egg problem. The "true" definition requires
-- * a functor `P : A ⥤ V`, where `V` is the universe of propositions with respect to `A` (defined
--   in layer 2), and `⥤` is just an instance of a Π type with a constant property, and
-- * quantification over all such `A`, as a Π instance (defined in layer 3).
--
-- So at this point, we only define a base class that references a specific property `P`, so that
-- we can later instantiate it for all `P` that are functors. This way, we can already define
-- combinators and the `Λ` notation in a generic way, instead of having a separate copy per layer.
--
-- On the other hand, functors do make sense in layer 1, but we wish to define them as specialized
-- Π types. So the class `HasPiType` can be regarded as a slight generalization of `HasFunctors`
-- that is only defined here in preparation of layers 2 and 3.
--
-- Since we cannot compare different instances of a type in layer 1, Π types are essentially just
-- universally quantified propositions, and functors are essentially just implication.

namespace HasPiType

  variable {V : Universe}

  @[reducible] def Pi {α : Sort u} (P : α → V) [HasType V (∀ a, P a)] : V := [∀ a, P a | V]

  def apply {α : Sort u} {P : α → V} [HasType V (∀ a, P a)] (F : Pi P) : ∀ a, P a := F

  instance coeFun {α : Sort u} (P : α → V) [HasType V (∀ a, P a)] :
      CoeFun (Pi P) (λ _ => ∀ a, P a) :=
    ⟨apply⟩

  def hasElim₂ {α : Sort u} (P : α → V) [HasType V (∀ a, P a)] {β : α → Sort u'}
               [∀ a, HasElim (P a) (β a)] :
      HasElim (Pi P) (∀ a, β a) :=
    ⟨λ F a => F a⟩

  def hasElim₂.app {α : Sort u} {P : α → V} [HasType V (∀ a, P a)] {β : α → Sort u'}
                   [∀ a, HasElim (P a) (β a)] {f : ∀ a, β a}
                   (F : HasElim.DefInst (Pi P) f (h := hasElim₂ P)) (a : α) :
      [P a]_{f a} :=
    F a

  instance {α : Sort u} (β : α → Sort u') [∀ a, HasType V (β a)] [HasType V (∀ a, [β a | V])] :
      HasType V (∀ a, β a) where
    T     := [∀ a, [β a | V] | V]
    hElim := hasElim₂ (λ a => [β a | V])

  @[reducible] def Pi₂ {α : Sort u} {β : α → Sort u'} (P : ∀ a, β a → V)
                       [∀ a, HasType V (∀ b, P a b)] [HasType V (∀ a, Pi (P a))] : V :=
    [∀ a b, P a b | V]

  def defAppPi {α : Sort u} {P : α → V} [HasType V (∀ a, P a)] (F : Pi P) : [Pi P]_{λ a => F a} :=
    F

  def defAppPi₂ {α : Sort u} {β : α → Sort u'} {P : ∀ a, β a → V} [∀ a, HasType V (∀ b, P a b)]
                [HasType V (∀ a, Pi (P a))] (F : Pi₂ P) :
      [Pi₂ P]_{λ a b => F a b} :=
    F

  -- Helper classes for the `functoriality` tactic.
  section Helpers

    class IsPiApp {Y : V} (y : Y) where
      {α : Sort u}
      {P : α → V}
      [hP : HasType V (∀ a, P a)]
      F : Pi P
      a : α
      codomainEq : P a = Y  -- must be `rfl` for meta code to work correctly

    namespace IsPiApp

      instance (priority := low) refl {α : Sort u} {P : α → V} [HasType V (∀ a, P a)] {F : Pi P}
                                      {a : α} :
          IsPiApp (F a) :=
        ⟨F, a, rfl⟩

      variable {Y : V} {y : Y} [hApp : IsPiApp.{u} y]

      instance : HasType V (∀ a, hApp.P a) := hApp.hP

    end IsPiApp

    class IsPiApp₂ {Y : V} (y : Y) where
      {α : Sort u}
      {β : α → Sort u'}
      {P : ∀ a, β a → V}
      [hPa (a : α) : HasType V (∀ b, P a b)]
      [hPiPa : HasType V (∀ a, Pi (P a))]
      F : Pi₂ P
      a : α
      b : β a
      codomainEq : P a b = Y

    namespace IsPiApp₂

      instance (priority := low) refl {α : Sort u} {β : α → Sort u'} (P : ∀ a, β a → V)
                                      [∀ a, HasType V (∀ b, P a b)] [HasType V (∀ a, Pi (P a))]
                                      {F : Pi₂ P} {a : α} {b : β a} :
          IsPiApp₂ (F a b) :=
        ⟨F, a, b, rfl⟩

      variable {Y : V} (y : Y) [hApp : IsPiApp₂.{u, u'} y]

      instance (a : hApp.α) : HasType V (∀ b, hApp.P a b) := hApp.hPa a
      instance : HasType V (∀ a, Pi (hApp.P a)) := hApp.hPiPa

    end IsPiApp₂

  end Helpers

end HasPiType

open HasPiType



class HasFunctors (α : Sort u) (V : Universe) where
  [hFun (Y : V) : HasType V (α → Y)]

namespace HasFunctors

  variable {V : Universe}

  instance (α : Sort u) [h : HasFunctors α V] (Y : V) : HasType V (α → Y) := h.hFun Y

  instance (α : Sort u) [h : HasFunctors α V] (Y : V) : HasType V (∀ a, (λ _ : α => Y) a) :=
    h.hFun Y

  @[reducible] def Fun (α : Sort u) [h : HasFunctors α V] (Y : V) : V := [α → Y | V]
  infixr:20 " ⥤ " => HasFunctors.Fun

  def hasElim₂ (α : Sort u) [HasFunctors α V] (Y : V) {β : Sort u'} [h : HasElim Y β] :
      HasElim (α ⥤ Y) (α → β) :=
    HasPiType.hasElim₂ (λ _ : α => Y)
  notation "[" A:0 "]__{" a:0 "}" => HasElim.DefInst A (h := HasFunctors.hasElim₂ _ _) a

  def hasElim₃ (α : Sort u) (β : Sort u') [HasFunctors α V] [HasFunctors β V] (Y : V) {γ : Sort u''}
               [h : HasElim Y γ] :
      HasElim (α ⥤ β ⥤ Y) (α → β → γ) :=
    hasElim₂ α (β ⥤ Y) (h := hasElim₂ β Y)
  notation "[" A:0 "]___{" a:0 "}" => HasElim.DefInst A (h := HasFunctors.hasElim₃ _ _ _) a

  def hasElim₄ (α : Sort u) (β : Sort u') (γ : Sort u'') [HasFunctors α V] [HasFunctors β V]
               [HasFunctors γ V] (Y : V) {δ : Sort u'''} [h : HasElim Y δ] :
      HasElim (α ⥤ β ⥤ γ ⥤ Y) (α → β → γ → δ) :=
    hasElim₂ α (β ⥤ γ ⥤ Y) (h := hasElim₃ β γ Y)
  notation "[" A:0 "]____{" a:0 "}" => HasElim.DefInst A (h := HasFunctors.hasElim₄ _ _ _ _) a

  instance (α : Sort u) [HasFunctors α V] (β : Sort u') [HasType V β] : HasType V (α → β) :=
    inferInstance

  def defAppFun {α : Sort u} [h : HasFunctors α V] {Y : V} (F : α ⥤ Y) : [α ⥤ Y]_{λ a => F a} := F

  def defAppFun₂ {α : Sort u} {β : Sort u'} [h : HasFunctors α V] [HasFunctors β V] {Y : V} (F : α ⥤ β ⥤ Y) :
      [α ⥤ β ⥤ Y]__{λ a b => F a b} :=
    F

  def defAppFun₃ {α : Sort u} {β : Sort u'} {γ : Sort u''} [h : HasFunctors α V] [HasFunctors β V]
                 [HasFunctors γ V] {Y : V} (F : α ⥤ β ⥤ γ ⥤ Y) :
      [α ⥤ β ⥤ γ ⥤ Y]___{λ a b c => F a b c} :=
    F

  def defAppFun₄ {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''} [h : HasFunctors α V]
                 [HasFunctors β V] [HasFunctors γ V] [HasFunctors δ V] {Y : V}
                 (F : α ⥤ β ⥤ γ ⥤ δ ⥤ Y) :
      [α ⥤ β ⥤ γ ⥤ δ ⥤ Y]____{λ a b c d => F a b c d} :=
    F

  -- Helper classes for the `functoriality` tactic.
  section Helpers

    variable {Y : V}

    class IsFunApp (y : Y) where
      {α : Sort u}
      [hα : HasFunctors α V]
      F : α ⥤ Y
      a : α

    namespace IsFunApp

      instance (priority := low) refl {α : Sort u} [HasFunctors α V] {F : α ⥤ Y} {a : α} :
          IsFunApp (F a) :=
        ⟨F, a⟩

      variable (y : Y) [hApp : IsFunApp.{u} y]

      instance : HasFunctors hApp.α V := hApp.hα

      def isPiApp : IsPiApp y := ⟨hApp.F, hApp.a, rfl⟩

    end IsFunApp

    class IsFunApp₂ (y : Y) where
      {α : Sort u}
      {β : Sort u'}
      [hα : HasFunctors α V]
      [hβ : HasFunctors β V]
      F : α ⥤ β ⥤ Y
      a : α
      b : β

    namespace IsFunApp₂

      instance (priority := low) refl {α : Sort u} {β : Sort u'} [HasFunctors α V] [HasFunctors β V]
                                      {F : α ⥤ β ⥤ Y} {a : α} {b : β} :
          IsFunApp₂ (F a b) :=
        ⟨F, a, b⟩

      variable (y : Y) [hApp : IsFunApp₂.{u, u'} y]

      instance : HasFunctors hApp.α V := hApp.hα
      instance : HasFunctors hApp.β V := hApp.hβ

      def isFunApp : IsFunApp y := ⟨hApp.F hApp.a, hApp.b⟩

      def F' : [hApp.α → hApp.β → Y | V] := hApp.F
      def isPiApp₂ : IsPiApp₂ y := ⟨hApp.F', hApp.a, hApp.b, rfl⟩

    end IsFunApp₂

    class IsFunApp₃ (y : Y) where
      {α : Sort u}
      {β : Sort u'}
      {γ : Sort u''}
      [hα : HasFunctors α V]
      [hβ : HasFunctors β V]
      [hγ : HasFunctors γ V]
      F : α ⥤ β ⥤ γ ⥤ Y
      a : α
      b : β
      c : γ

    namespace IsFunApp₃

      instance (priority := low) refl {α : Sort u} {β : Sort u'} {γ : Sort u''} [HasFunctors α V]
                                      [HasFunctors β V] [HasFunctors γ V] {F : α ⥤ β ⥤ γ ⥤ Y}
                                      {a : α} {b : β} {c : γ} :
          IsFunApp₃ (F a b c) :=
        ⟨F, a, b, c⟩

      variable (y : Y) [hApp : IsFunApp₃.{u, u', u''} y]

      instance : HasFunctors hApp.α V := hApp.hα
      instance : HasFunctors hApp.β V := hApp.hβ
      instance : HasFunctors hApp.γ V := hApp.hγ

      def isFunApp₂ : IsFunApp₂ y := ⟨hApp.F hApp.a, hApp.b, hApp.c⟩

      def isFunApp : IsFunApp y :=
        let _ : IsFunApp₂ y := isFunApp₂ y
        IsFunApp₂.isFunApp y

    end IsFunApp₃

    class IsFunApp₄ (y : Y) where
      {α : Sort u}
      {β : Sort u'}
      {γ : Sort u''}
      {δ : Sort u'''}
      [hα : HasFunctors α V]
      [hβ : HasFunctors β V]
      [hγ : HasFunctors γ V]
      [hδ : HasFunctors δ V]
      F : α ⥤ β ⥤ γ ⥤ δ ⥤ Y
      a : α
      b : β
      c : γ
      d : δ

    namespace IsFunApp₄

      instance (priority := low) refl {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''}
                                      [HasFunctors α V] [HasFunctors β V] [HasFunctors γ V]
                                      [HasFunctors δ V] {F : α ⥤ β ⥤ γ ⥤ δ ⥤ Y} {a : α} {b : β}
                                      {c : γ} {d : δ} :
          IsFunApp₄ (F a b c d) :=
        ⟨F, a, b, c, d⟩

      variable (y : Y) [hApp : IsFunApp₄.{u, u', u'', u'''} y]

      instance : HasFunctors hApp.α V := hApp.hα
      instance : HasFunctors hApp.β V := hApp.hβ
      instance : HasFunctors hApp.γ V := hApp.hγ
      instance : HasFunctors hApp.δ V := hApp.hδ

      def isFunApp₃ : IsFunApp₃ y := ⟨hApp.F hApp.a, hApp.b, hApp.c, hApp.d⟩

      def isFunApp₂ : IsFunApp₂ y :=
        let _ : IsFunApp₃ y := isFunApp₃ y
        IsFunApp₃.isFunApp₂ y

      def isFunApp : IsFunApp y :=
        let _ : IsFunApp₂ y := isFunApp₂ y
        IsFunApp₂.isFunApp y

    end IsFunApp₄

    class IsFunApp₂' (y : Y) extends IsFunApp.{u} y where
      h₂ : IsFunApp.{u'} y

    class IsFunApp₃' (y : Y) extends IsFunApp₂'.{u, u'} y where
      h₃ : IsFunApp.{u''} y

    class IsFunApp₄' (y : Y) extends IsFunApp₃'.{u, u', u''} y where
      h₄ : IsFunApp.{u'''} y

  end Helpers

end HasFunctors

open HasFunctors



class HasUnivFunctors (U V : Universe) where
  [hFun (A : U) : HasFunctors A V]

namespace HasUnivFunctors

  instance {U : Universe} (A : U) (V : Universe) [h : HasUnivFunctors U V] :
      HasFunctors A V :=
    h.hFun A

end HasUnivFunctors



class HasIdFun {U : Universe} [HasUnivFunctors U U] (A : U) where
  defIdFun : [A ⥤ A]_{id}

namespace HasIdFun

  section

    variable {U : Universe} [HasUnivFunctors U U] (A : U) [h : HasIdFun A]

    @[reducible] def idFun : A ⥤ A := h.defIdFun

  end

  section

    variable (α : Sort u) {U : Universe} [HasUnivFunctors U U] [HasFunctors α U] (B : U)
             [h : HasIdFun (α ⥤ B)]

    def defAppFun₂ : [(α ⥤ B) ⥤ α ⥤ B]__{λ F a => F a} := h.defIdFun

    @[reducible] def appFun₂ : (α ⥤ B) ⥤ α ⥤ B := defAppFun₂ α B

  end

end HasIdFun


class HasPiAppFun {α : Sort u} {V : Universe} [HasUnivFunctors V V] (P : α → V)
                  [HasType V (∀ a, P a)] where
  defPiAppFun (a : α) : [Pi P ⥤ P a]_{λ F : Pi P => F a}

namespace HasPiAppFun

  variable {α : Sort u} {V : Universe} [HasUnivFunctors V V] (P : α → V) [HasType V (∀ a, P a)]
           [h : HasPiAppFun P]

  @[reducible] def piAppFun (a : α) : Pi P ⥤ P a := h.defPiAppFun a

end HasPiAppFun

class HasPiAppFunPi {α : Sort u} {V : Universe} [HasUnivFunctors V V] (P : α → V)
                    [HasType V (∀ a, P a)] [HasType V (∀ a, Pi P ⥤ P a)] extends
    HasPiAppFun P where
  defPiAppFunPi : [∀ a, Pi P ⥤ P a | V]_{defPiAppFun}

namespace HasPiAppFunPi

  variable {α : Sort u} {V : Universe} [HasUnivFunctors V V] (P : α → V) [HasType V (∀ a, P a)]
           [HasType V (∀ a, Pi P ⥤ P a)] [h : HasPiAppFunPi P]

  @[reducible] def piAppFunPi : [∀ a, Pi P ⥤ P a | V] := h.defPiAppFunPi

  instance piAppFun.isPiApp {a : α} : IsPiApp (HasPiAppFun.piAppFun P a) := ⟨piAppFunPi P, a, rfl⟩

end HasPiAppFunPi


class HasSwapPi {α : Sort u} {β : Sort u'} {V : Universe} (P : α → β → V)
                [∀ a, HasType V (∀ b, P a b)] [HasType V (∀ a, Pi (P a))]
                [∀ b, HasType V (∀ a, P a b)] where
  defSwapPi (F : Pi₂ P) (b : β) : [∀ a, P a b | V]_{λ a => F a b}

namespace HasSwapPi

  variable {α : Sort u} {β : Sort u'} {V : Universe} {P : α → β → V} [∀ a, HasType V (∀ b, P a b)]
           [HasType V (∀ a, Pi (P a))] [∀ b, HasType V (∀ a, P a b)] [h : HasSwapPi P]

  @[reducible] def swapPi (F : Pi₂ P) (b : β) : [∀ a, P a b | V] := h.defSwapPi F b

end HasSwapPi

class HasSwapPi₂ {α : Sort u} {β : Sort u'} {V : Universe} (P : α → β → V)
                 [∀ a, HasType V (∀ b, P a b)] [HasType V (∀ a, Pi (P a))]
                 [∀ b, HasType V (∀ a, P a b)] [HasType V (∀ b, [∀ a, P a b | V])] extends
    HasSwapPi P where
  defSwapPi₂ (F : Pi₂ P) : [∀ b, [∀ a, P a b | V] | V]_{defSwapPi F}

namespace HasSwapPi₂

  variable {α : Sort u} {β : Sort u'} {V : Universe} {P : α → β → V} [∀ a, HasType V (∀ b, P a b)]
           [HasType V (∀ a, Pi (P a))] [∀ b, HasType V (∀ a, P a b)]
           [HasType V (∀ b, [∀ a, P a b | V])] [h : HasSwapPi₂ P]

  @[reducible] def swapPi₂ (F : Pi₂ P) : [∀ b a, P a b | V] := h.defSwapPi₂ F

  instance swapPi.isPiApp {F : Pi₂ P} {b : β} : IsPiApp (HasSwapPi.swapPi F b) :=
    ⟨swapPi₂ F, b, rfl⟩

end HasSwapPi₂

class HasSwapPiFun {α : Sort u} {β : Sort u'} {V : Universe} [HasUnivFunctors V V] (P : α → β → V)
                   [∀ a, HasType V (∀ b, P a b)] [HasType V (∀ a, Pi (P a))]
                   [∀ b, HasType V (∀ a, P a b)] [HasType V (∀ b, [∀ a, P a b | V])] extends
    HasSwapPi₂ P where
  defSwapPiFun : [Pi₂ P ⥤ [∀ b a, P a b | V]]_{defSwapPi₂}

namespace HasSwapPiFun

  variable {α : Sort u} {β : Sort u'} {V : Universe} [HasUnivFunctors V V] (P : α → β → V)
           [∀ a, HasType V (∀ b, P a b)] [HasType V (∀ a, Pi (P a))] [∀ b, HasType V (∀ a, P a b)]
           [HasType V (∀ b, [∀ a, P a b | V])] [h : HasSwapPiFun P]

  @[reducible] def swapPiFun : Pi₂ P ⥤ [∀ b a, P a b | V] := h.defSwapPiFun

  instance swapPi₂.isFunApp {F : Pi₂ P} : IsFunApp (HasSwapPi₂.swapPi₂ F) := ⟨swapPiFun P, F⟩

end HasSwapPiFun


class HasCompFunPi (α : Sort u) {V W : Universe} [HasFunctors α V] {B : V} (Q : B → W)
                   [HasType W (∀ b, Q b)] [∀ F : α ⥤ B, HasType W (∀ a, Q (F a))] where
  defCompFunPi (F : α ⥤ B) (G : Pi Q) : [∀ a, Q (F a) | W]_{λ a => G (F a)}

namespace HasCompFunPi

  variable {α : Sort u} {V W : Universe} [HasFunctors α V] {B : V} {Q : B → W}
           [HasType W (∀ b, Q b)] [∀ F : α ⥤ B, HasType W (∀ a, Q (F a))] [h : HasCompFunPi α Q]

  @[reducible] def compFunPi (F : α ⥤ B) (G : Pi Q) : [∀ a, Q (F a) | W] := h.defCompFunPi F G

  abbrev revCompFunPi (G : Pi Q) (F : α ⥤ B) : [∀ a, Q (F a) | W] := compFunPi F G

end HasCompFunPi

class HasRevCompFunPi₂ (α : Sort u) {V W : Universe} [HasFunctors α V] {B : V} (Q : B → W)
                       [HasType W (∀ b, Q b)] [∀ F : α ⥤ B, HasType W (∀ a, Q (F a))]
                       [HasType W (∀ F : α ⥤ B, [∀ a, Q (F a) | W])] extends
    HasCompFunPi α Q where
  defRevCompFunPi₂ (G : Pi Q) : [∀ F : α ⥤ B, [∀ a, Q (F a) | W] | W]_{λ F => defCompFunPi F G}

namespace HasRevCompFunPi₂

  variable (α : Sort u) {V W : Universe} [HasFunctors α V] {B : V} {Q : B → W}
           [HasType W (∀ b, Q b)] [∀ F : α ⥤ B, HasType W (∀ a, Q (F a))]
           [HasType W (∀ F : α ⥤ B, [∀ a, Q (F a) | W])] [h : HasRevCompFunPi₂ α Q]

  @[reducible] def revCompFunPi₂ (G : Pi Q) : [∀ (F : α ⥤ B) a, Q (F a) | W] := h.defRevCompFunPi₂ G

  instance revCompFunPi.isPiApp {G : Pi Q} {F : α ⥤ B} : IsPiApp (HasCompFunPi.revCompFunPi G F) :=
    ⟨revCompFunPi₂ α G, F, rfl⟩

end HasRevCompFunPi₂

class HasRevCompFunPiFun (α : Sort u) {V W : Universe} [HasUnivFunctors W W] [HasFunctors α V]
                         {B : V} (Q : B → W) [HasType W (∀ b, Q b)]
                         [∀ F : α ⥤ B, HasType W (∀ a, Q (F a))]
                         [HasType W (∀ F : α ⥤ B, [∀ a, Q (F a) | W])] extends
    HasRevCompFunPi₂ α Q where
  defRevCompFunPiFun : [Pi Q ⥤ [∀ (F : α ⥤ B) a, Q (F a) | W]]_{defRevCompFunPi₂}

namespace HasRevCompFunPiFun

  variable (α : Sort u) {V W : Universe} [HasUnivFunctors W W] [HasFunctors α V] {B : V}
           (Q : B → W) [HasType W (∀ b, Q b)] [∀ F : α ⥤ B, HasType W (∀ a, Q (F a))]
           [HasType W (∀ F : α ⥤ B, [∀ a, Q (F a) | W])] [h : HasRevCompFunPiFun α Q]

  @[reducible] def revCompFunPiFun : Pi Q ⥤ [∀ (F : α ⥤ B) a, Q (F a) | W] := h.defRevCompFunPiFun

  instance revCompFunPi₂.isFunApp {G : Pi Q} : IsFunApp (HasRevCompFunPi₂.revCompFunPi₂ α G) :=
    ⟨revCompFunPiFun α Q, G⟩

  instance revCompFunPi.isPiApp₂ {G : Pi Q} {F : α ⥤ B} :
      IsPiApp₂ (HasCompFunPi.revCompFunPi G F) :=
    ⟨revCompFunPiFun α Q, G, F, rfl⟩

end HasRevCompFunPiFun


class HasConstPi (α : Sort u) {V : Universe} (B : V) [HasType V (α → B)] where
  defConstPi (b : B) : [α → B | V]_{Function.const α b}

namespace HasConstPi

  variable (α : Sort u) {V : Universe} {B : V} [HasType V (α → B)] [h : HasConstPi α B]

  @[reducible] def constPi (b : B) : [α → B | V] := h.defConstPi b

end HasConstPi

class HasConstPiFun (α : Sort u) {V : Universe} [HasUnivFunctors V V] (B : V) [HasType V (α → B)]
                    extends
    HasConstPi α B where
  defConstPiFun : [B ⥤ [α → B | V]]_{defConstPi}

namespace HasConstPiFun

  variable (α : Sort u) {V : Universe} [HasUnivFunctors V V] (B : V) [HasType V (α → B)]
           [h : HasConstPiFun α B]

  @[reducible] def constPiFun : B ⥤ [α → B | V] := h.defConstPiFun

  instance constPi.isFunApp {b : B} : IsFunApp (HasConstPi.constPi α b) := ⟨constPiFun α B, b⟩

end HasConstPiFun


class HasDupPi {α : Sort u} {V : Universe} (P : α → α → V) [∀ a, HasType V (∀ a', P a a')]
               [HasType V (∀ a, Pi (P a))] [HasType V (∀ a, P a a)] where
  defDupPi (F : Pi₂ P) : [∀ a, P a a | V]_{λ a => F a a}

namespace HasDupPi

  variable {α : Sort u} {V : Universe} {P : α → α → V} [∀ a, HasType V (∀ a', P a a')]
           [HasType V (∀ a, Pi (P a))] [HasType V (∀ a, P a a)] [h : HasDupPi P]

  @[reducible] def dupPi (F : Pi₂ P) : [∀ a, P a a | V] := h.defDupPi F

end HasDupPi

class HasDupPiFun {α : Sort u} {V : Universe} [HasUnivFunctors V V] (P : α → α → V)
                  [∀ a, HasType V (∀ a', P a a')] [HasType V (∀ a, Pi (P a))]
                  [HasType V (∀ a, P a a)] extends
    HasDupPi P where
  defDupPiFun : [Pi₂ P ⥤ [∀ a, P a a | V]]_{defDupPi}

namespace HasDupPiFun

  variable {α : Sort u} {V : Universe} [HasUnivFunctors V V] (P : α → α → V)
           [∀ a, HasType V (∀ a', P a a')] [HasType V (∀ a, Pi (P a))] [HasType V (∀ a, P a a)]
           [h : HasDupPiFun P]

  @[reducible] def dupPiFun : Pi₂ P ⥤ [∀ a, P a a | V] := h.defDupPiFun

  instance dupPi.isFunApp {F : Pi₂ P} : IsFunApp (HasDupPi.dupPi F) := ⟨dupPiFun P, F⟩

end HasDupPiFun


class HasPiSelfAppPi {U V : Universe} [HasUnivFunctors V U] {A : U} (Q : A → V)
                     [HasType V (∀ a, Q a)] [∀ F : Pi Q ⥤ A, HasType V (∀ G, Q (F G))] where
  defPiSelfAppPi (F : Pi Q ⥤ A) : [∀ G, Q (F G) | V]_{λ G : Pi Q => G (F G)}

namespace HasPiSelfAppPi

  variable {U V : Universe} [HasUnivFunctors V U] {A : U} {Q : A → V} [HasType V (∀ a, Q a)]
           [∀ F : Pi Q ⥤ A, HasType V (∀ G, Q (F G))] [h : HasPiSelfAppPi Q]

  @[reducible] def piSelfAppPi (F : Pi Q ⥤ A) : [∀ G, Q (F G) | V] := h.defPiSelfAppPi F

end HasPiSelfAppPi

class HasPiSelfAppPi₂ {U V : Universe} [HasUnivFunctors V U] {A : U} (Q : A → V)
                      [HasType V (∀ a, Q a)] [∀ F : Pi Q ⥤ A, HasType V (∀ G, Q (F G))]
                      [HasType V (∀ F : Pi Q ⥤ A, [∀ G, Q (F G) | V])] extends
    HasPiSelfAppPi Q where
  defPiSelfAppPi₂ : [∀ F : Pi Q ⥤ A, [∀ G, Q (F G) | V] | V]_{defPiSelfAppPi}

namespace HasPiSelfAppPi₂

  variable {U V : Universe} [HasUnivFunctors V U] {A : U} (Q : A → V) [HasType V (∀ a, Q a)]
           [∀ F : Pi Q ⥤ A, HasType V (∀ G, Q (F G))]
           [HasType V (∀ F : Pi Q ⥤ A, [∀ G, Q (F G) | V])] [h : HasPiSelfAppPi₂ Q]

  @[reducible] def piSelfAppPi₂ : [∀ (F : Pi Q ⥤ A) G, Q (F G) | V] := h.defPiSelfAppPi₂

  instance revSelfAppFun.isPiApp {F : Pi Q ⥤ A} : IsPiApp (HasPiSelfAppPi.piSelfAppPi F) :=
    ⟨piSelfAppPi₂ Q, F, rfl⟩

end HasPiSelfAppPi₂


class HasSubstPi {α : Sort u} {V W : Universe} {P : α → V} [HasType V (∀ a, P a)] (Q : ∀ a, P a → W)
                 [∀ a, HasType W (∀ b, Q a b)] [HasType W (∀ a, Pi (Q a))]
                 [∀ F : Pi P, HasType W (∀ a, Q a (F a))] where
  defSubstPi (F : Pi P) (G : [∀ a, Pi (Q a) | W]) : [∀ a, Q a (F a) | W]_{λ a => G a (F a)}

namespace HasSubstPi

  variable {α : Sort u} {V W : Universe} {P : α → V} [HasType V (∀ a, P a)] {Q : ∀ a, P a → W}
           [∀ a, HasType W (∀ b, Q a b)] [HasType W (∀ a, Pi (Q a))]
           [∀ F : Pi P, HasType W (∀ a, Q a (F a))] [h : HasSubstPi Q]

  @[reducible] def substPi (F : Pi P) (G : [∀ a, Pi (Q a) | W]) : [∀ a, Q a (F a) | W] := h.defSubstPi F G

  abbrev revSubstPi (G : [∀ a, Pi (Q a) | W]) (F : Pi P) : [∀ a, Q a (F a) | W] := substPi F G

end HasSubstPi

class HasRevSubstPi₂ {α : Sort u} {V W : Universe} {P : α → V} [HasType V (∀ a, P a)]
                     (Q : ∀ a, P a → W) [∀ a, HasType W (∀ b, Q a b)] [HasType W (∀ a, Pi (Q a))]
                     [∀ F : Pi P, HasType W (∀ a, Q a (F a))]
                     [HasType W (∀ F : Pi P, [∀ a, Q a (F a) | W])] extends
    HasSubstPi Q where
  defRevSubstPi₂ (G : [∀ a, Pi (Q a) | W]) :
    [∀ F : Pi P, [∀ a, Q a (F a) | W] | W]_{λ F => defSubstPi F G}

namespace HasRevSubstPi₂

  variable {α : Sort u} {V W : Universe} {P : α → V} [HasType V (∀ a, P a)] {Q : ∀ a, P a → W}
           [∀ a, HasType W (∀ b, Q a b)] [HasType W (∀ a, Pi (Q a))]
           [∀ F : Pi P, HasType W (∀ a, Q a (F a))] [HasType W (∀ F : Pi P, [∀ a, Q a (F a) | W])]
           [h : HasRevSubstPi₂ Q]

  @[reducible] def revSubstPi₂ (G : [∀ a, Pi (Q a) | W]) : [∀ (F : Pi P) a, Q a (F a) | W] :=
    h.defRevSubstPi₂ G

  instance revSubstPi.isPiApp {F : Pi P} {G : [∀ a, Pi (Q a) | W]} :
      IsPiApp (HasSubstPi.revSubstPi G F) :=
    ⟨revSubstPi₂ G, F, rfl⟩

end HasRevSubstPi₂

class HasRevSubstPiFun {α : Sort u} {V W : Universe} [HasUnivFunctors W W] {P : α → V}
                       [HasType V (∀ a, P a)] (Q : ∀ a, P a → W) [∀ a, HasType W (∀ b, Q a b)]
                       [HasType W (∀ a, Pi (Q a))] [∀ F : Pi P, HasType W (∀ a, Q a (F a))]
                       [HasType W (∀ F : Pi P, [∀ a, Q a (F a) | W])] extends
    HasRevSubstPi₂ Q where
  defRevSubstPiFun : [[∀ a, Pi (Q a) | W] ⥤ [∀ (F : Pi P) a, Q a (F a) | W]]_{defRevSubstPi₂}

namespace HasRevSubstPiFun

  variable {α : Sort u} {V W : Universe} [HasUnivFunctors W W] {P : α → V} [HasType V (∀ a, P a)]
           (Q : ∀ a, P a → W) [∀ a, HasType W (∀ b, Q a b)] [HasType W (∀ a, Pi (Q a))]
           [∀ F : Pi P, HasType W (∀ a, Q a (F a))] [HasType W (∀ F : Pi P, [∀ a, Q a (F a) | W])]
           [h : HasRevSubstPiFun Q]

  @[reducible] def revSubstPiFun : [∀ a, Pi (Q a) | W] ⥤ [∀ (F : Pi P) a, Q a (F a) | W] :=
    h.defRevSubstPiFun

  instance revSubstPi₂.isFunApp {G : [∀ a, Pi (Q a) | W]} :
      IsFunApp (HasRevSubstPi₂.revSubstPi₂ G) :=
    ⟨revSubstPiFun Q, G⟩

  instance revSubstPi.isPiApp₂ {G : [∀ a, Pi (Q a) | W]} {F : Pi P} :
      IsPiApp₂ (HasSubstPi.revSubstPi G F) :=
    ⟨revSubstPiFun Q, G, F, rfl⟩

end HasRevSubstPiFun



class HasExternalLinearLogic (α : Sort u) (V : Universe) [HasUnivFunctors V V] extends
    HasFunctors α V where
  defRevAppFun₂  (B   : V) : [α ⥤ (α ⥤ B) ⥤ B]__{λ a F => F a}
  defRevCompFun₃ (B C : V) : [(B ⥤ C) ⥤ (α ⥤ B) ⥤ α ⥤ C]___{λ G F a => G (F a)}

namespace HasExternalLinearLogic

  variable {V : Universe} [hU : HasUnivFunctors V V]

  section

    variable {α : Sort u} [h : HasExternalLinearLogic α V]

    @[reducible] def revAppFun (a : α) (B : V) : (α ⥤ B) ⥤ B := (h.defRevAppFun₂ B) a

    @[reducible] def revCompFun {B C : V} (G : B ⥤ C) (F : α ⥤ B) : α ⥤ C := (h.defRevCompFun₃ B C) G F
    infixr:90 " ⊙ " => HasExternalLinearLogic.revCompFun

    abbrev compFun {B C : V} (F : α ⥤ B) (G : B ⥤ C) : α ⥤ C := G ⊙ F

  end

  section

    variable (α : Sort u) [h : HasExternalLinearLogic α V]

    @[reducible] def revAppFun₂ (B : V) : α ⥤ (α ⥤ B) ⥤ B := h.defRevAppFun₂ B

    instance revAppFun.isFunApp {a : α} {B : V} : IsFunApp (revAppFun a B) := ⟨revAppFun₂ α B, a⟩

    @[reducible] def revCompFun₂ {B C : V} (G : B ⥤ C) : (α ⥤ B) ⥤ (α ⥤ C) := (h.defRevCompFun₃ B C) G

    instance revCompFun.isFunApp {B C : V} {G : B ⥤ C} {F : α ⥤ B} : IsFunApp (G ⊙ F) :=
      ⟨revCompFun₂ α G, F⟩

    @[reducible] def revCompFun₃ (B C : V) : (B ⥤ C) ⥤ (α ⥤ B) ⥤ (α ⥤ C) := h.defRevCompFun₃ B C

    instance revCompFun₂.isFunApp {B C : V} {G : B ⥤ C} : IsFunApp (revCompFun₂ α G) :=
      ⟨revCompFun₃ α B C, G⟩

    instance revCompFun.isFunApp₂ {B C : V} {G : B ⥤ C} {F : α ⥤ B} : IsFunApp₂ (G ⊙ F) :=
      ⟨revCompFun₃ α B C, G, F⟩

    instance hasPiAppFun (B : V) : HasPiAppFun (λ _ : α => B) := ⟨λ a => revAppFun a B⟩

    local instance (B : V) : HasType V (∀ a, (α ⥤ B) ⥤ (λ _ : α => B) a) := h.hFun ((α ⥤ B) ⥤ B)
    instance hasPiAppFunPi (B : V) : HasPiAppFunPi (λ _ : α => B) := ⟨revAppFun₂ α B⟩

    instance hasCompFunPi (B C : V) : HasCompFunPi α (λ _ : B => C) := ⟨compFun⟩
    local instance (B C : V) : HasType V (∀ (F : α ⥤ B), [∀ a, (λ _ => C) (apply F a) | V]) :=
      (hU.hFun (α ⥤ B)).hFun (α ⥤ C)
    instance hasRevCompFunPi₂ (B C : V) : HasRevCompFunPi₂ α (λ _ : B => C) := ⟨revCompFun₂ α⟩
    instance hasRevCompFunPiFun (B C : V) : HasRevCompFunPiFun α (λ _ : B => C) :=
      ⟨revCompFun₃ α B C⟩

  end

end HasExternalLinearLogic


class HasLinearLogic (U : Universe) extends HasUnivFunctors U U where
  defIdFun       (A     : U) : [A ⥤ A]_{id}
  defRevAppFun₂  (A B   : U) : [A ⥤ (A ⥤ B) ⥤ B]__{λ a F => F a}
  defRevCompFun₃ (A B C : U) : [(B ⥤ C) ⥤ (A ⥤ B) ⥤ A ⥤ C]___{λ G F a => G (F a)}

namespace HasLinearLogic

  variable {U : Universe} [h : HasLinearLogic U]

  @[reducible] def idFun (A : U) : A ⥤ A := h.defIdFun A

  instance hasIdFun (A : U) : HasIdFun A := ⟨idFun A⟩

  instance hasExternalLinearLogic (A : U) : HasExternalLinearLogic A U where
    defRevAppFun₂  B   := h.defRevAppFun₂  A B
    defRevCompFun₃ B C := h.defRevCompFun₃ A B C

end HasLinearLogic


class HasExternalSubLinearLogic (α : Sort u) (V : Universe) [HasUnivFunctors V V]
                                [HasFunctors α V] where
  defConstFun₂ (B : V) : [B ⥤ α ⥤ B]__{λ b a => b}

namespace HasExternalSubLinearLogic

  variable (α : Sort u) {V : Universe} [HasUnivFunctors V V] [HasFunctors α V]
           [h : HasExternalSubLinearLogic α V]

  @[reducible] def constFun {B : V} (b : B) : α ⥤ B := (h.defConstFun₂ B) b

  @[reducible] def constFun₂ (B : V) : B ⥤ (α ⥤ B) := h.defConstFun₂ B

  instance constFun.isFunApp {B : V} {b : B} : IsFunApp (constFun α b) := ⟨constFun₂ α B, b⟩

  instance hasConstPi (B : V) : HasConstPi α B := ⟨constFun α⟩
  instance hasConstPiFun (B : V) : HasConstPiFun α B := ⟨constFun₂ α B⟩

end HasExternalSubLinearLogic

class HasExternalAffineLogic (α : Sort u) (V : Universe) [HasUnivFunctors V V] extends
  HasExternalLinearLogic α V, HasExternalSubLinearLogic α V


class HasSubLinearLogic (U : Universe) [HasUnivFunctors U U] where
  defConstFun₂ (A B : U) : [B ⥤ A ⥤ B]__{λ b a => b}

namespace HasSubLinearLogic

  variable {U : Universe} [HasUnivFunctors U U] [h : HasSubLinearLogic U]

  instance hasExternalSubLinearLogic (A : U) : HasExternalSubLinearLogic A U where
    defConstFun₂ B := h.defConstFun₂ A B

end HasSubLinearLogic

class HasAffineLogic (U : Universe) extends HasLinearLogic U, HasSubLinearLogic U

namespace HasAffineLogic

  variable {U : Universe} [h : HasAffineLogic U]

  instance hasExternalAffineLogic (A : U) : HasExternalAffineLogic A U := ⟨⟩

end HasAffineLogic


class HasExternalNonLinearLogic (α : Sort u) (V : Universe) [HasUnivFunctors V V]
                                [HasFunctors α V] where
  defDupFun₂ (B : V) : [(α ⥤ α ⥤ B) ⥤ α ⥤ B]__{λ F a => F a a}

namespace HasExternalNonLinearLogic

  section

    variable {α : Sort u} {V : Universe} [HasUnivFunctors V V] [HasFunctors α V]
             [h : HasExternalNonLinearLogic α V]

    @[reducible] def dupFun {B : V} (F : α ⥤ α ⥤ B) : α ⥤ B := (h.defDupFun₂ B) F

  end

  section

    variable (α : Sort u) {V : Universe} [HasUnivFunctors V V] [hαU : HasFunctors α V]
             [h : HasExternalNonLinearLogic α V]

    @[reducible] def dupFun₂ (B : V) : (α ⥤ α ⥤ B) ⥤ (α ⥤ B) := h.defDupFun₂ B

    instance dupFun.isFunApp {B : V} {F : α ⥤ α ⥤ B} : IsFunApp (dupFun F) :=
      ⟨dupFun₂ α B, F⟩

    local instance (B : V) : HasType V (∀ a : α, [∀ a' : α, (λ _ _ => B) a a' | V]) :=
      hαU.hFun (α ⥤ B)
    instance (B : V) : HasDupPi (λ _ _ : α => B) := ⟨dupFun⟩
    instance (B : V) : HasDupPiFun (λ _ _ : α => B) := ⟨dupFun₂ α B⟩

  end

end HasExternalNonLinearLogic

class HasExternalFullLogic (α : Sort u) (U : Universe) [HasUnivFunctors U U] extends
  HasExternalAffineLogic α U, HasExternalNonLinearLogic α U


class HasNonLinearLogic (U : Universe) [HasUnivFunctors U U] where
  defDupFun₂ (A B : U) : [(A ⥤ A ⥤ B) ⥤ A ⥤ B]__{λ F a => F a a}

namespace HasNonLinearLogic

  variable {U : Universe} [HasUnivFunctors U U] [h : HasNonLinearLogic U]

  instance hasExternalNonLinearLogic (A : U) : HasExternalNonLinearLogic A U where
    defDupFun₂ B := h.defDupFun₂ A B

end HasNonLinearLogic

class HasFullLogic (U : Universe) extends HasAffineLogic U, HasNonLinearLogic U

namespace HasFullLogic

  variable {U : Universe} [h : HasFullLogic U]

  instance hasExternalFullLogic (A : U) : HasExternalFullLogic A U := ⟨⟩

end HasFullLogic



class HasExternalPiType {α : Sort u} {V : Universe} [HasLinearLogic V] (P : α → V) extends
  HasType V (∀ a, P a), HasPiAppFun P

namespace HasExternalPiType

  variable {α : Sort u} {V : Universe} [HasLinearLogic V] (P : α → V) [h : HasExternalPiType P]

  instance hasConstImpl (X : V) : HasType V (∀ a, X ⥤ P a) where
    T     := X ⥤ Pi P
    hElim := ⟨λ F a => HasPiAppFun.piAppFun P a ⊙ F⟩

  instance hasPiAppFunPi : HasPiAppFunPi P := ⟨HasLinearLogic.idFun (Pi P)⟩

  -- TODO: top, product

end HasExternalPiType


class HasExternalPiType₂ {α : Sort u} {β : Sort u'} {V : Universe} [HasLinearLogic V]
                         (P : α → β → V) where
  [hAppPiType (a : α) : HasExternalPiType (P a)]
  [hSwapAppPiType (b : β) : HasExternalPiType (λ a => P a b)]
  [hPiType₂ : HasExternalPiType (λ a => Pi (P a))]
  [hSwapPi : HasSwapPi P]
  defRevSwapPiFun (b : β) : [Pi₂ P ⥤ [∀ a, P a b | V]]_{λ F => HasSwapPi.swapPi F b}

namespace HasExternalPiType₂

  variable {α : Sort u} {β : Sort u'} {V : Universe} [HasLinearLogic V] (P : α → β → V)
           [h : HasExternalPiType₂ P]

  instance (a : α) : HasExternalPiType (P a) := h.hAppPiType a
  instance (a : α) : HasExternalPiType ((λ a b => P a b) a) := h.hAppPiType a
  instance (b : β) : HasExternalPiType (λ a => P a b) := h.hSwapAppPiType b
  instance (b : β) : HasExternalPiType ((λ b a => P a b) b) := h.hSwapAppPiType b
  instance : HasExternalPiType (λ a => Pi (P a)) := h.hPiType₂
  instance : HasSwapPi P := h.hSwapPi

  instance : HasType V (∀ b, [∀ a, P a b | V]) where
    T     := Pi₂ P
    hElim := ⟨HasSwapPi.swapPi⟩

  instance : HasPiAppFun (λ b => [∀ a, P a b | V]) := ⟨h.defRevSwapPiFun⟩

  instance hasSwapPiType₂ : HasExternalPiType (λ b => [∀ a, P a b | V]) := ⟨⟩

  instance : HasSwapPi₂ P := ⟨id⟩
  instance : HasSwapPiFun P := ⟨HasLinearLogic.idFun (Pi₂ P)⟩

end HasExternalPiType₂
