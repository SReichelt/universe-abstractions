import UniverseAbstractions.Universes.Layer1.Axioms.Universes



namespace UniverseAbstractions.Layer1

set_option autoBoundImplicitLocal false

open Universe

universe u u' u'' u'''



-- Functors at layer 1 are just functions which are used to encode implication (i.e. we disregard
-- all information about concrete instances).
--
-- The most generic functor type constructor has the form `Sort u → V → V` because that offers
-- enough flexibility when combining different universes while still working well with
-- multifunctors.

-- TODO: Looks like we can reduce the universe polymorphism again.

class HasFunctors (α : Sort u) (V : Universe) where
  defFunType (Y : V) : DefType V (α → Y)

namespace HasFunctors

  variable {V : Universe}

  section

    @[reducible] def Fun (α : Sort u) [h : HasFunctors α V] (Y : V) : V := h.defFunType Y
    infixr:20 " ⥤ " => HasFunctors.Fun

    @[reducible] def apply {α : Sort u} [h : HasFunctors α V] {Y : V} (F : α ⥤ Y) (a : α) : Y :=
      ((h.defFunType Y).elim F) a

    instance coeFun (α : Sort u) [HasFunctors α V] (Y : V) : CoeFun (α ⥤ Y) (λ _ => α → Y) := ⟨apply⟩

    @[reducible] def apply₂ {α : Sort u} {β : Sort u'} [HasFunctors α V] [HasFunctors β V] {Y : V}
                            (F : α ⥤ β ⥤ Y) (a : α) (b : β) : Y :=
      F a b

    @[reducible] def apply₃ {α : Sort u} {β : Sort u'} {γ : Sort u''} [HasFunctors α V]
                            [HasFunctors β V] [HasFunctors γ V] {Y : V} (F : α ⥤ β ⥤ γ ⥤ Y)
                            (a : α) (b : β) (c : γ) : Y :=
      F a b c

    @[reducible] def apply₄ {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''}
                            [HasFunctors α V] [HasFunctors β V] [HasFunctors γ V] [HasFunctors δ V]
                            {Y : V} (F : α ⥤ β ⥤ γ ⥤ δ ⥤ Y) (a : α) (b : β) (c : γ) (d : δ) : Y :=
      F a b c d

  end

  -- Helper classes for the `functoriality` tactic.
  section Helpers

    variable {V : Universe} {Y : V}

    class IsFunApp (α : outParam (Sort u)) [outParam (HasFunctors α V)] (y : Y) where
      F : α ⥤ Y
      a : α

    instance (priority := low) IsFunApp.refl {α : Sort u} [HasFunctors α V] {F : α ⥤ Y} {a : α} :
        IsFunApp α (F a) :=
      ⟨F, a⟩

    class IsFunApp₂ (α : outParam (Sort u)) (β : outParam (Sort u')) [outParam (HasFunctors α V)]
                    [outParam (HasFunctors β V)] (y : Y) where
      F : α ⥤ β ⥤ Y
      a : α
      b : β

    namespace IsFunApp₂

      variable {α : Sort u} {β : Sort u'} [HasFunctors α V] [HasFunctors β V]

      instance (priority := low) refl {F : α ⥤ β ⥤ Y} {a : α} {b : β} : IsFunApp₂ α β (F a b) :=
        ⟨F, a, b⟩

      def isFunApp {y : Y} [hApp : IsFunApp₂ α β y] : IsFunApp β y :=
        ⟨apply hApp.F hApp.a, hApp.b⟩

    end IsFunApp₂

    class IsFunApp₃ (α : outParam (Sort u)) (β : outParam (Sort u')) (γ : outParam (Sort u''))
                    [outParam (HasFunctors α V)] [outParam (HasFunctors β V)]
                    [outParam (HasFunctors γ V)] (y : Y) where
      F : α ⥤ β ⥤ γ ⥤ Y
      a : α
      b : β
      c : γ

    namespace IsFunApp₃

      variable {α : Sort u} {β : Sort u'} {γ : Sort u''} [HasFunctors α V] [HasFunctors β V]
               [HasFunctors γ V]

      instance (priority := low) refl {F : α ⥤ β ⥤ γ ⥤ Y} {a : α} {b : β} {c : γ} :
          IsFunApp₃ α β γ (F a b c) :=
        ⟨F, a, b, c⟩

      def isFunApp₂ {y : Y} [hApp : IsFunApp₃ α β γ y] : IsFunApp₂ β γ y :=
        ⟨apply hApp.F hApp.a, hApp.b, hApp.c⟩

      def isFunApp {y : Y} [hApp : IsFunApp₃ α β γ y] : IsFunApp γ y :=
        let _ : IsFunApp₂ β γ y := isFunApp₂
        IsFunApp₂.isFunApp

    end IsFunApp₃

    class IsFunApp₄ (α : outParam (Sort u)) (β : outParam (Sort u')) (γ : outParam (Sort u''))
                    (δ : outParam (Sort u''')) [outParam (HasFunctors α V)]
                    [outParam (HasFunctors β V)] [outParam (HasFunctors γ V)]
                    [outParam (HasFunctors δ V)] (y : Y) where
      F : α ⥤ β ⥤ γ ⥤ δ ⥤ Y
      a : α
      b : β
      c : γ
      d : δ

    namespace IsFunApp₄

      variable {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''} [HasFunctors α V]
               [HasFunctors β V] [HasFunctors γ V] [HasFunctors δ V]

      instance (priority := low) refl {F : α ⥤ β ⥤ γ ⥤ δ ⥤ Y} {a : α} {b : β} {c : γ} {d : δ} :
          IsFunApp₄ α β γ δ (F a b c d) :=
        ⟨F, a, b, c, d⟩

      def isFunApp₃ {y : Y} [hApp : IsFunApp₄ α β γ δ y] : IsFunApp₃ β γ δ y :=
        ⟨apply hApp.F hApp.a, hApp.b, hApp.c, hApp.d⟩

      def isFunApp₂ {y : Y} [hApp : IsFunApp₄ α β γ δ y] : IsFunApp₂ γ δ y :=
        let _ : IsFunApp₃ β γ δ y := isFunApp₃
        IsFunApp₃.isFunApp₂

      def isFunApp {y : Y} [hApp : IsFunApp₄ α β γ δ y] : IsFunApp δ y :=
        let _ : IsFunApp₂ γ δ y := isFunApp₂
        IsFunApp₂.isFunApp

    end IsFunApp₄

    class IsFunApp₂' (α : outParam (Sort u)) (β : outParam (Sort u')) [outParam (HasFunctors α V)]
                     [outParam (HasFunctors β V)] (y : Y) extends
        IsFunApp β y where
      h₂ : IsFunApp α y

    class IsFunApp₃' (α : outParam (Sort u)) (β : outParam (Sort u')) (γ : outParam (Sort u''))
                     [outParam (HasFunctors α V)] [outParam (HasFunctors β V)]
                     [outParam (HasFunctors γ V)] (y : Y) extends
        IsFunApp₂' β γ y where
      h₃ : IsFunApp α y

    class IsFunApp₄' (α : outParam (Sort u)) (β : outParam (Sort u')) (γ : outParam (Sort u''))
                     (δ : outParam (Sort u''')) [outParam (HasFunctors α V)]
                     [outParam (HasFunctors β V)] [outParam (HasFunctors γ V)]
                     [outParam (HasFunctors δ V)] (y : Y) extends
        IsFunApp₃' β γ δ y where
      h₄ : IsFunApp α y

  end Helpers

  -- A `DefFun` is a functor that additionally incorporates a concrete function in its type. In
  -- layer 1, that function is essentially just a proof that the implication holds.
  section DefFun

    @[reducible] def DefFun (α : Sort u) [h : HasFunctors α V] (Y : V) (f : α → Y) :=
      DefType.DefInst (h.defFunType Y) f

    namespace DefFun

      notation:20 α:21 " ⥤{" f:0 "} " Y:21 => HasFunctors.DefFun α Y f

      variable {α : Sort u} [h : HasFunctors α V] {Y : V}

      def mk {f : α → Y} (F : α ⥤ Y) : α ⥤{f} Y := ⟨F⟩

      instance coeType (f : α → Y) : Coe (α ⥤{f} Y) (α ⥤ Y) :=
        DefType.DefInst.coeType (h.defFunType Y) f

      def isFunApp {f : α → Y} (F : α ⥤{f} Y) {a : α} : IsFunApp α (f a) := ⟨F, a⟩

      @[reducible] def cast {f g : α → Y} (F : α ⥤{f} Y) : α ⥤{g} Y := DefType.DefInst.cast F

      def defAppFun (F : α ⥤ Y) : α ⥤{apply F} Y := ⟨F⟩

    end DefFun

    structure DefFun₂ (α : Sort u) (β : Sort u') [HasFunctors α V] [HasFunctors β V] (Y : V)
                      (f : α → β → Y) where
      app (a : α) : β ⥤{f a} Y
      toDefFun : α ⥤{λ a => app a} (β ⥤ Y)

    namespace DefFun₂

      notation:20 α:21 " ⥤ " β:21 " ⥤{" f:0 "} " Y:21 => HasFunctors.DefFun₂ α β Y f

      variable {α : Sort u} {β : Sort u'} [HasFunctors α V] [HasFunctors β V] {Y : V}

      @[reducible] def inst {f : α → β → Y} (F : α ⥤ β ⥤{f} Y) : α ⥤ β ⥤ Y :=
        F.toDefFun

      instance coeType (f : α → β → Y) : Coe (α ⥤ β ⥤{f} Y) (α ⥤ β ⥤ Y) := ⟨inst⟩

      def isFunApp₂ {f : α → β → Y} (F : α ⥤ β ⥤{f} Y) {a : α} {b : β} :
          IsFunApp₂ α β (f a b) :=
        ⟨F, a, b⟩

      def cast {f g : α → β → Y} (F : α ⥤ β ⥤{f} Y) : α ⥤ β ⥤{g} Y :=
        ⟨λ a => DefFun.cast (F.app a), DefFun.cast F.toDefFun⟩

      def defAppFun (F : α ⥤ β ⥤ Y) : α ⥤ β ⥤{apply₂ F} Y :=
        ⟨λ a => DefFun.defAppFun (F a), DefFun.defAppFun F⟩

    end DefFun₂

    structure DefFun₃ (α : Sort u) (β : Sort u') (γ : Sort u'') [HasFunctors α V] [HasFunctors β V]
                      [HasFunctors γ V] (Y : V) (f : α → β → γ → Y) where
      app (a : α) : β ⥤ γ ⥤{f a} Y
      toDefFun : α ⥤{λ a => app a} (β ⥤ γ ⥤ Y)

    namespace DefFun₃

      notation:20 α:21 " ⥤ " β:21 " ⥤ " γ:21 " ⥤{" f:0 "} " Y:21 =>
        HasFunctors.DefFun₃ α β γ Y f

      variable {α : Sort u} {β : Sort u'} {γ : Sort u''} [HasFunctors α V] [HasFunctors β V]
               [HasFunctors γ V] {Y : V}

      @[reducible] def inst {f : α → β → γ → Y} (F : α ⥤ β ⥤ γ ⥤{f} Y) : α ⥤ β ⥤ γ ⥤ Y :=
        F.toDefFun

      instance coeType (f : α → β → γ → Y) : Coe (α ⥤ β ⥤ γ ⥤{f} Y) (α ⥤ β ⥤ γ ⥤ Y) := ⟨inst⟩

      def isFunApp₃ {f : α → β → γ → Y} (F : α ⥤ β ⥤ γ ⥤{f} Y) {a : α} {b : β} {c : γ} :
          IsFunApp₃ α β γ (f a b c) :=
        ⟨F, a, b, c⟩

      def cast {f g : α → β → γ → Y} (F : α ⥤ β ⥤ γ ⥤{f} Y) : α ⥤ β ⥤ γ ⥤{g} Y :=
        ⟨λ a => DefFun₂.cast (F.app a), DefFun.cast F.toDefFun⟩

      def defAppFun (F : α ⥤ β ⥤ γ ⥤ Y) : α ⥤ β ⥤ γ ⥤{apply₃ F} Y :=
        ⟨λ a => DefFun₂.defAppFun (F a), DefFun.defAppFun F⟩

    end DefFun₃

    structure DefFun₄ (α : Sort u) (β : Sort u') (γ : Sort u'') (δ : Sort u''') [HasFunctors α V]
                      [HasFunctors β V] [HasFunctors γ V] [HasFunctors δ V] (Y : V)
                      (f : α → β → γ → δ → Y) where
      app (a : α) : β ⥤ γ ⥤ δ ⥤{f a} Y
      toDefFun : α ⥤{λ a => app a} (β ⥤ γ ⥤ δ ⥤ Y)

    namespace DefFun₄

      notation:20 α:21 " ⥤ " β:21 " ⥤ " γ:21 " ⥤ " δ:21 " ⥤{" f:0 "} " Y:21 =>
        HasFunctors.DefFun₄ α β γ δ Y f

      variable {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''} [HasFunctors α V]
               [HasFunctors β V] [HasFunctors γ V] [HasFunctors δ V] {Y : V}

      @[reducible] def inst {f : α → β → γ → δ → Y} (F : α ⥤ β ⥤ γ ⥤ δ ⥤{f} Y) : α ⥤ β ⥤ γ ⥤ δ ⥤ Y :=
        F.toDefFun

      instance coeType (f : α → β → γ → δ → Y) : Coe (α ⥤ β ⥤ γ ⥤ δ ⥤{f} Y) (α ⥤ β ⥤ γ ⥤ δ ⥤ Y) :=
        ⟨inst⟩

      def isFunApp₄ {f : α → β → γ → δ → Y} (F : α ⥤ β ⥤ γ ⥤ δ ⥤{f} Y) {a : α} {b : β} {c : γ} {d : δ} :
          IsFunApp₄ α β γ δ (f a b c d) :=
        ⟨F, a, b, c, d⟩

      def cast {f g : α → β → γ → δ → Y} (F : α ⥤ β ⥤ γ ⥤ δ ⥤{f} Y) : α ⥤ β ⥤ γ ⥤ δ ⥤{g} Y :=
        ⟨λ a => DefFun₃.cast (F.app a), DefFun.cast F.toDefFun⟩

      def defAppFun (F : α ⥤ β ⥤ γ ⥤ δ ⥤ Y) : α ⥤ β ⥤ γ ⥤ δ ⥤{apply₄ F} Y :=
        ⟨λ a => DefFun₃.defAppFun (F a), DefFun.defAppFun F⟩

    end DefFun₄

  end DefFun

end HasFunctors

open HasFunctors


class HasUnivFunctors (U V : Universe) where
  [hFun (A : U) : HasFunctors A V]

namespace HasUnivFunctors

  instance {U : Universe} (A : U) (V : Universe) [h : HasUnivFunctors U V] : HasFunctors A V :=
    h.hFun A

end HasUnivFunctors



class HasIdFun {U : Universe} (A : U) [HasFunctors A U] where
  defIdFun : A ⥤{id} A

namespace HasIdFun

  variable {U : Universe} (A : U) [HasFunctors A U] [h : HasIdFun A]

  @[reducible] def idFun : A ⥤ A := h.defIdFun

end HasIdFun


class HasRevAppFun (α : Sort u) (V : Universe) [HasFunctors α V] [HasUnivFunctors V V]
                   where
  defRevAppFun₂ (B : V) : α ⥤ (α ⥤ B) ⥤{λ a F => F a} B

namespace HasRevAppFun

  section

    variable {α : Sort u} (a : α) {V : Universe} [HasFunctors α V] [HasUnivFunctors V V]
             [h : HasRevAppFun α V] (B : V)

    @[reducible] def revAppFun : (α ⥤ B) ⥤ B := (h.defRevAppFun₂ B).app a

  end

  section

    variable (α : Sort u) {V : Universe} [HasFunctors α V] [HasUnivFunctors V V]
             [h : HasRevAppFun α V] (B : V)

    @[reducible] def revAppFun₂ : α ⥤ (α ⥤ B) ⥤ B := h.defRevAppFun₂ B

    instance revAppFun.isFunApp {a : α} : IsFunApp α (revAppFun a B) := ⟨revAppFun₂ α B, a⟩

  end

end HasRevAppFun


class HasSwapFun (α : Sort u) (β : Sort u') (V : Universe) [HasFunctors α V] [HasFunctors β V] where
  defSwapFun₂ {C : V} (F : α ⥤ β ⥤ C) : β ⥤ α ⥤{λ b a => F a b} C

namespace HasSwapFun

  variable {α : Sort u} {β : Sort u'} {V : Universe} [HasFunctors α V] [HasFunctors β V]
           [h : HasSwapFun α β V] {C : V}

  @[reducible] def swapFun (F : α ⥤ β ⥤ C) (b : β) : α ⥤ C :=
    (h.defSwapFun₂ F).app b

  @[reducible] def swapFun₂ (F : α ⥤ β ⥤ C) : β ⥤ α ⥤ C := h.defSwapFun₂ F
  
  instance swapFun.isFunApp {F : α ⥤ β ⥤ C} {b : β} : IsFunApp β (HasSwapFun.swapFun F b) :=
    ⟨swapFun₂ F, b⟩

end HasSwapFun

class HasSwapFun₃ (α : Sort u) (β : Sort u') (V : Universe) [HasFunctors α V] [HasFunctors β V]
                  [HasUnivFunctors V V] extends
    HasSwapFun α β V where
  defSwapFun₃ (C : V) : (α ⥤ β ⥤ C) ⥤{HasSwapFun.swapFun₂} (β ⥤ α ⥤ C)

namespace HasSwapFun₃

  variable (α : Sort u) (β : Sort u') {V : Universe} [HasFunctors α V] [HasFunctors β V]
           [HasUnivFunctors V V] [h : HasSwapFun₃ α β V] (C : V)

  @[reducible] def swapFun₃ : (α ⥤ β ⥤ C) ⥤ (β ⥤ α ⥤ C) := h.defSwapFun₃ C

  instance swapFun₂.isFunApp {F : α ⥤ β ⥤ C} : IsFunApp (α ⥤ β ⥤ C) (HasSwapFun.swapFun₂ F) :=
    ⟨swapFun₃ α β C, F⟩

  instance swapFun.isFunApp₂ {F : α ⥤ β ⥤ C} {b : β} :
      IsFunApp₂ (α ⥤ β ⥤ C) β (HasSwapFun.swapFun F b) :=
    ⟨swapFun₃ α β C, F, b⟩

end HasSwapFun₃


class HasCompFun (α : Sort u) {V : Universe} (B : V) (W : Universe) [HasFunctors α V]
                 [HasFunctors B W] [HasFunctors α W] where
  defCompFun {C : W} (F : α ⥤ B) (G : B ⥤ C) : α ⥤{λ a => G (F a)} C

namespace HasCompFun

  variable {α : Sort u} {V W : Universe} [HasFunctors α V] [HasFunctors α W] {B : V}
           [HasFunctors B W] [h : HasCompFun α B W] {C : W}

  @[reducible] def compFun (F : α ⥤ B) (G : B ⥤ C) : α ⥤ C := h.defCompFun F G

  @[reducible] def revCompFun (G : B ⥤ C) (F : α ⥤ B) : α ⥤ C := compFun F G
  infixr:90 " ⊙ " => HasCompFun.revCompFun

end HasCompFun

class HasRevCompFun₂ (α : Sort u) (V W : Universe) [HasFunctors α V] [HasFunctors α W]
                     [HasUnivFunctors V W] where
  defRevCompFun₂ {B : V} {C : W} (G : B ⥤ C) : (α ⥤ B) ⥤ α ⥤{λ F a => G (F a)} C

namespace HasRevCompFun₂

  variable (α : Sort u) {V W : Universe} [HasFunctors α V] [HasFunctors α W] [HasUnivFunctors V W]
           [h : HasRevCompFun₂ α V W]

  instance hasCompFun (B : V) : HasCompFun α B W := ⟨λ F G => (h.defRevCompFun₂ G).app F⟩

  @[reducible] def revCompFun₂ {B : V} {C : W} (G : B ⥤ C) : (α ⥤ B) ⥤ (α ⥤ C) := h.defRevCompFun₂ G

  instance compFun.isFunApp {B : V} {C : W} {F : α ⥤ B} {G : B ⥤ C} :
      IsFunApp (α ⥤ B) (HasCompFun.compFun F G) :=
    ⟨revCompFun₂ α G, F⟩

  instance revCompFun.isFunApp {B : V} {C : W} {G : B ⥤ C} {F : α ⥤ B} : IsFunApp (α ⥤ B) (G ⊙ F) :=
    compFun.isFunApp α

end HasRevCompFun₂

class HasRevCompFun₃ (α : Sort u) (V W : Universe) [HasFunctors α V] [HasFunctors α W]
                     [HasUnivFunctors V W] [HasUnivFunctors W W] extends
    HasRevCompFun₂ α V W where
  defRevCompFun₃ (B : V) (C : W) : (B ⥤ C) ⥤{HasRevCompFun₂.revCompFun₂ α} ((α ⥤ B) ⥤ (α ⥤ C))

namespace HasRevCompFun₃

  variable (α : Sort u) {V W : Universe} [HasFunctors α V] [HasFunctors α W]
           [HasUnivFunctors V W] [HasUnivFunctors W W] [h : HasRevCompFun₃ α V W]

  @[reducible] def revCompFun₃ (B : V) (C : W) : (B ⥤ C) ⥤ (α ⥤ B) ⥤ (α ⥤ C) :=
    h.defRevCompFun₃ B C

  instance revCompFun₂.isFunApp {B : V} {C : W} {G : B ⥤ C} :
      IsFunApp (B ⥤ C) (HasRevCompFun₂.revCompFun₂ α G) :=
    ⟨revCompFun₃ α B C, G⟩

  instance revCompFun.isFunApp₂ {B : V} {C : W} {G : B ⥤ C} {F : α ⥤ B} :
      IsFunApp₂ (B ⥤ C) (α ⥤ B) (G ⊙ F) :=
    ⟨revCompFun₃ α B C, G, F⟩

end HasRevCompFun₃


class HasConstFun (α : Sort u) (V : Universe) [HasFunctors α V] where
  defConstFun {B : V} (b : B) : α ⥤{Function.const α b} B

namespace HasConstFun

  variable (α : Sort u) {V : Universe} [HasFunctors α V] [h : HasConstFun α V] {B : V}

  @[reducible] def constFun (b : B) : α ⥤ B := h.defConstFun b

end HasConstFun

class HasConstFun₂ (α : Sort u) (V : Universe) [HasFunctors α V] [HasUnivFunctors V V] extends
    HasConstFun α V where
  defConstFun₂ (B : V) : B ⥤{HasConstFun.constFun α} (α ⥤ B)

namespace HasConstFun₂

  variable (α : Sort u) {V : Universe} [HasFunctors α V] [HasUnivFunctors V V]
           [h : HasConstFun₂ α V] (B : V)

  @[reducible] def constFun₂ : B ⥤ (α ⥤ B) := h.defConstFun₂ B

  instance constFun.isFunApp {b : B} : IsFunApp B (HasConstFun.constFun α b) := ⟨constFun₂ α B, b⟩

end HasConstFun₂


class HasDupFun (α : Sort u) (V : Universe) [HasFunctors α V] where
  defDupFun {B : V} (F : α ⥤ α ⥤ B) : α ⥤{λ a => F a a} B

namespace HasDupFun

  variable {α : Sort u} {V : Universe} [HasFunctors α V] [h : HasDupFun α V] {B : V}

  @[reducible] def dupFun (F : α ⥤ α ⥤ B) : α ⥤ B := h.defDupFun F

end HasDupFun

class HasDupFun₂ (α : Sort u) (V : Universe) [HasFunctors α V] [HasUnivFunctors V V] extends
    HasDupFun α V where
  defDupFun₂ (B : V) : (α ⥤ α ⥤ B) ⥤{HasDupFun.dupFun} (α ⥤ B)

namespace HasDupFun₂

  variable (α : Sort u) {V : Universe} [HasFunctors α V] [HasUnivFunctors V V]
           [h : HasDupFun₂ α V] (B : V)

  @[reducible] def dupFun₂ : (α ⥤ α ⥤ B) ⥤ (α ⥤ B) := h.defDupFun₂ B

  instance dupFun.isFunαpp {F : α ⥤ α ⥤ B} : IsFunApp (α ⥤ α ⥤ B) (HasDupFun.dupFun F) :=
    ⟨dupFun₂ α B, F⟩

end HasDupFun₂


class HasRevSelfAppFun (V W : Universe) [HasUnivFunctors V W] [HasUnivFunctors W V]
                       [HasUnivFunctors W W] where
  defRevSelfAppFun₂ (A : V) (B : W) : ((A ⥤ B) ⥤ A) ⥤ (A ⥤ B) ⥤{λ F G => G (F G)} B

namespace HasRevSelfAppFun

  variable {V W : Universe} [HasUnivFunctors V W] [HasUnivFunctors W V] [HasUnivFunctors W W]
           [h : HasRevSelfAppFun V W]

  @[reducible] def revSelfAppFun {A : V} {B : W} (F : (A ⥤ B) ⥤ A) : (A ⥤ B) ⥤ B :=
    (h.defRevSelfAppFun₂ A B).app F

  @[reducible] def revSelfAppFun₂ (A : V) (B : W) : ((A ⥤ B) ⥤ A) ⥤ (A ⥤ B) ⥤ B :=
    h.defRevSelfAppFun₂ A B

  instance revSelfAppFun.isFunApp {A : V} {B : W} {F : (A ⥤ B) ⥤ A} :
      IsFunApp ((A ⥤ B) ⥤ A) (revSelfAppFun F) :=
    ⟨revSelfAppFun₂ A B, F⟩

end HasRevSelfAppFun


class HasSubstFun (α : Sort u) {V : Universe} (B : V) (W : Universe) [HasFunctors α V]
                  [HasFunctors B W] [HasFunctors α W] where
  defSubstFun {C : W} (F : α ⥤ B) (G : α ⥤ B ⥤ C) : α ⥤{λ a => G a (F a)} C

namespace HasSubstFun

  variable {α : Sort u} {V W : Universe} [HasFunctors α V] [HasFunctors α W]
           {B : V} [HasFunctors B W] [h : HasSubstFun α B W] {C : W}

  @[reducible] def substFun (F : α ⥤ B) (G : α ⥤ B ⥤ C) : α ⥤ C := h.defSubstFun F G

  @[reducible] def revSubstFun (G : α ⥤ B ⥤ C) (F : α ⥤ B) : α ⥤ C := substFun F G

end HasSubstFun

class HasRevSubstFun₂ (α : Sort u) (V W : Universe) [HasFunctors α V] [HasFunctors α W]
                      [HasUnivFunctors V W] where
  defRevSubstFun₂ {B : V} {C : W} (G : α ⥤ B ⥤ C) : (α ⥤ B) ⥤ α ⥤{λ F a => G a (F a)} C

namespace HasRevSubstFun₂

  variable {α : Sort u} {V W : Universe} [HasFunctors α V] [HasFunctors α W]
           [HasUnivFunctors V W] [h : HasRevSubstFun₂ α V W]

  instance hasSubstFun (B : V) : HasSubstFun α B W := ⟨λ F G => (h.defRevSubstFun₂ G).app F⟩

  @[reducible] def revSubstFun₂ {B : V} {C : W} (G : α ⥤ B ⥤ C) : (α ⥤ B) ⥤ (α ⥤ C) :=
    h.defRevSubstFun₂ G

  instance substFun.isFunApp {B : V} {C : W} {F : α ⥤ B} {G : α ⥤ B ⥤ C} :
      IsFunApp (α ⥤ B) (HasSubstFun.substFun F G) :=
    ⟨revSubstFun₂ G, F⟩

  instance revSubstFun.isFunApp {B : V} {C : W} {F : α ⥤ B} {G : α ⥤ B ⥤ C} :
      IsFunApp (α ⥤ B) (HasSubstFun.revSubstFun G F) :=
    substFun.isFunApp

end HasRevSubstFun₂

class HasRevSubstFun₃ (α : Sort u) (V W : Universe) [HasFunctors α V] [HasFunctors α W]
                      [HasUnivFunctors V W] [HasUnivFunctors W W] extends
    HasRevSubstFun₂ α V W where
  defRevSubstFun₃ (B : V) (C : W) : (α ⥤ B ⥤ C) ⥤{HasRevSubstFun₂.revSubstFun₂} ((α ⥤ B) ⥤ (α ⥤ C))

namespace HasRevSubstFun₃

  variable (α : Sort u) {V W : Universe} [HasFunctors α V] [HasFunctors α W]
           [HasUnivFunctors V W] [HasUnivFunctors W W] [h : HasRevSubstFun₃ α V W]

  @[reducible] def revSubstFun₃ (B : V) (C : W) : (α ⥤ B ⥤ C) ⥤ (α ⥤ B) ⥤ (α ⥤ C) :=
    h.defRevSubstFun₃ B C

  instance revSubstFun₂.isFunApp {B : V} {C : W} {G : α ⥤ B ⥤ C} :
      IsFunApp (α ⥤ B ⥤ C) (HasRevSubstFun₂.revSubstFun₂ G) :=
    ⟨revSubstFun₃ α B C, G⟩

  instance revSubstFun.isFunApp₂ {B : V} {C : W} {G : α ⥤ B ⥤ C} {F : α ⥤ B} :
      IsFunApp₂ (α ⥤ B ⥤ C) (α ⥤ B) (HasSubstFun.revSubstFun G F) :=
    ⟨revSubstFun₃ α B C, G, F⟩

end HasRevSubstFun₃



class HasLinearLogic (U : Universe) extends HasUnivFunctors U U where
  [hIdFun (A : U) : HasIdFun A]
  [hRevAppFun (A : U) : HasRevAppFun A U]
  [hRevCompFun₃ (A : U) : HasRevCompFun₃ A U U]

namespace HasLinearLogic

  variable {U : Universe} [h : HasLinearLogic U]

  instance (A : U) : HasIdFun A := h.hIdFun A
  instance (A : U) : HasRevAppFun A U := h.hRevAppFun A
  instance (A : U) : HasRevCompFun₃ A U U := h.hRevCompFun₃ A

  @[reducible] def defAppFun₂ (A B : U) : (A ⥤ B) ⥤ A ⥤{λ F a => F a} B :=
    ⟨DefFun.defAppFun, (h.hIdFun (A ⥤ B)).defIdFun⟩

  @[reducible] def appFun₂ (A B : U) : (A ⥤ B) ⥤ A ⥤ B := defAppFun₂ A B

end HasLinearLogic


class HasSubLinearLogic (U : Universe) [HasUnivFunctors U U] where
  [hConstFun₂ (A : U) : HasConstFun₂ A U]

namespace HasSubLinearLogic

  variable {U : Universe} [HasUnivFunctors U U] [h : HasSubLinearLogic U]

  instance (A : U) : HasConstFun₂ A U := h.hConstFun₂ A

end HasSubLinearLogic

class HasAffineLogic (U : Universe) extends HasLinearLogic U, HasSubLinearLogic U


class HasNonLinearLogic (U : Universe) [HasUnivFunctors U U] where
  [hDupFun₂ (A : U) : HasDupFun₂ A U]

namespace HasNonLinearLogic

  variable {U : Universe} [HasUnivFunctors U U] [h : HasNonLinearLogic U]

  instance (A : U) : HasDupFun₂ A U := h.hDupFun₂ A

end HasNonLinearLogic

class HasFullLogic (U : Universe) extends HasAffineLogic U, HasNonLinearLogic U
