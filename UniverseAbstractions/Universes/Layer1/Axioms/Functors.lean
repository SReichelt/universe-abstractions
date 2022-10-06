import UniverseAbstractions.Universes.Layer1.Axioms.Universes



namespace UniverseAbstractions.Layer1

set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 2500

universe u u' u'' u'''



-- Π types have a bit of a chicken-and-egg problem. The "true" definition requires
-- * a functor `P : A ⥤ V`, where `V` is the universe of propositions with respect to `A` (defined
--   in layer 2), and `⥤` is just an instant of a Π type with a constant property, and
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

class HasPiType {α : Sort u} {V : Universe} (P : α → V) where
  defPiType : DefType V (∀ a, P a)

namespace HasPiType

  variable {V : Universe}

  @[reducible] def Pi {α : Sort u} (P : α → V) [h : HasPiType P] : V := h.defPiType

  @[reducible] def apply {α : Sort u} {P : α → V} [h : HasPiType P] (F : Pi P) (a : α) : P a :=
    (h.defPiType.elim F) a

  instance coeFun {α : Sort u} (P : α → V) [HasPiType P] : CoeFun (Pi P) (λ _ => ∀ a, P a) :=
    ⟨apply⟩

  @[reducible] def Pi₂ {α : Sort u} {β : Sort u'} (P : α → β → V) [hPa : ∀ a, HasPiType (P a)]
                       [hPiPa : HasPiType (λ a => Pi (P a))] : V :=
    Pi (λ a => Pi (P a))

  @[reducible] def apply₂ {α : Sort u} {β : Sort u'} {P : α → β → V} [∀ a, HasPiType (P a)]
                          [HasPiType (λ a => Pi (P a))] (F : Pi₂ P) (a : α) (b : β) : P a b :=
    F a b

  @[reducible] def defPiType₂ {α : Sort u} {β : Sort u'} (P : α → β → V) [∀ a, HasPiType (P a)]
                              [HasPiType (λ a => Pi (P a))] :
      DefType V (∀ a b, P a b) where
    A    := Pi₂ P
    elim := apply₂

  @[reducible] def Pi₃ {α : Sort u} {β : Sort u'} {γ : Sort u''} (P : α → β → γ → V)
                       [hPab : ∀ a b, HasPiType (P a b)]
                       [hPiPab : ∀ a, HasPiType (λ b => Pi (P a b))]
                       [hPiPa : HasPiType (λ a => Pi₂ (P a))] : V :=
    Pi (λ a => Pi₂ (P a))

  @[reducible] def apply₃ {α : Sort u} {β : Sort u'} {γ : Sort u''} {P : α → β → γ → V}
                          [∀ a b, HasPiType (P a b)] [∀ a, HasPiType (λ b => Pi (P a b))]
                          [HasPiType (λ a => Pi₂ (P a))] (F : Pi₃ P) (a : α) (b : β) (c : γ) :
                          P a b c :=
    F a b c

  @[reducible] def defPiType₃ {α : Sort u} {β : Sort u'} {γ : Sort u''} (P : α → β → γ → V)
                              [∀ a b, HasPiType (P a b)] [∀ a, HasPiType (λ b => Pi (P a b))]
                              [HasPiType (λ a => Pi₂ (P a))] :
      DefType V (∀ a b c, P a b c) where
    A    := Pi₃ P
    elim := apply₃

  @[reducible] def Pi₄ {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''}
                       (P : α → β → γ → δ → V) [hPabc : ∀ a b c, HasPiType (P a b c)]
                       [hPiPabc : ∀ a b, HasPiType (λ c => Pi (P a b c))]
                       [hPiPab : ∀ a, HasPiType (λ b => Pi₂ (P a b))]
                       [hPiPa : HasPiType (λ a => Pi₃ (P a))] : V :=
    Pi (λ a => Pi₃ (P a))

  @[reducible] def apply₄ {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''}
                          {P : α → β → γ → δ → V} [∀ a b c, HasPiType (P a b c)]
                          [∀ a b, HasPiType (λ c => Pi (P a b c))]
                          [∀ a, HasPiType (λ b => Pi₂ (P a b))] [HasPiType (λ a => Pi₃ (P a))]
                          (F : Pi₄ P) (a : α) (b : β) (c : γ) (d : δ) : P a b c d :=
    F a b c d

  @[reducible] def defPiType₄ {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''}
                              (P : α → β → γ → δ → V) [∀ a b c, HasPiType (P a b c)]
                              [∀ a b, HasPiType (λ c => Pi (P a b c))]
                              [∀ a, HasPiType (λ b => Pi₂ (P a b))]
                              [HasPiType (λ a => Pi₃ (P a))] :
      DefType V (∀ a b c d, P a b c d) where
    A    := Pi₄ P
    elim := apply₄

  -- Helper classes for the `functoriality` tactic.
  section Helpers

    class IsPiApp {Y : V} (y : Y) where
      {α : Sort u}
      {P : α → V}
      [hP : HasPiType P]
      F : Pi P
      a : α
      codomainEq : P a = Y  -- must be `rfl` for meta code to work correctly

    namespace IsPiApp

      instance (priority := low) refl {α : Sort u} {P : α → V} [HasPiType P] {F : Pi P} {a : α} :
          IsPiApp (F a) :=
        ⟨F, a, rfl⟩

      variable {Y : V} {y : Y} [hApp : IsPiApp.{u} y]

      instance : HasPiType hApp.P := hApp.hP

    end IsPiApp

    class IsPiApp₂ {Y : V} (y : Y) where
      {α : Sort u}
      {β : Sort u'}
      {P : α → β → V}
      [hPa (a : α) : HasPiType (P a)]
      [hPiPa : HasPiType (λ a => Pi (P a))]
      F : Pi₂ P
      a : α
      b : β
      codomainEq : P a b = Y

    namespace IsPiApp₂

      instance (priority := low) refl {α : Sort u} {β : Sort u'} {P : α → β → V}
                                      [∀ a, HasPiType (P a)] [HasPiType (λ a => Pi (P a))]
                                      {F : Pi₂ P} {a : α} {b : β} :
          IsPiApp₂ (F a b) :=
        ⟨F, a, b, rfl⟩

      variable {Y : V} (y : Y) [hApp : IsPiApp₂.{u, u'} y]

      instance (a : hApp.α) : HasPiType (hApp.P a) := hApp.hPa a
      instance : HasPiType (λ a => Pi (hApp.P a)) := hApp.hPiPa

      def isPiApp : IsPiApp y := ⟨hApp.F hApp.a, hApp.b, hApp.codomainEq⟩

    end IsPiApp₂

    class IsPiApp₃ {Y : V} (y : Y) where
      {α : Sort u}
      {β : Sort u'}
      {γ : Sort u''}
      {P : α → β → γ → V}
      [hPab (a : α) (b : β) : HasPiType (P a b)]
      [hPiPab (a : α) : HasPiType (λ b => Pi (P a b))]
      [hPiPa : HasPiType (λ a => Pi₂ (P a))]
      F : Pi₃ P
      a : α
      b : β
      c : γ
      codomainEq : P a b c = Y

    namespace IsPiApp₃

      instance (priority := low) refl {α : Sort u} {β : Sort u'} {γ : Sort u''} {P : α → β → γ → V}
                                      [∀ a b, HasPiType (P a b)]
                                      [∀ a, HasPiType (λ b => Pi (P a b))]
                                      [HasPiType (λ a => Pi₂ (P a))]
                                      {F : Pi₃ P} {a : α} {b : β} {c : γ} :
          IsPiApp₃ (F a b c) :=
        ⟨F, a, b, c, rfl⟩

      variable {Y : V} (y : Y) [hApp : IsPiApp₃.{u, u', u''} y]

      instance (a : hApp.α) (b : hApp.β) : HasPiType (hApp.P a b) := hApp.hPab a b
      instance (a : hApp.α) : HasPiType (λ b => Pi (hApp.P a b)) := hApp.hPiPab a
      instance : HasPiType (λ a => Pi₂ (hApp.P a)) := hApp.hPiPa

      def isPiApp₂ : IsPiApp₂ y := ⟨hApp.F hApp.a, hApp.b, hApp.c, hApp.codomainEq⟩

      def isPiApp : IsPiApp y :=
        let _ : IsPiApp₂ y := isPiApp₂ y
        IsPiApp₂.isPiApp y

    end IsPiApp₃

    class IsPiApp₄ {Y : V} (y : Y) where
      {α : Sort u}
      {β : Sort u'}
      {γ : Sort u''}
      {δ : Sort u'''}
      {P : α → β → γ → δ → V}
      [hPabc (a : α) (b : β) (c : γ) : HasPiType (P a b c)]
      [hPiPabc (a : α) (b : β) : HasPiType (λ c => Pi (P a b c))]
      [hPiPab (a : α) : HasPiType (λ b => Pi₂ (P a b))]
      [hPiPa : HasPiType (λ a => Pi₃ (P a))]
      F : Pi₄ P
      a : α
      b : β
      c : γ
      d : δ
      codomainEq : P a b c d = Y

    namespace IsPiApp₄

      instance (priority := low) refl {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''}
                                      {P : α → β → γ → δ → V} [∀ a b c, HasPiType (P a b c)]
                                      [∀ a b, HasPiType (λ c => Pi (P a b c))]
                                      [∀ a, HasPiType (λ b => Pi₂ (P a b))]
                                      [HasPiType (λ a => Pi₃ (P a))]
                                      {F : Pi₄ P} {a : α} {b : β} {c : γ} {d : δ} :
          IsPiApp₄ (F a b c d) :=
        ⟨F, a, b, c, d, rfl⟩

      variable {Y : V} (y : Y) [hApp : IsPiApp₄.{u, u', u'', u'''} y]

      instance (a : hApp.α) (b : hApp.β) (c : hApp.γ) : HasPiType (hApp.P a b c) := hApp.hPabc a b c
      instance (a : hApp.α) (b : hApp.β) : HasPiType (λ c => Pi (hApp.P a b c)) := hApp.hPiPabc a b
      instance (a : hApp.α) : HasPiType (λ b => Pi₂ (hApp.P a b)) := hApp.hPiPab a
      instance : HasPiType (λ a => Pi₃ (hApp.P a)) := hApp.hPiPa

      def isPiApp₃ : IsPiApp₃ y := ⟨hApp.F hApp.a, hApp.b, hApp.c, hApp.d, hApp.codomainEq⟩

      def isPiApp₂ : IsPiApp₂ y :=
        let _ : IsPiApp₃ y := isPiApp₃ y
        IsPiApp₃.isPiApp₂ y

      def isPiApp : IsPiApp y :=
        let _ : IsPiApp₂ y := isPiApp₂ y
        IsPiApp₂.isPiApp y

    end IsPiApp₄

    class IsPiApp₂' {Y : V} (y : Y) extends IsPiApp.{u} y where
      h₂ : IsPiApp.{u'} y

    class IsPiApp₃' {Y : V} (y : Y) extends IsPiApp₂'.{u, u'} y where
      h₃ : IsPiApp.{u''} y

    class IsPiApp₄' {Y : V} (y : Y) extends IsPiApp₃'.{u, u', u''} y where
      h₄ : IsPiApp.{u'''} y

  end Helpers

  section DefPi

    -- Note: Do dot make this `@[reducible]`. The functoriality tactic needs to be able to determine
    -- whether a given type is an application of `DefPi`.
    def DefPi {α : Sort u} (P : α → V) [h : HasPiType P] (f : ∀ a, P a) :=
      DefType.DefInst h.defPiType f

    namespace DefPi

      variable {α : Sort u} {P : α → V} [h : HasPiType P]

      def mk {f : ∀ a, P a} (F : Pi P) : DefPi P f := ⟨F⟩

      @[reducible] def inst {f : ∀ a, P a} (F : DefPi P f) : Pi P := DefType.DefInst.inst F

      instance coeType (f : ∀ a, P a) : Coe (DefPi P f) (Pi P) :=
        DefType.DefInst.coeType h.defPiType f

      def isPiApp {f : ∀ a, P a} (F : DefPi P f) {a : α} : IsPiApp (f a) := ⟨F, a, rfl⟩

      @[reducible] def cast {f g : ∀ a, P a} (F : DefPi P f) : DefPi P g := DefType.DefInst.cast F

      def defAppPi (F : Pi P) : DefPi P (apply F) := ⟨F⟩

    end DefPi

    -- We could define this as `DefType.DefInst (defPiType₂ P) f` (see `fromDefInst`), but defining
    -- it as a structure has the advantage that the `functoriality` tactic can be implemented
    -- generically for all `DefPiₙ`. Moreover, the nested structure allows us to build derived
    -- functors using simpler building blocks.
    structure DefPi₂ {α : Sort u} {β : Sort u'} (P : α → β → V) [hPa : ∀ a, HasPiType (P a)]
                     [hPiPa : HasPiType (λ a => Pi (P a))] (f : ∀ a b, P a b) where
      app (a : α) : DefPi (P a) (f a)
      toDefPi : DefPi (λ a => Pi (P a)) (λ a => app a)

    namespace DefPi₂

      variable {α : Sort u} {β : Sort u'} {P : α → β → V} [∀ a, HasPiType (P a)]
               [HasPiType (λ a => Pi (P a))]

      def mk' {f : ∀ a b, P a b} (F : Pi₂ P) : DefPi₂ P f :=
        ⟨λ a => DefPi.mk (F a), DefPi.defAppPi F⟩

      @[reducible] def inst {f : ∀ a b, P a b} (F : DefPi₂ P f) : Pi₂ P := F.toDefPi

      instance coeType (f : ∀ a b, P a b) : Coe (DefPi₂ P f) (Pi₂ P) := ⟨inst⟩

      def toDefInst {f : ∀ a b, P a b} (F : DefPi₂ P f) : DefType.DefInst (defPiType₂ P) f :=
        ⟨F.inst⟩

      def fromDefInst {f : ∀ a b, P a b} (F : DefType.DefInst (defPiType₂ P) f) : DefPi₂ P f :=
        ⟨λ a => ⟨F.inst a⟩, DefPi.defAppPi F.inst⟩

      def isPiApp₂ {f : ∀ a b, P a b} (F : DefPi₂ P f) {a : α} {b : β} : IsPiApp₂ (f a b) :=
        ⟨F, a, b, rfl⟩

      def cast {f g : ∀ a b, P a b} (F : DefPi₂ P f) : DefPi₂ P g :=
        ⟨λ a => DefPi.cast (F.app a), F.toDefPi⟩

      def defAppPi (F : Pi₂ P) : DefPi₂ P (apply₂ F) :=
        ⟨λ a => DefPi.defAppPi (F a), DefPi.defAppPi F⟩

    end DefPi₂

    structure DefPi₃ {α : Sort u} {β : Sort u'} {γ : Sort u''} (P : α → β → γ → V)
                     [hPab : ∀ a b, HasPiType (P a b)] [hPiPab : ∀ a, HasPiType (λ b => Pi (P a b))]
                     [hPiPa : HasPiType (λ a => Pi₂ (P a))] (f : ∀ a b c, P a b c) where
      app (a : α) : DefPi₂ (P a) (f a)
      toDefPi : DefPi (λ a => Pi₂ (P a)) (λ a => app a)

    namespace DefPi₃

      variable {α : Sort u} {β : Sort u'} {γ : Sort u''} {P : α → β → γ → V}
               [∀ a b, HasPiType (P a b)] [∀ a, HasPiType (λ b => Pi (P a b))]
               [HasPiType (λ a => Pi₂ (P a))]

      def mk' {f : ∀ a b c, P a b c} (F : Pi₃ P) : DefPi₃ P f :=
        ⟨λ a => DefPi₂.mk' (F a), DefPi.defAppPi F⟩

      @[reducible] def inst {f : ∀ a b c, P a b c} (F : DefPi₃ P f) : Pi₃ P := F.toDefPi

      instance coeType (f : ∀ a b c, P a b c) : Coe (DefPi₃ P f) (Pi₃ P) := ⟨inst⟩

      def toDefInst {f : ∀ a b c, P a b c} (F : DefPi₃ P f) : DefType.DefInst (defPiType₃ P) f :=
        ⟨F.inst⟩

      def fromDefInst {f : ∀ a b c, P a b c} (F : DefType.DefInst (defPiType₃ P) f) : DefPi₃ P f :=
        ⟨λ a => ⟨λ b => ⟨F.inst a b⟩,
                 DefPi.defAppPi (F.inst a)⟩,
         DefPi.defAppPi F.inst⟩

      def toDefPi₂ {f : ∀ a b c, P a b c} (F : DefPi₃ P f) :
          DefPi₂ (λ a b => Pi (P a b)) (λ a b => (F.app a).app b) :=
        ⟨λ a => (F.app a).toDefPi, F.toDefPi⟩

      def isPiApp₃ {f : ∀ a b c, P a b c} (F : DefPi₃ P f) {a : α} {b : β} {c : γ} :
          IsPiApp₃ (f a b c) :=
        ⟨F, a, b, c, rfl⟩

      def cast {f g : ∀ a b c, P a b c} (F : DefPi₃ P f) : DefPi₃ P g :=
        ⟨λ a => DefPi₂.cast (F.app a), F.toDefPi⟩

      def defAppPi (F : Pi₃ P) : DefPi₃ P (apply₃ F) :=
        ⟨λ a => DefPi₂.defAppPi (F a), DefPi.defAppPi F⟩

    end DefPi₃

    structure DefPi₄ {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''}
                     (P : α → β → γ → δ → V) [hPabc : ∀ a b c, HasPiType (P a b c)]
                     [hPiPabc : ∀ a b, HasPiType (λ c => Pi (P a b c))]
                     [hPiPab : ∀ a, HasPiType (λ b => Pi₂ (P a b))]
                     [hPiPa : HasPiType (λ a => Pi₃ (P a))] (f : ∀ a b c d, P a b c d) where
      app (a : α) : DefPi₃ (P a) (f a)
      toDefPi : DefPi (λ a => Pi₃ (P a)) (λ a => app a)

    namespace DefPi₄

      variable {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''} {P : α → β → γ → δ → V}
               [∀ a b c, HasPiType (P a b c)] [∀ a b, HasPiType (λ c => Pi (P a b c))]
               [∀ a, HasPiType (λ b => Pi₂ (P a b))] [HasPiType (λ a => Pi₃ (P a))]

      def mk' {f : ∀ a b c d, P a b c d} (F : Pi₄ P) : DefPi₄ P f :=
        ⟨λ a => DefPi₃.mk' (F a), DefPi.defAppPi F⟩

      @[reducible] def inst {f : ∀ a b c d, P a b c d} (F : DefPi₄ P f) : Pi₄ P := F.toDefPi

      instance coeType (f : ∀ a b c d, P a b c d) : Coe (DefPi₄ P f) (Pi₄ P) := ⟨inst⟩

      def toDefInst {f : ∀ a b c d, P a b c d} (F : DefPi₄ P f) : DefType.DefInst (defPiType₄ P) f :=
        ⟨F.inst⟩

      def fromDefInst {f : ∀ a b c d, P a b c d} (F : DefType.DefInst (defPiType₄ P) f) :
          DefPi₄ P f :=
        ⟨λ a => ⟨λ b => ⟨λ c => ⟨F.inst a b c⟩,
                         DefPi.defAppPi (F.inst a b)⟩,
                 DefPi.defAppPi (F.inst a)⟩,
         DefPi.defAppPi F.inst⟩

      def toDefPi₂ {f : ∀ a b c d, P a b c d} (F : DefPi₄ P f) :
          DefPi₂ (λ a b => Pi₂ (P a b)) (λ a b => (F.app a).app b) :=
        ⟨λ a => (F.app a).toDefPi, F.toDefPi⟩

      def toDefPi₃ {f : ∀ a b c d, P a b c d} (F : DefPi₄ P f) :
          DefPi₃ (λ a b c => Pi (P a b c)) (λ a b c => ((F.app a).app b).app c) :=
        ⟨λ a => (F.app a).toDefPi₂, F.toDefPi⟩

      def isPiApp₄ {f : ∀ a b c d, P a b c d} (F : DefPi₄ P f) {a : α} {b : β} {c : γ} {d : δ} :
          IsPiApp₄ (f a b c d) :=
        ⟨F, a, b, c, d, rfl⟩

      def cast {f g : ∀ a b c d, P a b c d} (F : DefPi₄ P f) : DefPi₄ P g :=
        ⟨λ a => DefPi₃.cast (F.app a), F.toDefPi⟩

      def defAppPi (F : Pi₄ P) : DefPi₄ P (apply₄ F) :=
        ⟨λ a => DefPi₃.defAppPi (F a), DefPi.defAppPi F⟩

    end DefPi₄

  end DefPi

  instance {α : Sort u} (P : α → V) [h : HasPiType P] {β : Sort u'} (b : β) :
    HasPiType ((Function.const β P) b) := h

  instance {α : Sort u} (P : α → V) [h : HasPiType P] {β : Sort u'} (b : β) {γ : Sort u''} (c : γ) :
    HasPiType ((Function.const β (Function.const γ P)) b c) := h

  instance {α : Sort u} (P : α → V) [h : HasPiType P] {β : Sort u'} (b : β) :
    HasPiType (λ a => (Function.const β (P a)) b) := h

  instance {α : Sort u} {β : Sort u'} (P : α → β → V) (a : α) [h : HasPiType (P a)] {γ : Sort u''}
           (c : γ) :
    HasPiType ((Function.const γ P) c a) := h

  instance {α : Sort u} {β : Sort u'} {γ : Sort u''} (P : α → β → γ → V) (a : α) (b : β)
           [h : HasPiType (P a b)] {δ : Sort u'''} (d : δ) :
    HasPiType ((Function.const δ P) d a b) := h

end HasPiType

open HasPiType



class HasFunctors (α : Sort u) {U : Universe.{u}} (Y : U) extends HasPiType (Function.const α Y)

namespace HasFunctors

  variable {U : Universe.{u}}

  section

    instance (α : Sort u) (Y : U) [h : HasFunctors α Y] : HasPiType (λ _ : α => Y) := h.toHasPiType

    instance {α : Sort u} (Y : U) [h : HasFunctors α Y] {β : Sort u'} (b : β) :
        HasFunctors α ((Function.const β Y) b) :=
      h

    instance (α : Sort u) (Y : U) [h : HasFunctors α Y] {β : Sort u'} (f : α → β) :
        HasPiType (λ a => (Function.const β Y) (f a)) :=
      h.toHasPiType

    instance (α : Sort u) (Y : U) [h : HasFunctors α Y] {β : Sort u'} (f : α → β) :
        HasPiType (λ a => (Function.const α (Function.const β Y)) a (f a)) :=
      h.toHasPiType

    instance (α : Sort u) {β : Sort u'} (P : β → U) [HasPiType P] [h : HasFunctors α (Pi P)] :
        HasPiType (λ a => Pi ((Function.const α P) a)) :=
      h.toHasPiType

    instance (α : Sort u) (β : Sort u') (γ : Sort u'') (P : β → γ → U) [∀ b, HasPiType (P b)]
             [HasPiType (λ b => Pi (P b))] [h : HasFunctors α (Pi₂ P)] :
        HasPiType (λ a => Pi₂ ((Function.const α P) a)) :=
      h.toHasPiType

    instance (α : Sort u) (β : Sort u') (γ : Sort u'') (δ : Sort u''') (P : β → γ → δ → U)
             [∀ b c, HasPiType (P b c)] [∀ b, HasPiType (λ c => Pi (P b c))]
             [HasPiType (λ b => Pi₂ (P b))] [h : HasFunctors α (Pi₃ P)] :
        HasPiType (λ a => Pi₃ ((Function.const α P) a)) :=
      h.toHasPiType

    instance {α : Sort u} (P : α → U) [HasPiType P] (a : α) [h : HasFunctors (Pi P) (P a)] :
        HasPiType (λ F => (Function.const (Pi P) P) F a) :=
      h.toHasPiType

    instance {α : Sort u} (P : α → U) [HasPiType P] (a : α) [h : HasFunctors (Pi P) (P a)] :
        HasPiType (λ F => (λ F' a' => Function.const (Pi P) (P a') F') F a) :=
      h.toHasPiType

    @[reducible] def Fun (α : Sort u) (Y : U) [HasFunctors α Y] : U := Pi (Function.const α Y)
    infixr:20 " ⥤ " => HasFunctors.Fun

    @[reducible] def apply {α : Sort u} {Y : U} [HasFunctors α Y] (F : α ⥤ Y) (a : α) : Y :=
      HasPiType.apply F a

    instance coeFun (α : Sort u) (Y : U) [HasFunctors α Y] : CoeFun (α ⥤ Y) (λ _ => α → Y) :=
      ⟨apply⟩

    @[reducible] def apply₂ {α β : Sort u} {Y : U} [HasFunctors β Y] [HasFunctors α (β ⥤ Y)]
                            (F : α ⥤ β ⥤ Y) (a : α) (b : β) : Y :=
      F a b

    @[reducible] def apply₃ {α β γ : Sort u} {Y : U} [HasFunctors γ Y] [HasFunctors β (γ ⥤ Y)]
                            [HasFunctors α (β ⥤ γ ⥤ Y)] (F : α ⥤ β ⥤ γ ⥤ Y) (a : α) (b : β)
                            (c : γ) : Y :=
      F a b c

    @[reducible] def apply₄ {α β γ δ : Sort u} {Y : U} [HasFunctors δ Y] [HasFunctors γ (δ ⥤ Y)]
                            [HasFunctors β (γ ⥤ δ ⥤ Y)] [HasFunctors α (β ⥤ γ ⥤ δ ⥤ Y)]
                            (F : α ⥤ β ⥤ γ ⥤ δ ⥤ Y) (a : α) (b : β) (c : γ) (d : δ) : Y :=
      F a b c d

  end

  -- Helper classes for the `functoriality` tactic.
  section Helpers

    variable {Y : U}

    class IsFunApp (y : Y) where
      {α : Sort u}
      [hα : HasFunctors α Y]
      F : α ⥤ Y
      a : α

    namespace IsFunApp

      instance (priority := low) refl {α : Sort u} [HasFunctors α Y] {F : α ⥤ Y} {a : α} :
          IsFunApp (F a) :=
        ⟨F, a⟩

      variable (y : Y) [hApp : IsFunApp y]

      instance : HasFunctors hApp.α Y := hApp.hα

      def isPiApp : IsPiApp y := ⟨hApp.F, hApp.a, rfl⟩

    end IsFunApp

    class IsFunApp₂ (y : Y) where
      {α β : Sort u}
      [hβ : HasFunctors β Y]
      [hα : HasFunctors α (β ⥤ Y)]
      F : α ⥤ β ⥤ Y
      a : α
      b : β

    namespace IsFunApp₂

      instance (priority := low) refl {α β : Sort u} [HasFunctors β Y] [HasFunctors α (β ⥤ Y)]
                                      {F : α ⥤ β ⥤ Y} {a : α} {b : β} :
          IsFunApp₂ (F a b) :=
        ⟨F, a, b⟩

      variable (y : Y) [hApp : IsFunApp₂ y]

      instance : HasFunctors hApp.β Y := hApp.hβ
      instance : HasFunctors hApp.α (hApp.β ⥤ Y) := hApp.hα

      def isFunApp : IsFunApp y := ⟨hApp.F hApp.a, hApp.b⟩

      def isPiApp₂ : IsPiApp₂ y := ⟨hApp.F, hApp.a, hApp.b, rfl⟩

    end IsFunApp₂

    class IsFunApp₃ (y : Y) where
      {α β γ : Sort u}
      [hγ : HasFunctors γ Y]
      [hβ : HasFunctors β (γ ⥤ Y)]
      [hα : HasFunctors α (β ⥤ γ ⥤ Y)]
      F : α ⥤ β ⥤ γ ⥤ Y
      a : α
      b : β
      c : γ

    namespace IsFunApp₃

      instance (priority := low) refl {α β γ : Sort u} [HasFunctors γ Y] [HasFunctors β (γ ⥤ Y)]
                                      [HasFunctors α (β ⥤ γ ⥤ Y)] {F : α ⥤ β ⥤ γ ⥤ Y} {a : α}
                                      {b : β} {c : γ} :
          IsFunApp₃ (F a b c) :=
        ⟨F, a, b, c⟩

      variable (y : Y) [hApp : IsFunApp₃ y]

      instance : HasFunctors hApp.γ Y := hApp.hγ
      instance : HasFunctors hApp.β (hApp.γ ⥤ Y) := hApp.hβ
      instance : HasFunctors hApp.α (hApp.β ⥤ hApp.γ ⥤ Y) := hApp.hα

      def isFunApp₂ : IsFunApp₂ y := ⟨hApp.F hApp.a, hApp.b, hApp.c⟩

      def isFunApp : IsFunApp y :=
        let _ : IsFunApp₂ y := isFunApp₂ y
        IsFunApp₂.isFunApp y

      def isPiApp₃ : IsPiApp₃ y := ⟨hApp.F, hApp.a, hApp.b, hApp.c, rfl⟩

    end IsFunApp₃

    class IsFunApp₄ (y : Y) where
      {α β γ δ : Sort u}
      [hδ : HasFunctors δ Y]
      [hγ : HasFunctors γ (δ ⥤ Y)]
      [hβ : HasFunctors β (γ ⥤ δ ⥤ Y)]
      [hα : HasFunctors α (β ⥤ γ ⥤ δ ⥤ Y)]
      F : α ⥤ β ⥤ γ ⥤ δ ⥤ Y
      a : α
      b : β
      c : γ
      d : δ

    namespace IsFunApp₄

      instance (priority := low) refl {α β γ δ : Sort u} [HasFunctors δ Y] [HasFunctors γ (δ ⥤ Y)]
                                      [HasFunctors β (γ ⥤ δ ⥤ Y)] [HasFunctors α (β ⥤ γ ⥤ δ ⥤ Y)]
                                      {F : α ⥤ β ⥤ γ ⥤ δ ⥤ Y} {a : α} {b : β} {c : γ} {d : δ} :
          IsFunApp₄ (F a b c d) :=
        ⟨F, a, b, c, d⟩

      variable (y : Y) [hApp : IsFunApp₄ y]

      instance : HasFunctors hApp.δ Y := hApp.hδ
      instance : HasFunctors hApp.γ (hApp.δ ⥤ Y) := hApp.hγ
      instance : HasFunctors hApp.β (hApp.γ ⥤ hApp.δ ⥤ Y) := hApp.hβ
      instance : HasFunctors hApp.α (hApp.β ⥤ hApp.γ ⥤ hApp.δ ⥤ Y) := hApp.hα

      def isFunApp₃ : IsFunApp₃ y := ⟨hApp.F hApp.a, hApp.b, hApp.c, hApp.d⟩

      def isFunApp₂ : IsFunApp₂ y :=
        let _ : IsFunApp₃ y := isFunApp₃ y
        IsFunApp₃.isFunApp₂ y

      def isFunApp : IsFunApp y :=
        let _ : IsFunApp₂ y := isFunApp₂ y
        IsFunApp₂.isFunApp y

      def isPiApp₄ : IsPiApp₄ y := ⟨hApp.F, hApp.a, hApp.b, hApp.c, hApp.d, rfl⟩

    end IsFunApp₄

    class IsFunApp₂' (y : Y) extends IsFunApp y where
      h₂ : IsFunApp y

    namespace IsFunApp₂'

      variable (y : Y) [hApp : IsFunApp₂' y]

      def isPiApp₂' : IsPiApp₂' y where
        toIsPiApp := IsFunApp.isPiApp y
        h₂ := IsFunApp.isPiApp y (hApp := hApp.h₂)

    end IsFunApp₂'

    class IsFunApp₃' (y : Y) extends IsFunApp₂' y where
      h₃ : IsFunApp y

    namespace IsFunApp₃'

      variable (y : Y) [hApp : IsFunApp₃' y]

      def isPiApp₃' : IsPiApp₃' y where
        toIsPiApp₂' := IsFunApp₂'.isPiApp₂' y
        h₃ := IsFunApp.isPiApp y (hApp := hApp.h₃)

    end IsFunApp₃'

    class IsFunApp₄' (y : Y) extends IsFunApp₃' y where
      h₄ : IsFunApp y

    namespace IsFunApp₄'

      variable (y : Y) [hApp : IsFunApp₄' y]

      def isPiApp₄' : IsPiApp₄' y where
        toIsPiApp₃' := IsFunApp₃'.isPiApp₃' y
        h₄ := IsFunApp.isPiApp y (hApp := hApp.h₄)

    end IsFunApp₄'

  end Helpers

  section DefFun

    @[reducible] def DefFun (α : Sort u) (Y : U) [HasFunctors α Y] (f : α → Y) :=
      DefPi (Function.const α Y) f

    namespace DefFun

      notation:20 α:21 " ⥤{" f:0 "} " Y:21 => HasFunctors.DefFun α Y f

      variable {α : Sort u} {Y : U} [h : HasFunctors α Y]

      @[reducible] def mk {f : α → Y} (F : α ⥤ Y) : α ⥤{f} Y := DefPi.mk F

      @[reducible] def inst {f : α → Y} (F : α ⥤{f} Y) : α ⥤ Y := DefPi.inst F

      instance coeType (f : α → Y) : Coe (α ⥤{f} Y) (α ⥤ Y) :=
        DefPi.coeType (P := Function.const α Y) f

      def isFunApp {f : α → Y} (F : α ⥤{f} Y) {a : α} : IsFunApp (f a) := ⟨F, a⟩

      @[reducible] def cast {f g : α → Y} (F : α ⥤{f} Y) : α ⥤{g} Y := DefPi.cast F

      @[reducible] def defAppFun (F : α ⥤ Y) : α ⥤{apply F} Y := DefPi.defAppPi F

    end DefFun

    @[reducible] def DefFun₂ (α β : Sort u) (Y : U) [HasFunctors β Y] [HasFunctors α (β ⥤ Y)]
                             (f : α → β → Y) :=
      DefPi₂ (Function.const α (Function.const β Y)) f

    namespace DefFun₂

      notation:20 α:21 " ⥤ " β:21 " ⥤{" f:0 "} " Y:21 => HasFunctors.DefFun₂ α β Y f

      variable {α β : Sort u} {Y : U} [HasFunctors β Y] [HasFunctors α (β ⥤ Y)]

      @[reducible] def mk {f : α → β → Y} (app : ∀ a, β ⥤{f a} Y)
                          (toDefFun : α ⥤{λ a => app a} (β ⥤ Y)) :
          α ⥤ β ⥤{f} Y :=
        DefPi₂.mk app toDefFun

      @[reducible] def mk' {f : α → β → Y} (F : α ⥤ β ⥤ Y) : α ⥤ β ⥤{f} Y := DefPi₂.mk' F

      @[reducible] def app {f : α → β → Y} (F : α ⥤ β ⥤{f} Y) (a : α) : β ⥤{f a} Y :=
        DefPi₂.app F a

      @[reducible] def toDefFun {f : α → β → Y} (F : α ⥤ β ⥤{f} Y) :
          α ⥤{λ a => F.app a} (β ⥤ Y) :=
        DefPi₂.toDefPi F

      @[reducible] def inst {f : α → β → Y} (F : α ⥤ β ⥤{f} Y) : α ⥤ β ⥤ Y := DefPi₂.inst F

      instance coeType (f : α → β → Y) : Coe (α ⥤ β ⥤{f} Y) (α ⥤ β ⥤ Y) := ⟨inst⟩

      def isFunApp₂ {f : α → β → Y} (F : α ⥤ β ⥤{f} Y) {a : α} {b : β} : IsFunApp₂ (f a b) :=
        ⟨F, a, b⟩

      @[reducible] def cast {f g : α → β → Y} (F : α ⥤ β ⥤{f} Y) : α ⥤ β ⥤{g} Y := DefPi₂.cast F

      @[reducible] def defAppFun (F : α ⥤ β ⥤ Y) : α ⥤ β ⥤{apply₂ F} Y := DefPi₂.defAppPi F

    end DefFun₂

    @[reducible] def DefFun₃ (α β γ : Sort u) (Y : U) [HasFunctors γ Y] [HasFunctors β (γ ⥤ Y)]
                             [HasFunctors α (β ⥤ γ ⥤ Y)] (f : α → β → γ → Y) :=
      DefPi₃ (Function.const α (Function.const β (Function.const γ Y))) f

    namespace DefFun₃

      notation:20 α:21 " ⥤ " β:21 " ⥤ " γ:21 " ⥤{" f:0 "} " Y:21 =>
        HasFunctors.DefFun₃ α β γ Y f

      variable {α β γ : Sort u} {Y : U} [HasFunctors γ Y] [HasFunctors β (γ ⥤ Y)]
               [HasFunctors α (β ⥤ γ ⥤ Y)]

      @[reducible] def mk {f : α → β → γ → Y} (app : ∀ a, β ⥤ γ ⥤{f a} Y)
                          (toDefFun : α ⥤{λ a => app a} (β ⥤ γ ⥤ Y)) :
          α ⥤ β ⥤ γ ⥤{f} Y :=
        DefPi₃.mk app toDefFun

      @[reducible] def mk' {f : α → β → γ → Y} (F : α ⥤ β ⥤ γ ⥤ Y) : α ⥤ β ⥤ γ ⥤{f} Y :=
        DefPi₃.mk' F

      @[reducible] def app {f : α → β → γ → Y} (F : α ⥤ β ⥤ γ ⥤{f} Y) (a : α) : β ⥤ γ ⥤{f a} Y :=
        DefPi₃.app F a

      @[reducible] def toDefFun {f : α → β → γ → Y} (F : α ⥤ β ⥤ γ ⥤{f} Y) :
          α ⥤{λ a => F.app a} (β ⥤ γ ⥤ Y) :=
        DefPi₃.toDefPi F

      @[reducible] def toDefFun₂ {f : α → β → γ → Y} (F : α ⥤ β ⥤ γ ⥤{f} Y) :
          α ⥤ β ⥤{λ a b => (F.app a).app b} (γ ⥤ Y) :=
        DefPi₃.toDefPi₂ F

      @[reducible] def inst {f : α → β → γ → Y} (F : α ⥤ β ⥤ γ ⥤{f} Y) : α ⥤ β ⥤ γ ⥤ Y :=
        DefPi₃.inst F

      instance coeType (f : α → β → γ → Y) : Coe (α ⥤ β ⥤ γ ⥤{f} Y) (α ⥤ β ⥤ γ ⥤ Y) := ⟨inst⟩

      def isFunApp₃ {f : α → β → γ → Y} (F : α ⥤ β ⥤ γ ⥤{f} Y) {a : α} {b : β} {c : γ} :
          IsFunApp₃ (f a b c) :=
        ⟨F, a, b, c⟩

      @[reducible] def cast {f g : α → β → γ → Y} (F : α ⥤ β ⥤ γ ⥤{f} Y) : α ⥤ β ⥤ γ ⥤{g} Y :=
        DefPi₃.cast F

      @[reducible] def defAppFun (F : α ⥤ β ⥤ γ ⥤ Y) : α ⥤ β ⥤ γ ⥤{apply₃ F} Y :=
        DefPi₃.defAppPi F

    end DefFun₃

    @[reducible] def DefFun₄ (α β γ δ : Sort u) (Y : U) [HasFunctors δ Y] [HasFunctors γ (δ ⥤ Y)]
                             [HasFunctors β (γ ⥤ δ ⥤ Y)] [HasFunctors α (β ⥤ γ ⥤ δ ⥤ Y)]
                             (f : α → β → γ → δ → Y) :=
      DefPi₄ (Function.const α (Function.const β (Function.const γ (Function.const δ Y)))) f

    namespace DefFun₄

      notation:20 α:21 " ⥤ " β:21 " ⥤ " γ:21 " ⥤ " δ:21 " ⥤{" f:0 "} " Y:21 =>
        HasFunctors.DefFun₄ α β γ δ Y f

      variable {α β γ δ : Sort u} {Y : U} [HasFunctors δ Y] [HasFunctors γ (δ ⥤ Y)]
               [HasFunctors β (γ ⥤ δ ⥤ Y)] [HasFunctors α (β ⥤ γ ⥤ δ ⥤ Y)]

      @[reducible] def mk {f : α → β → γ → δ → Y} (app : ∀ a, β ⥤ γ ⥤ δ ⥤{f a} Y)
                          (toDefFun : α ⥤{λ a => app a} (β ⥤ γ ⥤ δ ⥤ Y)) :
          α ⥤ β ⥤ γ ⥤ δ ⥤{f} Y :=
        DefPi₄.mk app toDefFun

      @[reducible] def mk' {f : α → β → γ → δ → Y} (F : α ⥤ β ⥤ γ ⥤ δ ⥤ Y) :
          α ⥤ β ⥤ γ ⥤ δ ⥤{f} Y :=
        DefPi₄.mk' F

      @[reducible] def app {f : α → β → γ → δ → Y} (F : α ⥤ β ⥤ γ ⥤ δ ⥤{f} Y)(a : α) :
          β ⥤ γ ⥤ δ ⥤{f a} Y :=
        DefPi₄.app F a

      @[reducible] def toDefFun {f : α → β → γ → δ → Y} (F : α ⥤ β ⥤ γ ⥤ δ ⥤{f} Y) :
          α ⥤{λ a => F.app a} (β ⥤ γ ⥤ δ ⥤ Y) :=
        DefPi₄.toDefPi F

      @[reducible] def toDefFun₂ {f : α → β → γ → δ → Y} (F : α ⥤ β ⥤ γ ⥤ δ ⥤{f} Y) :
          α ⥤ β ⥤{λ a b => (F.app a).app b} (γ ⥤ δ ⥤ Y) :=
        DefPi₄.toDefPi₂ F

      @[reducible] def toDefFun₃ {f : α → β → γ → δ → Y} (F : α ⥤ β ⥤ γ ⥤ δ ⥤{f} Y) :
          α ⥤ β ⥤ γ ⥤{λ a b c => ((F.app a).app b).app c} (δ ⥤ Y) :=
        DefPi₄.toDefPi₃ F

      @[reducible] def inst {f : α → β → γ → δ → Y} (F : α ⥤ β ⥤ γ ⥤ δ ⥤{f} Y) : α ⥤ β ⥤ γ ⥤ δ ⥤ Y :=
        DefPi₄.inst F

      instance coeType (f : α → β → γ → δ → Y) : Coe (α ⥤ β ⥤ γ ⥤ δ ⥤{f} Y) (α ⥤ β ⥤ γ ⥤ δ ⥤ Y) :=
        ⟨inst⟩

      def isFunApp₄ {f : α → β → γ → δ → Y} (F : α ⥤ β ⥤ γ ⥤ δ ⥤{f} Y) {a : α} {b : β} {c : γ} {d : δ} :
          IsFunApp₄ (f a b c d) :=
        ⟨F, a, b, c, d⟩

      @[reducible] def cast {f g : α → β → γ → δ → Y} (F : α ⥤ β ⥤ γ ⥤ δ ⥤{f} Y) : α ⥤ β ⥤ γ ⥤ δ ⥤{g} Y :=
        DefPi₄.cast F

      @[reducible] def defAppFun (F : α ⥤ β ⥤ γ ⥤ δ ⥤ Y) : α ⥤ β ⥤ γ ⥤ δ ⥤{apply₄ F} Y :=
        DefPi₄.defAppPi F

    end DefFun₄

  end DefFun

end HasFunctors

open HasFunctors



class HasUnivFunctors (U V : Universe.{u}) where
  [hFun (A : U) (B : V) : HasFunctors A B]

namespace HasUnivFunctors

  variable {U V : Universe.{u}} [h : HasUnivFunctors U V]

  instance (A : U) (B : V) : HasFunctors A B := h.hFun A B

end HasUnivFunctors



class HasIdFun {U : Universe} (A : U) [HasFunctors A A] where
  defIdFun : A ⥤{id} A

namespace HasIdFun

  section

    variable {U : Universe} (A : U) [HasFunctors A A] [h : HasIdFun A]

    @[reducible] def idFun : A ⥤ A := h.defIdFun

  end

  section

    variable {α : Sort u} {V : Universe} [HasUnivFunctors V V] (P : α → V) [HasPiType P]
             [h : HasIdFun (Pi P)]

    def defAppPi₂ : DefPi₂ (Function.const (Pi P) P) (λ F a => F a) := ⟨DefPi.defAppPi, h.defIdFun⟩

    @[reducible] def appPi₂ : Pi₂ (Function.const (Pi P) P) := defAppPi₂ P

  end

  section

    variable {U : Universe} [HasUnivFunctors U U] (A B : U) [h : HasIdFun (A ⥤ B)]

    def defAppFun₂ : (A ⥤ B) ⥤ A ⥤{λ F a => F a} B := defAppPi₂ (Function.const A B)

    @[reducible] def appFun₂ : (A ⥤ B) ⥤ A ⥤ B := defAppFun₂ A B

  end

end HasIdFun


class HasPiAppFun {α : Sort u} {V : Universe} [HasUnivFunctors V V] (P : α → V) [HasPiType P] where
  defPiAppFun (a : α) : Pi P ⥤{λ F => F a} P a

namespace HasPiAppFun

  section

    variable {α : Sort u} {V : Universe} [HasUnivFunctors V V] (P : α → V) [HasPiType P]
             [h : HasPiAppFun P]

    @[reducible] def piAppFun (a : α) : Pi P ⥤ P a := h.defPiAppFun a

  end

  section

    variable {α : Sort u} (a : α) {U : Universe.{u}} [HasUnivFunctors U U] (B : U) [HasFunctors α B]
             [h : HasPiAppFun (Function.const α B)]

    def defRevAppFun : (α ⥤ B) ⥤{λ F => F a} B := h.defPiAppFun a

    @[reducible] def revAppFun : (α ⥤ B) ⥤ B := defRevAppFun a B

  end

end HasPiAppFun

class HasPiAppFunPi {α : Sort u} {V : Universe} [HasUnivFunctors V V] (P : α → V) [HasPiType P]
                    [HasPiType (λ a => Pi P ⥤ P a)] extends
    HasPiAppFun P where
  defPiAppFunPi : DefPi (λ a => Pi P ⥤ P a) (HasPiAppFun.piAppFun P)

namespace HasPiAppFunPi

  section

    variable {α : Sort u} {V : Universe} [HasUnivFunctors V V] (P : α → V) [HasPiType P]
             [HasPiType (λ a => Pi P ⥤ P a)] [h : HasPiAppFunPi P]

    @[reducible] def piAppFunPi : Pi (λ a => Pi P ⥤ P a) := h.defPiAppFunPi

    instance piAppFun.isPiApp {a : α} : IsPiApp (HasPiAppFun.piAppFun P a) := ⟨piAppFunPi P, a, rfl⟩

  end

  section

    variable (α : Sort u) {U : Universe.{u}} (B : U) [HasFunctors α B] [HasUnivFunctors U U]
             [hααBB : HasFunctors α ((α ⥤ B) ⥤ B)]

    instance : HasPiType (λ a => Pi (Function.const α B) ⥤ (Function.const α B) a) :=
      hααBB.toHasPiType

    variable [h : HasPiAppFunPi (Function.const α B)]

    def defRevAppFun₂ : α ⥤ (α ⥤ B) ⥤{λ a F => F a} B :=
      ⟨λ a => HasPiAppFun.defRevAppFun a B, h.defPiAppFunPi⟩

    @[reducible] def revAppFun₂ : α ⥤ (α ⥤ B) ⥤ B := defRevAppFun₂ α B

    instance revAppFun.isFunApp {a : α} : IsFunApp (HasPiAppFun.revAppFun a B) :=
      ⟨revAppFun₂ α B, a⟩

  end

end HasPiAppFunPi


class HasSwapPi {α : Sort u} {β : Sort u'} {V : Universe} (P : α → β → V) [∀ a, HasPiType (P a)]
                [HasPiType (λ a => Pi (P a))] [∀ b, HasPiType (λ a => P a b)] where
  defSwapPi (F : Pi₂ P) (b : β) : DefPi (λ a => P a b) (λ a => F a b)

namespace HasSwapPi

  section

    variable {α : Sort u} {β : Sort u'} {V : Universe} {P : α → β → V} [∀ a, HasPiType (P a)]
             [HasPiType (λ a => Pi (P a))] [∀ b, HasPiType (λ a => P a b)] [h : HasSwapPi P]

    @[reducible] def swapPi (F : Pi₂ P) (b : β) : Pi (λ a => P a b) := h.defSwapPi F b

    def defSwapDefPi {f : ∀ a b, P a b} (F : DefPi₂ P f) (b : β) :
        DefPi (λ a => P a b) (λ a => f a b) :=
      ⟨swapPi F b⟩

  end

  section

    variable {α : Sort u} {V : Universe} [HasUnivFunctors V V] (P : α → V) [HasPiType P]
             [HasIdFun (Pi P)] [HasSwapPi (Function.const (Pi P) P)]

    instance (priority := low) hasPiAppFun : HasPiAppFun P :=
      ⟨λ a => ⟨swapPi (HasIdFun.appPi₂ P) a⟩⟩

  end

  section

    variable {α β : Sort u} {U : Universe.{u}} {C : U} [HasFunctors β C] [HasFunctors α (β ⥤ C)]
             [HasFunctors α C] [h : HasSwapPi (Function.const α (Function.const β C))]

    def defSwapFun (F : α ⥤ β ⥤ C) (b : β) : α ⥤{λ a => F a b} C := h.defSwapPi F b

    @[reducible] def swapFun (F : α ⥤ β ⥤ C) (b : β) : α ⥤ C := defSwapFun F b

    @[reducible] def revSwapFun (b : β) (F : α ⥤ β ⥤ C) : α ⥤ C := swapFun F b

    def defSwapDefFun {f : α → β → C} (F : α ⥤ β ⥤{f} C) (b : β) : α ⥤{λ a => f a b} C :=
      ⟨swapFun F b⟩

  end

end HasSwapPi

class HasSwapPi₂ {α : Sort u} {β : Sort u'} {V : Universe} (P : α → β → V) [∀ a, HasPiType (P a)]
                 [HasPiType (λ a => Pi (P a))] [∀ b, HasPiType (λ a => P a b)]
                 [HasPiType (λ b => Pi (λ a => P a b))] extends
    HasSwapPi P where
  defSwapPi₂ (F : Pi₂ P) : DefPi (λ b => Pi (λ a => P a b)) (HasSwapPi.swapPi F)

namespace HasSwapPi₂

  section

    variable {α : Sort u} {β : Sort u'} {V : Universe} {P : α → β → V} [∀ a, HasPiType (P a)]
             [HasPiType (λ a => Pi (P a))] [∀ b, HasPiType (λ a => P a b)]
             [HasPiType (λ b => Pi (λ a => P a b))] [h : HasSwapPi₂ P]

    @[reducible] def swapPi₂ (F : Pi₂ P) : Pi₂ (λ b a => P a b) := h.defSwapPi₂ F

    def defSwapPi₂' (F : Pi₂ P) : DefPi₂ (λ b a => P a b) (λ b a => F a b) :=
      ⟨h.defSwapPi F, h.defSwapPi₂ F⟩

    def defSwapDefPi₂ {f : ∀ a b, P a b} (F : DefPi₂ P f) :
        DefPi₂ (λ b a => P a b) (λ b a => f a b) :=
      ⟨HasSwapPi.defSwapDefPi F, ⟨swapPi₂ F⟩⟩

    instance swapPi.isPiApp {F : Pi₂ P} {b : β} : IsPiApp (HasSwapPi.swapPi F b) :=
      ⟨swapPi₂ F, b, rfl⟩

  end

  section

    variable {α : Sort u} {V : Universe} [HasUnivFunctors V V] (P : α → V) [HasPiType P]
             [HasPiType (λ a => Pi P ⥤ P a)] [HasIdFun (Pi P)]
             [HasSwapPi₂ (Function.const (Pi P) P)]

    instance (priority := low) hasPiAppFunPi : HasPiAppFunPi P :=
      ⟨⟨swapPi₂ (P := Function.const (Pi P) P) (HasIdFun.appPi₂ P)⟩⟩

  end

  section

    variable {α β : Sort u} {U : Universe.{u}} {C : U} [HasFunctors β C] [HasFunctors α (β ⥤ C)]
             [HasFunctors α C] [HasFunctors β (α ⥤ C)]
             [h : HasSwapPi₂ (Function.const α (Function.const β C))]

    def defSwapFun₂ (F : α ⥤ β ⥤ C) : β ⥤ α ⥤{λ b a => F a b} C :=
      ⟨HasSwapPi.defSwapFun F, h.defSwapPi₂ F⟩

    @[reducible] def swapFun₂ (F : α ⥤ β ⥤ C) : β ⥤ α ⥤ C := defSwapFun₂ F

    def defSwapDefFun₂ {f : α → β → C} (F : α ⥤ β ⥤{f} C) : β ⥤ α ⥤{λ b a => f a b} C :=
      ⟨HasSwapPi.defSwapDefFun F, ⟨swapFun₂ F⟩⟩

    instance swapFun.isFunApp {F : α ⥤ β ⥤ C} {b : β} : IsFunApp (HasSwapPi.swapFun F b) :=
      ⟨swapFun₂ F, b⟩

  end

end HasSwapPi₂

class HasSwapPiFun {α : Sort u} {β : Sort u'} {V : Universe} [HasUnivFunctors V V] (P : α → β → V)
                   [∀ a, HasPiType (P a)] [HasPiType (λ a => Pi (P a))]
                   [∀ b, HasPiType (λ a => P a b)] [HasPiType (λ b => Pi (λ a => P a b))] extends
    HasSwapPi₂ P where
  defSwapPiFun : Pi₂ P ⥤{HasSwapPi₂.swapPi₂} Pi₂ (λ b a => P a b)

namespace HasSwapPiFun

  section

    variable {α : Sort u} {β : Sort u'} {V : Universe} [HasUnivFunctors V V] (P : α → β → V)
             [∀ a, HasPiType (P a)] [HasPiType (λ a => Pi (P a))] [∀ b, HasPiType (λ a => P a b)]
             [HasPiType (λ b => Pi (λ a => P a b))] [h : HasSwapPiFun P]

    @[reducible] def swapPiFun : Pi₂ P ⥤ Pi₂ (λ b a => P a b) := h.defSwapPiFun

    instance swapPi₂.isFunApp {F : Pi₂ P} : IsFunApp (HasSwapPi₂.swapPi₂ F) :=
      ⟨swapPiFun P, F⟩

  end

  section

    variable (α β : Sort u) {U : Universe.{u}} [HasUnivFunctors U U] (C : U) [HasFunctors β C]
             [HasFunctors α (β ⥤ C)] [HasFunctors α C] [HasFunctors β (α ⥤ C)]
             [h : HasSwapPiFun (Function.const α (Function.const β C))]

    def defSwapFun₃ : (α ⥤ β ⥤ C) ⥤ β ⥤ α ⥤{λ F b a => F a b} C :=
      ⟨HasSwapPi₂.defSwapFun₂, h.defSwapPiFun⟩

    @[reducible] def swapFun₃ : (α ⥤ β ⥤ C) ⥤ (β ⥤ α ⥤ C) := defSwapFun₃ α β C

    instance swapFun₂.isFunApp {F : α ⥤ β ⥤ C} : IsFunApp (HasSwapPi₂.swapFun₂ F) :=
      ⟨swapFun₃ α β C, F⟩

  end

end HasSwapPiFun


class HasCompFunPi (α : Sort u) {V : Universe.{u}} {W : Universe} {B : V} [HasFunctors α B]
                   (Q : B → W) [HasPiType Q] [∀ F : α ⥤ B, HasPiType (λ a => Q (F a))] where
  defCompFunPi (F : α ⥤ B) (G : Pi Q) : DefPi (λ a => Q (F a)) (λ a => G (F a))

namespace HasCompFunPi

  section

    variable {α : Sort u} {V : Universe.{u}} {W : Universe} {B : V} [HasFunctors α B] {Q : B → W}
             [HasPiType Q] [∀ F : α ⥤ B, HasPiType (λ a => Q (F a))] [h : HasCompFunPi α Q]

    @[reducible] def compFunPi (F : α ⥤ B) (G : Pi Q) : Pi (λ a => Q (F a)) := h.defCompFunPi F G

    @[reducible] def revCompFunPi (G : Pi Q) (F : α ⥤ B) : Pi (λ a => Q (F a)) := compFunPi F G

    def defCompFunDefPi (F : α ⥤ B) {g : ∀ b, Q b} (G : DefPi Q g) :
        DefPi (λ a => Q (F a)) (λ a => g (F a)) :=
      ⟨compFunPi F G⟩

  end

  section

    variable {α : Sort u} {V W : Universe.{u}} {B : V} [HasFunctors α B] {C : W} [HasFunctors B C]
             [HasFunctors α C] [h : HasCompFunPi α (Function.const B C)]

    def defCompFun (F : α ⥤ B) (G : B ⥤ C) : α ⥤{λ a => G (F a)} C := h.defCompFunPi F G

    @[reducible] def compFun (F : α ⥤ B) (G : B ⥤ C) : α ⥤ C := defCompFun F G

    @[reducible] def revCompFun (G : B ⥤ C) (F : α ⥤ B) : α ⥤ C := compFun F G
    infixr:90 " ⊙ " => HasCompFunPi.revCompFun

    def defCompFunDefFun (F : α ⥤ B) {g : B → C} (G : B ⥤{g} C) : α ⥤{λ a => g (F a)} C :=
      ⟨compFun F G⟩

    def defCompDefFunFun {f : α → B} (F : α ⥤{f} B) (G : B ⥤ C) : α ⥤{λ a => G (f a)} C :=
      ⟨compFun F G⟩

    def defCompDefFun {f : α → B} (F : α ⥤{f} B) {g : B → C} (G : B ⥤{g} C) :
        α ⥤{λ a => g (f a)} C :=
      ⟨compFun (B := B) F G⟩

  end

end HasCompFunPi

class HasRevCompFunPi₂ (α : Sort u) {V : Universe.{u}} {W : Universe} {B : V} [HasFunctors α B]
                       (Q : B → W) [HasPiType Q] [∀ F : α ⥤ B, HasPiType (λ a => Q (F a))]
                       [HasPiType (λ F : α ⥤ B => Pi (λ a => Q (F a)))] extends
    HasCompFunPi α Q where
  defRevCompFunPi₂ (G : Pi Q) :
    DefPi (λ F : α ⥤ B => Pi (λ a => Q (F a))) (HasCompFunPi.revCompFunPi G)

namespace HasRevCompFunPi₂

  section

    variable (α : Sort u) {V : Universe.{u}} {W : Universe} {B : V} [HasFunctors α B] {Q : B → W}
             [HasPiType Q] [∀ F : α ⥤ B, HasPiType (λ a => Q (F a))]
             [HasPiType (λ F : α ⥤ B => Pi (λ a => Q (F a)))] [h : HasRevCompFunPi₂ α Q]

    @[reducible] def revCompFunPi₂ (G : Pi Q) : Pi₂ (λ (F : α ⥤ B) a => Q (F a)) :=
      h.defRevCompFunPi₂ G

    def defRevCompFunDefPi₂ {g : ∀ b, Q b} (G : DefPi Q g) :
        DefPi₂ (λ (F : α ⥤ B) a => Q (F a)) (λ F a => g (F a)) :=
      ⟨λ F => HasCompFunPi.defCompFunDefPi F G, ⟨revCompFunPi₂ α G⟩⟩

    instance revCompFunPi.isPiApp {G : Pi Q} {F : α ⥤ B} :
        IsPiApp (HasCompFunPi.revCompFunPi G F) :=
      ⟨revCompFunPi₂ α G, F, rfl⟩

  end

  section

    variable (α : Sort u) {V W : Universe.{u}} [HasUnivFunctors V W] {B : V} [HasFunctors α B]
             {C : W} [HasFunctors α C] [h : HasRevCompFunPi₂ α (Function.const B C)]

    def defRevCompFun₂ (G : B ⥤ C) : (α ⥤ B) ⥤ α ⥤{λ F a => G (F a)} C :=
      ⟨λ F => HasCompFunPi.defCompFun F G, h.defRevCompFunPi₂ G⟩

    @[reducible] def revCompFun₂ (G : B ⥤ C) : (α ⥤ B) ⥤ (α ⥤ C) := defRevCompFun₂ α G

    def defRevCompDefFun₂ {g : B → C} (G : B ⥤{g} C) : (α ⥤ B) ⥤ α ⥤{λ F a => g (F a)} C :=
      ⟨λ F => HasCompFunPi.defCompFunDefFun F G, ⟨revCompFun₂ α G⟩⟩

    instance revCompFun.isFunApp {G : B ⥤ C} {F : α ⥤ B} :
        IsFunApp (HasCompFunPi.revCompFun G F) :=
      ⟨revCompFun₂ α G, F⟩

  end

end HasRevCompFunPi₂

class HasRevCompFunPiFun (α : Sort u) {V : Universe.{u}} {W : Universe} [HasUnivFunctors W W]
                         {B : V} [HasFunctors α B] (Q : B → W) [HasPiType Q]
                         [∀ F : α ⥤ B, HasPiType (λ a => Q (F a))]
                         [HasPiType (λ F : α ⥤ B => Pi (λ a => Q (F a)))] extends
    HasRevCompFunPi₂ α Q where
  defRevCompFunPiFun : Pi Q ⥤{HasRevCompFunPi₂.revCompFunPi₂ α} Pi₂ (λ (F : α ⥤ B) a => Q (F a))

namespace HasRevCompFunPiFun

  section

    variable (α : Sort u) {V : Universe.{u}} {W : Universe} [HasUnivFunctors W W] {B : V}
             [HasFunctors α B] (Q : B → W) [HasPiType Q] [∀ F : α ⥤ B, HasPiType (λ a => Q (F a))]
             [HasPiType (λ F : α ⥤ B => Pi (λ a => Q (F a)))] [h : HasRevCompFunPiFun α Q]

    @[reducible] def revCompFunPiFun : Pi Q ⥤ Pi₂ (λ (F : α ⥤ B) a => Q (F a)) :=
      h.defRevCompFunPiFun

    instance revCompFunPi₂.isFunApp {G : Pi Q} : IsFunApp (HasRevCompFunPi₂.revCompFunPi₂ α G) :=
      ⟨revCompFunPiFun α Q, G⟩

    instance revCompFunPi.isPiApp₂ {G : Pi Q} {F : α ⥤ B} :
        IsPiApp₂ (HasCompFunPi.revCompFunPi G F) :=
      ⟨revCompFunPiFun α Q, G, F, rfl⟩

  end

  section

    variable {α : Sort u} {V W : Universe.{u}} [HasUnivFunctors V W]
             [hW : HasUnivFunctors W W] {B : V} [HasFunctors α B] (F : α ⥤ B) (Q : B → W)
             [HasPiType Q] [∀ F : α ⥤ B, HasPiType (λ a => Q (F a))]
             [HasPiType (λ F : α ⥤ B => Pi (λ a => Q (F a)))] [HasRevCompFunPiFun α Q]

    instance : HasPiType (λ G => (Function.const (Pi Q) (λ F' => Pi (λ a => Q (F' a)))) G F) :=
      (hW.hFun (Pi Q) (Pi (λ a => Q (F a)))).toHasPiType

    variable [HasSwapPi (Function.const (Pi Q) (λ F : α ⥤ B => Pi (λ a => Q (F a))))]

    def compFunPiFun : Pi Q ⥤ Pi (λ a => Q (F a)) :=
      HasSwapPi.swapPi (P := Function.const (Pi Q) (λ F : α ⥤ B => Pi (λ a => Q (F a))))
                       (revCompFunPiFun α Q) F

    instance compFunPi.isPiApp₂' {G : Pi Q} : IsPiApp₂' (HasCompFunPi.compFunPi F G) :=
      ⟨⟨compFunPiFun F Q, G, rfl⟩⟩

  end

  section

    variable (α : Sort u) {V W : Universe.{u}} [HasUnivFunctors V W] [HasUnivFunctors W W]
             {B : V} [HasFunctors α B] (Q : B → W) [HasPiType Q]
             [∀ F : α ⥤ B, HasPiType (λ a => Q (F a))]
             [HasPiType (λ F : α ⥤ B => Pi (λ a => Q (F a)))] [HasRevCompFunPiFun α Q]
             [HasPiType (λ F : α ⥤ B => (Pi Q ⥤ Pi (λ a => Q (F a))))]
             [HasSwapPi₂ (Function.const (Pi Q) (λ F : α ⥤ B => Pi (λ a => Q (F a))))]

    def compFunPiFunPi : Pi (λ F : α ⥤ B => (Pi Q ⥤ Pi (λ a => Q (F a)))) :=
      HasSwapPi₂.swapPi₂ (P := Function.const (Pi Q) (λ F : α ⥤ B => Pi (λ a => Q (F a))))
                         (revCompFunPiFun α Q)

    instance compFunPiFun.isPiApp {F : α ⥤ B} : IsPiApp (compFunPiFun F Q) :=
      ⟨compFunPiFunPi α Q, F, rfl⟩

  end

  section

    variable (α : Sort u) {V W : Universe.{u}} [HasUnivFunctors V W] [HasUnivFunctors W W] (B : V)
             [HasFunctors α B] (C : W) [HasFunctors α C]
             [h : HasRevCompFunPiFun α (Function.const B C)]

    def defRevCompFun₃ : (B ⥤ C) ⥤ (α ⥤ B) ⥤ α ⥤{λ G F a => G (F a)} C :=
      ⟨λ G => HasRevCompFunPi₂.defRevCompFun₂ α G, h.defRevCompFunPiFun⟩

    @[reducible] def revCompFun₃ : (B ⥤ C) ⥤ (α ⥤ B) ⥤ (α ⥤ C) := defRevCompFun₃ α B C

    instance revCompFun₂.isFunApp {G : B ⥤ C} : IsFunApp (HasRevCompFunPi₂.revCompFun₂ α G) :=
      ⟨revCompFun₃ α B C, G⟩

    instance revCompFun.isFunApp₂ {G : B ⥤ C} {F : α ⥤ B} : IsFunApp₂ (G ⊙ F) :=
      ⟨revCompFun₃ α B C, G, F⟩

  end

  section

    variable {α : Sort u} {V W : Universe.{u}} [HasUnivFunctors V W] [HasUnivFunctors W W] {B : V}
             [HasFunctors α B] (F : α ⥤ B) (C : W) [HasFunctors α C]
             [h : HasRevCompFunPiFun α (Function.const B C)]
             [HasSwapPi (Function.const (B ⥤ C) (Function.const (α ⥤ B) (α ⥤ C)))]

    def defCompFun₂ : (B ⥤ C) ⥤ α ⥤{λ G a => G (F a)} C :=
      ⟨λ G => HasCompFunPi.defCompFun F G, ⟨HasSwapPi.swapFun (revCompFun₃ α B C) F⟩⟩

    @[reducible] def compFun₂ : (B ⥤ C) ⥤ (α ⥤ C) := defCompFun₂ F C

    instance compFun.isFunApp₂' {G : B ⥤ C} : IsFunApp₂' (HasCompFunPi.compFun F G) :=
      ⟨⟨compFun₂ F C, G⟩⟩

  end

  section

    variable (α : Sort u) {V W : Universe.{u}} [HasUnivFunctors V W] [HasUnivFunctors W W] (B : V)
             [HasFunctors α B] (C : W) [HasFunctors α C] [HasRevCompFunPiFun α (Function.const B C)]
             [HasSwapPi₂ (Function.const (B ⥤ C) (Function.const (α ⥤ B) (α ⥤ C)))]

    def defCompFun₃ : (α ⥤ B) ⥤ (B ⥤ C) ⥤ α ⥤{λ F G a => G (F a)} C :=
      ⟨λ F => defCompFun₂ F C, ⟨HasSwapPi₂.swapFun₂ (revCompFun₃ α B C)⟩⟩

    @[reducible] def compFun₃ : (α ⥤ B) ⥤ (B ⥤ C) ⥤ (α ⥤ C) := defCompFun₃ α B C

    instance compFun₂.isFunApp {F : α ⥤ B} : IsFunApp (compFun₂ F C) := ⟨compFun₃ α B C, F⟩

  end

end HasRevCompFunPiFun


class HasConstPi (α : Sort u) {V : Universe} (B : V) [HasPiType (Function.const α B)] where
  defConstPi (b : B) : DefPi (Function.const α B) (Function.const α b)

namespace HasConstPi

  section

    variable (α : Sort u) {V : Universe} {B : V} [HasPiType (Function.const α B)]
             [h : HasConstPi α B]

    @[reducible] def constPi (b : B) : Pi (Function.const α B) := h.defConstPi b

  end

  section

    variable (α : Sort u) {U : Universe.{u}} {B : U} [HasFunctors α B] [h : HasConstPi α B]

    def defConstFun (b : B) : α ⥤{Function.const α b} B := h.defConstPi b

    @[reducible] def constFun (b : B) : α ⥤ B := defConstFun α b

  end

  section

    variable (α β : Sort u) {U : Universe.{u}} {C : U} [HasFunctors β C] [HasFunctors α (β ⥤ C)]
             [h₁ : HasConstPi β C] [h₂ : HasConstPi α (β ⥤ C)]

    def defConstFun₂ (c : C) : α ⥤ β ⥤{Function.const α (Function.const β c)} C :=
      ⟨λ _ => h₁.defConstPi c, h₂.defConstPi (constFun β c)⟩

    @[reducible] def constFun₂ (c : C) : α ⥤ β ⥤ C := defConstFun₂ α β c

  end

end HasConstPi

class HasConstPiFun (α : Sort u) {V : Universe} [HasUnivFunctors V V] (B : V)
                    [HasPiType (Function.const α B)] extends
    HasConstPi α B where
  defConstPiFun : B ⥤{HasConstPi.constPi α} Pi (Function.const α B)

namespace HasConstPiFun

  section

    variable (α : Sort u) {V : Universe} [HasUnivFunctors V V] (B : V)
             [HasPiType (Function.const α B)] [h : HasConstPiFun α B]

    @[reducible] def constPiFun : B ⥤ Pi (Function.const α B) := h.defConstPiFun

    instance constPi.isFunApp {b : B} : IsFunApp (HasConstPi.constPi α b) := ⟨constPiFun α B, b⟩

  end

  section

    variable (α : Sort u) {U : Universe.{u}} [HasUnivFunctors U U] (B : U) [HasFunctors α B]
             [h : HasConstPiFun α B]

    def defConstFun₂ : B ⥤ α ⥤{λ b _ => b} B :=
      ⟨λ b => HasConstPi.defConstFun α b, h.defConstPiFun⟩

    @[reducible] def constFun₂ : B ⥤ (α ⥤ B) := defConstFun₂ α B

    instance constFun.isFunApp {b : B} : IsFunApp (HasConstPi.constFun α b) := ⟨constFun₂ α B, b⟩

  end

end HasConstPiFun


class HasDupPi {α : Sort u} {V : Universe} (P : α → α → V) [∀ a, HasPiType (P a)]
               [HasPiType (λ a => Pi (P a))] [HasPiType (λ a => P a a)] where
  defDupPi (F : Pi₂ P) : DefPi (λ a => P a a) (λ a => F a a)

namespace HasDupPi

  section

    variable {α : Sort u} {V : Universe} {P : α → α → V} [∀ a, HasPiType (P a)]
             [HasPiType (λ a => Pi (P a))] [HasPiType (λ a => P a a)] [h : HasDupPi P]

    @[reducible] def dupPi (F : Pi₂ P) : Pi (λ a => P a a) := h.defDupPi F

    def defDupDefPi {f : ∀ a a', P a a'} (F : DefPi₂ P f) : DefPi (λ a => P a a) (λ a => f a a) :=
      ⟨dupPi F⟩

  end

  section

    variable {α : Sort u} {U : Universe.{u}} {B : U} [HasFunctors α B] [HasFunctors α (α ⥤ B)]
             [h : HasDupPi (Function.const α (Function.const α B))]

    def defDupFun (F : α ⥤ α ⥤ B) : α ⥤{λ a => F a a} B := h.defDupPi F

    @[reducible] def dupFun (F : α ⥤ α ⥤ B) : α ⥤ B := defDupFun F

    def defDupDefFun {f : α → α → B} (F : α ⥤ α ⥤{f} B) : α ⥤{λ a => f a a} B := ⟨dupFun F⟩

  end

end HasDupPi

class HasDupPiFun {α : Sort u} {V : Universe} [HasUnivFunctors V V] (P : α → α → V)
                  [∀ a, HasPiType (P a)] [HasPiType (λ a => Pi (P a))] [HasPiType (λ a => P a a)]
                  extends
    HasDupPi P where
  defDupPiFun : Pi₂ P ⥤{HasDupPi.dupPi} Pi (λ a => P a a)

namespace HasDupPiFun

  section

    variable {α : Sort u} {V : Universe} [HasUnivFunctors V V] (P : α → α → V)
             [∀ a, HasPiType (P a)] [HasPiType (λ a => Pi (P a))] [HasPiType (λ a => P a a)]
             [h : HasDupPiFun P]

    @[reducible] def dupPiFun : Pi₂ P ⥤ Pi (λ a => P a a) := h.defDupPiFun

    instance dupPi.isFunApp {F : Pi₂ P} : IsFunApp (HasDupPi.dupPi F) :=
      ⟨dupPiFun P, F⟩

  end

  section

    variable (α : Sort u) {U : Universe.{u}} [HasUnivFunctors U U] (B : U) [HasFunctors α B]
             [HasFunctors α (α ⥤ B)] [h : HasDupPiFun (Function.const α (Function.const α B))]

    def defDupFun₂ : (α ⥤ α ⥤ B) ⥤ α ⥤{λ F a => F a a} B :=
      ⟨λ F => HasDupPi.defDupFun F, h.defDupPiFun⟩

    @[reducible] def dupFun₂ : (α ⥤ α ⥤ B) ⥤ (α ⥤ B) := defDupFun₂ α B

    instance dupFun.isFunApp {F : α ⥤ α ⥤ B} : IsFunApp (HasDupPi.dupFun F) :=
      ⟨dupFun₂ α B, F⟩

  end

end HasDupPiFun


class HasPiSelfAppPi {U V : Universe.{u}} [HasUnivFunctors V U] {A : U} (Q : A → V) [HasPiType Q]
                     [∀ F : Pi Q ⥤ A, HasPiType (λ G => Q (F G))] where
  defPiSelfAppPi (F : Pi Q ⥤ A) : DefPi (λ G => Q (F G)) (λ G => G (F G))

namespace HasPiSelfAppPi

  section

    variable {U V : Universe.{u}} [HasUnivFunctors V U] {A : U} {Q : A → V} [HasPiType Q]
             [∀ F : Pi Q ⥤ A, HasPiType (λ G => Q (F G))] [h : HasPiSelfAppPi Q]

    @[reducible] def piSelfAppPi (F : Pi Q ⥤ A) : Pi (λ G => Q (F G)) := h.defPiSelfAppPi F

  end

  section

    variable {U V : Universe.{u}} [HasUnivFunctors V U] {A : U} {B : V} [HasFunctors A B]
             [HasFunctors (A ⥤ B) B] [h : HasPiSelfAppPi (Function.const A B)]

    def defRevSelfAppFun (F : (A ⥤ B) ⥤ A) : (A ⥤ B) ⥤{λ G => G (F G)} B := h.defPiSelfAppPi F

    @[reducible] def revSelfAppFun (F : (A ⥤ B) ⥤ A) : (A ⥤ B) ⥤ B := defRevSelfAppFun F

  end

end HasPiSelfAppPi

class HasPiSelfAppPi₂ {U V : Universe.{u}} [HasUnivFunctors V U] {A : U} (Q : A → V) [HasPiType Q]
                      [∀ F : Pi Q ⥤ A, HasPiType (λ G => Q (F G))]
                      [HasPiType (λ (F : Pi Q ⥤ A) => Pi (λ G => Q (F G)))] extends
    HasPiSelfAppPi Q where
  defPiSelfAppPi₂ : DefPi (λ (F : Pi Q ⥤ A) => Pi (λ G => Q (F G))) HasPiSelfAppPi.piSelfAppPi

namespace HasPiSelfAppPi₂

  section

    variable {U V : Universe.{u}} [HasUnivFunctors V U] {A : U} (Q : A → V) [HasPiType Q]
             [∀ F : Pi Q ⥤ A, HasPiType (λ G => Q (F G))]
             [HasPiType (λ (F : Pi Q ⥤ A) => Pi (λ G => Q (F G)))] [h : HasPiSelfAppPi₂ Q]

    @[reducible] def piSelfAppPi₂ : Pi₂ (λ (F : Pi Q ⥤ A) G => Q (F G)) := h.defPiSelfAppPi₂

    instance revSelfAppFun.isPiApp {F : Pi Q ⥤ A} : IsPiApp (HasPiSelfAppPi.piSelfAppPi F) :=
      ⟨piSelfAppPi₂ Q, F, rfl⟩

  end

  section

    variable {U V : Universe.{u}} [HasUnivFunctors U V] [HasUnivFunctors V U]
             [HasUnivFunctors V V] (A : U) (B : V) [h : HasPiSelfAppPi₂ (Function.const A B)]

    def defRevSelfAppFun₂ : ((A ⥤ B) ⥤ A) ⥤ (A ⥤ B) ⥤{λ F G => G (F G)} B :=
      ⟨λ F => HasPiSelfAppPi.defRevSelfAppFun F, h.defPiSelfAppPi₂⟩

    @[reducible] def revSelfAppFun₂ : ((A ⥤ B) ⥤ A) ⥤ (A ⥤ B) ⥤ B := defRevSelfAppFun₂ A B

    instance revSelfAppFun.isFunApp {F : (A ⥤ B) ⥤ A} :
        IsFunApp (HasPiSelfAppPi.revSelfAppFun F) :=
      ⟨revSelfAppFun₂ A B, F⟩

  end

end HasPiSelfAppPi₂


class HasSubstPi {α : Sort u} {V W : Universe} {P : α → V} [HasPiType P] (Q : ∀ a, P a → W)
                 [∀ a, HasPiType (Q a)] [HasPiType (λ a => Pi (Q a))]
                 [∀ F : Pi P, HasPiType (λ a => Q a (F a))] where
  defSubstPi (F : Pi P) (G : Pi (λ a => Pi (Q a))) : DefPi (λ a => Q a (F a)) (λ a => G a (F a))

namespace HasSubstPi

  section

    variable {α : Sort u} {V W : Universe} {P : α → V} [HasPiType P] {Q : ∀ a, P a → W}
             [∀ a, HasPiType (Q a)] [HasPiType (λ a => Pi (Q a))]
             [∀ F : Pi P, HasPiType (λ a => Q a (F a))] [h : HasSubstPi Q]

    @[reducible] def substPi (F : Pi P) (G : Pi (λ a => Pi (Q a))) : Pi (λ a => Q a (F a)) :=
      h.defSubstPi F G

    @[reducible] def revSubstPi (G : Pi (λ a => Pi (Q a))) (F : Pi P) : Pi (λ a => Q a (F a)) :=
      substPi F G

  end

  -- We can use `HasSubstPi` to implement `HasCompFunPi` and `HasPiSelfAppPi`, but if we also wanted
  -- to implement `HasSwapPi` and `HasDupPi`, we would need to define a type class to cast
  -- individual `Pi` instances whose properties contain functors.
  -- (We could implement it for functors instead of arbitrary Π types, though.)

  section

    variable (α : Sort u) {V : Universe.{u}} {W : Universe} {B : V} [HasFunctors α B]
             (Q : B → W) [HasPiType Q] [hQ : ∀ F : α ⥤ B, HasPiType (λ a => Q (F a))]
             [hPiQ : HasPiType (Function.const α (Pi Q))]

    instance : HasPiType (λ a => Pi ((Function.const α Q) a)) := hPiQ
    instance (F : α ⥤ B) : HasPiType (λ a => (Function.const α Q) a (F a)) := hQ F

    variable [HasSubstPi (P := Function.const α B) (Function.const α Q)] [HasConstPi α (Pi Q)]

    instance (priority := low) hasCompFunPi : HasCompFunPi α Q :=
      ⟨λ F G => ⟨substPi (Q := Function.const α Q) F (HasConstPi.constPi α G)⟩⟩

  end

  section

    variable {U V : Universe.{u}} [HasUnivFunctors V U] [HasUnivFunctors V V] {A : U} (Q : A → V)
             [HasPiType Q] [∀ F : Pi Q ⥤ A, HasPiType (λ G => Q (F G))]
             [hSubst : HasSubstPi (Function.const (Pi Q) Q)] [HasIdFun (Pi Q)]

    instance : HasSubstPi (λ _ : Pi Q => Q) := hSubst

    instance (priority := low) hasPiSelfAppPi : HasPiSelfAppPi Q :=
      ⟨λ F => ⟨substPi F (HasIdFun.idFun (Pi Q))⟩⟩

  end

  section

    variable {α : Sort u} {V W : Universe.{u}} {B : V} [HasFunctors α B] {C : W} [HasFunctors B C]
             [HasFunctors α (B ⥤ C)] [HasFunctors α C]
             [h : HasSubstPi (Function.const α (Function.const B C))]

    def defSubstFun (F : α ⥤ B) (G : α ⥤ B ⥤ C) : α ⥤{λ a => G a (F a)} C := h.defSubstPi F G

    @[reducible] def substFun (F : α ⥤ B) (G : α ⥤ B ⥤ C) : α ⥤ C := defSubstFun F G

    @[reducible] def revSubstFun (G : α ⥤ B ⥤ C) (F : α ⥤ B) : α ⥤ C := substFun F G

  end

end HasSubstPi

class HasRevSubstPi₂ {α : Sort u} {V W : Universe} {P : α → V} [HasPiType P] (Q : ∀ a, P a → W)
                     [∀ a, HasPiType (Q a)] [HasPiType (λ a => Pi (Q a))]
                     [∀ F : Pi P, HasPiType (λ a => Q a (F a))]
                     [HasPiType (λ F : Pi P => Pi (λ a => Q a (F a)))] extends
    HasSubstPi Q where
  defRevSubstPi₂ (G : Pi (λ a => Pi (Q a))) :
    DefPi (λ F : Pi P => Pi (λ a => Q a (F a))) (HasSubstPi.revSubstPi G)

namespace HasRevSubstPi₂

  section

    variable {α : Sort u} {V W : Universe} {P : α → V} [HasPiType P] {Q : ∀ a, P a → W}
             [∀ a, HasPiType (Q a)] [HasPiType (λ a => Pi (Q a))]
             [∀ F : Pi P, HasPiType (λ a => Q a (F a))]
             [HasPiType (λ F : Pi P => Pi (λ a => Q a (F a)))] [h : HasRevSubstPi₂ Q]

    @[reducible] def revSubstPi₂ (G : Pi (λ a => Pi (Q a))) : Pi₂ (λ (F : Pi P) a => Q a (F a)) :=
      h.defRevSubstPi₂ G

    instance revSubstPi.isPiApp {F : Pi P} {G : Pi (λ a => Pi (Q a))} :
        IsPiApp (HasSubstPi.revSubstPi G F) :=
      ⟨revSubstPi₂ G, F, rfl⟩

  end

  section

    variable (α : Sort u) {V : Universe.{u}} {W : Universe} {B : V} [HasFunctors α B]
             (Q : B → W) [HasPiType Q] [∀ F : α ⥤ B, HasPiType (λ a => Q (F a))]
             [HasPiType (λ F : α ⥤ B => Pi (λ a => Q (F a)))] [HasPiType (Function.const α (Pi Q))]
             [HasRevSubstPi₂ (P := Function.const α B) (Function.const α Q)] [HasConstPi α (Pi Q)]

    instance (priority := low) hasRevCompFunPi₂ : HasRevCompFunPi₂ α Q :=
      ⟨λ G => ⟨revSubstPi₂ (Q := Function.const α Q) (HasConstPi.constPi α G)⟩⟩

  end

  section

    variable {U V : Universe.{u}} [HasUnivFunctors V U] [HasUnivFunctors V V] {A : U} (Q : A → V)
             [HasPiType Q] [∀ F : Pi Q ⥤ A, HasPiType (λ G => Q (F G))]
             [HasPiType (λ (F : Pi Q ⥤ A) => Pi (λ G => Q (F G)))]
             [hRevSubst₂ : HasRevSubstPi₂ (Function.const (Pi Q) Q)] [HasIdFun (Pi Q)]

    instance : HasRevSubstPi₂ (λ _ : Pi Q => Q) := hRevSubst₂

    instance (priority := low) hasPiSelfAppPi₂ : HasPiSelfAppPi₂ Q :=
      ⟨⟨revSubstPi₂ (HasIdFun.idFun (Pi Q))⟩⟩

  end

  section

    variable {α : Sort u} {V W : Universe.{u}} [HasUnivFunctors V W] {B : V} [HasFunctors α B]
             {C : W} [HasFunctors α (B ⥤ C)] [HasFunctors α C]
             [h : HasRevSubstPi₂ (Function.const α (Function.const B C))]

    def defRevSubstFun₂ (G : α ⥤ B ⥤ C) : (α ⥤ B) ⥤ α ⥤{λ F a => G a (F a)} C :=
      ⟨λ F => HasSubstPi.defSubstFun F G, h.defRevSubstPi₂ G⟩

    @[reducible] def revSubstFun₂ (G : α ⥤ B ⥤ C) : (α ⥤ B) ⥤ (α ⥤ C) := defRevSubstFun₂ G

    instance revSubstFun.isFunApp {F : α ⥤ B} {G : α ⥤ B ⥤ C} :
        IsFunApp (HasSubstPi.revSubstFun G F) :=
      ⟨revSubstFun₂ G, F⟩

  end

end HasRevSubstPi₂

class HasRevSubstPiFun {α : Sort u} {V W : Universe} [HasUnivFunctors W W] {P : α → V} [HasPiType P]
                       (Q : ∀ a, P a → W) [∀ a, HasPiType (Q a)] [HasPiType (λ a => Pi (Q a))]
                       [∀ F : Pi P, HasPiType (λ a => Q a (F a))]
                       [HasPiType (λ F : Pi P => Pi (λ a => Q a (F a)))] extends
    HasRevSubstPi₂ Q where
  defRevSubstPiFun :
    Pi (λ a => Pi (Q a)) ⥤{HasRevSubstPi₂.revSubstPi₂} Pi (λ F : Pi P => Pi (λ a => Q a (F a)))

namespace HasRevSubstPiFun

  section

    variable {α : Sort u} {V W : Universe} [HasUnivFunctors W W] {P : α → V} [HasPiType P]
             (Q : ∀ a, P a → W) [∀ a, HasPiType (Q a)] [HasPiType (λ a => Pi (Q a))]
             [∀ F : Pi P, HasPiType (λ a => Q a (F a))]
             [HasPiType (λ F : Pi P => Pi (λ a => Q a (F a)))] [h : HasRevSubstPiFun Q]

    @[reducible] def revSubstPiFun : Pi (λ a => Pi (Q a)) ⥤ Pi₂ (λ (F : Pi P) a => Q a (F a)) :=
      h.defRevSubstPiFun

    instance revSubstPi₂.isFunApp {G : Pi (λ a => Pi (Q a))} :
        IsFunApp (HasRevSubstPi₂.revSubstPi₂ G) :=
      ⟨revSubstPiFun Q, G⟩

    instance revSubstPi.isPiApp₂ {G : Pi (λ a => Pi (Q a))} {F : Pi P} :
        IsPiApp₂ (HasSubstPi.revSubstPi G F) :=
      ⟨revSubstPiFun Q, G, F, rfl⟩

  end

  section

    variable {α : Sort u} {V W : Universe} [hW : HasUnivFunctors W W] {P : α → V} [HasPiType P]
             (F : Pi P) (Q : ∀ a, P a → W) [∀ a, HasPiType (Q a)] [HasPiType (λ a => Pi (Q a))]
             [∀ F : Pi P, HasPiType (λ a => Q a (F a))]
             [HasPiType (λ F : Pi P => Pi (λ a => Q a (F a)))] [HasRevSubstPiFun Q]

    instance :
        HasPiType (λ G => (Function.const (Pi (λ a => Pi (Q a))) (λ F' => Pi (λ a => Q a (F' a)))) G F) :=
      (hW.hFun (Pi (λ a => Pi (Q a))) (Pi (λ a => Q a (F a)))).toHasPiType

    variable [HasSwapPi (Function.const (Pi (λ a => Pi (Q a)))
                                        (λ F : Pi P => Pi (λ a => Q a (F a))))]

    def substPiFun : Pi (λ a => Pi (Q a)) ⥤ Pi (λ a => Q a (F a)) :=
      HasSwapPi.swapPi (P := Function.const (Pi (λ a => Pi (Q a)))
                                            (λ F : Pi P => Pi (λ a => Q a (F a))))
                       (revSubstPiFun Q) F

    instance substPi.isPiApp₂' {G : Pi (λ a => Pi (Q a))} : IsPiApp₂' (HasSubstPi.substPi F G) :=
      ⟨⟨substPiFun F Q, G, rfl⟩⟩

  end

  section

    variable {α : Sort u} {V W : Universe} [HasUnivFunctors W W] {P : α → V} [HasPiType P]
             (Q : ∀ a, P a → W) [∀ a, HasPiType (Q a)] [HasPiType (λ a => Pi (Q a))]
             [∀ F : Pi P, HasPiType (λ a => Q a (F a))]
             [HasPiType (λ F : Pi P => Pi (λ a => Q a (F a)))]
             [HasPiType (λ F : Pi P => (Pi (λ a => Pi (Q a)) ⥤ Pi (λ a => Q a (F a))))]
             [HasRevSubstPiFun Q]
             [HasSwapPi₂ (Function.const (Pi (λ a => Pi (Q a)))
                                         (λ F : Pi P => Pi (λ a => Q a (F a))))]

    def substPiFunPi : Pi (λ F : Pi P => (Pi (λ a => Pi (Q a)) ⥤ Pi (λ a => Q a (F a)))) :=
      HasSwapPi₂.swapPi₂ (P := Function.const (Pi (λ a => Pi (Q a)))
                                              (λ F : Pi P => Pi (λ a => Q a (F a))))
                         (revSubstPiFun Q)

    instance substPiFun.isPiApp {F : Pi P} : IsPiApp (substPiFun F Q) := ⟨substPiFunPi Q, F, rfl⟩

  end

  section

    variable (α : Sort u) {V : Universe.{u}} {W : Universe} [HasUnivFunctors W W] {B : V}
             [HasFunctors α B] (Q : B → W) [HasPiType Q] [∀ F : α ⥤ B, HasPiType (λ a => Q (F a))]
             [HasPiType (λ (F : α ⥤ B) => Pi (λ a => Q (F a)))]
             [HasPiType (Function.const α (Pi Q))]
             [HasRevSubstPiFun (P := Function.const α B) (Function.const α Q)]
             [HasConstPiFun α (Pi Q)]
             [HasCompFunPi (Pi Q) (Function.const (Pi (Function.const α (Pi Q)))
                                                  (Pi₂ (λ (F : α ⥤ B) a => Q (F a))))]

    instance (priority := low) hasRevCompFunPiFun : HasRevCompFunPiFun α Q :=
      ⟨⟨revSubstPiFun (Function.const α Q) ⊙ HasConstPiFun.constPiFun α (Pi Q)⟩⟩

  end

  section

    variable (α : Sort u) {V W : Universe.{u}} [HasUnivFunctors V W] [HasUnivFunctors W W] (B : V)
             [HasFunctors α B] (C : W) [HasFunctors α (B ⥤ C)] [HasFunctors α C]
             [h : HasRevSubstPiFun (Function.const α (Function.const B C))]

    def defRevSubstFun₃ : (α ⥤ B ⥤ C) ⥤ (α ⥤ B) ⥤ α ⥤{λ G F a => G a (F a)} C :=
      ⟨λ G => HasRevSubstPi₂.defRevSubstFun₂ G, h.defRevSubstPiFun⟩

    @[reducible] def revSubstFun₃ : (α ⥤ B ⥤ C) ⥤ (α ⥤ B) ⥤ (α ⥤ C) := defRevSubstFun₃ α B C

    instance revSubstFun₂.isFunApp {G : α ⥤ B ⥤ C} : IsFunApp (HasRevSubstPi₂.revSubstFun₂ G) :=
      ⟨revSubstFun₃ α B C, G⟩

    instance revSubstFun.isFunApp₂ {G : α ⥤ B ⥤ C} {F : α ⥤ B} :
        IsFunApp₂ (HasSubstPi.revSubstFun G F) :=
      ⟨revSubstFun₃ α B C, G, F⟩

  end

  section

    variable {α : Sort u} {V W : Universe.{u}} [HasUnivFunctors V W] [HasUnivFunctors W W] {B : V}
             [HasFunctors α B] (F : α ⥤ B) (C : W) [HasFunctors α (B ⥤ C)] [HasFunctors α C]
             [HasRevSubstPiFun (Function.const α (Function.const B C))]
             [HasSwapPi (Function.const (α ⥤ B ⥤ C) (Function.const (α ⥤ B) (α ⥤ C)))]

    def defSubstFun₂ : (α ⥤ B ⥤ C) ⥤ α ⥤{λ G a => G a (F a)} C :=
      ⟨λ G => HasSubstPi.defSubstFun F G, ⟨HasSwapPi.swapFun (revSubstFun₃ α B C) F⟩⟩

    @[reducible] def substFun₂ : (α ⥤ B ⥤ C) ⥤ (α ⥤ C) := defSubstFun₂ F C

    instance substFun.isFunApp₂' {G : α ⥤ B ⥤ C} : IsFunApp₂' (HasSubstPi.substFun F G) :=
      ⟨⟨substFun₂ F C, G⟩⟩

  end

  section

    variable (α : Sort u) {V W : Universe.{u}} [HasUnivFunctors V W] [HasUnivFunctors W W] (B : V)
             [HasFunctors α B] (C : W) [HasFunctors α (B ⥤ C)] [HasFunctors α C]
             [HasRevSubstPiFun (Function.const α (Function.const B C))]
             [HasSwapPi₂ (Function.const (α ⥤ B ⥤ C) (Function.const (α ⥤ B) (α ⥤ C)))]

    def defSubstFun₃ : (α ⥤ B) ⥤ (α ⥤ B ⥤ C) ⥤ α ⥤{λ F G a => G a (F a)} C :=
      ⟨λ F => defSubstFun₂ F C, ⟨HasSwapPi₂.swapFun₂ (revSubstFun₃ α B C)⟩⟩

    @[reducible] def substFun₃ : (α ⥤ B) ⥤ (α ⥤ B ⥤ C) ⥤ (α ⥤ C) := defSubstFun₃ α B C

    instance substFun₂.isFunApp {F : α ⥤ B} : IsFunApp (substFun₂ F C) := ⟨substFun₃ α B C, F⟩

  end

end HasRevSubstPiFun



class HasExternalLinearLogic (α : Sort u) (U : Universe.{u}) [HasUnivFunctors U U] where
  [hFun (B : U) : HasFunctors α B]
  defRevAppFun₂  (B   : U) : α ⥤ (α ⥤ B) ⥤{λ a F => F a} B
  defRevCompFun₃ (B C : U) : (B ⥤ C) ⥤ (α ⥤ B) ⥤ α ⥤{λ G F a => G (F a)} C

namespace HasExternalLinearLogic

  variable (α : Sort u) {U : Universe.{u}} [HasUnivFunctors U U] [h : HasExternalLinearLogic α U]

  instance (B : U) : HasFunctors α B := h.hFun B

  instance hasPiAppFun (B : U) : HasPiAppFun (Function.const α B) := ⟨(h.defRevAppFun₂ B).app⟩
  instance (B : U) : HasPiAppFun (λ _ : α => B) := hasPiAppFun α B

  instance hasPiAppFunPi (B : U) : HasPiAppFunPi (Function.const α B) :=
    ⟨(h.defRevAppFun₂ B).toDefFun⟩
  instance (B : U) : HasPiAppFunPi (λ _ : α => B) := hasPiAppFunPi α B

  instance hasCompFunPi (B C : U) : HasCompFunPi α (Function.const B C) :=
    ⟨λ F G => ((h.defRevCompFun₃ B C).app G).app F⟩
  instance (B C : U) : HasCompFunPi α (λ _ : B => C) := hasCompFunPi α B C

  instance hasRevCompFunPi₂ (B C : U) : HasRevCompFunPi₂ α (Function.const B C) :=
    ⟨λ G => ((h.defRevCompFun₃ B C).app G).toDefPi⟩
  instance (B C : U) : HasRevCompFunPi₂ α (λ _ : B => C) := hasRevCompFunPi₂ α B C

  instance hasRevCompFunPiFun (B C : U) : HasRevCompFunPiFun α (Function.const B C) :=
    ⟨(h.defRevCompFun₃ B C).toDefFun⟩
  instance (B C : U) : HasRevCompFunPiFun α (λ _ : B => C) := hasRevCompFunPiFun α B C

end HasExternalLinearLogic


class HasLinearLogic (U : Universe) extends HasUnivFunctors U U where
  defIdFun       (A     : U) : A ⥤{id} A
  defRevAppFun₂  (A B   : U) : A ⥤ (A ⥤ B) ⥤{λ a F => F a} B
  defRevCompFun₃ (A B C : U) : (B ⥤ C) ⥤ (A ⥤ B) ⥤ A ⥤{λ G F a => G (F a)} C

namespace HasLinearLogic

  def construct (U : Universe) [HasUnivFunctors U U] [hId : ∀ A : U, HasIdFun A]
                [hRevApp : ∀ A B : U, HasPiAppFunPi (Function.const A B)]
                [hRevComp : ∀ A B C : U, HasRevCompFunPiFun A (Function.const B C)] :
      HasLinearLogic U where
    defIdFun       A     := (hId A).defIdFun
    defRevAppFun₂  A B   := ⟨(hRevApp A B).defPiAppFun, (hRevApp A B).defPiAppFunPi⟩
    defRevCompFun₃ A B C := ⟨λ G => ⟨λ F => (hRevComp A B C).defCompFunPi F G,
                                     (hRevComp A B C).defRevCompFunPi₂ G⟩,
                             (hRevComp A B C).defRevCompFunPiFun⟩

  variable {U : Universe} [h : HasLinearLogic U]

  instance hasIdFun (A : U) : HasIdFun A := ⟨h.defIdFun A⟩

  instance hasExternalLinearLogic (A : U) : HasExternalLinearLogic A U where
    defRevAppFun₂  B   := h.defRevAppFun₂  A B
    defRevCompFun₃ B C := h.defRevCompFun₃ A B C

end HasLinearLogic


class HasExternalSubLinearLogic (α : Sort u) (U : Universe.{u}) [HasUnivFunctors U U]
                                [∀ B : U, HasFunctors α B] where
  defConstFun₂ (B : U) : B ⥤ α ⥤{λ b a => b} B

namespace HasExternalSubLinearLogic

  variable (α : Sort u) {U : Universe.{u}} [HasUnivFunctors U U] [∀ B : U, HasFunctors α B]
           [h : HasExternalSubLinearLogic α U]

  instance hasConstPi (B : U) : HasConstPi α B := ⟨(h.defConstFun₂ B).app⟩

  instance hasConstPiFun (B : U) : HasConstPiFun α B := ⟨(h.defConstFun₂ B).toDefFun⟩

end HasExternalSubLinearLogic

class HasExternalAffineLogic (α : Sort u) (U : Universe.{u}) [HasUnivFunctors U U] extends
  HasExternalLinearLogic α U, HasExternalSubLinearLogic α U


class HasSubLinearLogic (U : Universe) [HasUnivFunctors U U] where
  defConstFun₂ (A B : U) : B ⥤ A ⥤{λ b a => b} B

namespace HasSubLinearLogic

  def construct (U : Universe) [HasUnivFunctors U U] [hConst : ∀ A B : U, HasConstPiFun A B] :
      HasSubLinearLogic U where
    defConstFun₂ A B := ⟨(hConst A B).defConstPi, (hConst A B).defConstPiFun⟩

  variable {U : Universe} [HasUnivFunctors U U] [h : HasSubLinearLogic U]

  instance hasExternalSubLinearLogic (A : U) : HasExternalSubLinearLogic A U where
    defConstFun₂ B := h.defConstFun₂ A B

end HasSubLinearLogic

class HasAffineLogic (U : Universe) extends HasLinearLogic U, HasSubLinearLogic U

namespace HasAffineLogic

  variable {U : Universe} [h : HasAffineLogic U]

  instance hasExternalAffineLogic (A : U) : HasExternalAffineLogic A U := ⟨⟩

end HasAffineLogic


class HasExternalNonLinearLogic (α : Sort u) (U : Universe.{u}) [HasUnivFunctors U U]
                                [∀ B : U, HasFunctors α B] where
  defDupFun₂ (B : U) : (α ⥤ α ⥤ B) ⥤ α ⥤{λ F a => F a a} B

namespace HasExternalNonLinearLogic

  variable (α : Sort u) {U : Universe.{u}} [HasUnivFunctors U U] [∀ B : U, HasFunctors α B]
           [h : HasExternalNonLinearLogic α U]

  instance hasDupPi (B : U) : HasDupPi (Function.const α (Function.const α B)) :=
    ⟨(h.defDupFun₂ B).app⟩
  instance (B : U) : HasDupPi (λ _ : α => Function.const α B) := hasDupPi α B
  instance (B : U) : HasDupPi (λ _ _ : α => B) := hasDupPi α B

  instance hasDupPiFun (B : U) : HasDupPiFun (Function.const α (Function.const α B)) :=
    ⟨(h.defDupFun₂ B).toDefFun⟩
  instance (B : U) : HasDupPiFun (λ _ : α => Function.const α B) := hasDupPiFun α B
  instance (B : U) : HasDupPiFun (λ _ _ : α => B) := hasDupPiFun α B

end HasExternalNonLinearLogic

class HasExternalFullLogic (α : Sort u) (U : Universe.{u}) [HasUnivFunctors U U] extends
  HasExternalAffineLogic α U, HasExternalNonLinearLogic α U


class HasNonLinearLogic (U : Universe) [HasUnivFunctors U U] where
  defDupFun₂ (A B : U) : (A ⥤ A ⥤ B) ⥤ A ⥤{λ F a => F a a} B

namespace HasNonLinearLogic

  def construct (U : Universe) [HasUnivFunctors U U]
                [hDup : ∀ A B : U, HasDupPiFun (Function.const A (Function.const A B))] :
      HasNonLinearLogic U where
    defDupFun₂ A B := ⟨(hDup A B).defDupPi, (hDup A B).defDupPiFun⟩

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
  HasPiType P, HasPiAppFun P

namespace HasExternalPiType

  variable {α : Sort u} {V : Universe} [HasLinearLogic V] (P : α → V) [h : HasExternalPiType P]

  instance hasConstImpl (X : V) : HasPiType (λ a => X ⥤ P a) where
    defPiType := { A    := X ⥤ Pi P,
                   elim := λ F a => HasPiAppFun.piAppFun P a ⊙ F }

  instance hasPiAppFunPi : HasPiAppFunPi P := ⟨⟨HasIdFun.idFun (Pi P)⟩⟩

  -- TODO: top, product

end HasExternalPiType


class HasExternalPiType₂ {α : Sort u} {β : Sort u'} {V : Universe} [HasLinearLogic V]
                         (P : α → β → V) where
  [hAppPiType (a : α) : HasExternalPiType (P a)]
  [hSwapAppPiType (b : β) : HasExternalPiType (λ a => P a b)]
  [hPiType₂ : HasExternalPiType (λ a => Pi (P a))]
  [hSwapPi : HasSwapPi P]
  defRevSwapPiFun (b : β) : Pi₂ P ⥤{λ F => HasSwapPi.swapPi F b} Pi (λ a => P a b)

namespace HasExternalPiType₂

  variable {α : Sort u} {β : Sort u'} {V : Universe} [HasLinearLogic V] (P : α → β → V)
           [h : HasExternalPiType₂ P]

  instance (a : α) : HasExternalPiType (P a) := h.hAppPiType a
  instance (a : α) : HasExternalPiType ((λ a b => P a b) a) := h.hAppPiType a
  instance (b : β) : HasExternalPiType (λ a => P a b) := h.hSwapAppPiType b
  instance (b : β) : HasExternalPiType ((λ b a => P a b) b) := h.hSwapAppPiType b
  instance : HasExternalPiType (λ a => Pi (P a)) := h.hPiType₂
  instance : HasSwapPi P := h.hSwapPi

  instance : HasPiType (λ b => Pi (λ a => P a b)) where
    defPiType := { A    := Pi₂ P,
                   elim := HasSwapPi.swapPi }

  instance : HasPiAppFun (λ b => Pi (λ a => P a b)) := ⟨h.defRevSwapPiFun⟩

  instance hasSwapPiType₂ : HasExternalPiType (λ b => Pi (λ a => P a b)) := ⟨⟩

  instance : HasSwapPi₂ P := ⟨λ F => ⟨F⟩⟩
  instance : HasSwapPiFun P := ⟨⟨HasIdFun.idFun (Pi₂ P)⟩⟩

end HasExternalPiType₂
