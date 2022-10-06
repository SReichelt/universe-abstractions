import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations.NaturalTransformations
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedFunctors
import UniverseAbstractions.Universes.Layer1.Meta.Tactics.Functoriality

import UniverseAbstractions.Universes.Layer2.Axioms.Universes



namespace UniverseAbstractions.Layer2

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 500000

universe u u' u'' u''' w

open Layer1.HasPreorderRelation Layer1.HasEquivalenceRelationBase

variable {Prp : Universe} [Layer1.HasLinearLogic Prp] [Layer1.HasEquivalences Prp]



section

  variable {V : Universe} [HasPropositions Prp V]

  instance funDefEq {α : Sort u} (P : α → V) :
      HasDefEq (∀ a, P a) where
    DefEq f g     := ∀ a, f a ≃ g a
    refl  f       := λ a => idIso (f a)
    symm  efg     := λ a => (efg a)⁻¹
    trans efg egh := λ a => egh a • efg a

  instance funDefEq₂ {α : Sort u} {β : Sort u'} (P : α → β → V) :
      HasDefEq (∀ a b, P a b) where
    DefEq f g     := ∀ a b, f a b ≃ g a b
    refl  f       := λ a b => idIso (f a b)
    symm  efg     := λ a b => (efg a b)⁻¹
    trans efg egh := λ a b => egh a b • efg a b

  instance funDefEq₃ {α : Sort u} {β : Sort u'} {γ : Sort u''} (P : α → β → γ → V) :
      HasDefEq (∀ a b c, P a b c) where
    DefEq f g     := ∀ a b c, f a b c ≃ g a b c
    refl  f       := λ a b c => idIso (f a b c)
    symm  efg     := λ a b c => (efg a b c)⁻¹
    trans efg egh := λ a b c => egh a b c • efg a b c

  instance funDefEq₄ {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''}
                     (P : α → β → γ → δ → V) :
      HasDefEq (∀ a b c d, P a b c d) where
    DefEq f g     := ∀ a b c d, f a b c d ≃ g a b c d
    refl  f       := λ a b c d => idIso (f a b c d)
    symm  efg     := λ a b c d => (efg a b c d)⁻¹
    trans efg egh := λ a b c d => egh a b c d • efg a b c d

end



-- In contrast to layer 1, `Layer2.HasPiType` is not a base class of `Layer2.HasFunctors`. This is
-- because the well-definedness conditions (aka `congrArg`) of Π types and functors are different:
-- Π types need a dependent version that relies on the definition layer 2 type equivalence. So we
-- define `Layer2.HasPiType` later and only introduce a common base class `Layer2.HasPiTypeBase`
-- without `congrArg` here.

class HasPiTypeBase {α : Sort u} {V : Universe} [HasPropositions Prp V] (P : α → V) where
  defPiType : DefType V (∀ a, P a)
  defCongrFunFun (F G : defPiType.A) (a : α) :
    F ≃ G ⥤{λ e => (defPiType.elimCongrArg e) a} (defPiType.elim F) a ≃ (defPiType.elim G) a

namespace HasPiTypeBase

  open Layer1.HasPiType

  variable {V : Universe} [HasPropositions Prp V]

  section

    variable {α : Sort u} (P : α → V) [h : HasPiTypeBase P]

    instance toLayer1 : Layer1.HasPiType P := ⟨h.defPiType.toDefType⟩

  end

  section

    variable {α : Sort u} {P : α → V} [h : HasPiTypeBase P]

    def byDef {f : ∀ a, P a} {F : Layer1.HasPiType.DefPi P f} [hF : DefType.HasDefInstEq F] {a : α} :
        F.inst a ≃ f a :=
      hF.e a

    @[reducible] def congrFun {F G : Pi P} (e : F ≃ G) (a : α) : F a ≃ G a :=
      (h.defPiType.elimCongrArg e) a

    @[reducible] def congrFunFun (F G : Pi P) (a : α) : F ≃ G ⥤ F a ≃ G a := h.defCongrFunFun F G a

    instance congrFun.isFunApp {F G : Pi P} (e : F ≃ G) (a : α) :
        Layer1.HasFunctors.IsFunApp (congrFun e a) :=
      ⟨congrFunFun F G a, e⟩

    -- We _define_ quantification over an equivalence as an equivalence of functors (and then later
    -- introduce axioms for functor extensionality to make this quantification behave as expected).
    -- Note that `DefPi` with respect to this definition is the same as `DefEquiv`.

    instance hasEqPi (F G : Pi P) : Layer1.HasPiType (λ a => F a ≃ G a) where
      defPiType := DefType.defEqType F G

    instance hasEqPi.hasPiAppFun (F G : Pi P) : Layer1.HasPiAppFun (λ a => F a ≃ G a) :=
      ⟨λ a => ⟨congrFunFun F G a⟩⟩

    instance hasEqExtPi (F G : Pi P) : Layer1.HasExternalPiType (λ a => F a ≃ G a) := ⟨⟩

    instance hasNatBase (F G : Pi P) :
        HasNaturalTransformationsBase (P := λ a => asPreorder (P a)) (apply F) (apply G) where
      toHasExternalPiType := hasEqExtPi F G

    instance congrFun.isPiApp {F G : Pi P} (e : F ≃ G) (a : α) : IsPiApp (congrFun e a) where
      hP := hasEqPi F G
      F := e
      a := a
      codomainEq := rfl

    -- TODO: Improve the functoriality tactic to make this work.
    --instance congrFun.isPiApp₂' {F G : Pi P} (e : F ≃ G) (a : α) : IsPiApp₂' (congrFun e a) :=
    --  ⟨Layer1.HasFunctors.IsFunApp.isPiApp (congrFun e a)⟩

    instance (F : Pi P) : HasIdNatBase (P := λ a => asPreorder (P a)) (apply F) where
      defIdNat := ⟨idIso F⟩

    instance idIso.isPiApp (F : Pi P) {a : α} : IsPiApp (idIso (F a)) :=
      HasIdNatBase.idHom.isPiApp (P := λ a => asPreorder (P a)) (apply F)

    instance (F G : Pi P) : HasInvNatBase (apply F) (apply G) where
      defInvNat eFG := ⟨invIso eFG⟩
      defInvNatFun  := by functoriality

    instance invIso.isPiApp {F G : Pi P} (eFG : Pi (λ a => F a ≃ G a)) {a : α} :
        IsPiApp (eFG a)⁻¹ :=
      HasInvNatBase.invIso.isPiApp

    instance (F G H : Pi P) :
        HasCompNatBase (P := λ a => asPreorder (P a)) (apply F) (apply G) (apply H) where
      defCompNat eFG eGH := ⟨compIso eFG eGH⟩
      defCompNatFun₂     := by functoriality

    instance compIso.isPiApp {F G H : Pi P} (eFG : Pi (λ a => F a ≃ G a))
                             (eGH : Pi (λ a => G a ≃ H a)) {a : α} :
        IsPiApp (eGH a • eFG a) :=
      HasCompNatBase.compHom.isPiApp (P := λ a => asPreorder (P a))

  end

  section

    variable {α : Sort u} {β : Sort u'} {P : α → β → V} [∀ a, HasPiTypeBase (P a)]
             [HasPiTypeBase (λ a => Pi (P a))]

    def byDef₂ {f : ∀ a b, P a b} {F : Layer1.HasPiType.DefPi₂ P f}
               [hFa : ∀ a, DefType.HasDefInstEq (F.app a)] [hF : DefType.HasDefInstEq F.toDefPi]
               {a : α} {b : β} :
        F.inst a b ≃ f a b :=
      byDef (hF := hFa a) • congrFun (byDef (hF := hF)) b

    @[reducible] def congrFun₂ {F G : Pi₂ P} (e : F ≃ G) (a : α) (b : β) : F a b ≃ G a b :=
      congrFun (congrFun e a) b

    instance hasEqPi₂ (F G : Pi₂ P) : Layer1.HasPiType (λ a => Pi (λ b => F a b ≃ G a b)) :=
      hasEqPi F G

    instance congrFun₂.isPiApp₂ {F G : Pi₂ P} (e : F ≃ G) (a : α) (b : β) :
        IsPiApp₂ (congrFun₂ e a b) where
      hPiPa := hasEqPi₂ F G
      F := e
      a := a
      b := b
      codomainEq := rfl

    instance idIso.isPiApp₂ (F : Pi₂ P) (a : α) (b : β) : IsPiApp₂ (idIso (F a b)) where
      hPiPa := hasEqPi₂ F F
      F := idIso F
      a := a
      b := b
      codomainEq := rfl

    instance invIso.isPiApp₂ {F G : Pi₂ P} (eFG : Pi₂ (λ a b => F a b ≃ G a b)) (a : α) (b : β) :
        IsPiApp₂ (eFG a b)⁻¹ where
      hPiPa := hasEqPi₂ G F
      F := invIso eFG
      a := a
      b := b
      codomainEq := rfl

    instance compIso.isPiApp₂ {F G H : Pi₂ P} (eFG : Pi₂ (λ a b => F a b ≃ G a b))
                              (eGH : Pi₂ (λ a b => G a b ≃ H a b)) (a : α) (b : β) :
        IsPiApp₂ (eGH a b • eFG a b) where
      hPiPa := hasEqPi₂ F H
      F := compIso eFG eGH
      a := a
      b := b
      codomainEq := rfl

  end

  section

    variable {α : Sort u} {β : Sort u'} {γ : Sort u''} {P : α → β → γ → V}
             [∀ a b, HasPiTypeBase (P a b)] [∀ a, HasPiTypeBase (λ b => Pi (P a b))]
             [HasPiTypeBase (λ a => Pi₂ (P a))]

    def byDef₃ {f : ∀ a b c, P a b c} {F : Layer1.HasPiType.DefPi₃ P f}
               [hFab : ∀ a b, DefType.HasDefInstEq ((F.app a).app b)]
               [hFa : ∀ a, DefType.HasDefInstEq (F.app a).toDefPi]
               [hF : DefType.HasDefInstEq F.toDefPi] {a : α} {b : β} {c : γ} :
        F.inst a b c ≃ f a b c :=
      byDef₂ (hFa := hFab a) (hF := hFa a) • congrFun₂ (byDef (hF := hF)) b c

    @[reducible] def congrFun₃ {F G : Pi₃ P} (e : F ≃ G) (a : α) (b : β) (c : γ) :
        F a b c ≃ G a b c :=
      congrFun₂ (congrFun e a) b c

    instance hasEqPi₃ (F G : Pi₃ P) : Layer1.HasPiType (λ a => Pi₂ (λ b c => F a b c ≃ G a b c)) :=
      hasEqPi₂ F G

    instance congrFun₃.isPiApp₃ {F G : Pi₃ P} (e : F ≃ G) (a : α) (b : β) (c : γ) :
        IsPiApp₃ (congrFun₃ e a b c) where
      hPiPa := hasEqPi₃ F G
      F := e
      a := a
      b := b
      c := c
      codomainEq := rfl

    instance idIso.isPiApp₃ (F : Pi₃ P) (a : α) (b : β) (c : γ) : IsPiApp₃ (idIso (F a b c)) where
      hPiPa := hasEqPi₃ F F
      F := idIso F
      a := a
      b := b
      c := c
      codomainEq := rfl

    instance invIso.isPiApp₃ {F G : Pi₃ P} (eFG : Pi₃ (hPiPab := λ a => hasEqPi₂ (F a) (G a))
                                                      (hPiPa := hasEqPi₃ F G)
                                                      (λ a b c => F a b c ≃ G a b c)) (a : α)
                             (b : β) (c : γ) :
        IsPiApp₃ (eFG a b c)⁻¹ where
      hPiPa := hasEqPi₃ G F
      F := invIso eFG
      a := a
      b := b
      c := c
      codomainEq := rfl

    instance compIso.isPiApp₃ {F G H : Pi₃ P}
                              (eFG : Pi₃ (hPiPab := λ a => hasEqPi₂ (F a) (G a))
                                         (hPiPa := hasEqPi₃ F G) (λ a b c => F a b c ≃ G a b c))
                              (eGH : Pi₃ (hPiPab := λ a => hasEqPi₂ (G a) (H a))
                                         (hPiPa := hasEqPi₃ G H) (λ a b c => G a b c ≃ H a b c))
                                         (a : α) (b : β) (c : γ) :
        IsPiApp₃ (eGH a b c • eFG a b c) where
      hPiPa := hasEqPi₃ F H
      F := compIso eFG eGH
      a := a
      b := b
      c := c
      codomainEq := rfl

  end

  section

    variable {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''} {P : α → β → γ → δ → V}
             [∀ a b c, HasPiTypeBase (P a b c)] [∀ a b, HasPiTypeBase (λ c => Pi (P a b c))]
             [∀ a, HasPiTypeBase (λ b => Pi₂ (P a b))] [HasPiTypeBase (λ a => Pi₃ (P a))]

    def byDef₄ {f : ∀ a b c d, P a b c d} {F : Layer1.HasPiType.DefPi₄ P f}
               [hFabc : ∀ a b c, DefType.HasDefInstEq (((F.app a).app b).app c)]
               [hFab : ∀ a b, DefType.HasDefInstEq ((F.app a).app b).toDefPi]
               [hFa : ∀ a, DefType.HasDefInstEq (F.app a).toDefPi]
               [hF : DefType.HasDefInstEq F.toDefPi] {a : α} {b : β} {c : γ} {d : δ} :
        F.inst a b c d ≃ f a b c d :=
      byDef₃ (hFab := hFabc a) (hFa := hFab a) (hF := hFa a) • congrFun₃ (byDef (hF := hF)) b c d

    @[reducible] def congrFun₄ {F G : Pi₄ P} (e : F ≃ G) (a : α) (b : β) (c : γ) (d : δ) :
        F a b c d ≃ G a b c d :=
      congrFun₃ (congrFun e a) b c d

    instance hasEqPi₄ (F G : Pi₄ P) :
        Layer1.HasPiType (λ a => Pi₃ (hPiPab := λ b => hasEqPi₂ (F a b) (G a b))
                                     (hPiPa := hasEqPi₃ (F a) (G a))
                                     (λ b c d => F a b c d ≃ G a b c d)) :=
      hasEqPi₃ F G

    instance congrFun₄.isPiApp₄ {F G : Pi₄ P} (e : F ≃ G) (a : α) (b : β) (c : γ) (d : δ):
        IsPiApp₄ (congrFun₄ e a b c d) where
      hPiPa := hasEqPi₄ F G
      F := e
      a := a
      b := b
      c := c
      d := d
      codomainEq := rfl

    instance idIso.isPiApp₄ (F : Pi₄ P) (a : α) (b : β) (c : γ) (d : δ) :
        IsPiApp₄ (idIso (F a b c d)) where
      hPiPa := hasEqPi₄ F F
      F := idIso F
      a := a
      b := b
      c := c
      d := d
      codomainEq := rfl

    instance invIso.isPiApp₄ {F G : Pi₄ P} (eFG : Pi₄ (hPiPabc := λ a b => hasEqPi₂ (F a b) (G a b))
                                                      (hPiPab := λ a => hasEqPi₃ (F a) (G a))
                                                      (hPiPa := hasEqPi₄ F G)
                                                      (λ a b c d => F a b c d ≃ G a b c d))
                             (a : α) (b : β) (c : γ) (d : δ) :
        IsPiApp₄ (eFG a b c d)⁻¹ where
      hPiPa := hasEqPi₄ G F
      F := invIso eFG
      a := a
      b := b
      c := c
      d := d
      codomainEq := rfl

    instance compIso.isPiApp₄ {F G H : Pi₄ P}
                              (eFG : Pi₄ (hPiPabc := λ a b => hasEqPi₂ (F a b) (G a b))
                                         (hPiPab := λ a => hasEqPi₃ (F a) (G a))
                                         (hPiPa := hasEqPi₄ F G)
                                         (λ a b c d => F a b c d ≃ G a b c d))
                              (eGH : Pi₄ (hPiPabc := λ a b => hasEqPi₂ (G a b) (H a b))
                                         (hPiPab := λ a => hasEqPi₃ (G a) (H a))
                                         (hPiPa := hasEqPi₄ G H)
                                         (λ a b c d => G a b c d ≃ H a b c d)) (a : α) (b : β)
                              (c : γ) (d : δ) :
        IsPiApp₄ (eGH a b c d • eFG a b c d) where
      hPiPa := hasEqPi₄ F H
      F := compIso eFG eGH
      a := a
      b := b
      c := c
      d := d
      codomainEq := rfl

  end

  section

    @[reducible] def defPiType₂ {α : Sort u} {β : Sort u'} (P : α → β → V)
                                [∀ a, HasPiTypeBase (P a)] [HasPiTypeBase (λ a => Pi (P a))] :
        DefType V (∀ a b, P a b) where
      toDefType    := Layer1.HasPiType.defPiType₂ P
      elimCongrArg := congrFun₂

    @[reducible] def defPiType₃ {α : Sort u} {β : Sort u'} {γ : Sort u''} (P : α → β → γ → V)
                                [∀ a b, HasPiTypeBase (P a b)]
                                [∀ a, HasPiTypeBase (λ b => Pi (P a b))]
                                [HasPiTypeBase (λ a => Pi₂ (P a))] :
        DefType V (∀ a b c, P a b c) where
      toDefType    := Layer1.HasPiType.defPiType₃ P
      elimCongrArg := congrFun₃

    @[reducible] def defPiType₄ {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''}
                                (P : α → β → γ → δ → V) [∀ a b c, HasPiTypeBase (P a b c)]
                                [∀ a b, HasPiTypeBase (λ c => Pi (P a b c))]
                                [∀ a, HasPiTypeBase (λ b => Pi₂ (P a b))]
                                [HasPiTypeBase (λ a => Pi₃ (P a))] :
        DefType V (∀ a b c d, P a b c d) where
      toDefType    := Layer1.HasPiType.defPiType₄ P
      elimCongrArg := congrFun₄

  end

  -- Helper classes for the `functoriality` tactic.
  section Helpers

    class IsPiApp {Y : V} (y : Y) where
      {α : Sort u}
      {P : α → V}
      [hP : HasPiTypeBase P]
      F : Pi P
      a : α
      codomainEq : P a = Y  -- must be `rfl` for meta code to work correctly
      e : codomainEq ▸ F a ≃ y

    namespace IsPiApp

      instance (priority := low) refl {α : Sort u} {P : α → V} [HasPiTypeBase P] {F : Pi P} {a : α} :
          IsPiApp (F a) :=
        ⟨F, a, rfl, idIso (F a)⟩

      variable {Y : V} {y : Y} [hApp : IsPiApp.{u} y]

      instance : HasPiTypeBase hApp.P := hApp.hP

      instance toLayer1 : Layer1.HasPiType.IsPiApp y := ⟨hApp.F, hApp.a, hApp.codomainEq⟩

    end IsPiApp

    class IsPiApp₂ {Y : V} (y : Y) where
      {α : Sort u}
      {β : Sort u'}
      {P : α → β → V}
      [hPa (a : α) : HasPiTypeBase (P a)]
      [hPiPa : HasPiTypeBase (λ a => Pi (P a))]
      F : Pi₂ P
      a : α
      b : β
      codomainEq : P a b = Y
      e : codomainEq ▸ F a b ≃ y

    namespace IsPiApp₂

      instance (priority := low) refl {α : Sort u} {β : Sort u'} {P : α → β → V}
                                      [∀ a, HasPiTypeBase (P a)] [HasPiTypeBase (λ a => Pi (P a))]
                                      {F : Pi₂ P} {a : α} {b : β} :
          IsPiApp₂ (F a b) :=
        ⟨F, a, b, rfl, idIso (F a b)⟩

      variable {Y : V} (y : Y) [hApp : IsPiApp₂.{u, u'} y]

      instance (a : hApp.α) : HasPiTypeBase (hApp.P a) := hApp.hPa a
      instance : HasPiTypeBase (λ a => Pi (hApp.P a)) := hApp.hPiPa

      def isPiApp : IsPiApp y := ⟨hApp.F hApp.a, hApp.b, hApp.codomainEq, hApp.e⟩

      instance toLayer1 : Layer1.HasPiType.IsPiApp₂ y := ⟨hApp.F, hApp.a, hApp.b, hApp.codomainEq⟩

    end IsPiApp₂

    class IsPiApp₃ {Y : V} (y : Y) where
      {α : Sort u}
      {β : Sort u'}
      {γ : Sort u''}
      {P : α → β → γ → V}
      [hPab (a : α) (b : β) : HasPiTypeBase (P a b)]
      [hPiPab (a : α) : HasPiTypeBase (λ b => Pi (P a b))]
      [hPiPa : HasPiTypeBase (λ a => Pi₂ (P a))]
      F : Pi₃ P
      a : α
      b : β
      c : γ
      codomainEq : P a b c = Y
      e : codomainEq ▸ F a b c ≃ y

    namespace IsPiApp₃

      instance (priority := low) refl {α : Sort u} {β : Sort u'} {γ : Sort u''} {P : α → β → γ → V}
                                      [∀ a b, HasPiTypeBase (P a b)]
                                      [∀ a, HasPiTypeBase (λ b => Pi (P a b))]
                                      [HasPiTypeBase (λ a => Pi₂ (P a))]
                                      {F : Pi₃ P} {a : α} {b : β} {c : γ} :
          IsPiApp₃ (F a b c) :=
        ⟨F, a, b, c, rfl, idIso (F a b c)⟩

      variable {Y : V} (y : Y) [hApp : IsPiApp₃.{u, u', u''} y]

      instance (a : hApp.α) (b : hApp.β) : HasPiTypeBase (hApp.P a b) := hApp.hPab a b
      instance (a : hApp.α) : HasPiTypeBase (λ b => Pi (hApp.P a b)) := hApp.hPiPab a
      instance : HasPiTypeBase (λ a => Pi₂ (hApp.P a)) := hApp.hPiPa

      def isPiApp₂ : IsPiApp₂ y := ⟨hApp.F hApp.a, hApp.b, hApp.c, hApp.codomainEq, hApp.e⟩

      def isPiApp : IsPiApp y :=
        let _ : IsPiApp₂ y := isPiApp₂ y
        IsPiApp₂.isPiApp y

      instance toLayer1 : Layer1.HasPiType.IsPiApp₃ y :=
        ⟨hApp.F, hApp.a, hApp.b, hApp.c, hApp.codomainEq⟩

    end IsPiApp₃

    class IsPiApp₄ {Y : V} (y : Y) where
      {α : Sort u}
      {β : Sort u'}
      {γ : Sort u''}
      {δ : Sort u'''}
      {P : α → β → γ → δ → V}
      [hPabc (a : α) (b : β) (c : γ) : HasPiTypeBase (P a b c)]
      [hPiPabc (a : α) (b : β) : HasPiTypeBase (λ c => Pi (P a b c))]
      [hPiPab (a : α) : HasPiTypeBase (λ b => Pi₂ (P a b))]
      [hPiPa : HasPiTypeBase (λ a => Pi₃ (P a))]
      F : Pi₄ P
      a : α
      b : β
      c : γ
      d : δ
      codomainEq : P a b c d = Y
      e : codomainEq ▸ F a b c d ≃ y

    namespace IsPiApp₄

      instance (priority := low) refl {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''}
                                      {P : α → β → γ → δ → V} [∀ a b c, HasPiTypeBase (P a b c)]
                                      [∀ a b, HasPiTypeBase (λ c => Pi (P a b c))]
                                      [∀ a, HasPiTypeBase (λ b => Pi₂ (P a b))]
                                      [HasPiTypeBase (λ a => Pi₃ (P a))]
                                      {F : Pi₄ P} {a : α} {b : β} {c : γ} {d : δ} :
          IsPiApp₄ (F a b c d) :=
        ⟨F, a, b, c, d, rfl, idIso (F a b c d)⟩

      variable {Y : V} (y : Y) [hApp : IsPiApp₄.{u, u', u'', u'''} y]

      instance (a : hApp.α) (b : hApp.β) (c : hApp.γ) : HasPiTypeBase (hApp.P a b c) := hApp.hPabc a b c
      instance (a : hApp.α) (b : hApp.β) : HasPiTypeBase (λ c => Pi (hApp.P a b c)) := hApp.hPiPabc a b
      instance (a : hApp.α) : HasPiTypeBase (λ b => Pi₂ (hApp.P a b)) := hApp.hPiPab a
      instance : HasPiTypeBase (λ a => Pi₃ (hApp.P a)) := hApp.hPiPa

      def isPiApp₃ : IsPiApp₃ y := ⟨hApp.F hApp.a, hApp.b, hApp.c, hApp.d, hApp.codomainEq, hApp.e⟩

      def isPiApp₂ : IsPiApp₂ y :=
        let _ : IsPiApp₃ y := isPiApp₃ y
        IsPiApp₃.isPiApp₂ y

      def isPiApp : IsPiApp y :=
        let _ : IsPiApp₂ y := isPiApp₂ y
        IsPiApp₂.isPiApp y

      instance toLayer1 : Layer1.HasPiType.IsPiApp₄ y :=
        ⟨hApp.F, hApp.a, hApp.b, hApp.c, hApp.d, hApp.codomainEq⟩

    end IsPiApp₄

    class IsPiApp₂' {Y : V} (y : Y) extends IsPiApp.{u} y where
      h₂ : IsPiApp.{u'} y

    namespace IsPiApp₂'

      variable {Y : V} (y : Y) [h : IsPiApp₂' y]

      instance toLayer1 : Layer1.HasPiType.IsPiApp₂' y := ⟨inferInstance⟩

    end IsPiApp₂'

    class IsPiApp₃' {Y : V} (y : Y) extends IsPiApp₂'.{u, u'} y where
      h₃ : IsPiApp.{u''} y

    namespace IsPiApp₃'

      variable {Y : V} (y : Y) [h : IsPiApp₃' y]

      instance toLayer1 : Layer1.HasPiType.IsPiApp₃' y := ⟨inferInstance⟩

    end IsPiApp₃'

    class IsPiApp₄' {Y : V} (y : Y) extends IsPiApp₃'.{u, u', u''} y where
      h₄ : IsPiApp.{u'''} y

    namespace IsPiApp₄'

      variable {Y : V} (y : Y) [h : IsPiApp₄' y]

      instance toLayer1 : Layer1.HasPiType.IsPiApp₄' y := ⟨inferInstance⟩

    end IsPiApp₄'

  end Helpers

  section DefPi

    -- Note: Do dot make this `@[reducible]`. The functoriality tactic needs to be able to determine
    -- whether a given type is an application of `DefPi`.
    def DefPi {α : Sort u} (P : α → V) [h : HasPiTypeBase P] (f : ∀ a, P a) :=
      DefType.DefInst h.defPiType f

    namespace DefPi

      variable {α : Sort u} {P : α → V} [h : HasPiTypeBase P]

      def mk {f : ∀ a, P a} (F : Layer1.HasPiType.DefPi P f) (e : ∀ a, F.inst a ≃ f a) :
          DefPi P f :=
        ⟨F, ⟨e⟩⟩

      @[reducible] def inst {f : ∀ a, P a} (F : DefPi P f) : Pi P := F.toDefInst.inst

      instance coeType (f : ∀ a, P a) : Coe (DefPi P f) (Pi P) :=
        DefType.DefInst.coeType h.defPiType f

      @[reducible] def toLayer1 {f : ∀ a, P a} (F : DefPi P f) : Layer1.HasPiType.DefPi P f :=
        F.toDefInst

      instance (f : ∀ a, P a) : Coe (DefPi P f) (Layer1.HasPiType.DefPi P f) := ⟨toLayer1⟩

      -- TODO: It seems that this should work.
      --def isPiApp {f : ∀ a, P a} (F : DefPi P f) {a : α} : IsPiApp (f a) := ⟨F, a, rfl, F.e a⟩

      @[reducible] def cast {f g : ∀ a, P a} (efg : ∀ a, f a ≃ g a) (F : DefPi P f) : DefPi P g :=
        DefType.DefInst.cast efg F

      @[reducible] def DefEquiv {f : ∀ a, P a} (F G : DefPi P f) :=
        DefType.DefInst.DefInstEquiv F G

      namespace DefEquiv

        theorem is_DefPi {f : ∀ a, P a} (F G : DefPi P f) :
            DefEquiv F G = Layer1.HasPiType.DefPi (λ a => F.inst a ≃ G.inst a)
                                                  (λ a => (G.e a)⁻¹ • F.e a) :=
          rfl

        @[reducible] def cast {f g : ∀ a, P a} {efgF efgG : ∀ a, f a ≃ g a} {F G : DefPi P f}
                              (e : DefEquiv F G) :
            DefEquiv (cast efgF F) (cast efgG G) :=
          Layer1.DefType.DefInst.cast e

      end DefEquiv

      @[reducible] def defAppPi (F : Pi P) : DefPi P (apply F) := DefType.DefInst.fromInst F

      def defCongrFun {f g : ∀ a, P a} (F : DefPi P f) (G : DefPi P g) (e : F.inst ≃ G.inst)
                      (a : α) :
          f a ≃ g a :=
        byDef • congrFun e a • byDef⁻¹

      def hasEqPi {f g : ∀ a, P a} (F : DefPi P f) (G : DefPi P g) :
          Layer1.HasPiType (λ a => f a ≃ g a) where
        defPiType := { A    := F.inst ≃ G.inst,
                       elim := defCongrFun F G }

    end DefPi

    structure DefPi₂ {α : Sort u} {β : Sort u'} (P : α → β → V) [∀ a, HasPiTypeBase (P a)]
                     [HasPiTypeBase (λ a => Pi (P a))] (f : ∀ a b, P a b) where
      app (a : α) : DefPi (P a) (f a)
      toDefPi : DefPi (λ a => Pi (P a)) (λ a => (app a).inst)

    namespace DefPi₂

      variable {α : Sort u} {β : Sort u'} {P : α → β → V} [∀ a, HasPiTypeBase (P a)]
               [HasPiTypeBase (λ a => Pi (P a))]

      @[reducible] def inst {f : ∀ a b, P a b} (F : DefPi₂ P f) : Pi₂ P := F.toDefPi

      instance coeType (f : ∀ a b, P a b) : Coe (DefPi₂ P f) (Pi₂ P) := ⟨inst⟩

      @[reducible] def toLayer1 {f : ∀ a b, P a b} (F : DefPi₂ P f) : Layer1.HasPiType.DefPi₂ P f :=
        ⟨λ a => (F.app a).toLayer1, F.toDefPi.toLayer1⟩

      instance (f : ∀ a b, P a b) : Coe (DefPi₂ P f) (Layer1.HasPiType.DefPi₂ P f) := ⟨toLayer1⟩

      def e {f : ∀ a b, P a b} (F : DefPi₂ P f) (a : α) (b : β) : F.inst a b ≃ f a b :=
        byDef₂ (F := F.toLayer1)

      def toDefInst {f : ∀ a b, P a b} (F : DefPi₂ P f) : DefType.DefInst (defPiType₂ P) f :=
        ⟨⟨F.inst⟩, ⟨F.e⟩⟩

      def fromDefInst {f : ∀ a b, P a b} (F : DefType.DefInst (defPiType₂ P) f) : DefPi₂ P f :=
        ⟨λ a => ⟨⟨F.inst a⟩, ⟨F.e a⟩⟩, DefPi.defAppPi F.inst⟩

      def cast {f g : ∀ a b, P a b} (efg : ∀ a b, f a b ≃ g a b) (F : DefPi₂ P f) : DefPi₂ P g :=
        ⟨λ a => DefPi.cast (efg a) (F.app a), F.toDefPi⟩

      structure DefEquiv {f : ∀ a b, P a b} (F G : DefPi₂ P f) where
        app (a : α) : DefPi.DefEquiv (F.app a) (G.app a)
        toDefEquiv : DefPi.DefEquiv (DefPi.cast (g := λ a => (G.app a).inst)
                                                (λ a => (app a).e) F.toDefPi) G.toDefPi

      namespace DefEquiv

        @[reducible] def cast {f g : ∀ a b, P a b} {efgF efgG : ∀ a b, f a b ≃ g a b}
                              {F G : DefPi₂ P f} (e : DefEquiv F G) :
            DefEquiv (cast efgF F) (cast efgG G) :=
          ⟨λ a => DefPi.DefEquiv.cast (e.app a), e.toDefEquiv⟩

        variable {f : ∀ a b, P a b} {F G : DefPi₂ P f}

        def e (e : DefEquiv F G) : F.inst ≃ G.inst := e.toDefEquiv.e

        @[reducible] def toDefPi₂ (e : DefEquiv F G) :
            Layer1.HasPiType.DefPi₂ (hPiPa := hasEqPi₂ F.inst G.inst)
                                    (λ a b => F.inst a b ≃ G.inst a b)
                                    (λ a b => (G.e a b)⁻¹ • F.e a b) :=
          let _ := hasEqPi₂ F.inst G.inst
          ⟨λ a => ⟨compIso (compIso (F.toDefPi.e a) (e.app a).e) (invIso (G.toDefPi.e a))⟩,
           e.toDefEquiv⟩

        @[reducible] def fromDefPi₂ (e : Layer1.HasPiType.DefPi₂ (hPiPa := hasEqPi₂ F.inst G.inst)
                                                                 (λ a b => F.inst a b ≃ G.inst a b)
                                                                 (λ a b => (G.e a b)⁻¹ • F.e a b)) :
            DefEquiv F G :=
          let _ := hasEqPi₂ F.inst G.inst
          ⟨λ a => ⟨compIso (compIso (invIso (F.toDefPi.e a)) (e.app a).inst) (G.toDefPi.e a)⟩,
           ⟨e.inst⟩⟩

      end DefEquiv

      def defAppPi (F : Pi₂ P) : DefPi₂ P (apply₂ F) :=
        ⟨λ a => DefPi.defAppPi (F a), DefPi.defAppPi F⟩

      def hasEqPi₂ {f g : ∀ a b, P a b} (F : DefPi₂ P f) (G : DefPi₂ P g) :
          Layer1.HasPiType (λ a => Pi (h := DefPi.hasEqPi (F.app a) (G.app a))
                                      (λ b => f a b ≃ g a b)) :=
        DefPi.hasEqPi F.toDefPi G.toDefPi

    end DefPi₂

    structure DefPi₃ {α : Sort u} {β : Sort u'} {γ : Sort u''} (P : α → β → γ → V)
                     [∀ a b, HasPiTypeBase (P a b)] [∀ a, HasPiTypeBase (λ b => Pi (P a b))]
                     [HasPiTypeBase (λ a => Pi₂ (P a))] (f : ∀ a b c, P a b c) where
      app (a : α) : DefPi₂ (P a) (f a)
      toDefPi : DefPi (λ a => Pi₂ (P a)) (λ a => (app a).inst)

    namespace DefPi₃

      variable {α : Sort u} {β : Sort u'} {γ : Sort u''} {P : α → β → γ → V}
               [∀ a b, HasPiTypeBase (P a b)] [∀ a, HasPiTypeBase (λ b => Pi (P a b))]
               [HasPiTypeBase (λ a => Pi₂ (P a))]

      @[reducible] def inst {f : ∀ a b c, P a b c} (F : DefPi₃ P f) : Pi₃ P := F.toDefPi

      instance coeType (f : ∀ a b c, P a b c) : Coe (DefPi₃ P f) (Pi₃ P) := ⟨inst⟩

      @[reducible] def toLayer1 {f : ∀ a b c, P a b c} (F : DefPi₃ P f) :
          Layer1.HasPiType.DefPi₃ P f :=
        ⟨λ a => (F.app a).toLayer1, F.toDefPi.toLayer1⟩

      instance (f : ∀ a b c, P a b c) : Coe (DefPi₃ P f) (Layer1.HasPiType.DefPi₃ P f) := ⟨toLayer1⟩

      def e {f : ∀ a b c, P a b c} (F : DefPi₃ P f) (a : α) (b : β) (c : γ) :
          F.inst a b c ≃ f a b c :=
        byDef₃ (F := F.toLayer1)

      def toDefInst {f : ∀ a b c, P a b c} (F : DefPi₃ P f) : DefType.DefInst (defPiType₃ P) f :=
        ⟨⟨F.inst⟩, ⟨F.e⟩⟩

      def fromDefInst {f : ∀ a b c, P a b c} (F : DefType.DefInst (defPiType₃ P) f) : DefPi₃ P f :=
        ⟨λ a => ⟨λ b => ⟨⟨F.inst a b⟩, ⟨F.e a b⟩⟩,
                 DefPi.defAppPi (F.inst a)⟩,
         DefPi.defAppPi F.inst⟩

      def cast {f g : ∀ a b c, P a b c} (efg : ∀ a b c, f a b c ≃ g a b c) (F : DefPi₃ P f) :
          DefPi₃ P g :=
        ⟨λ a => DefPi₂.cast (efg a) (F.app a), F.toDefPi⟩

      structure DefEquiv {f : ∀ a b c, P a b c} (F G : DefPi₃ P f) where
        app (a : α) : DefPi₂.DefEquiv (F.app a) (G.app a)
        toDefEquiv : DefPi.DefEquiv (DefPi.cast (g := λ a => (G.app a).inst)
                                                (λ a => (app a).e) F.toDefPi) G.toDefPi

      namespace DefEquiv

        @[reducible] def cast {f g : ∀ a b c, P a b c} {efgF efgG : ∀ a b c, f a b c ≃ g a b c}
                              {F G : DefPi₃ P f} (e : DefEquiv F G) :
            DefEquiv (cast efgF F) (cast efgG G) :=
          ⟨λ a => DefPi₂.DefEquiv.cast (e.app a), e.toDefEquiv⟩

        variable {f : ∀ a b c, P a b c} {F G : DefPi₃ P f}

        def e (e : DefEquiv F G) : F.inst ≃ G.inst := e.toDefEquiv.e

        -- TODO
        --@[reducible] def toDefPi₃ (e : DefEquiv F G) :
        --    Layer1.HasPiType.DefPi₃ (hPiPab := λ a => hasEqPi₂ (F.inst a) (G.inst a))
        --                            (hPiPa := hasEqPi₃ F.inst G.inst)
        --                            (λ a b c => F.inst a b c ≃ G.inst a b c)
        --                            (λ a b c => (G.e a b c)⁻¹ • F.e a b c) :=
        --  _

        -- TODO
        --@[reducible] def fromDefPi₃ (e : Layer1.HasPiType.DefPi₃ (hPiPab := λ a => hasEqPi₂ (F.inst a) (G.inst a))
        --                                                         (hPiPa := hasEqPi₃ F.inst G.inst)
        --                                                         (λ a b c => F.inst a b c ≃ G.inst a b c)
        --                                                         (λ a b c => (G.e a b c)⁻¹ • F.e a b c)) :
        --    DefEquiv F G :=
        --  _

      end DefEquiv

      def defAppPi (F : Pi₃ P) : DefPi₃ P (apply₃ F) :=
        ⟨λ a => DefPi₂.defAppPi (F a), DefPi.defAppPi F⟩

      def hasEqPi₃ {f g : ∀ a b c, P a b c} (F : DefPi₃ P f) (G : DefPi₃ P g) :
          Layer1.HasPiType (λ a => Pi₂ (hPa := λ b => DefPi.hasEqPi ((F.app a).app b)
                                                                    ((G.app a).app b))
                                       (hPiPa := DefPi₂.hasEqPi₂ (F.app a) (G.app a))
                                       (λ b c => f a b c ≃ g a b c)) :=
        DefPi.hasEqPi F.toDefPi G.toDefPi

    end DefPi₃

    structure DefPi₄ {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''}
                     (P : α → β → γ → δ → V) [∀ a b c, HasPiTypeBase (P a b c)]
                     [∀ a b, HasPiTypeBase (λ c => Pi (P a b c))]
                     [∀ a, HasPiTypeBase (λ b => Pi₂ (P a b))] [HasPiTypeBase (λ a => Pi₃ (P a))]
                     (f : ∀ a b c d, P a b c d) where
      app (a : α) : DefPi₃ (P a) (f a)
      toDefPi : DefPi (λ a => Pi₃ (P a)) (λ a => (app a).inst)

    namespace DefPi₄

      variable {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''} {P : α → β → γ → δ → V}
               [∀ a b c, HasPiTypeBase (P a b c)] [∀ a b, HasPiTypeBase (λ c => Pi (P a b c))]
               [∀ a, HasPiTypeBase (λ b => Pi₂ (P a b))] [HasPiTypeBase (λ a => Pi₃ (P a))]

      @[reducible] def inst {f : ∀ a b c d, P a b c d} (F : DefPi₄ P f) : Pi₄ P := F.toDefPi

      instance coeType (f : ∀ a b c d, P a b c d) : Coe (DefPi₄ P f) (Pi₄ P) := ⟨inst⟩

      @[reducible] def toLayer1 {f : ∀ a b c d, P a b c d} (F : DefPi₄ P f) :
          Layer1.HasPiType.DefPi₄ P f :=
        ⟨λ a => (F.app a).toLayer1, F.toDefPi.toLayer1⟩

      instance (f : ∀ a b c d, P a b c d) : Coe (DefPi₄ P f) (Layer1.HasPiType.DefPi₄ P f) :=
        ⟨toLayer1⟩

      def e {f : ∀ a b c d, P a b c d} (F : DefPi₄ P f) (a : α) (b : β) (c : γ) (d : δ) :
          F.inst a b c d ≃ f a b c d :=
        byDef₄ (F := F.toLayer1)

      def toDefInst {f : ∀ a b c d, P a b c d} (F : DefPi₄ P f) :
          DefType.DefInst (defPiType₄ P) f :=
        ⟨⟨F.inst⟩, ⟨F.e⟩⟩

      def fromDefInst {f : ∀ a b c d, P a b c d} (F : DefType.DefInst (defPiType₄ P) f) :
          DefPi₄ P f :=
        ⟨λ a => ⟨λ b => ⟨λ c => ⟨⟨F.inst a b c⟩, ⟨F.e a b c⟩⟩,
                         DefPi.defAppPi (F.inst a b)⟩,
                 DefPi.defAppPi (F.inst a)⟩,
         DefPi.defAppPi F.inst⟩

      def cast {f g : ∀ a b c d, P a b c d} (efg : ∀ a b c d, f a b c d ≃ g a b c d)
               (F : DefPi₄ P f) :
          DefPi₄ P g :=
        ⟨λ a => DefPi₃.cast (efg a) (F.app a), F.toDefPi⟩

      structure DefEquiv {f : ∀ a b c d, P a b c d} (F G : DefPi₄ P f) where
        app (a : α) : DefPi₃.DefEquiv (F.app a) (G.app a)
        toDefEquiv : DefPi.DefEquiv (DefPi.cast (g := λ a => (G.app a).inst)
                                                (λ a => (app a).e) F.toDefPi) G.toDefPi

      namespace DefEquiv

        @[reducible] def cast {f g : ∀ a b c d, P a b c d}
                              {efgF efgG : ∀ a b c d, f a b c d ≃ g a b c d}
                              {F G : DefPi₄ P f} (e : DefEquiv F G) :
            DefEquiv (cast efgF F) (cast efgG G) :=
          ⟨λ a => DefPi₃.DefEquiv.cast (e.app a), e.toDefEquiv⟩

        variable {f : ∀ a b c d, P a b c d} {F G : DefPi₄ P f}

        def e (e : DefEquiv F G) : F.inst ≃ G.inst := e.toDefEquiv.e

        -- TODO
        --@[reducible] def toDefPi₃ (e : DefEquiv F G) :
        --    Layer1.HasPiType.DefPi₄ (hPiPabc := λ a b => hasEqPi₂ (F.inst a b) (G.inst a b))
        --                            (hPiPab := λ a => hasEqPi₃ (F.inst a) (G.inst a))
        --                            (hPiPa := hasEqPi₄ F.inst G.inst)
        --                            (λ a b c d => F.inst a b c d ≃ G.inst a b c d)
        --                            (λ a b c d => (G.e a b c d)⁻¹ • F.e a b c d) :=
        --  _

        -- TODO
        --@[reducible] def fromDefPi₃ (e : Layer1.HasPiType.DefPi₄ (hPiPabc := λ a b => hasEqPi₂ (F.inst a b) (G.inst a b))
        --                                                         (hPiPab := λ a => hasEqPi₃ (F.inst a) (G.inst a))
        --                                                         (hPiPa := hasEqPi₄ F.inst G.inst)
        --                                                         (λ a b c d => F.inst a b c d ≃ G.inst a b c d)
        --                                                         (λ a b c d => (G.e a b c d)⁻¹ • F.e a b c d) :
        --    DefEquiv F G :=
        --  _

      end DefEquiv

      def defAppPi (F : Pi₄ P) : DefPi₄ P (apply₄ F) :=
        ⟨λ a => DefPi₃.defAppPi (F a), DefPi.defAppPi F⟩

      def hasEqPi₄ {f g : ∀ a b c d, P a b c d} (F : DefPi₄ P f) (G : DefPi₄ P g) :
          Layer1.HasPiType (λ a => Pi₃ (hPab := λ b c => DefPi.hasEqPi (((F.app a).app b).app c)
                                                                       (((G.app a).app b).app c))
                                       (hPiPab := λ b => DefPi₂.hasEqPi₂ ((F.app a).app b)
                                                                         ((G.app a).app b))
                                       (hPiPa := DefPi₃.hasEqPi₃ (F.app a) (G.app a))
                                       (λ b c d => f a b c d ≃ g a b c d)) :=
        DefPi.hasEqPi F.toDefPi G.toDefPi

    end DefPi₄

  end DefPi

  section DefPiAppEq

    structure DefPiAppEq {α : Sort u} {β : Sort u'} [Layer1.HasEquivalenceRelationBase Prp α]
                         {P : β → V} [HasPiTypeBase P] {f : α → ∀ b, P b} (app : ∀ a, DefPi P (f a))
                         (hfe : ∀ {a₁ a₂ : α} (e : a₁ ≃ a₂) b, f a₁ b ≃ f a₂ b) where
      defAppEq {a₁ a₂ : α} (e : a₁ ≃ a₂) :
        DefPi.DefEquiv (P := P) (DefPi.cast (hfe e) (app a₁)) (app a₂)
      defAppEqFun (a₁ a₂ : α) : a₁ ≃ a₂ ⥤{λ e => (defAppEq e).e} (app a₁).inst ≃ (app a₂).inst

    namespace DefPiAppEq

      variable {α : Sort u} {β : Sort u'} [Layer1.HasEquivalenceRelationBase Prp α] {P : β → V}
               [HasPiTypeBase P]

      section

        variable {f : α → ∀ b, P b} {app : ∀ a, DefPi P (f a)}
                 {hfe : ∀ {a₁ a₂ : α} (e : a₁ ≃ a₂) b, f a₁ b ≃ f a₂ b} (eq : DefPiAppEq app hfe)

        @[reducible] def appEq {a₁ a₂ : α} (e : a₁ ≃ a₂) : (app a₁).inst ≃ (app a₂).inst :=
          (eq.defAppEq e).e

        @[reducible] def appEqFun (a₁ a₂ : α) : a₁ ≃ a₂ ⥤ (app a₁).inst ≃ (app a₂).inst :=
          (eq.defAppEqFun a₁ a₂).inst

        instance appEq.isFunApp {a₁ a₂ : α} (e : a₁ ≃ a₂) :
            Layer1.HasFunctors.IsFunApp (appEq eq e) :=
          ⟨appEqFun eq a₁ a₂, e⟩

        def eqFun : EquivalenceFunctor α (Pi P) where
          φ  := λ a => (app a).inst
          hφ := { inst := appEqFun eq }

      end

      def cast {f g : α → ∀ b, P b} (efg : ∀ a b, f a b ≃ g a b) {app : ∀ a, DefPi P (f a)}
               {hfe : ∀ {a₁ a₂ : α} (e : a₁ ≃ a₂) b, f a₁ b ≃ f a₂ b}
               {hge : ∀ {a₁ a₂ : α} (e : a₁ ≃ a₂) b, g a₁ b ≃ g a₂ b} (eq : DefPiAppEq app hfe) :
          DefPiAppEq (λ a => DefPi.cast (efg a) (app a)) hge where
        defAppEq e  := ⟨(eq.defAppEq e).e⟩
        defAppEqFun := eq.defAppEqFun

    end DefPiAppEq

    structure DefPiAppEq₂ {α : Sort u} {β : Sort u'} {γ : Sort u''}
                          [Layer1.HasEquivalenceRelationBase Prp α] {P : β → γ → V}
                          [∀ b, HasPiTypeBase (P b)] [HasPiTypeBase (λ b => Pi (P b))]
                          {f : α → ∀ b c, P b c} (app : ∀ a, DefPi₂ P (f a))
                          (hfe : ∀ {a₁ a₂ : α} (e : a₁ ≃ a₂) b c, f a₁ b c ≃ f a₂ b c) where
      defAppEq {a₁ a₂ : α} (e : a₁ ≃ a₂) :
        DefPi₂.DefEquiv (P := P) (DefPi₂.cast (hfe e) (app a₁)) (app a₂)
      defAppEqFun (a₁ a₂ : α) : a₁ ≃ a₂ ⥤{λ e => (defAppEq e).e} (app a₁).inst ≃ (app a₂).inst

    namespace DefPiAppEq₂

      variable {α : Sort u} {β : Sort u'} {γ : Sort u''} [Layer1.HasEquivalenceRelationBase Prp α]
               {P : β → γ → V} [∀ b, HasPiTypeBase (P b)] [HasPiTypeBase (λ b => Pi (P b))]

      section

        variable {f : α → ∀ b c, P b c} {app : ∀ a, DefPi₂ P (f a)}
                 {hfe : ∀ {a₁ a₂ : α} (e : a₁ ≃ a₂) b c, f a₁ b c ≃ f a₂ b c}
                 (eq : DefPiAppEq₂ app hfe)

        @[reducible] def appEq {a₁ a₂ : α} (e : a₁ ≃ a₂) : (app a₁).inst ≃ (app a₂).inst :=
          (eq.defAppEq e).e

        @[reducible] def appEqFun (a₁ a₂ : α) : a₁ ≃ a₂ ⥤ (app a₁).inst ≃ (app a₂).inst :=
          (eq.defAppEqFun a₁ a₂).inst

        instance appEq.isFunApp {a₁ a₂ : α} (e : a₁ ≃ a₂) :
            Layer1.HasFunctors.IsFunApp (appEq eq e) :=
          ⟨appEqFun eq a₁ a₂, e⟩

        def eqFun : EquivalenceFunctor α (Pi₂ P) where
          φ  := λ a => (app a).inst
          hφ := { inst := appEqFun eq }

      end

      def cast {f g : α → ∀ b c, P b c} (efg : ∀ a b c, f a b c ≃ g a b c)
               {app : ∀ a, DefPi₂ P (f a)}
               {hfe : ∀ {a₁ a₂ : α} (e : a₁ ≃ a₂) b c, f a₁ b c ≃ f a₂ b c}
               {hge : ∀ {a₁ a₂ : α} (e : a₁ ≃ a₂) b c, g a₁ b c ≃ g a₂ b c}
               (eq : DefPiAppEq₂ app hfe) :
          DefPiAppEq₂ (λ a => DefPi₂.cast (efg a) (app a)) hge where
        defAppEq e  := ⟨λ b => ⟨((eq.defAppEq e).app b).e⟩, (eq.defAppEq e).toDefEquiv⟩
        defAppEqFun := eq.defAppEqFun

    end DefPiAppEq₂

    structure DefPiAppEq₃ {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''}
                          [Layer1.HasEquivalenceRelationBase Prp α] {P : β → γ → δ → V}
                          [∀ b c, HasPiTypeBase (P b c)] [∀ b, HasPiTypeBase (λ c => Pi (P b c))]
                          [HasPiTypeBase (λ b => Pi₂ (P b))] {f : α → ∀ b c d, P b c d}
                          (app : ∀ a, DefPi₃ P (f a))
                          (hfe : ∀ {a₁ a₂ : α} (e : a₁ ≃ a₂) b c d, f a₁ b c d ≃ f a₂ b c d) where
      defAppEq {a₁ a₂ : α} (e : a₁ ≃ a₂) :
        DefPi₃.DefEquiv (P := P) (DefPi₃.cast (hfe e) (app a₁)) (app a₂)
      defAppEqFun (a₁ a₂ : α) : a₁ ≃ a₂ ⥤{λ e => (defAppEq e).e} (app a₁).inst ≃ (app a₂).inst

    namespace DefPiAppEq₃

      variable {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''}
               [Layer1.HasEquivalenceRelationBase Prp α] {P : β → γ → δ → V}
               [∀ b c, HasPiTypeBase (P b c)] [∀ b, HasPiTypeBase (λ c => Pi (P b c))]
               [HasPiTypeBase (λ b => Pi₂ (P b))]

      section

        variable {f : α → ∀ b c d, P b c d} {app : ∀ a, DefPi₃ P (f a)}
                 {hfe : ∀ {a₁ a₂ : α} (e : a₁ ≃ a₂) b c d, f a₁ b c d ≃ f a₂ b c d}
                 (eq : DefPiAppEq₃ app hfe)

        @[reducible] def appEq {a₁ a₂ : α} (e : a₁ ≃ a₂) : (app a₁).inst ≃ (app a₂).inst :=
          (eq.defAppEq e).e

        @[reducible] def appEqFun (a₁ a₂ : α) : a₁ ≃ a₂ ⥤ (app a₁).inst ≃ (app a₂).inst :=
          (eq.defAppEqFun a₁ a₂).inst

        instance appEq.isFunApp {a₁ a₂ : α} (e : a₁ ≃ a₂) :
            Layer1.HasFunctors.IsFunApp (appEq eq e) :=
          ⟨appEqFun eq a₁ a₂, e⟩

        def eqFun : EquivalenceFunctor α (Pi₃ P) where
          φ  := λ a => (app a).inst
          hφ := { inst := appEqFun eq }

      end

      def cast {f g : α → ∀ b c d, P b c d} (efg : ∀ a b c d, f a b c d ≃ g a b c d)
               {app : ∀ a, DefPi₃ P (f a)}
               {hfe : ∀ {a₁ a₂ : α} (e : a₁ ≃ a₂) b c d, f a₁ b c d ≃ f a₂ b c d}
               {hge : ∀ {a₁ a₂ : α} (e : a₁ ≃ a₂) b c d, g a₁ b c d ≃ g a₂ b c d}
               (eq : DefPiAppEq₃ app hfe) :
          DefPiAppEq₃ (λ a => DefPi₃.cast (efg a) (app a)) hge where
        defAppEq e  := ⟨λ b => ⟨λ c => ⟨(((eq.defAppEq e).app b).app c).e⟩,
                                ((eq.defAppEq e).app b).toDefEquiv⟩,
                        (eq.defAppEq e).toDefEquiv⟩
        defAppEqFun := eq.defAppEqFun

    end DefPiAppEq₃

  end DefPiAppEq

  instance {α : Sort u} (P : α → V) [h : HasPiTypeBase P] {β : Sort u'} (b : β) :
    HasPiTypeBase ((Function.const β P) b) := h

  instance {α : Sort u} (P : α → V) [h : HasPiTypeBase P] {β : Sort u'} (b : β) {γ : Sort u''}
           (c : γ) :
    HasPiTypeBase ((Function.const β (Function.const γ P)) b c) := h

  instance {α : Sort u} (P : α → V) [h : HasPiTypeBase P] {β : Sort u'} (b : β) :
    HasPiTypeBase (λ a => (Function.const β (P a)) b) := h

  instance {α : Sort u} {β : Sort u'} (P : α → β → V) (a : α) [h : HasPiTypeBase (P a)]
           {γ : Sort u''} (c : γ) :
    HasPiTypeBase ((Function.const γ P) c a) := h

  instance {α : Sort u} {β : Sort u'} {γ : Sort u''} (P : α → β → γ → V) (a : α) (b : β)
           [h : HasPiTypeBase (P a b)] {δ : Sort u'''} (d : δ) :
    HasPiTypeBase ((Function.const δ P) d a b) := h

end HasPiTypeBase

open HasPiTypeBase



section

  variable {U : Universe.{u}} [HasPropositions Prp U]

  instance (α : Sort u) [Layer1.HasEquivalenceRelationBase Prp α] (Y : U) :
      HasDefEq (EquivalenceFunctor α Y) :=
    HasDefEq.lift (α := α → Y) PreorderFunctor.φ

  instance (α β : Sort u) [Layer1.HasEquivalenceRelationBase Prp α]
           [Layer1.HasEquivalenceRelationBase Prp β] (Y : U) :
      HasDefEq (EquivalenceFunctor₂ α β Y) :=
    HasDefEq.lift (α := α → β → Y) PreorderFunctor₂.φ

  instance (α β γ : Sort u) [Layer1.HasEquivalenceRelationBase Prp α]
           [Layer1.HasEquivalenceRelationBase Prp β] [Layer1.HasEquivalenceRelationBase Prp γ]
           (Y : U) :
      HasDefEq (EquivalenceFunctor₃ α β γ Y) :=
    HasDefEq.lift (α := α → β → γ → Y) PreorderFunctor₃.φ

  instance (α β γ δ : Sort u) [Layer1.HasEquivalenceRelationBase Prp α]
           [Layer1.HasEquivalenceRelationBase Prp β] [Layer1.HasEquivalenceRelationBase Prp γ]
           [Layer1.HasEquivalenceRelationBase Prp δ] (Y : U) :
      HasDefEq (EquivalenceFunctor₄ α β γ δ Y) :=
    HasDefEq.lift (α := α → β → γ → δ → Y) PreorderFunctor₄.φ

end


class HasFunctors (α : Sort u) {U : Universe.{u}} [HasPropositions Prp U]
                  [Layer1.HasEquivalenceRelationBase Prp α] (Y : U) where
  defFunType : DefType U (EquivalenceFunctor α Y)
  defCongrFunFun (F G : defFunType.A) (a : α) :
    F ≃ G ⥤{λ e => (defFunType.elimCongrArg e) a} (defFunType.elim F) a ≃ (defFunType.elim G) a

namespace HasFunctors

  open Layer1.HasFunctors

  variable {U : Universe.{u}} [HasPropositions Prp U]

  section

    variable (α : Sort u) [Layer1.HasEquivalenceRelationBase Prp α] (Y : U) [h : HasFunctors α Y]

    instance toHasPiTypeBase : HasPiTypeBase (Function.const α Y) where
      defPiType      := { A            := h.defFunType.A,
                          elim         := λ F => (h.defFunType.elim F).φ,
                          elimCongrArg := h.defFunType.elimCongrArg }
      defCongrFunFun := h.defCongrFunFun

    instance : HasPiTypeBase (λ _ : α => Y) := h.toHasPiTypeBase

    instance toLayer1 : Layer1.HasFunctors α Y := ⟨⟩

  end

  section

    open Layer1.HasPiType

    instance {α : Sort u} [Layer1.HasEquivalenceRelationBase Prp α] (Y : U) [h : HasFunctors α Y]
             {β : Sort u'} (b : β) :
        HasFunctors α ((Function.const β Y) b) :=
      h

    instance (α : Sort u) [Layer1.HasEquivalenceRelationBase Prp α] (Y : U) [h : HasFunctors α Y]
             {β : Sort u'} (b : β) :
        HasPiTypeBase ((Function.const β (Function.const α Y)) b) :=
      h.toHasPiTypeBase

    instance (α : Sort u) [Layer1.HasEquivalenceRelationBase Prp α] (Y : U) [h : HasFunctors α Y]
             {β : Sort u'} {γ : Sort u'} (b : β) (c : γ) :
        HasPiTypeBase ((Function.const γ (Function.const β (Function.const α Y))) c b) :=
      h.toHasPiTypeBase

    instance (α : Sort u) [Layer1.HasEquivalenceRelationBase Prp α] (Y : U) [h : HasFunctors α Y]
             {β : Sort u'} (f : α → β) :
        HasPiTypeBase (λ a => (Function.const β Y) (f a)) :=
      h.toHasPiTypeBase

    instance (α : Sort u) [Layer1.HasEquivalenceRelationBase Prp α] (Y : U) [h : HasFunctors α Y]
             {β : Sort u'} (f : α → β) :
        HasPiTypeBase (λ a => (Function.const α (Function.const β Y)) a (f a)) :=
      h.toHasPiTypeBase

    instance {α β : Sort u} [Layer1.HasEquivalenceRelationBase Prp α]
             [Layer1.HasEquivalenceRelationBase Prp β] {Y : U} [HasFunctors β Y]
             [h : HasFunctors α (β ⥤ Y)] :
        HasPiTypeBase (λ a => Layer1.HasPiType.Pi (Function.const α (Function.const β Y) a)) :=
      h.toHasPiTypeBase

    instance (α : Sort u) [Layer1.HasEquivalenceRelationBase Prp α] {β : Sort u'} (P : β → U)
             [HasPiTypeBase P] [h : HasFunctors α (Pi P)] :
        HasPiTypeBase (λ a => Pi ((Function.const α P) a)) :=
      h.toHasPiTypeBase

    instance (α : Sort u) [Layer1.HasEquivalenceRelationBase Prp α] (β : Sort u') (γ : Sort u'')
             (P : β → γ → U) [∀ b, HasPiTypeBase (P b)] [HasPiTypeBase (λ b => Pi (P b))]
             [h : HasFunctors α (Pi₂ P)] :
        HasPiTypeBase (λ a => Pi₂ ((Function.const α P) a)) :=
      h.toHasPiTypeBase

    instance (α : Sort u) [Layer1.HasEquivalenceRelationBase Prp α] (β : Sort u') (γ : Sort u'')
             (δ : Sort u''') (P : β → γ → δ → U) [∀ b c, HasPiTypeBase (P b c)]
             [∀ b, HasPiTypeBase (λ c => Pi (P b c))] [HasPiTypeBase (λ b => Pi₂ (P b))]
             [h : HasFunctors α (Pi₃ P)] :
        HasPiTypeBase (λ a => Pi₃ ((Function.const α P) a)) :=
      h.toHasPiTypeBase

    instance {α : Sort u} (P : α → U) [HasPiTypeBase P] (a : α) [h : HasFunctors (Pi P) (P a)] :
        HasPiTypeBase (λ F => (Function.const (Pi P) P) F a) :=
      h.toHasPiTypeBase

    instance {α : Sort u} (P : α → U) [HasPiTypeBase P] (a : α) [h : HasFunctors (Pi P) (P a)] :
        HasPiTypeBase (λ F => (λ F' a' => Function.const (Pi P) (P a') F') F a) :=
      h.toHasPiTypeBase

  end

  section

    variable {α : Sort u} [Layer1.HasEquivalenceRelationBase Prp α] {Y : U} [h : HasFunctors α Y]

    @[reducible] def equivalenceFunctor (F : α ⥤ Y) : EquivalenceFunctor α Y := h.defFunType.elim F

    def byDef {f : α → Y} {F : α ⥤{f} Y} [hF : DefType.HasDefInstEq F] {a : α} : F.inst a ≃ f a :=
      HasPiTypeBase.byDef

    @[reducible] def congrArgFun (F : α ⥤ Y) (a b : α) : a ≃ b ⥤ F a ≃ F b :=
      (equivalenceFunctor F).hφ.inst a b

    @[reducible] def congrArg (F : α ⥤ Y) {a b : α} (e : a ≃ b) : F a ≃ F b :=
      (congrArgFun F a b) e

    def congr {F G : α ⥤ Y} (eFG : F ≃ G) {a b : α} (eab : a ≃ b) : F a ≃ G b :=
      congrArg G eab • congrFun eFG a

    def congr' {F G : α ⥤ Y} (eFG : F ≃ G) {a b : α} (eab : a ≃ b) : F a ≃ G b :=
      congrFun eFG b • congrArg F eab

    instance apply.isEquivalenceFunctor (F : α ⥤ Y) :
        IsPreorderFunctor (α := asPreorder α) (β := asPreorder Y) (apply (α := α) F) where
      inst := congrArgFun F

    @[reducible] def eqPiFun [Layer1.HasNonLinearLogic Prp] (F G : α ⥤ Y) :
        EquivalenceFunctor α Prp where
      φ  := λ a => F a ≃ G a
      hφ := { inst := λ a₁ a₂ => Λ e => Layer1.HasHomEquivalences.isoEquiv (α := asPreorder Y)
                                                                           (congrArg F e⁻¹)
                                                                           (congrArg G e) }

    instance hasFunEqPi [Layer1.HasNonLinearLogic Prp] (F G : α ⥤ Y) :
        Layer1.HasFunctorialPiType (eqPiFun F G) where
      toHasPiType := hasEqPi F G

    instance hasNat (F G : α ⥤ Y) :
        HasNaturalTransformations (equivalenceFunctor F) (equivalenceFunctor G) where
      toHasNaturalTransformationsBase := hasNatBase F G

  end

  section

    variable {α β : Sort u} [Layer1.HasEquivalenceRelationBase Prp α]
             [Layer1.HasEquivalenceRelationBase Prp β] {Y : U} [HasFunctors β Y]
             [HasFunctors α (β ⥤ Y)]

    def byDef₂ {f : α → β → Y} {F : α ⥤ β ⥤{f} Y} [hFa : ∀ a, DefType.HasDefInstEq (F.app a)]
               [hF : DefType.HasDefInstEq F.toDefFun] {a : α} {b : β} :
        F.inst a b ≃ f a b :=
      HasPiTypeBase.byDef₂

    @[reducible] def congrArg₂ (F : α ⥤ β ⥤ Y) {a₁ a₂ : α} (ea : a₁ ≃ a₂) {b₁ b₂ : β}
                               (eb : b₁ ≃ b₂) :
        F a₁ b₁ ≃ F a₂ b₂ :=
      congr (congrArg F ea) eb

    instance apply₂.isEquivalenceFunctor₂ (F : α ⥤ β ⥤ Y) :
        IsPreorderFunctor₂ (α := asPreorder α) (β := asPreorder β) (γ := asPreorder Y)
                           (apply₂ (α := α) (β := β) F) where
      app  a := apply.isEquivalenceFunctor (F a)
      app₂ b := { inst := λ a₁ a₂ => Λ e => congrFun (congrArg F e) b }

  end

  section

    variable {α β γ : Sort u} [Layer1.HasEquivalenceRelationBase Prp α]
             [Layer1.HasEquivalenceRelationBase Prp β] [Layer1.HasEquivalenceRelationBase Prp γ]
             {Y : U} [HasFunctors γ Y] [HasFunctors β (γ ⥤ Y)] [HasFunctors α (β ⥤ γ ⥤ Y)]

    def byDef₃ {f : α → β → γ → Y} {F : α ⥤ β ⥤ γ ⥤{f} Y}
               [hFab : ∀ a b, DefType.HasDefInstEq ((F.app a).app b)]
               [hFa : ∀ a, DefType.HasDefInstEq (F.app a).toDefFun]
               [hF : DefType.HasDefInstEq F.toDefFun] {a : α} {b : β} {c : γ} :
        F.inst a b c ≃ f a b c :=
      HasPiTypeBase.byDef₃

    @[reducible] def congrArg₃ (F : α ⥤ β ⥤ γ ⥤ Y) {a₁ a₂ : α} (ea : a₁ ≃ a₂) {b₁ b₂ : β}
                               (eb : b₁ ≃ b₂) {c₁ c₂ : γ} (ec : c₁ ≃ c₂) :
        F a₁ b₁ c₁ ≃ F a₂ b₂ c₂ :=
      congr (congrArg₂ F ea eb) ec

    instance apply₃.isEquivalenceFunctor₃ (F : α ⥤ β ⥤ γ ⥤ Y) :
        IsPreorderFunctor₃ (α := asPreorder α) (β := asPreorder β) (γ := asPreorder γ)
                           (δ := asPreorder Y) (apply₃ (α := α) (β := β) (γ := γ) F) where
      app   a   := (apply₂.isEquivalenceFunctor₂ (F a)).toAbstractMultiFun₂
      app₂₃ b c := { inst := λ a₁ a₂ => Λ e => congrFun₂ (congrArg F e) b c }

  end

  section

    variable {α β γ δ : Sort u} [Layer1.HasEquivalenceRelationBase Prp α]
             [Layer1.HasEquivalenceRelationBase Prp β] [Layer1.HasEquivalenceRelationBase Prp γ]
             [Layer1.HasEquivalenceRelationBase Prp δ] {Y : U} [HasFunctors δ Y]
             [HasFunctors γ (δ ⥤ Y)] [HasFunctors β (γ ⥤ δ ⥤ Y)] [HasFunctors α (β ⥤ γ ⥤ δ ⥤ Y)]

    def byDef₄ {f : α → β → γ → δ → Y} {F : α ⥤ β ⥤ γ ⥤ δ ⥤{f} Y}
               [hFabc : ∀ a b c, DefType.HasDefInstEq (((F.app a).app b).app c)]
               [hFab : ∀ a b, DefType.HasDefInstEq ((F.app a).app b).toDefFun]
               [hFa : ∀ a, DefType.HasDefInstEq (F.app a).toDefFun]
               [hF : DefType.HasDefInstEq F.toDefFun] {a : α} {b : β} {c : γ} {d : δ} :
        F.inst a b c d ≃ f a b c d :=
      HasPiTypeBase.byDef₄

    @[reducible] def congrArg₄ (F : α ⥤ β ⥤ γ ⥤ δ ⥤ Y) {a₁ a₂ : α} (ea : a₁ ≃ a₂) {b₁ b₂ : β}
                               (eb : b₁ ≃ b₂) {c₁ c₂ : γ} (ec : c₁ ≃ c₂) {d₁ d₂ : δ} (ed : d₁ ≃ d₂) :
        F a₁ b₁ c₁ d₁ ≃ F a₂ b₂ c₂ d₂ :=
      congr (congrArg₃ F ea eb ec) ed

    instance apply₄.isEquivalenceFunctor₄ (F : α ⥤ β ⥤ γ ⥤ δ ⥤ Y) :
        IsPreorderFunctor₄ (α := asPreorder α) (β := asPreorder β) (γ := asPreorder γ)
                           (δ := asPreorder δ) (ε := asPreorder Y)
                           (apply₄ (α := α) (β := β) (γ := γ) (δ := δ) F) where
      app    a     := (apply₃.isEquivalenceFunctor₃ (F a)).toAbstractMultiFun₃
      app₂₃₄ b c d := { inst := λ a₁ a₂ => Λ e => congrFun₃ (congrArg F e) b c d }

  end

  section

    @[reducible] def defFunType₂ (α β : Sort u) [Layer1.HasEquivalenceRelationBase Prp α]
                                 [Layer1.HasEquivalenceRelationBase Prp β] (Y : U) [HasFunctors β Y]
                                 [HasFunctors α (β ⥤ Y)] :
        DefType U (EquivalenceFunctor₂ α β Y) where
      A              := α ⥤ β ⥤ Y
      elim F         := ⟨apply₂ (α := α) (β := β) F⟩
      elimCongrArg e := congrFun₂ e

    @[reducible] def defFunType₃ (α β γ : Sort u) [Layer1.HasEquivalenceRelationBase Prp α]
                                 [Layer1.HasEquivalenceRelationBase Prp β]
                                 [Layer1.HasEquivalenceRelationBase Prp γ] (Y : U) [HasFunctors γ Y]
                                 [HasFunctors β (γ ⥤ Y)] [HasFunctors α (β ⥤ γ ⥤ Y)] :
        DefType U (EquivalenceFunctor₃ α β γ Y) where
      A              := α ⥤ β ⥤ γ ⥤ Y
      elim F         := ⟨apply₃ (α := α) (β := β) (γ := γ) F⟩
      elimCongrArg e := congrFun₃ e

    @[reducible] def defFunType₄ (α β γ δ : Sort u) [Layer1.HasEquivalenceRelationBase Prp α]
                                 [Layer1.HasEquivalenceRelationBase Prp β]
                                 [Layer1.HasEquivalenceRelationBase Prp γ]
                                 [Layer1.HasEquivalenceRelationBase Prp δ] (Y : U) [HasFunctors δ Y]
                                 [HasFunctors γ (δ ⥤ Y)] [HasFunctors β (γ ⥤ δ ⥤ Y)]
                                 [HasFunctors α (β ⥤ γ ⥤ δ ⥤ Y)] :
        DefType U (EquivalenceFunctor₄ α β γ δ Y) where
      A              := α ⥤ β ⥤ γ ⥤ δ ⥤ Y
      elim F         := ⟨apply₄ (α := α) (β := β) (γ := γ) (δ := δ) F⟩
      elimCongrArg e := congrFun₄ e

  end

  -- Helper classes for the `functoriality` tactic.
  section Helpers

    variable {Y : U}

    class IsFunApp (y : Y) where
      {α : Sort u}
      [hαEq : Layer1.HasEquivalenceRelationBase Prp α]
      [hα : HasFunctors α Y]
      F : α ⥤ Y
      a : α
      e : F a ≃ y

    namespace IsFunApp

      instance (priority := low) refl {α : Sort u} [Layer1.HasEquivalenceRelationBase Prp α]
                                      [HasFunctors α Y] {F : α ⥤ Y} {a : α} :
          IsFunApp (F a) :=
        ⟨F, a, idIso (F a)⟩

      variable (y : Y) [hApp : IsFunApp y]

      instance : Layer1.HasEquivalenceRelationBase Prp hApp.α := hApp.hαEq
      instance : HasFunctors hApp.α Y := hApp.hα

      def isPiApp : IsPiApp y := ⟨hApp.F, hApp.a, rfl, hApp.e⟩

      instance toLayer1 : Layer1.HasFunctors.IsFunApp y := ⟨hApp.F, hApp.a⟩

    end IsFunApp

    class IsFunApp₂ (y : Y) where
      {α β : Sort u}
      [hαEq : Layer1.HasEquivalenceRelationBase Prp α]
      [hβEq : Layer1.HasEquivalenceRelationBase Prp β]
      [hβ : HasFunctors β Y]
      [hα : HasFunctors α (β ⥤ Y)]
      F : α ⥤ β ⥤ Y
      a : α
      b : β
      e : F a b ≃ y

    namespace IsFunApp₂

      instance (priority := low) refl {α β : Sort u} [Layer1.HasEquivalenceRelationBase Prp α]
                                      [Layer1.HasEquivalenceRelationBase Prp β] [HasFunctors β Y]
                                      [HasFunctors α (β ⥤ Y)] {F : α ⥤ β ⥤ Y} {a : α} {b : β} :
          IsFunApp₂ (F a b) :=
        ⟨F, a, b, idIso (F a b)⟩

      variable (y : Y) [hApp : IsFunApp₂ y]

      instance : Layer1.HasEquivalenceRelationBase Prp hApp.α := hApp.hαEq
      instance : Layer1.HasEquivalenceRelationBase Prp hApp.β := hApp.hβEq
      instance : HasFunctors hApp.β Y := hApp.hβ
      instance : HasFunctors hApp.α (hApp.β ⥤ Y) := hApp.hα

      def isFunApp : IsFunApp y := ⟨hApp.F hApp.a, hApp.b, hApp.e⟩

      def isPiApp₂ : IsPiApp₂ y := ⟨hApp.F, hApp.a, hApp.b, rfl, hApp.e⟩

      instance toLayer1 : Layer1.HasFunctors.IsFunApp₂ y := ⟨hApp.F, hApp.a, hApp.b⟩

    end IsFunApp₂

    class IsFunApp₃ (y : Y) where
      {α β γ : Sort u}
      [hαEq : Layer1.HasEquivalenceRelationBase Prp α]
      [hβEq : Layer1.HasEquivalenceRelationBase Prp β]
      [hγEq : Layer1.HasEquivalenceRelationBase Prp γ]
      [hγ : HasFunctors γ Y]
      [hβ : HasFunctors β (γ ⥤ Y)]
      [hα : HasFunctors α (β ⥤ γ ⥤ Y)]
      F : α ⥤ β ⥤ γ ⥤ Y
      a : α
      b : β
      c : γ
      e : F a b c ≃ y

    namespace IsFunApp₃

      instance (priority := low) refl {α β γ : Sort u} [Layer1.HasEquivalenceRelationBase Prp α]
                                      [Layer1.HasEquivalenceRelationBase Prp β]
                                      [Layer1.HasEquivalenceRelationBase Prp γ] [HasFunctors γ Y]
                                      [HasFunctors β (γ ⥤ Y)] [HasFunctors α (β ⥤ γ ⥤ Y)]
                                      {F : α ⥤ β ⥤ γ ⥤ Y} {a : α} {b : β} {c : γ} :
          IsFunApp₃ (F a b c) :=
        ⟨F, a, b, c, idIso (F a b c)⟩

      variable (y : Y) [hApp : IsFunApp₃ y]

      instance : Layer1.HasEquivalenceRelationBase Prp hApp.α := hApp.hαEq
      instance : Layer1.HasEquivalenceRelationBase Prp hApp.β := hApp.hβEq
      instance : Layer1.HasEquivalenceRelationBase Prp hApp.γ := hApp.hγEq
      instance : HasFunctors hApp.γ Y := hApp.hγ
      instance : HasFunctors hApp.β (hApp.γ ⥤ Y) := hApp.hβ
      instance : HasFunctors hApp.α (hApp.β ⥤ hApp.γ ⥤ Y) := hApp.hα

      def isFunApp₂ : IsFunApp₂ y := ⟨hApp.F hApp.a, hApp.b, hApp.c, hApp.e⟩

      def isFunApp : IsFunApp y :=
        let _ : IsFunApp₂ y := isFunApp₂ y
        IsFunApp₂.isFunApp y

      -- TODO: Don't know why this fails.
      --def isPiApp₃ : IsPiApp₃ y := ⟨hApp.F, hApp.a, hApp.b, hApp.c, rfl, hApp.e⟩

      instance toLayer1 : Layer1.HasFunctors.IsFunApp₃ y := ⟨hApp.F, hApp.a, hApp.b, hApp.c⟩

    end IsFunApp₃

    class IsFunApp₄ (y : Y) where
      {α β γ δ : Sort u}
      [hαEq : Layer1.HasEquivalenceRelationBase Prp α]
      [hβEq : Layer1.HasEquivalenceRelationBase Prp β]
      [hγEq : Layer1.HasEquivalenceRelationBase Prp γ]
      [hδEq : Layer1.HasEquivalenceRelationBase Prp δ]
      [hδ : HasFunctors δ Y]
      [hγ : HasFunctors γ (δ ⥤ Y)]
      [hβ : HasFunctors β (γ ⥤ δ ⥤ Y)]
      [hα : HasFunctors α (β ⥤ γ ⥤ δ ⥤ Y)]
      F : α ⥤ β ⥤ γ ⥤ δ ⥤ Y
      a : α
      b : β
      c : γ
      d : δ
      e : F a b c d ≃ y

    namespace IsFunApp₄

      instance (priority := low) refl {α β γ δ : Sort u} [Layer1.HasEquivalenceRelationBase Prp α]
                                      [Layer1.HasEquivalenceRelationBase Prp β]
                                      [Layer1.HasEquivalenceRelationBase Prp γ]
                                      [Layer1.HasEquivalenceRelationBase Prp δ] [HasFunctors δ Y]
                                      [HasFunctors γ (δ ⥤ Y)] [HasFunctors β (γ ⥤ δ ⥤ Y)]
                                      [HasFunctors α (β ⥤ γ ⥤ δ ⥤ Y)] {F : α ⥤ β ⥤ γ ⥤ δ ⥤ Y}
                                      {a : α} {b : β} {c : γ} {d : δ} :
          IsFunApp₄ (F a b c d) :=
        ⟨F, a, b, c, d, idIso (F a b c d)⟩

      variable (y : Y) [hApp : IsFunApp₄ y]

      instance : Layer1.HasEquivalenceRelationBase Prp hApp.α := hApp.hαEq
      instance : Layer1.HasEquivalenceRelationBase Prp hApp.β := hApp.hβEq
      instance : Layer1.HasEquivalenceRelationBase Prp hApp.γ := hApp.hγEq
      instance : Layer1.HasEquivalenceRelationBase Prp hApp.δ := hApp.hδEq
      instance : HasFunctors hApp.δ Y := hApp.hδ
      instance : HasFunctors hApp.γ (hApp.δ ⥤ Y) := hApp.hγ
      instance : HasFunctors hApp.β (hApp.γ ⥤ hApp.δ ⥤ Y) := hApp.hβ
      instance : HasFunctors hApp.α (hApp.β ⥤ hApp.γ ⥤ hApp.δ ⥤ Y) := hApp.hα

      def isFunApp₃ : IsFunApp₃ y := ⟨hApp.F hApp.a, hApp.b, hApp.c, hApp.d, hApp.e⟩

      def isFunApp₂ : IsFunApp₂ y :=
        let _ : IsFunApp₃ y := isFunApp₃ y
        IsFunApp₃.isFunApp₂ y

      def isFunApp : IsFunApp y :=
        let _ : IsFunApp₂ y := isFunApp₂ y
        IsFunApp₂.isFunApp y

      -- TODO: Don't know why this fails.
      --def isPiApp₄ : IsPiApp₄ y := ⟨hApp.F, hApp.a, hApp.b, hApp.c, hApp.d, rfl, hApp.e⟩

      instance toLayer1 : Layer1.HasFunctors.IsFunApp₄ y := ⟨hApp.F, hApp.a, hApp.b, hApp.c, hApp.d⟩

    end IsFunApp₄

    class IsFunApp₂' (y : Y) extends IsFunApp y where
      h₂ : IsFunApp y

    namespace IsFunApp₂'

      variable (y : Y) [hApp : IsFunApp₂' y]

      def isPiApp₂' : IsPiApp₂' y where
        toIsPiApp := IsFunApp.isPiApp y
        h₂ := IsFunApp.isPiApp y (hApp := hApp.h₂)

      instance toLayer1 : Layer1.HasFunctors.IsFunApp₂' y := ⟨inferInstance⟩

    end IsFunApp₂'

    class IsFunApp₃' (y : Y) extends IsFunApp₂' y where
      h₃ : IsFunApp y

    namespace IsFunApp₃'

      variable (y : Y) [hApp : IsFunApp₃' y]

      def isPiApp₃' : IsPiApp₃' y where
        toIsPiApp₂' := IsFunApp₂'.isPiApp₂' y
        h₃ := IsFunApp.isPiApp y (hApp := hApp.h₃)

      instance toLayer1 : Layer1.HasFunctors.IsFunApp₃' y := ⟨inferInstance⟩

    end IsFunApp₃'

    class IsFunApp₄' (y : Y) extends IsFunApp₃' y where
      h₄ : IsFunApp y

    namespace IsFunApp₄'

      variable (y : Y) [hApp : IsFunApp₄' y]

      def isPiApp₄' : IsPiApp₄' y where
        toIsPiApp₃' := IsFunApp₃'.isPiApp₃' y
        h₄ := IsFunApp.isPiApp y (hApp := hApp.h₄)

      instance toLayer1 : Layer1.HasFunctors.IsFunApp₄' y := ⟨inferInstance⟩

    end IsFunApp₄'

  end Helpers

  section DefFun

    def DefFun (α : Sort u) [Layer1.HasEquivalenceRelationBase Prp α] (Y : U) [h : HasFunctors α Y]
               (f : EquivalenceFunctor α Y) :=
      DefType.DefInst h.defFunType f

    @[reducible] def DefFun' (α : Sort u) [Layer1.HasEquivalenceRelationBase Prp α] (Y : U)
                             [h : HasFunctors α Y] (f : α → Y)
                             (hf : ∀ a₁ a₂, a₁ ≃ a₂ ⥤ f a₁ ≃ f a₂) :=
      DefFun α Y (EquivalenceFunctor.mk f (hφ := IsPreorderFunctor.construct hf))

    namespace DefFun

      notation:20 α:21 " ⥤⦃" f:0 "⦄ " Y:21 => HasFunctors.DefFun α Y f
      notation:20 α:21 " ⥤{" f:0 ", " hf:0 "} " Y:21 => HasFunctors.DefFun' α Y f hf

      variable {α : Sort u} [Layer1.HasEquivalenceRelationBase Prp α] {Y : U} [h : HasFunctors α Y]

      @[reducible] def mk {f : EquivalenceFunctor α Y} (F : α ⥤ Y) (e : ∀ a, F a ≃ f a) :
          α ⥤⦃f⦄ Y :=
        ⟨⟨F⟩, ⟨e⟩⟩

      @[reducible] def inst {f : EquivalenceFunctor α Y} (F : α ⥤⦃f⦄ Y) : α ⥤ Y := F.toDefInst.inst

      instance coeType (f : EquivalenceFunctor α Y) : Coe (α ⥤⦃f⦄ Y) (α ⥤ Y) :=
        DefType.DefInst.coeType h.defFunType f

      def toLayer1 {f : EquivalenceFunctor α Y} (F : α ⥤⦃f⦄ Y) : α ⥤{f.φ} Y :=
        ⟨F.inst⟩

      instance (f : EquivalenceFunctor α Y) : Coe (α ⥤⦃f⦄ Y) (α ⥤{f.φ} Y) := ⟨toLayer1⟩

      def toDefPi {f : EquivalenceFunctor α Y} (F : α ⥤⦃f⦄ Y) : DefPi (Function.const α Y) f.φ :=
        ⟨⟨F.inst⟩, ⟨F.e⟩⟩

      instance (f : EquivalenceFunctor α Y) : Coe (α ⥤⦃f⦄ Y) (DefPi (Function.const α Y) f.φ) :=
        ⟨toDefPi⟩

      instance {f : EquivalenceFunctor α Y} (F : α ⥤⦃f⦄ Y) : DefType.HasDefInstEq F.toLayer1 :=
        F.toDefPi.toHasDefInstEq

      def isFunApp {f : EquivalenceFunctor α Y} (F : α ⥤⦃f⦄ Y) {a : α} : IsFunApp (f a) :=
        ⟨F.inst, a, F.e a⟩

      @[reducible] def cast {f g : EquivalenceFunctor α Y} (efg : ∀ a : α, f a ≃ g a)
                            (F : α ⥤⦃f⦄ Y) :
          α ⥤⦃g⦄ Y :=
        DefType.DefInst.cast efg F
      infix:60 " ► " => HasFunctors.DefFun.cast

      @[reducible] def DefEquiv {f : EquivalenceFunctor α Y} (F G : α ⥤⦃f⦄ Y) :=
        DefPi.DefEquiv (toDefPi F) (toDefPi G)
      infix:25 " {≃} " => HasFunctors.DefFun.DefEquiv

      @[reducible] def defAppFun (F : α ⥤ Y) : α ⥤⦃EquivalenceFunctor.mk (apply F)⦄ Y :=
        DefType.DefInst.fromInst F

      def hasEqPi {f g : EquivalenceFunctor α Y} (F : α ⥤⦃f⦄ Y) (G : α ⥤⦃g⦄ Y) :
          Layer1.HasPiType (λ a => f a ≃ g a) :=
        DefPi.hasEqPi F.toDefPi G.toDefPi

    end DefFun

    structure DefFun₂ (α β : Sort u) [Layer1.HasEquivalenceRelationBase Prp α]
                      [Layer1.HasEquivalenceRelationBase Prp β] (Y : U) [HasFunctors β Y]
                      [HasFunctors α (β ⥤ Y)] (f : EquivalenceFunctor₂ α β Y) where
      app (a : α) : β ⥤⦃f.app a⦄ Y
      appEq : DefPiAppEq (λ a => DefFun.toDefPi (app a)) (λ e b => (f.app₂ b).hφ e)
      toDefFun : α ⥤⦃DefPiAppEq.eqFun appEq⦄ (β ⥤ Y)

    @[reducible] def DefFun₂' (α β : Sort u) [Layer1.HasEquivalenceRelationBase Prp α]
                              [Layer1.HasEquivalenceRelationBase Prp β] (Y : U) [HasFunctors β Y]
                              [HasFunctors α (β ⥤ Y)] (f : α → β → Y)
                              (hfa : ∀ a b₁ b₂, b₁ ≃ b₂ ⥤ f a b₁ ≃ f a b₂)
                              (hfb : ∀ a₁ a₂ b, a₁ ≃ a₂ ⥤ f a₁ b ≃ f a₂ b) :=
      DefFun₂ α β Y (EquivalenceFunctor₂.mk f (hφ := IsPreorderFunctor₂.construct hfa hfb))

    namespace DefFun₂

      notation:20 α:21 " ⥤ " β:21 " ⥤⦃" f:0 "⦄ " Y:21 => HasFunctors.DefFun₂ α β Y f

      notation:20 α:21 " ⥤ " β:21 " ⥤{" f:0 ", " hfa:0 ", " hfb:0 "} " Y:21 =>
        HasFunctors.DefFun₂' α β Y f hfa hfb

      variable {α β : Sort u} [Layer1.HasEquivalenceRelationBase Prp α]
               [Layer1.HasEquivalenceRelationBase Prp β] {Y : U} [HasFunctors β Y]
               [HasFunctors α (β ⥤ Y)]

      @[reducible] def inst {f : EquivalenceFunctor₂ α β Y} (F : α ⥤ β ⥤⦃f⦄ Y) : α ⥤ β ⥤ Y :=
        F.toDefFun

      instance coeType (f : EquivalenceFunctor₂ α β Y) : Coe (α ⥤ β ⥤⦃f⦄ Y) (α ⥤ β ⥤ Y) := ⟨inst⟩

      @[reducible] def toLayer1 {f : EquivalenceFunctor₂ α β Y} (F : α ⥤ β ⥤⦃f⦄ Y) :
          α ⥤ β ⥤{f.φ} Y :=
        ⟨λ a => (F.app a).toLayer1, F.toDefFun.toLayer1⟩

      instance (f : EquivalenceFunctor₂ α β Y) : Coe (α ⥤ β ⥤⦃f⦄ Y) (α ⥤ β ⥤{f.φ} Y) :=
        ⟨toLayer1⟩

      def e {f : EquivalenceFunctor₂ α β Y} (F : α ⥤ β ⥤⦃f⦄ Y) (a : α) (b : β) :
          F.inst a b ≃ f a b :=
        byDef₂ (F := F.toLayer1)

      def isFunApp₂ {f : EquivalenceFunctor₂ α β Y} (F : α ⥤ β ⥤⦃f⦄ Y) {a : α} {b : β} :
          IsFunApp₂ (f a b) :=
        ⟨F.inst, a, b, F.e a b⟩

      def toDefInst {f : EquivalenceFunctor₂ α β Y} (F : α ⥤ β ⥤⦃f⦄ Y) :
          DefType.DefInst (defFunType₂ α β Y) f :=
        ⟨⟨F.inst⟩, ⟨F.e⟩⟩

      -- TODO: Apparently there is a defeq issue.
      --def fromDefInst {f : EquivalenceFunctor₂ α β Y} (F : DefType.DefInst (defFunType₂ α β Y) f) :
      --    α ⥤ β ⥤⦃f⦄ Y where
      --  app a    := ⟨⟨apply (α := α) (Y := β ⥤ Y) F.inst a⟩, λ b => F.e a b⟩
      --  appEq    := { defAppEq    := λ e => ⟨congrArg (α := α) (Y := β ⥤ Y) F.inst e⟩,
      --                defAppEqFun := λ a₁ a₂ => ⟨congrArgFun F.inst a₁ a₂⟩ }
      --  toDefFun := DefFun.defAppFun F.inst

      @[reducible] def cast {f g : EquivalenceFunctor₂ α β Y}
                            (efg : ∀ (a : α) (b : β), f a b ≃ g a b) (F : α ⥤ β ⥤⦃f⦄ Y) :
          α ⥤ β ⥤⦃g⦄ Y where
        app a    := DefFun.cast (f := f.app a) (g := g.app a) (efg a) (F.app a)
        appEq    := DefPiAppEq.cast efg (hfe := λ e b => (f.hφ.app₂ b) e) F.appEq
        toDefFun := F.toDefFun
      infix:60 " ►► " => HasFunctors.DefFun₂.cast

      def toDefPi₂ {f : EquivalenceFunctor₂ α β Y} (F : α ⥤ β ⥤⦃f⦄ Y) :
          DefPi₂ (Function.const α (Function.const β Y)) f.φ :=
        ⟨λ a => (F.app a).toDefPi, F.toDefFun.toDefPi⟩

      instance (f : EquivalenceFunctor₂ α β Y) :
          Coe (α ⥤ β ⥤⦃f⦄ Y) (DefPi₂ (Function.const α (Function.const β Y)) f.φ) :=
        ⟨toDefPi₂⟩

      @[reducible] def DefEquiv {f : EquivalenceFunctor₂ α β Y} (F G : α ⥤ β ⥤⦃f⦄ Y) :=
        DefPi₂.DefEquiv (toDefPi₂ F) (toDefPi₂ G)
      infix:25 " {≃≃} " => HasFunctors.DefFun₂.DefEquiv

      @[reducible] def defAppFun (F : α ⥤ β ⥤ Y) :
          α ⥤ β ⥤⦃EquivalenceFunctor₂.mk (apply₂ F)⦄ Y where
        app a    := DefFun.defAppFun (F a)
        appEq    := { defAppEq    := λ e => ⟨congrArg F e⟩,
                      defAppEqFun := λ a₁ a₂ => ⟨congrArgFun F a₁ a₂⟩ }
        toDefFun := DefFun.defAppFun F

      def hasEqPi₂ {f g : EquivalenceFunctor₂ α β Y} (F : α ⥤ β ⥤⦃f⦄ Y) (G : α ⥤ β ⥤⦃g⦄ Y) :
          Layer1.HasPiType (λ a => Layer1.HasPiType.Pi (h := DefFun.hasEqPi (F.app a) (G.app a))
                                                       (λ b => f a b ≃ g a b)) :=
        DefPi₂.hasEqPi₂ F.toDefPi₂ G.toDefPi₂

    end DefFun₂

    structure DefFun₃ (α β γ : Sort u) [Layer1.HasEquivalenceRelationBase Prp α]
                      [Layer1.HasEquivalenceRelationBase Prp β]
                      [Layer1.HasEquivalenceRelationBase Prp γ] (Y : U) [HasFunctors γ Y]
                      [HasFunctors β (γ ⥤ Y)] [HasFunctors α (β ⥤ γ ⥤ Y)]
                      (f : EquivalenceFunctor₃ α β γ Y) where
      app (a : α) : β ⥤ γ ⥤⦃f.app a⦄ Y
      appEq : DefPiAppEq₂ (λ a => DefFun₂.toDefPi₂ (app a)) (λ e b c => (f.hφ.app₂₃ b c) e)
      toDefFun : α ⥤⦃DefPiAppEq₂.eqFun appEq⦄ (β ⥤ γ ⥤ Y)

    @[reducible] def DefFun₃' (α β γ : Sort u) [Layer1.HasEquivalenceRelationBase Prp α]
                              [Layer1.HasEquivalenceRelationBase Prp β]
                              [Layer1.HasEquivalenceRelationBase Prp γ] (Y : U) [HasFunctors γ Y]
                              [HasFunctors β (γ ⥤ Y)] [HasFunctors α (β ⥤ γ ⥤ Y)]
                              (f : α → β → γ → Y)
                              (hfab : ∀ a b c₁ c₂, c₁ ≃ c₂ ⥤ f a b c₁ ≃ f a b c₂)
                              (hfac : ∀ a b₁ b₂ c, b₁ ≃ b₂ ⥤ f a b₁ c ≃ f a b₂ c)
                              (hfbc : ∀ a₁ a₂ b c, a₁ ≃ a₂ ⥤ f a₁ b c ≃ f a₂ b c) :=
      DefFun₃ α β γ Y (EquivalenceFunctor₃.mk f (hφ := IsPreorderFunctor₃.construct hfab hfac hfbc))

    namespace DefFun₃

      notation:20 α:21 " ⥤ " β:21 " ⥤ " γ:21 " ⥤⦃" f:0 "⦄ " Y:21 =>
        HasFunctors.DefFun₃ α β γ Y f

      notation:20 α:21 " ⥤ " β:21 " ⥤ " γ:21 " ⥤{" f:0 ", " hfab:0 ", " hfac:0 ", " hfbc:0 "} " Y:21 =>
        HasFunctors.DefFun₃' α β γ Y f hfab hfac hfbc

      variable {α β γ : Sort u} [Layer1.HasEquivalenceRelationBase Prp α]
               [Layer1.HasEquivalenceRelationBase Prp β] [Layer1.HasEquivalenceRelationBase Prp γ]
               {Y : U} [HasFunctors γ Y] [HasFunctors β (γ ⥤ Y)] [HasFunctors α (β ⥤ γ ⥤ Y)]

      @[reducible] def inst {f : EquivalenceFunctor₃ α β γ Y} (F : α ⥤ β ⥤ γ ⥤⦃f⦄ Y) :
          α ⥤ β ⥤ γ ⥤ Y :=
        F.toDefFun

      instance coeType (f : EquivalenceFunctor₃ α β γ Y) :
          Coe (α ⥤ β ⥤ γ ⥤⦃f⦄ Y) (α ⥤ β ⥤ γ ⥤ Y) :=
        ⟨inst⟩

      @[reducible] def toLayer1 {f : EquivalenceFunctor₃ α β γ Y} (F : α ⥤ β ⥤ γ ⥤⦃f⦄ Y) :
          α ⥤ β ⥤ γ ⥤{f.φ} Y :=
        ⟨λ a => (F.app a).toLayer1, F.toDefFun.toLayer1⟩

      instance (f : EquivalenceFunctor₃ α β γ Y) : Coe (α ⥤ β ⥤ γ ⥤⦃f⦄ Y) (α ⥤ β ⥤ γ ⥤{f.φ} Y) :=
        ⟨toLayer1⟩

      def e {f : EquivalenceFunctor₃ α β γ Y} (F : α ⥤ β ⥤ γ ⥤⦃f⦄ Y) (a : α) (b : β) (c : γ) :
          F.inst a b c ≃ f a b c :=
        byDef₃ (F := F.toLayer1)

      def isFunApp₃ {f : EquivalenceFunctor₃ α β γ Y} (F : α ⥤ β ⥤ γ ⥤⦃f⦄ Y) {a : α} {b : β}
                    {c : γ} :
          IsFunApp₃ (f a b c) :=
        ⟨F.inst, a, b, c, F.e a b c⟩

      def toDefInst {f : EquivalenceFunctor₃ α β γ Y} (F : α ⥤ β ⥤ γ ⥤⦃f⦄ Y) :
          DefType.DefInst (defFunType₃ α β γ Y) f :=
        ⟨⟨F.inst⟩, ⟨F.e⟩⟩

      -- TODO: See above.
      --def fromDefInst {f : EquivalenceFunctor₃ α β γ Y}
      --                (F : DefType.DefInst (defFunType₃ α β γ Y) f) :
      --    α ⥤ β ⥤ γ ⥤⦃f⦄ Y where
      --  app a    := ⟨⟨apply (α := α) (Y := β ⥤ γ ⥤ Y) F.inst a⟩, λ b c => F.e a b c⟩
      --  appEq    := _
      --  toDefFun := DefFun.defAppFun F.inst

      @[reducible] def cast {f g : EquivalenceFunctor₃ α β γ Y}
                            (efg : ∀ (a : α) (b : β) (c : γ), f a b c ≃ g a b c)
                            (F : α ⥤ β ⥤ γ ⥤⦃f⦄ Y) :
          α ⥤ β ⥤ γ ⥤⦃g⦄ Y where
        app a    := DefFun₂.cast (f := f.app a) (g := g.app a) (efg a) (F.app a)
        appEq    := DefPiAppEq₂.cast efg (hfe := λ e b c => (f.hφ.app₂₃ b c) e) F.appEq
        toDefFun := F.toDefFun
      infix:60 " ►►► " => HasFunctors.DefFun₃.cast

      def toDefPi₃ {f : EquivalenceFunctor₃ α β γ Y} (F : α ⥤ β ⥤ γ ⥤⦃f⦄ Y) :
          DefPi₃ (Function.const α (Function.const β (Function.const γ Y))) f.φ :=
        ⟨λ a => (F.app a).toDefPi₂, F.toDefFun.toDefPi⟩

      instance (f : EquivalenceFunctor₃ α β γ Y) :
          Coe (α ⥤ β ⥤ γ ⥤⦃f⦄ Y)
              (DefPi₃ (Function.const α (Function.const β (Function.const γ Y))) f.φ) :=
        ⟨toDefPi₃⟩

      @[reducible] def DefEquiv {f : EquivalenceFunctor₃ α β γ Y}
                                (F G : α ⥤ β ⥤ γ ⥤⦃f⦄ Y) :=
        DefPi₃.DefEquiv (toDefPi₃ F) (toDefPi₃ G)
      infix:25 " {≃≃≃} " => HasFunctors.DefFun₃.DefEquiv

      @[reducible] def defAppFun (F : α ⥤ β ⥤ γ ⥤ Y) :
          α ⥤ β ⥤ γ ⥤⦃EquivalenceFunctor₃.mk (apply₃ F)⦄ Y where
        app a    := DefFun₂.defAppFun (F a)
        appEq    := { defAppEq    := λ e => ⟨λ b => ⟨congrFun (congrArg F e) b⟩, ⟨congrArg F e⟩⟩,
                      defAppEqFun := λ a₁ a₂ => ⟨congrArgFun F a₁ a₂⟩ }
        toDefFun := DefFun.defAppFun F

      def hasEqPi₃ {f g : EquivalenceFunctor₃ α β γ Y} (F : α ⥤ β ⥤ γ ⥤⦃f⦄ Y)
                                                       (G : α ⥤ β ⥤ γ ⥤⦃g⦄ Y) :
          Layer1.HasPiType (λ a => Layer1.HasPiType.Pi₂ (hPa := λ b => DefFun.hasEqPi ((F.app a).app b)
                                                                                      ((G.app a).app b))
                                                        (hPiPa := DefFun₂.hasEqPi₂ (F.app a) (G.app a))
                                                        (λ b c => f a b c ≃ g a b c)) :=
        DefPi₃.hasEqPi₃ F.toDefPi₃ G.toDefPi₃

    end DefFun₃

    structure DefFun₄ (α β γ δ : Sort u) [Layer1.HasEquivalenceRelationBase Prp α]
                      [Layer1.HasEquivalenceRelationBase Prp β]
                      [Layer1.HasEquivalenceRelationBase Prp γ]
                      [Layer1.HasEquivalenceRelationBase Prp δ] (Y : U) [HasFunctors δ Y]
                      [HasFunctors γ (δ ⥤ Y)] [HasFunctors β (γ ⥤ δ ⥤ Y)]
                      [HasFunctors α (β ⥤ γ ⥤ δ ⥤ Y)] (f : EquivalenceFunctor₄ α β γ δ Y) where
      app (a : α) : β ⥤ γ ⥤ δ ⥤⦃f.app a⦄ Y
      appEq : DefPiAppEq₃ (λ a => DefFun₃.toDefPi₃ (app a)) (λ e b c d => (f.hφ.app₂₃₄ b c d) e)
      toDefFun : α ⥤⦃DefPiAppEq₃.eqFun appEq⦄ (β ⥤ γ ⥤ δ ⥤ Y)

    @[reducible] def DefFun₄' (α β γ δ : Sort u) [Layer1.HasEquivalenceRelationBase Prp α]
                              [Layer1.HasEquivalenceRelationBase Prp β]
                              [Layer1.HasEquivalenceRelationBase Prp γ]
                              [Layer1.HasEquivalenceRelationBase Prp δ] (Y : U) [HasFunctors δ Y]
                              [HasFunctors γ (δ ⥤ Y)] [HasFunctors β (γ ⥤ δ ⥤ Y)]
                              [HasFunctors α (β ⥤ γ ⥤ δ ⥤ Y)]
                              (f : α → β → γ → δ → Y)
                              (hfabc : ∀ a b c d₁ d₂, d₁ ≃ d₂ ⥤ f a b c d₁ ≃ f a b c d₂)
                              (hfabd : ∀ a b c₁ c₂ d, c₁ ≃ c₂ ⥤ f a b c₁ d ≃ f a b c₂ d)
                              (hfacd : ∀ a b₁ b₂ c d, b₁ ≃ b₂ ⥤ f a b₁ c d ≃ f a b₂ c d)
                              (hfbcd : ∀ a₁ a₂ b c d, a₁ ≃ a₂ ⥤ f a₁ b c d ≃ f a₂ b c d) :=
      DefFun₄ α β γ δ Y
              (EquivalenceFunctor₄.mk f (hφ := IsPreorderFunctor₄.construct hfabc hfabd hfacd hfbcd))

    namespace DefFun₄

      notation:20 α:21 " ⥤ " β:21 " ⥤ " γ:21 " ⥤ " δ:21 " ⥤⦃" f:0 "⦄ " Y:21 =>
        HasFunctors.DefFun₄ α β γ δ Y f

      notation:20 α:21 " ⥤ " β:21 " ⥤ " γ:21 " ⥤ " δ:21 " ⥤{" f:0 ", " hfabc:0 ", " hfabd:0 ", " hfacd:0 ", " hfbcd:0 "} " Y:21 =>
        HasFunctors.DefFun₄' α β γ δ Y f hfabc hfabd hfacd hfbcd

      variable {α β γ δ : Sort u} [Layer1.HasEquivalenceRelationBase Prp α]
               [Layer1.HasEquivalenceRelationBase Prp β] [Layer1.HasEquivalenceRelationBase Prp γ]
               [Layer1.HasEquivalenceRelationBase Prp δ] {Y : U} [HasFunctors δ Y]
               [HasFunctors γ (δ ⥤ Y)] [HasFunctors β (γ ⥤ δ ⥤ Y)] [HasFunctors α (β ⥤ γ ⥤ δ ⥤ Y)]

      @[reducible] def inst {f : EquivalenceFunctor₄ α β γ δ Y} (F : α ⥤ β ⥤ γ ⥤ δ ⥤⦃f⦄ Y) :
          α ⥤ β ⥤ γ ⥤ δ ⥤ Y :=
        F.toDefFun

      instance coeType (f : EquivalenceFunctor₄ α β γ δ Y) :
          Coe (α ⥤ β ⥤ γ ⥤ δ ⥤⦃f⦄ Y) (α ⥤ β ⥤ γ ⥤ δ ⥤ Y) :=
        ⟨inst⟩

      @[reducible] def toLayer1 {f : EquivalenceFunctor₄ α β γ δ Y} (F : α ⥤ β ⥤ γ ⥤ δ ⥤⦃f⦄ Y) :
          α ⥤ β ⥤ γ ⥤ δ ⥤{f.φ} Y :=
        ⟨λ a => (F.app a).toLayer1, F.toDefFun.toLayer1⟩

      instance (f : EquivalenceFunctor₄ α β γ δ Y) :
          Coe (α ⥤ β ⥤ γ ⥤ δ ⥤⦃f⦄ Y) (α ⥤ β ⥤ γ ⥤ δ ⥤{f.φ} Y) :=
        ⟨toLayer1⟩

      def e {f : EquivalenceFunctor₄ α β γ δ Y} (F : α ⥤ β ⥤ γ ⥤ δ ⥤⦃f⦄ Y) (a : α) (b : β) (c : γ)
            (d : δ) :
          F.inst a b c d ≃ f a b c d :=
        byDef₄ (F := F.toLayer1)

      def isFunApp₄ {f : EquivalenceFunctor₄ α β γ δ Y} (F : α ⥤ β ⥤ γ ⥤ δ ⥤⦃f⦄ Y) {a : α} {b : β}
                    {c : γ} {d : δ} :
          IsFunApp₄ (f a b c d) :=
        ⟨F.inst, a, b, c, d, F.e a b c d⟩

      def toDefInst {f : EquivalenceFunctor₄ α β γ δ Y} (F : α ⥤ β ⥤ γ ⥤ δ ⥤⦃f⦄ Y) :
          DefType.DefInst (defFunType₄ α β γ δ Y) f :=
        ⟨⟨F.inst⟩, ⟨F.e⟩⟩

      -- TODO: See above.
      --def fromDefInst {f : EquivalenceFunctor₄ α β γ δ Y}
      --                (F : DefType.DefInst (defFunType₄ α β γ δ Y) f) :
      --    α ⥤ β ⥤ γ ⥤ δ ⥤⦃f⦄ Y where
      --  app a    := ⟨⟨apply (α := α) (Y := β ⥤ γ ⥤ Y) F.inst a⟩, λ b c d => F.e a b c d⟩
      --  appEq    := _
      --  toDefFun := DefFun.defAppFun F.inst

      -- TODO: This is really slow to type-check.
      --@[reducible] def cast {f g : EquivalenceFunctor₄ α β γ δ Y}
      --                      (efg : ∀ (a : α) (b : β) (c : γ) (d : δ), f a b c d ≃ g a b c d)
      --                      (F : α ⥤ β ⥤ γ ⥤ δ ⥤⦃f⦄ Y) :
      --    α ⥤ β ⥤ γ ⥤ δ ⥤⦃g⦄ Y where
      --  app a    := DefFun₃.cast (f := f.app a) (g := g.app a) (efg a) (F.app a)
      --  appEq    := DefPiAppEq₃.cast efg (hfe := λ e b c d => (f.hφ.app₂₃₄ b c d) e) F.appEq
      --  toDefFun := F.toDefFun
      --infix:60 " ►►►► " => HasFunctors.DefFun₄.cast

      def toDefPi₄ {f : EquivalenceFunctor₄ α β γ δ Y} (F : α ⥤ β ⥤ γ ⥤ δ ⥤⦃f⦄ Y) :
          DefPi₄ (Function.const α (Function.const β (Function.const γ (Function.const δ Y)))) f.φ :=
        ⟨λ a => (F.app a).toDefPi₃, F.toDefFun.toDefPi⟩

      instance (f : EquivalenceFunctor₄ α β γ δ Y) :
          Coe (α ⥤ β ⥤ γ ⥤ δ ⥤⦃f⦄ Y)
              (DefPi₄ (Function.const α (Function.const β (Function.const γ (Function.const δ Y))))
                      f.φ) :=
        ⟨toDefPi₄⟩

      @[reducible] def DefEquiv {f : EquivalenceFunctor₄ α β γ δ Y} (F G : α ⥤ β ⥤ γ ⥤ δ ⥤⦃f⦄ Y) :=
        DefPi₄.DefEquiv (toDefPi₄ F) (toDefPi₄ G)
      infix:25 " {≃≃≃≃} " => HasFunctors.DefFun₄.DefEquiv

      @[reducible] def defAppFun (F : α ⥤ β ⥤ γ ⥤ δ ⥤ Y) :
          α ⥤ β ⥤ γ ⥤ δ ⥤⦃EquivalenceFunctor₄.mk (apply₄ F)⦄ Y where
        app a    := DefFun₃.defAppFun (F a)
        appEq    := { defAppEq    := λ e => ⟨λ b => ⟨λ c => ⟨congrFun₂ (congrArg F e) b c⟩,
                                                     ⟨congrFun (congrArg F e) b⟩⟩,
                                             ⟨congrArg F e⟩⟩,
                      defAppEqFun := λ a₁ a₂ => ⟨congrArgFun F a₁ a₂⟩ }
        toDefFun := DefFun.defAppFun F

      def hasEqPi₄ {f g : EquivalenceFunctor₄ α β γ δ Y} (F : α ⥤ β ⥤ γ ⥤ δ ⥤⦃f⦄ Y)
                                                         (G : α ⥤ β ⥤ γ ⥤ δ ⥤⦃g⦄ Y) :
          Layer1.HasPiType (λ a => Layer1.HasPiType.Pi₃ (hPab := λ b c => DefFun.hasEqPi (((F.app a).app b).app c)
                                                                                         (((G.app a).app b).app c))
                                                        (hPiPab := λ b => DefFun₂.hasEqPi₂ ((F.app a).app b)
                                                                                           ((G.app a).app b))
                                                        (hPiPa := DefFun₃.hasEqPi₃ (F.app a) (G.app a))
                                                        (λ b c d => f a b c d ≃ g a b c d)) :=
        DefPi₄.hasEqPi₄ F.toDefPi₄ G.toDefPi₄

    end DefFun₄

  end DefFun

end HasFunctors

open HasFunctors



class HasUnivFunctors (U V : Universe.{u}) [HasPropositions Prp U] [HasPropositions Prp V] where
  [hFun (A : U) (B : V) : HasFunctors A B]

namespace HasUnivFunctors

  variable (U V : Universe.{u}) [HasPropositions Prp U] [HasPropositions Prp V]
           [h : HasUnivFunctors U V]

  instance (A : U) (B : V) : HasFunctors A B := h.hFun A B

  instance toLayer1 : Layer1.HasUnivFunctors U V := ⟨⟩

end HasUnivFunctors



class HasIdFun {U : Universe} [HasPropositions Prp U] (A : U) [HasFunctors A A] where
  defIdFun : A ⥤⦃EquivalenceFunctor.idFun A⦄ A

namespace HasIdFun

  variable {U : Universe} [HasPropositions Prp U] (A : U) [HasFunctors A A] [h : HasIdFun A]

  instance toLayer1 : Layer1.HasIdFun A := ⟨h.defIdFun.toLayer1⟩

  instance hasDefInstEq : DefType.HasDefInstEq (toLayer1 A).defIdFun := ⟨h.defIdFun.e⟩

end HasIdFun


class HasPiAppFun {α : Sort u} {V : Universe} [HasPropositions Prp V] [HasUnivFunctors V V]
                  (P : α → V) [HasPiTypeBase P] where
  defPiAppFun (a : α) : Layer1.HasPiType.Pi P ⥤{λ F => F a, λ F₁ F₂ => congrFunFun F₁ F₂ a} P a

namespace HasPiAppFun

  variable {α : Sort u} {V : Universe} [HasPropositions Prp V] [HasUnivFunctors V V] (P : α → V)
           [HasPiTypeBase P] [h : HasPiAppFun P]

  instance toLayer1 : Layer1.HasPiAppFun P := ⟨λ a => (h.defPiAppFun a).toLayer1⟩

  instance hasDefInstEq (a : α) : DefType.HasDefInstEq ((toLayer1 P).defPiAppFun a) :=
    ⟨(h.defPiAppFun a).e⟩

end HasPiAppFun

class HasPiAppFunPi {α : Sort u} {V : Universe} [HasPropositions Prp V] [HasUnivFunctors V V]
                    (P : α → V) [HasPiTypeBase P]
                    [HasPiTypeBase (λ a => Layer1.HasPiType.Pi P ⥤ P a)] extends
    HasPiAppFun P where
  defPiAppFunPi : DefPi (λ a => Layer1.HasPiType.Pi P ⥤ P a) (Layer1.HasPiAppFun.piAppFun P)

namespace HasPiAppFunPi

  variable {α : Sort u} {V : Universe} [HasPropositions Prp V] [HasUnivFunctors V V] (P : α → V)
           [HasPiTypeBase P] [HasPiTypeBase (λ a => Layer1.HasPiType.Pi P ⥤ P a)]
           [h : HasPiAppFunPi P]

  instance toLayer1 : Layer1.HasPiAppFunPi P := ⟨h.defPiAppFunPi.toLayer1⟩

  instance hasDefInstEq : DefType.HasDefInstEq (toLayer1 P).defPiAppFunPi := ⟨h.defPiAppFunPi.e⟩

end HasPiAppFunPi


class HasSwapPi {α : Sort u} {β : Sort u'} {V : Universe} [HasPropositions Prp V] (P : α → β → V)
                [∀ a, HasPiTypeBase (P a)] [HasPiTypeBase (λ a => Layer1.HasPiType.Pi (P a))]
                [∀ b, HasPiTypeBase (λ a => P a b)] where
  defSwapPi (F : Layer1.HasPiType.Pi₂ P) (b : β) : DefPi (λ a => P a b) (λ a => F a b)

namespace HasSwapPi

  variable {α : Sort u} {β : Sort u'} {V : Universe} [HasPropositions Prp V] (P : α → β → V)
           [∀ a, HasPiTypeBase (P a)] [HasPiTypeBase (λ a => Layer1.HasPiType.Pi (P a))]
           [∀ b, HasPiTypeBase (λ a => P a b)] [h : HasSwapPi P]

  instance toLayer1 : Layer1.HasSwapPi P := ⟨λ F b => (h.defSwapPi F b).toLayer1⟩

  instance hasDefInstEq (F : Layer1.HasPiType.Pi₂ P) (b : β) :
      DefType.HasDefInstEq ((toLayer1 P).defSwapPi F b) :=
    ⟨(h.defSwapPi F b).e⟩

  -- TODO: derive `HasPiAppFun` from `HasSwapPi`, etc., like in layer 1

end HasSwapPi

class HasSwapPi₂ {α : Sort u} {β : Sort u'} {V : Universe} [HasPropositions Prp V] (P : α → β → V)
                 [∀ a, HasPiTypeBase (P a)] [HasPiTypeBase (λ a => Layer1.HasPiType.Pi (P a))]
                 [∀ b, HasPiTypeBase (λ a => P a b)]
                 [HasPiTypeBase (λ b => Layer1.HasPiType.Pi (λ a => P a b))] extends
    HasSwapPi P where
  defSwapPi₂ (F : Layer1.HasPiType.Pi₂ P) :
    DefPi (λ b => Layer1.HasPiType.Pi (λ a => P a b)) (Layer1.HasSwapPi.swapPi F)

namespace HasSwapPi₂

  def defSwapPi₂' {α : Sort u} {β : Sort u'} {V : Universe} [HasPropositions Prp V] {P : α → β → V}
                  [∀ a, HasPiTypeBase (P a)] [HasPiTypeBase (λ a => Layer1.HasPiType.Pi (P a))]
                  [∀ b, HasPiTypeBase (λ a => P a b)]
                  [HasPiTypeBase (λ b => Layer1.HasPiType.Pi (λ a => P a b))] [h : HasSwapPi₂ P]
                  (F : Layer1.HasPiType.Pi₂ P) :
      DefPi₂ (λ b a => P a b) (λ b a => F a b) :=
    ⟨h.defSwapPi F, h.defSwapPi₂ F⟩

  variable {α : Sort u} {β : Sort u'} {V : Universe} [HasPropositions Prp V] (P : α → β → V)
           [∀ a, HasPiTypeBase (P a)] [HasPiTypeBase (λ a => Layer1.HasPiType.Pi (P a))]
           [∀ b, HasPiTypeBase (λ a => P a b)]
           [HasPiTypeBase (λ b => Layer1.HasPiType.Pi (λ a => P a b))] [h : HasSwapPi₂ P]

  instance toLayer1 : Layer1.HasSwapPi₂ P := ⟨λ F => (h.defSwapPi₂ F).toLayer1⟩

  instance hasDefInstEq (F : Layer1.HasPiType.Pi₂ P) :
      DefType.HasDefInstEq ((toLayer1 P).defSwapPi₂ F) :=
    ⟨(h.defSwapPi₂ F).e⟩

end HasSwapPi₂

class HasSwapPiFun {α : Sort u} {β : Sort u'} {V : Universe} [HasPropositions Prp V]
                   [HasUnivFunctors V V] (P : α → β → V) [∀ a, HasPiTypeBase (P a)]
                   [HasPiTypeBase (λ a => Layer1.HasPiType.Pi (P a))]
                   [∀ b, HasPiTypeBase (λ a => P a b)]
                   [HasPiTypeBase (λ b => Layer1.HasPiType.Pi (λ a => P a b))] extends
    HasSwapPi₂ P where
  defSwapPiEq : DefPiAppEq₂ (HasSwapPi₂.defSwapPi₂' (P := P)) (λ e b a => congrFun₂ e a b)
  defSwapPiFun :
    Layer1.HasPiType.Pi₂ P ⥤⦃defSwapPiEq.eqFun⦄ Layer1.HasPiType.Pi₂ (λ b a => P a b)

namespace HasSwapPiFun

  variable {α : Sort u} {β : Sort u'} {V : Universe} [HasPropositions Prp V] [HasUnivFunctors V V]
           (P : α → β → V) [∀ a, HasPiTypeBase (P a)]
           [HasPiTypeBase (λ a => Layer1.HasPiType.Pi (P a))] [∀ b, HasPiTypeBase (λ a => P a b)]
           [HasPiTypeBase (λ b => Layer1.HasPiType.Pi (λ a => P a b))] [h : HasSwapPiFun P]

  instance toLayer1 : Layer1.HasSwapPiFun P := ⟨h.defSwapPiFun.toLayer1⟩

  instance hasDefInstEq : DefType.HasDefInstEq (toLayer1 P).defSwapPiFun := ⟨h.defSwapPiFun.e⟩

end HasSwapPiFun


class HasCompFunPi (α : Sort u) [Layer1.HasEquivalenceRelationBase Prp α] {V : Universe.{u}}
                   [HasPropositions Prp V] {W : Universe} [HasPropositions Prp W] {B : V}
                   [HasFunctors α B] (Q : B → W) [HasPiTypeBase Q]
                   [∀ F : α ⥤ B, HasPiTypeBase (λ a => Q (F a))] where
  defCompFunPi (F : α ⥤ B) (G : Layer1.HasPiType.Pi Q) : DefPi (λ a => Q (F a)) (λ a => G (F a))

namespace HasCompFunPi

  variable (α : Sort u) [Layer1.HasEquivalenceRelationBase Prp α] {V : Universe.{u}}
           [HasPropositions Prp V] {W : Universe} [HasPropositions Prp W] {B : V} [HasFunctors α B]
           (Q : B → W)  [HasPiTypeBase Q] [∀ F : α ⥤ B, HasPiTypeBase (λ a => Q (F a))]
           [h : HasCompFunPi α Q]

  instance toLayer1 : Layer1.HasCompFunPi α Q := ⟨λ F G => (h.defCompFunPi F G).toLayer1⟩

  instance hasDefInstEq (F : α ⥤ B) (G : Layer1.HasPiType.Pi Q) :
      DefType.HasDefInstEq ((toLayer1 α Q).defCompFunPi F G) :=
    ⟨(h.defCompFunPi F G).e⟩

end HasCompFunPi

class HasRevCompFunPi₂ (α : Sort u) [Layer1.HasEquivalenceRelationBase Prp α] {V : Universe.{u}}
                       [HasPropositions Prp V] {W : Universe} [HasPropositions Prp W] {B : V}
                       [HasFunctors α B] (Q : B → W) [HasPiTypeBase Q]
                       [∀ F : α ⥤ B, HasPiTypeBase (λ a => Q (F a))]
                       [HasPiTypeBase (λ F : α ⥤ B => Layer1.HasPiType.Pi (λ a => Q (F a)))] extends
    HasCompFunPi α Q where
  defRevCompFunPi₂ (G : Layer1.HasPiType.Pi Q) :
    DefPi (λ F : α ⥤ B => Layer1.HasPiType.Pi (λ a => Q (F a))) (Layer1.HasCompFunPi.revCompFunPi G)

namespace HasRevCompFunPi₂

  variable (α : Sort u) [Layer1.HasEquivalenceRelationBase Prp α] {V : Universe.{u}}
           [HasPropositions Prp V] {W : Universe} [HasPropositions Prp W] {B : V} [HasFunctors α B]
           (Q : B → W) [HasPiTypeBase Q] [∀ F : α ⥤ B, HasPiTypeBase (λ a => Q (F a))]
           [HasPiTypeBase (λ F : α ⥤ B => Layer1.HasPiType.Pi (λ a => Q (F a)))]
           [h : HasRevCompFunPi₂ α Q]

  instance toLayer1 : Layer1.HasRevCompFunPi₂ α Q := ⟨λ G => (h.defRevCompFunPi₂ G).toLayer1⟩

  instance hasDefInstEq (G : Layer1.HasPiType.Pi Q) :
      DefType.HasDefInstEq ((toLayer1 α Q).defRevCompFunPi₂ G) :=
    ⟨(h.defRevCompFunPi₂ G).e⟩

end HasRevCompFunPi₂

class HasRevCompFunPiFun (α : Sort u) [Layer1.HasEquivalenceRelationBase Prp α] {V : Universe.{u}}
                         [HasPropositions Prp V] {W : Universe} [HasPropositions Prp W]
                         [HasUnivFunctors W W] {B : V} [HasFunctors α B] (Q : B → W)
                         [HasPiTypeBase Q] [∀ F : α ⥤ B, HasPiTypeBase (λ a => Q (F a))]
                         [HasPiTypeBase (λ F : α ⥤ B => Layer1.HasPiType.Pi (λ a => Q (F a)))]
                         extends
    HasRevCompFunPi₂ α Q where
  defRevCompFunPiEq :
    DefPiAppEq₂ (λ G => ⟨λ F => defCompFunPi F G, defRevCompFunPi₂ G⟩) (λ e F a => congrFun e (F a))
  defRevCompFunPiFun :
    Layer1.HasPiType.Pi Q
    ⥤⦃defRevCompFunPiEq.eqFun⦄
    Layer1.HasPiType.Pi₂ (λ (F : α ⥤ B) a => Q (F a))

namespace HasRevCompFunPiFun

  section

    variable (α : Sort u) [Layer1.HasEquivalenceRelationBase Prp α] {V : Universe.{u}}
             [HasPropositions Prp V] {W : Universe} [HasPropositions Prp W] [HasUnivFunctors W W]
             {B : V} [HasFunctors α B] (Q : B → W) [HasPiTypeBase Q]
             [∀ F : α ⥤ B, HasPiTypeBase (λ a => Q (F a))]
             [HasPiTypeBase (λ F : α ⥤ B => Layer1.HasPiType.Pi (λ a => Q (F a)))]
             [h : HasRevCompFunPiFun α Q]

    instance toLayer1 : Layer1.HasRevCompFunPiFun α Q := ⟨h.defRevCompFunPiFun.toLayer1⟩

    instance hasDefInstEq : DefType.HasDefInstEq (toLayer1 α Q).defRevCompFunPiFun :=
      ⟨h.defRevCompFunPiFun.e⟩

  end

  section

    variable {α : Sort u} [Layer1.HasEquivalenceRelationBase Prp α] {V W : Universe.{u}}
             [HasPropositions Prp V] [HasPropositions Prp W] [HasUnivFunctors V W]
             [HasUnivFunctors W W] {B : V} [HasFunctors α B] (F : α ⥤ B) (C : W) [HasFunctors α C]
             [h : HasRevCompFunPiFun α (Function.const B C)]
             [HasSwapPi (Function.const (B ⥤ C) (Function.const (α ⥤ B) (α ⥤ C)))]

    instance compFun₂.hasDefInstEq :
        DefType.HasDefInstEq (Layer1.HasRevCompFunPiFun.defCompFun₂ F C).toDefFun :=
      ⟨λ G => HasFunctors.byDef •
              congrFun (HasFunctors.byDef (hF := HasRevCompFunPiFun.hasDefInstEq α (Function.const B C))) F •
              HasFunctors.byDef (hF := HasSwapPi.hasDefInstEq (Function.const (B ⥤ C) (Function.const (α ⥤ B) (α ⥤ C))) (Layer1.HasRevCompFunPiFun.revCompFun₃ α B C) F)⟩

  end

  section

    variable (α : Sort u) [Layer1.HasEquivalenceRelationBase Prp α] {V W : Universe.{u}}
             [HasPropositions Prp V] [HasPropositions Prp W] [HasUnivFunctors V W]
             [HasUnivFunctors W W] (B : V) [HasFunctors α B] (C : W) [HasFunctors α C]
             [HasRevCompFunPiFun α (Function.const B C)]
             [HasSwapPi₂ (Function.const (B ⥤ C) (Function.const (α ⥤ B) (α ⥤ C)))]

    instance compFun₃.hasDefInstEq :
        DefType.HasDefInstEq (Layer1.HasRevCompFunPiFun.defCompFun₃ α B C).toDefFun :=
      ⟨λ F => HasFunctors.byDef (hF := HasSwapPi₂.hasDefInstEq (Function.const (B ⥤ C) (Function.const (α ⥤ B) (α ⥤ C))) (Layer1.HasRevCompFunPiFun.revCompFun₃ α B C))⟩

  end

end HasRevCompFunPiFun


class HasConstPi (α : Sort u) {V : Universe} [HasPropositions Prp V] (B : V)
                 [HasPiTypeBase (Function.const α B)] where
  defConstPi (b : B) : DefPi (Function.const α B) (Function.const α b)

namespace HasConstPi

  variable (α : Sort u) {V : Universe} [HasPropositions Prp V] (B : V)
           [HasPiTypeBase (Function.const α B)] [h : HasConstPi α B]

  instance toLayer1 : Layer1.HasConstPi α B := ⟨λ b => (h.defConstPi b).toLayer1⟩

  instance hasDefInstEq (b : B) : DefType.HasDefInstEq ((toLayer1 α B).defConstPi b) :=
    ⟨(h.defConstPi b).e⟩

end HasConstPi

class HasConstPiFun (α : Sort u) {V : Universe} [HasPropositions Prp V] [HasUnivFunctors V V]
                    (B : V) [HasPiTypeBase (Function.const α B)] extends
    HasConstPi α B where
  defConstPiEq : DefPiAppEq defConstPi (λ e a => e)
  defConstPiFun : B ⥤⦃defConstPiEq.eqFun⦄ Layer1.HasPiType.Pi (Function.const α B)

namespace HasConstPiFun

  variable (α : Sort u) {V : Universe} [HasPropositions Prp V] [HasUnivFunctors V V] (B : V)
           [HasPiTypeBase (Function.const α B)] [h : HasConstPiFun α B]

  instance toLayer1 : Layer1.HasConstPiFun α B := ⟨h.defConstPiFun.toLayer1⟩

  instance hasDefInstEq : DefType.HasDefInstEq (toLayer1 α B).defConstPiFun := ⟨h.defConstPiFun.e⟩

end HasConstPiFun


class HasDupPi {α : Sort u} {V : Universe} [HasPropositions Prp V] (P : α → α → V)
               [∀ a, HasPiTypeBase (P a)] [HasPiTypeBase (λ a => Layer1.HasPiType.Pi (P a))]
               [HasPiTypeBase (λ a => P a a)] where
  defDupPi (F : Layer1.HasPiType.Pi₂ P) : DefPi (λ a => P a a) (λ a => F a a)

namespace HasDupPi

  variable {α : Sort u} {V : Universe} [HasPropositions Prp V] (P : α → α → V)
           [∀ a, HasPiTypeBase (P a)] [HasPiTypeBase (λ a => Layer1.HasPiType.Pi (P a))]
           [HasPiTypeBase (λ a => P a a)] [h : HasDupPi P]

  instance toLayer1 : Layer1.HasDupPi P := ⟨λ F => (h.defDupPi F).toLayer1⟩

  instance hasDefInstEq (F : Layer1.HasPiType.Pi₂ P) :
      DefType.HasDefInstEq ((toLayer1 P).defDupPi F) :=
    ⟨(h.defDupPi F).e⟩

end HasDupPi

class HasDupPiFun {α : Sort u} {V : Universe} [HasPropositions Prp V] [HasUnivFunctors V V]
                  (P : α → α → V) [∀ a, HasPiTypeBase (P a)]
                  [HasPiTypeBase (λ a => Layer1.HasPiType.Pi (P a))] [HasPiTypeBase (λ a => P a a)]
                  extends
    HasDupPi P where
  defDupPiEq : DefPiAppEq defDupPi (λ e a => congrFun₂ e a a)
  defDupPiFun : Layer1.HasPiType.Pi₂ P ⥤⦃defDupPiEq.eqFun⦄ Layer1.HasPiType.Pi (λ a => P a a)

namespace HasDupPiFun

  variable {α : Sort u} {V : Universe} [HasPropositions Prp V] [HasUnivFunctors V V] (P : α → α → V)
           [∀ a, HasPiTypeBase (P a)] [HasPiTypeBase (λ a => Layer1.HasPiType.Pi (P a))]
           [HasPiTypeBase (λ a => P a a)] [h : HasDupPiFun P]

  instance toLayer1 : Layer1.HasDupPiFun P := ⟨h.defDupPiFun.toLayer1⟩

  instance hasDefInstEq : DefType.HasDefInstEq (toLayer1 P).defDupPiFun := ⟨h.defDupPiFun.e⟩

end HasDupPiFun


class HasPiSelfAppPi {U V : Universe.{u}} [HasPropositions Prp U] [HasPropositions Prp V]
                     [HasUnivFunctors V U] {A : U} (Q : A → V)
                     [HasPiTypeBase Q]
                     [∀ F : Layer1.HasPiType.Pi Q ⥤ A, HasPiTypeBase (λ G => Q (F G))] where
  defPiSelfAppPi (F : Layer1.HasPiType.Pi Q ⥤ A) : DefPi (λ G => Q (F G)) (λ G => G (F G))

namespace HasPiSelfAppPi

  variable {U V : Universe.{u}} [HasPropositions Prp U] [HasPropositions Prp V]
           [HasUnivFunctors V U] {A : U} (Q : A → V) [HasPiTypeBase Q]
           [∀ F : Layer1.HasPiType.Pi Q ⥤ A, HasPiTypeBase (λ G => Q (F G))] [h : HasPiSelfAppPi Q]

  instance toLayer1 : Layer1.HasPiSelfAppPi Q := ⟨λ F => (h.defPiSelfAppPi F).toLayer1⟩

  instance hasDefInstEq (F : Layer1.HasPiType.Pi Q ⥤ A) :
      DefType.HasDefInstEq ((toLayer1 Q).defPiSelfAppPi F) :=
    ⟨(h.defPiSelfAppPi F).e⟩

end HasPiSelfAppPi

class HasPiSelfAppPi₂ {U V : Universe.{u}} [HasPropositions Prp U] [HasPropositions Prp V]
                      [HasUnivFunctors V U] {A : U} (Q : A → V)
                      [HasPiTypeBase Q]
                      [∀ F : Layer1.HasPiType.Pi Q ⥤ A, HasPiTypeBase (λ G => Q (F G))]
                      [HasPiTypeBase (λ (F : Layer1.HasPiType.Pi Q ⥤ A) =>
                                      Layer1.HasPiType.Pi (λ G => Q (F G)))] extends
    HasPiSelfAppPi Q where
  defPiSelfAppPi₂ : DefPi (λ (F : Layer1.HasPiType.Pi Q ⥤ A) => Layer1.HasPiType.Pi (λ G => Q (F G)))
                          Layer1.HasPiSelfAppPi.piSelfAppPi

namespace HasPiSelfAppPi₂

  variable {U V : Universe.{u}} [HasPropositions Prp U] [HasPropositions Prp V]
           [HasUnivFunctors V U] {A : U} (Q : A → V) [HasPiTypeBase Q]
           [∀ F : Layer1.HasPiType.Pi Q ⥤ A, HasPiTypeBase (λ G => Q (F G))]
           [HasPiTypeBase (λ (F : Layer1.HasPiType.Pi Q ⥤ A) => Layer1.HasPiType.Pi (λ G => Q (F G)))]
           [h : HasPiSelfAppPi₂ Q]

  instance toLayer1 : Layer1.HasPiSelfAppPi₂ Q := ⟨h.defPiSelfAppPi₂.toLayer1⟩

  instance hasDefInstEq : DefType.HasDefInstEq (toLayer1 Q).defPiSelfAppPi₂ :=
    ⟨h.defPiSelfAppPi₂.e⟩

end HasPiSelfAppPi₂


class HasSubstPi {α : Sort u} {V W : Universe} [HasPropositions Prp V] [HasPropositions Prp W]
                 {P : α → V} [HasPiTypeBase P] (Q : ∀ a, P a → W) [∀ a, HasPiTypeBase (Q a)]
                 [HasPiTypeBase (λ a => Layer1.HasPiType.Pi (Q a))]
                 [∀ F : Layer1.HasPiType.Pi P, HasPiTypeBase (λ a => Q a (F a))] where
  defSubstPi (F : Layer1.HasPiType.Pi P) (G : Layer1.HasPiType.Pi (λ a => Layer1.HasPiType.Pi (Q a))) :
    DefPi (λ a => Q a (F a)) (λ a => G a (F a))

namespace HasSubstPi

  variable {α : Sort u} {V W : Universe} [HasPropositions Prp V] [HasPropositions Prp W] {P : α → V}
           [HasPiTypeBase P] (Q : ∀ a, P a → W) [∀ a, HasPiTypeBase (Q a)]
           [HasPiTypeBase (λ a => Layer1.HasPiType.Pi (Q a))]
           [∀ F : Layer1.HasPiType.Pi P, HasPiTypeBase (λ a => Q a (F a))] [h : HasSubstPi Q]

  instance toLayer1 : Layer1.HasSubstPi Q := ⟨λ F G => (h.defSubstPi F G).toLayer1⟩

  instance hasDefInstEq (F : Layer1.HasPiType.Pi P)
                        (G : Layer1.HasPiType.Pi (λ a => Layer1.HasPiType.Pi (Q a))) :
      DefType.HasDefInstEq ((toLayer1 Q).defSubstPi F G) :=
    ⟨(h.defSubstPi F G).e⟩

end HasSubstPi

class HasRevSubstPi₂ {α : Sort u} {V W : Universe} [HasPropositions Prp V] [HasPropositions Prp W]
                     {P : α → V} [HasPiTypeBase P] (Q : ∀ a, P a → W) [∀ a, HasPiTypeBase (Q a)]
                     [HasPiTypeBase (λ a => Layer1.HasPiType.Pi (Q a))]
                     [∀ F : Layer1.HasPiType.Pi P, HasPiTypeBase (λ a => Q a (F a))]
                     [HasPiTypeBase (λ F : Layer1.HasPiType.Pi P =>
                                     Layer1.HasPiType.Pi (λ a => Q a (F a)))] extends
    HasSubstPi Q where
  defRevSubstPi₂ (G : Layer1.HasPiType.Pi (λ a => Layer1.HasPiType.Pi (Q a))) :
    DefPi (λ F : Layer1.HasPiType.Pi P => Layer1.HasPiType.Pi (λ a => Q a (F a)))
          (Layer1.HasSubstPi.revSubstPi G)

namespace HasRevSubstPi₂

  variable {α : Sort u} {V W : Universe} [HasPropositions Prp V] [HasPropositions Prp W] {P : α → V}
           [HasPiTypeBase P] (Q : ∀ a, P a → W) [∀ a, HasPiTypeBase (Q a)]
           [HasPiTypeBase (λ a => Layer1.HasPiType.Pi (Q a))]
           [∀ F : Layer1.HasPiType.Pi P, HasPiTypeBase (λ a => Q a (F a))]
           [HasPiTypeBase (λ F : Layer1.HasPiType.Pi P => Layer1.HasPiType.Pi (λ a => Q a (F a)))]
           [h : HasRevSubstPi₂ Q]

  instance toLayer1 : Layer1.HasRevSubstPi₂ Q := ⟨λ G => (h.defRevSubstPi₂ G).toLayer1⟩

  instance hasDefInstEq (G : Layer1.HasPiType.Pi (λ a => Layer1.HasPiType.Pi (Q a))) :
      DefType.HasDefInstEq ((toLayer1 Q).defRevSubstPi₂ G) :=
    ⟨(h.defRevSubstPi₂ G).e⟩

end HasRevSubstPi₂

class HasRevSubstPiFun {α : Sort u} {V W : Universe} [HasPropositions Prp V] [HasPropositions Prp W]
                       [HasUnivFunctors W W] {P : α → V} [HasPiTypeBase P] (Q : ∀ a, P a → W)
                       [∀ a, HasPiTypeBase (Q a)] [HasPiTypeBase (λ a => Layer1.HasPiType.Pi (Q a))]
                       [∀ F : Layer1.HasPiType.Pi P, HasPiTypeBase (λ a => Q a (F a))]
                       [HasPiTypeBase (λ F : Layer1.HasPiType.Pi P =>
                                       Layer1.HasPiType.Pi (λ a => Q a (F a)))] extends
    HasRevSubstPi₂ Q where
  defRevSubstPiEq :
    DefPiAppEq₂ (λ G => ⟨λ F => defSubstPi F G, defRevSubstPi₂ G⟩)
                (λ e F a => congrFun (congrFun e a) (F a))
  defRevSubstPiFun :
    Layer1.HasPiType.Pi (λ a => Layer1.HasPiType.Pi (Q a))
    ⥤⦃defRevSubstPiEq.eqFun⦄
    Layer1.HasPiType.Pi (λ F : Layer1.HasPiType.Pi P => Layer1.HasPiType.Pi (λ a => Q a (F a)))

namespace HasRevSubstPiFun

  section

    variable {α : Sort u} {V W : Universe} [HasPropositions Prp V] [HasPropositions Prp W]
             [HasUnivFunctors W W] {P : α → V} [HasPiTypeBase P] (Q : ∀ a, P a → W)
             [∀ a, HasPiTypeBase (Q a)] [HasPiTypeBase (λ a => Layer1.HasPiType.Pi (Q a))]
             [∀ F : Layer1.HasPiType.Pi P, HasPiTypeBase (λ a => Q a (F a))]
             [HasPiTypeBase (λ F : Layer1.HasPiType.Pi P => Layer1.HasPiType.Pi (λ a => Q a (F a)))]
             [h : HasRevSubstPiFun Q]

    instance toLayer1 : Layer1.HasRevSubstPiFun Q := ⟨h.defRevSubstPiFun.toLayer1⟩

    instance hasDefInstEq : DefType.HasDefInstEq (toLayer1 Q).defRevSubstPiFun :=
      ⟨h.defRevSubstPiFun.e⟩

  end

  section

    variable {α : Sort u} [Layer1.HasEquivalenceRelationBase Prp α] {V W : Universe.{u}}
             [HasPropositions Prp V] [HasPropositions Prp W] [HasUnivFunctors V W]
             [HasUnivFunctors W W] {B : V} [HasFunctors α B] (F : α ⥤ B) (C : W)
             [HasFunctors α (B ⥤ C)] [HasFunctors α C]
             [h : HasRevSubstPiFun (Function.const α (Function.const B C))]
             [HasSwapPi (Function.const (α ⥤ B ⥤ C) (Function.const (α ⥤ B) (α ⥤ C)))]

    instance substFun₂.hasDefInstEq :
        DefType.HasDefInstEq (Layer1.HasRevSubstPiFun.defSubstFun₂ F C).toDefFun :=
      ⟨λ G => HasFunctors.byDef •
              congrFun (HasFunctors.byDef (hF := HasRevSubstPiFun.hasDefInstEq (Function.const α (Function.const B C)))) F •
              HasFunctors.byDef (hF := HasSwapPi.hasDefInstEq (Function.const (α ⥤ B ⥤ C) (Function.const (α ⥤ B) (α ⥤ C))) (Layer1.HasRevSubstPiFun.revSubstFun₃ α B C) F)⟩

  end

  section

    variable (α : Sort u) [Layer1.HasEquivalenceRelationBase Prp α] {V W : Universe.{u}}
             [HasPropositions Prp V] [HasPropositions Prp W] [HasUnivFunctors V W]
             [HasUnivFunctors W W] (B : V) [HasFunctors α B] (C : W) [HasFunctors α (B ⥤ C)]
             [HasFunctors α C] [HasRevSubstPiFun (Function.const α (Function.const B C))]
             [HasSwapPi₂ (Function.const (α ⥤ B ⥤ C) (Function.const (α ⥤ B) (α ⥤ C)))]

    instance substFun₃.hasDefInstEq :
        DefType.HasDefInstEq (Layer1.HasRevSubstPiFun.defSubstFun₃ α B C).toDefFun :=
      ⟨λ F => HasFunctors.byDef (hF := HasSwapPi₂.hasDefInstEq (Function.const (α ⥤ B ⥤ C) (Function.const (α ⥤ B) (α ⥤ C))) (Layer1.HasRevSubstPiFun.revSubstFun₃ α B C))⟩

  end

end HasRevSubstPiFun



class HasExternalLinearLogic (α : Sort u) [Layer1.HasEquivalenceRelationBase Prp α]
                             (U : Universe.{u}) [HasPropositions Prp U] [HasUnivFunctors U U] where
  [hFun (B : U) : HasFunctors α B]
  defRevAppFun₂ (B : U) :
    α ⥤ (α ⥤ B) ⥤{λ a F => F a,
                   λ a F₁ F₂ => congrFunFun F₁ F₂ a,
                   λ a₁ a₂ F => congrArgFun F a₁ a₂} B
  defRevCompFun₃ (B C : U) :
    (B ⥤ C) ⥤ (α ⥤ B) ⥤ α ⥤{λ G F a => G (F a),
                              λ G F a₁ a₂ => Λ e => congrArg G (congrArg F e),
                              λ G F₁ F₂ a => Λ e => congrArg G (congrFun e a),
                              λ G₁ G₂ F a => Λ e => congrFun e (F a)} C

namespace HasExternalLinearLogic

  instance (α : Sort u) [Layer1.HasEquivalenceRelationBase Prp α] {U : Universe.{u}}
           [HasPropositions Prp U] [HasUnivFunctors U U] [h : HasExternalLinearLogic α U] (B : U) :
      HasFunctors α B :=
    h.hFun B

  instance toLayer1 (α : Sort u) [Layer1.HasEquivalenceRelationBase Prp α] (U : Universe.{u})
                    [HasPropositions Prp U] [HasUnivFunctors U U] [h : HasExternalLinearLogic α U] :
      Layer1.HasExternalLinearLogic α U where
    defRevAppFun₂  B   := (h.defRevAppFun₂  B).toLayer1
    defRevCompFun₃ B C := (h.defRevCompFun₃ B C).toLayer1

  variable (α : Sort u) [Layer1.HasEquivalenceRelationBase Prp α] {U : Universe.{u}}
           [HasPropositions Prp U] [HasUnivFunctors U U] [h : HasExternalLinearLogic α U]

  @[reducible] def revAppFun.congrArg {a₁ a₂ : α} (e : a₁ ≃ a₂) (B : U) :
      Layer1.HasPiAppFun.revAppFun a₁ B ≃ Layer1.HasPiAppFun.revAppFun a₂ B :=
    (h.defRevAppFun₂ B).appEq.appEq e

  @[reducible] def revCompFun.congrArgRight {B C : U} {F₁ F₂ : α ⥤ B} (e : F₁ ≃ F₂) (G : B ⥤ C) :
      G ⊙ F₁ ≃ G ⊙ F₂ :=
    ((h.defRevCompFun₃ B C).app G).appEq.appEq e

  @[reducible] def revCompFun.congrArgLeft {B C : U} (F : α ⥤ B) {G₁ G₂ : B ⥤ C} (e : G₁ ≃ G₂) :
      G₁ ⊙ F ≃ G₂ ⊙ F :=
    DefPi.defCongrFun ((h.defRevCompFun₃ B C).app G₁).toDefPi₂.toDefPi
                      ((h.defRevCompFun₃ B C).app G₂).toDefPi₂.toDefPi
                      ((h.defRevCompFun₃ B C).appEq.appEq e) F

  @[reducible] def revCompFun₂.congrArg {B C : U} {G₁ G₂ : B ⥤ C} (e : G₁ ≃ G₂) :
      Layer1.HasRevCompFunPi₂.revCompFun₂ α G₁ ≃ Layer1.HasRevCompFunPi₂.revCompFun₂ α G₂ :=
    (h.defRevCompFun₃ B C).appEq.appEq e

  instance {B C : U} (F₁ F₂ : α ⥤ B) (G₁ G₂ : B ⥤ C) :
      Layer1.HasPiType (λ a => G₁ (F₁ a) ≃ G₂ (F₂ a)) :=
    DefFun.hasEqPi (((h.defRevCompFun₃ B C).app G₁).app F₁)
                   (((h.defRevCompFun₃ B C).app G₂).app F₂)

  instance {B C : U} (G₁ G₂ : B ⥤ C) : Layer1.HasCompFunPi α (λ b => G₁ b ≃ G₂ b) :=
    ⟨λ F e => ⟨revCompFun.congrArgLeft α F e⟩⟩

  instance {B C : U} (G₁ G₂ : B ⥤ C) :
      Layer1.HasPiType (λ F : α ⥤ B => Layer1.HasPiType.Pi (λ a => G₁ (F a) ≃ G₂ (F a))) :=
    DefFun.hasEqPi ((h.defRevCompFun₃ B C).app G₁).toDefFun
                   ((h.defRevCompFun₃ B C).app G₂).toDefFun

  instance {B C : U} (G₁ G₂ : B ⥤ C) : Layer1.HasRevCompFunPi₂ α (λ b => G₁ b ≃ G₂ b) :=
    ⟨λ e => ⟨revCompFun₂.congrArg α e⟩⟩

  instance {B C : U} (G₁ G₂ : B ⥤ C) : Layer1.HasRevCompFunPiFun α (λ b => G₁ b ≃ G₂ b) :=
    ⟨⟨(h.defRevCompFun₃ B C).appEq.appEqFun G₁ G₂⟩⟩

  instance hasPiAppFun (B : U) : HasPiAppFun (Function.const α B) := ⟨(h.defRevAppFun₂ B).app⟩
  instance (B : U) : HasPiAppFun (λ _ : α => B) := hasPiAppFun α B

  instance hasPiAppFunPi (B : U) : HasPiAppFunPi (Function.const α B) :=
    ⟨(h.defRevAppFun₂ B).toDefFun.toDefPi⟩
  instance (B : U) : HasPiAppFunPi (λ _ : α => B) := hasPiAppFunPi α B

  instance hasCompFunPi (B C : U) : HasCompFunPi α (Function.const B C) :=
    ⟨λ F G => (((h.defRevCompFun₃ B C).app G).app F).toDefPi⟩
  instance (B C : U) : HasCompFunPi α (λ _ : B => C) := hasCompFunPi α B C

  instance hasRevCompFunPi₂ (B C : U) : HasRevCompFunPi₂ α (Function.const B C) :=
    ⟨λ G => ((h.defRevCompFun₃ B C).app G).toDefFun.toDefPi⟩
  instance (B C : U) : HasRevCompFunPi₂ α (λ _ : B => C) := hasRevCompFunPi₂ α B C
 
  compiler_slow instance hasRevCompFunPiFun (B C : U) : HasRevCompFunPiFun α (Function.const B C) where
    defRevCompFunPiEq  := { defAppEq    := λ e => { app        := λ G => ⟨(((h.defRevCompFun₃ B C).appEq.defAppEq e).app G).e⟩,
                                                    toDefEquiv := ⟨((h.defRevCompFun₃ B C).appEq.defAppEq e).toDefEquiv.e⟩ },
                            defAppEqFun := λ G₁ G₂ => ⟨((h.defRevCompFun₃ B C).appEq.defAppEqFun G₁ G₂).inst⟩ }
    defRevCompFunPiFun := { inst := (h.defRevCompFun₃ B C).toDefFun.inst,
                            e    := (h.defRevCompFun₃ B C).toDefFun.e }

  compiler_slow instance (B C : U) : HasRevCompFunPiFun α (λ _ : B => C) := hasRevCompFunPiFun α B C

  instance revAppFun.hasDefInstEq (B : U) (a : α) :
      DefType.HasDefInstEq (Layer1.HasPiAppFun.defRevAppFun a B) :=
    HasPiAppFun.hasDefInstEq (Function.const α B) a

  def revAppFun.byDef {B : U} {a : α} {F : α ⥤ B} :
      (Layer1.HasPiAppFun.revAppFun a B) F ≃ F a :=
    HasFunctors.byDef

  instance revAppFun₂.hasDefInstEq (B : U) :
      DefType.HasDefInstEq (Layer1.HasPiAppFunPi.defRevAppFun₂ α B).toDefPi :=
    HasPiAppFunPi.hasDefInstEq (Function.const α B)

  def revAppFun₂.byDef {B : U} {a : α} :
      (Layer1.HasPiAppFunPi.revAppFun₂ α B) a ≃ Layer1.HasPiAppFun.revAppFun a B :=
    HasFunctors.byDef

  def revAppFun₂.byDef₂ {B : U} {a : α} {F : α ⥤ B} :
      (Layer1.HasPiAppFunPi.revAppFun₂ α B) a F ≃ F a :=
    HasFunctors.byDef₂ (F := Layer1.HasPiAppFunPi.defRevAppFun₂ α B)
                       (hFa := revAppFun.hasDefInstEq α B) (hF := revAppFun₂.hasDefInstEq α B)

  instance compFun.hasDefInstEq {B C : U} (F : α ⥤ B) (G : B ⥤ C) :
      DefType.HasDefInstEq (Layer1.HasCompFunPi.defCompFun F G) :=
    HasCompFunPi.hasDefInstEq α (Function.const B C) F G

  def compFun.byDef {B C : U} {F : α ⥤ B} {G : B ⥤ C} {a : α} : (G ⊙ F) a ≃ G (F a) :=
    HasFunctors.byDef

  instance revCompFun₂.hasDefInstEq {B C : U} (G : B ⥤ C) :
      DefType.HasDefInstEq (Layer1.HasRevCompFunPi₂.defRevCompFun₂ α G).toDefPi :=
    HasRevCompFunPi₂.hasDefInstEq α (Function.const B C) G

  def revCompFun₂.byDef {B C : U} {G : B ⥤ C} {F : α ⥤ B} :
      (Layer1.HasRevCompFunPi₂.revCompFun₂ α G) F ≃ G ⊙ F :=
    HasFunctors.byDef

  def revCompFun₂.byDef₂ {B C : U} {G : B ⥤ C} {F : α ⥤ B} {a : α} :
      (Layer1.HasRevCompFunPi₂.revCompFun₂ α G) F a ≃ G (F a) :=
    HasFunctors.byDef₂ (F := Layer1.HasRevCompFunPi₂.defRevCompFun₂ α G)
                       (hFa := λ F => compFun.hasDefInstEq α F G)
                       (hF := revCompFun₂.hasDefInstEq α G)

  compiler_slow instance revCompFun₃.hasDefInstEq (B C : U):
      DefType.HasDefInstEq (Layer1.HasRevCompFunPiFun.defRevCompFun₃ α B C).toDefPi :=
    HasRevCompFunPiFun.hasDefInstEq α (Function.const B C)

  compiler_slow def revCompFun₃.byDef {B C : U} {G : B ⥤ C} :
      (Layer1.HasRevCompFunPiFun.revCompFun₃ α B C) G ≃ Layer1.HasRevCompFunPi₂.revCompFun₂ α G :=
    HasFunctors.byDef

  compiler_slow def revCompFun₃.byDef₂ {B C : U} {G : B ⥤ C} {F : α ⥤ B} :
      (Layer1.HasRevCompFunPiFun.revCompFun₃ α B C) G F ≃ G ⊙ F :=
    HasFunctors.byDef₂ (α := B ⥤ C) (β := α ⥤ B) (Y := α ⥤ C)
                       (F := (Layer1.HasRevCompFunPiFun.defRevCompFun₃ α B C).toDefFun₂)
                       (hFa := revCompFun₂.hasDefInstEq α)
                       (hF := revCompFun₃.hasDefInstEq α B C)

  compiler_slow def revCompFun₃.byDef₃ {B C : U} {G : B ⥤ C} {F : α ⥤ B} {a : α} :
      (Layer1.HasRevCompFunPiFun.revCompFun₃ α B C) G F a ≃ G (F a) :=
    HasFunctors.byDef₃ (F := Layer1.HasRevCompFunPiFun.defRevCompFun₃ α B C)
                       (hFab := λ G F => compFun.hasDefInstEq α F G)
                       (hFa := revCompFun₂.hasDefInstEq α)
                       (hF := revCompFun₃.hasDefInstEq α B C)

end HasExternalLinearLogic


class HasLinearLogic (U : Universe) [HasPropositions Prp U] extends HasUnivFunctors U U where
  defIdFun (A : U) : A ⥤⦃EquivalenceFunctor.idFun A⦄ A
  defRevAppFun₂ (A B : U) :
    A ⥤ (A ⥤ B) ⥤{λ a F => F a,
                   λ a F₁ F₂ => congrFunFun F₁ F₂ a,
                   λ a₁ a₂ F => congrArgFun F a₁ a₂} B
  defRevCompFun₃ (A B C : U) :
    (B ⥤ C) ⥤ (A ⥤ B) ⥤ A ⥤{λ G F a => G (F a),
                              λ G F a₁ a₂ => Λ e => congrArg G (congrArg F e),
                              λ G F₁ F₂ a => Λ e => congrArg G (congrFun e a),
                              λ G₁ G₂ F a => Λ e => congrFun e (F a)} C

namespace HasLinearLogic

  instance {U : Universe} [HasPropositions Prp U] [h : HasLinearLogic U] (A B : U) :
      HasFunctors A B :=
    h.hFun A B

  instance toLayer1 (U : Universe) [HasPropositions Prp U] [h : HasLinearLogic U] :
      Layer1.HasLinearLogic U where
    defIdFun       A     := (h.defIdFun       A).toLayer1
    defRevAppFun₂  A B   := (h.defRevAppFun₂  A B).toLayer1
    defRevCompFun₃ A B C := (h.defRevCompFun₃ A B C).toLayer1

  variable {U : Universe} [HasPropositions Prp U] [h : HasLinearLogic U]

  instance hasIdFun (A : U) : HasIdFun A := ⟨h.defIdFun A⟩

  instance hasExternalLinearLogic (A : U) : HasExternalLinearLogic A U where
    defRevAppFun₂  B   := h.defRevAppFun₂  A B
    defRevCompFun₃ B C := h.defRevCompFun₃ A B C

  instance idFun.hasDefInstEq (A : U) : DefType.HasDefInstEq (Layer1.HasIdFun.defIdFun (A := A)) :=
    HasIdFun.hasDefInstEq A

  def idFun.byDef {A : U} {a : A} : (Layer1.HasIdFun.idFun A) a ≃ a := HasPiTypeBase.byDef

end HasLinearLogic


class HasExternalSubLinearLogic [Layer1.HasSubLinearLogic Prp] (α : Sort u)
                                [Layer1.HasEquivalenceRelationBase Prp α] (U : Universe.{u})
                                [HasPropositions Prp U] [HasUnivFunctors U U]
                                [∀ B : U, HasFunctors α B] where
  defConstFun₂ (B : U) :
    B ⥤ α ⥤{λ b a => b,
             λ b a₁ a₂ => Layer1.HasConstPi.constFun (a₁ ≃ a₂) (idIso b),
             λ b₁ b₂ a => Layer1.HasIdFun.idFun (b₁ ≃ b₂)} B

namespace HasExternalSubLinearLogic

  variable [Layer1.HasSubLinearLogic Prp]

  instance toLayer1 (α : Sort u) [Layer1.HasEquivalenceRelationBase Prp α] (U : Universe.{u})
                    [HasPropositions Prp U] [HasUnivFunctors U U] [∀ B : U, HasFunctors α B]
                    [h : HasExternalSubLinearLogic α U] :
      Layer1.HasExternalSubLinearLogic α U where
    defConstFun₂ B := (h.defConstFun₂ B).toLayer1

  variable (α : Sort u) [Layer1.HasEquivalenceRelationBase Prp α] {U : Universe.{u}}
           [HasPropositions Prp U] [HasUnivFunctors U U] [∀ B : U, HasFunctors α B]
           [h : HasExternalSubLinearLogic α U]

  instance (B : U) : Layer1.HasConstPi α B := Layer1.HasExternalSubLinearLogic.hasConstPi α B

  @[reducible] def constFun.congrArg {B : U} {b₁ b₂ : B} (e : b₁ ≃ b₂) :
      Layer1.HasConstPi.constFun α b₁ ≃ Layer1.HasConstPi.constFun α b₂ :=
    (h.defConstFun₂ B).appEq.appEq e

  instance {B : U} (b₁ b₂ : B) : Layer1.HasPiType (Function.const α (b₁ ≃ b₂)) :=
    DefFun.hasEqPi ((h.defConstFun₂ B).app b₁) ((h.defConstFun₂ B).app b₂)

  instance {B : U} (b₁ b₂ : B) : Layer1.HasConstPi α (b₁ ≃ b₂) :=
    ⟨λ e => ⟨constFun.congrArg α e⟩⟩

  instance {B : U} (b₁ b₂ : B) : Layer1.HasConstPiFun α (b₁ ≃ b₂) :=
    ⟨⟨(h.defConstFun₂ B).appEq.appEqFun b₁ b₂⟩⟩

  instance hasConstPi (B : U) : HasConstPi α B := ⟨λ b => ((h.defConstFun₂ B).app b).toDefPi⟩

  instance hasConstPiFun (B : U) : HasConstPiFun α B where
    defConstPiEq  := { defAppEq    := λ e => ⟨((h.defConstFun₂ B).appEq.defAppEq e).e⟩,
                       defAppEqFun := λ b₁ b₂ => ⟨((h.defConstFun₂ B).appEq.defAppEqFun b₁ b₂).inst⟩ }
    defConstPiFun := (h.defConstFun₂ B).toDefFun

  instance constFun.hasDefInstEq (B : U) (b : B) :
      DefType.HasDefInstEq (Layer1.HasConstPi.defConstFun α b) :=
    HasConstPi.hasDefInstEq α B b

  def constFun.byDef {B : U} {b : B} {a : α} : (Layer1.HasConstPi.constFun α b) a ≃ b :=
    HasFunctors.byDef

  instance constFun₂.hasDefInstEq (B : U) :
      DefType.HasDefInstEq (Layer1.HasConstPiFun.defConstFun₂ α B).toDefPi :=
    HasConstPiFun.hasDefInstEq α B

  def constFun₂.byDef {B : U} {b : B} :
      (Layer1.HasConstPiFun.constFun₂ α B) b ≃ Layer1.HasConstPi.constFun α b :=
    HasFunctors.byDef

  def constFun₂.byDef₂ {B : U} {b : B} {a : α} : (Layer1.HasConstPiFun.constFun₂ α B) b a ≃ b :=
    HasFunctors.byDef₂ (F := Layer1.HasConstPiFun.defConstFun₂ α B)
                       (hFa := constFun.hasDefInstEq α B) (hF := constFun₂.hasDefInstEq α B)

end HasExternalSubLinearLogic

class HasExternalAffineLogic [Layer1.HasSubLinearLogic Prp] (α : Sort u)
                             [Layer1.HasEquivalenceRelationBase Prp α] (U : Universe.{u})
                             [HasPropositions Prp U] [HasUnivFunctors U U] extends
  HasExternalLinearLogic α U, HasExternalSubLinearLogic α U


class HasSubLinearLogic [Layer1.HasSubLinearLogic Prp] (U : Universe) [HasPropositions Prp U]
                        [HasUnivFunctors U U] where
  defConstFun₂ (A B : U) :
    B ⥤ A ⥤{λ b a => b,
             λ b a₁ a₂ => Layer1.HasConstPi.constFun (a₁ ≃ a₂) (idIso b),
             λ b₁ b₂ a => Layer1.HasIdFun.idFun (b₁ ≃ b₂)} B

namespace HasSubLinearLogic

  variable [Layer1.HasSubLinearLogic Prp]

  instance toLayer1 (U : Universe) [HasPropositions Prp U] [HasUnivFunctors U U]
                    [h : HasSubLinearLogic U] :
      Layer1.HasSubLinearLogic U where
    defConstFun₂ A B := (h.defConstFun₂ A B).toLayer1

  variable {U : Universe} [HasPropositions Prp U] [HasUnivFunctors U U] [h : HasSubLinearLogic U]

  instance hasExternalSubLinearLogic (A : U) : HasExternalSubLinearLogic A U where
    defConstFun₂ B := h.defConstFun₂ A B

end HasSubLinearLogic

class HasAffineLogic [Layer1.HasSubLinearLogic Prp] (U : Universe) [HasPropositions Prp U] extends
  HasLinearLogic U, HasSubLinearLogic U

namespace HasAffineLogic

  variable [Layer1.HasSubLinearLogic Prp]

  instance toLayer1 (U : Universe) [HasPropositions Prp U] [HasAffineLogic U] :
      Layer1.HasAffineLogic U :=
    ⟨⟩

  variable {U : Universe} [HasPropositions Prp U] [h : HasAffineLogic U]

  instance hasExternalAffineLogic (A : U) : HasExternalAffineLogic A U := ⟨⟩

end HasAffineLogic


class HasExternalNonLinearLogic [Layer1.HasNonLinearLogic Prp] (α : Sort u)
                                [Layer1.HasEquivalenceRelationBase Prp α] (U : Universe.{u})
                                [HasPropositions Prp U] [HasUnivFunctors U U]
                                [∀ B : U, HasFunctors α B] where
  defDupFun₂ (B : U) :
    (α ⥤ α ⥤ B) ⥤ α ⥤{λ F a => F a a,
                        λ F a₁ a₂ => Λ e => congrArg₂ F e e,
                        λ F₁ F₂ a => Λ e => congrFun₂ e a a} B

namespace HasExternalNonLinearLogic

  variable [Layer1.HasNonLinearLogic Prp]

  instance toLayer1 (α : Sort u) [Layer1.HasEquivalenceRelationBase Prp α] (U : Universe.{u})
                    [HasPropositions Prp U] [HasUnivFunctors U U] [∀ B : U, HasFunctors α B]
                    [h : HasExternalNonLinearLogic α U] :
      Layer1.HasExternalNonLinearLogic α U where
    defDupFun₂ B := (h.defDupFun₂ B).toLayer1

  variable (α : Sort u) [Layer1.HasEquivalenceRelationBase Prp α] {U : Universe.{u}}
           [HasPropositions Prp U] [HasUnivFunctors U U] [∀ B : U, HasFunctors α B]
           [h : HasExternalNonLinearLogic α U]

  @[reducible] def dupFun.congrArg {B : U} {F₁ F₂ : α ⥤ α ⥤ B} (e : F₁ ≃ F₂) :
      Layer1.HasDupPi.dupFun F₁ ≃ Layer1.HasDupPi.dupFun F₂ :=
    (h.defDupFun₂ B).appEq.appEq e

  instance {B : U} (F₁ F₂ : α ⥤ α ⥤ B) (a₁ : α) : Layer1.HasPiType (λ a₂ => F₁ a₁ a₂ ≃ F₂ a₁ a₂) :=
    hasEqPi (F₁ a₁) (F₂ a₁)

  instance {B : U} (F₁ F₂ : α ⥤ α ⥤ B) :
      Layer1.HasPiType (λ a₁ => Layer1.HasPiType.Pi (λ a₂ => F₁ a₁ a₂ ≃ F₂ a₁ a₂)) :=
    hasEqPi₂ F₁ F₂

  instance {B : U} (F₁ F₂ : α ⥤ α ⥤ B) : Layer1.HasPiType (λ a => F₁ a a ≃ F₂ a a) :=
    DefFun.hasEqPi ((h.defDupFun₂ B).app F₁) ((h.defDupFun₂ B).app F₂)

  instance {B : U} (F₁ F₂ : α ⥤ α ⥤ B) : Layer1.HasDupPi (λ a₁ a₂ => F₁ a₁ a₂ ≃ F₂ a₁ a₂) :=
    ⟨λ e => ⟨dupFun.congrArg α e⟩⟩

  instance {B : U} (F₁ F₂ : α ⥤ α ⥤ B) : Layer1.HasDupPiFun (λ a₁ a₂ => F₁ a₁ a₂ ≃ F₂ a₁ a₂) :=
    ⟨⟨(h.defDupFun₂ B).appEq.appEqFun F₁ F₂⟩⟩

  instance hasDupPi (B : U) : HasDupPi (Function.const α (Function.const α B)) :=
    ⟨λ F => ((h.defDupFun₂ B).app F).toDefPi⟩
  instance (B : U) : HasDupPi (λ _ : α => Function.const α B) := hasDupPi α B
  instance (B : U) : HasDupPi (λ _ _ : α => B) := hasDupPi α B

  instance hasDupPiFun (B : U) : HasDupPiFun (Function.const α (Function.const α B)) where
    defDupPiEq  := { defAppEq    := λ e => ⟨((h.defDupFun₂ B).appEq.defAppEq e).e⟩,
                     defAppEqFun := λ F₁ F₂ => ⟨((h.defDupFun₂ B).appEq.defAppEqFun F₁ F₂).inst⟩ }
    defDupPiFun := { inst := (h.defDupFun₂ B).toDefFun.inst,
                     e    := (h.defDupFun₂ B).toDefFun.e }
  instance (B : U) : HasDupPiFun (λ _ : α => Function.const α B) := hasDupPiFun α B
  instance (B : U) : HasDupPiFun (λ _ _ : α => B) := hasDupPiFun α B

  instance dupFun.hasDefInstEq (B : U) (F : α ⥤ α ⥤ B) :
      DefType.HasDefInstEq (Layer1.HasDupPi.defDupFun F) :=
    HasDupPi.hasDefInstEq (Function.const α (Function.const α B)) F

  def dupFun.byDef {B : U} {F : α ⥤ α ⥤ B} {a : α} : (Layer1.HasDupPi.dupFun F) a ≃ F a a :=
    HasFunctors.byDef

  instance dupFun₂.hasDefInstEq (B : U) :
      DefType.HasDefInstEq (Layer1.HasDupPiFun.defDupFun₂ α B).toDefPi :=
    HasDupPiFun.hasDefInstEq (Function.const α (Function.const α B))

  def dupFun₂.byDef {B : U} {F : α ⥤ α ⥤ B} :
      (Layer1.HasDupPiFun.dupFun₂ α B) F ≃ Layer1.HasDupPi.dupFun F :=
    HasFunctors.byDef

  def dupFun₂.byDef₂ {B : U} {F : α ⥤ α ⥤ B} {a : α} :
      (Layer1.HasDupPiFun.dupFun₂ α B) F a ≃ F a a :=
    HasFunctors.byDef₂ (F := Layer1.HasDupPiFun.defDupFun₂ α B)
                       (hFa := dupFun.hasDefInstEq α B) (hF := dupFun₂.hasDefInstEq α B)

end HasExternalNonLinearLogic

class HasExternalFullLogic [Layer1.HasSubLinearLogic Prp] [Layer1.HasNonLinearLogic Prp] (α : Sort u)
                           [Layer1.HasEquivalenceRelationBase Prp α] (U : Universe.{u})
                           [HasPropositions Prp U] [HasUnivFunctors U U] extends
  HasExternalAffineLogic α U, HasExternalNonLinearLogic α U


class HasNonLinearLogic [Layer1.HasNonLinearLogic Prp] (U : Universe) [HasPropositions Prp U]
                        [HasUnivFunctors U U] where
  defDupFun₂ (A B : U) :
    (A ⥤ A ⥤ B) ⥤ A ⥤{λ F a => F a a,
                        λ F a₁ a₂ => Λ e => congrArg₂ F e e,
                        λ F₁ F₂ a => Λ e => congrFun₂ e a a} B

namespace HasNonLinearLogic

  variable [Layer1.HasNonLinearLogic Prp]

  instance toLayer1 (U : Universe) [HasPropositions Prp U] [HasUnivFunctors U U]
                    [h : HasNonLinearLogic U] :
      Layer1.HasNonLinearLogic U where
    defDupFun₂ A B := (h.defDupFun₂ A B).toLayer1

  variable {U : Universe} [HasPropositions Prp U] [HasUnivFunctors U U] [h : HasNonLinearLogic U]

  instance hasExternalNonLinearLogic (A : U) : HasExternalNonLinearLogic A U where
    defDupFun₂ B := h.defDupFun₂ A B

end HasNonLinearLogic

class HasFullLogic [Layer1.HasSubLinearLogic Prp] [Layer1.HasNonLinearLogic Prp] (U : Universe)
                   [HasPropositions Prp U] extends
  HasAffineLogic U, HasNonLinearLogic U

namespace HasFullLogic

  variable [Layer1.HasSubLinearLogic Prp] [Layer1.HasNonLinearLogic Prp]

  instance toLayer1 (U : Universe) [HasPropositions Prp U] [HasFullLogic U] :
      Layer1.HasFullLogic U :=
    ⟨⟩

  variable {U : Universe} [HasPropositions Prp U] [h : HasFullLogic U]

  instance hasExternalFullLogic (A : U) : HasExternalFullLogic A U := ⟨⟩

end HasFullLogic
