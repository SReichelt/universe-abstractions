import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedFunctors
import UniverseAbstractions.Universes.Layer1.Meta.Reflect.Universes



namespace UniverseAbstractions.Layer1.Meta

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 10000
set_option linter.unusedVariables false

open Lean Lean.Meta Qq UniverseAbstractions.Meta
     HasPiType HasFunctors



-- In this file, we reflect dependent and independent object-level functors as meta-level functors.
-- This seems like the right thing to do because it subsequently gives us the power to use
-- object-level infrastructure at the meta level; e.g. we could construct object-level functors
-- using the functor notation at the meta level. Unfortunately, it also complicates things quite a
-- bit because the `quote4` library cannot see through our abstractions very well. As a result, we
-- essentially need to define everything twice, first using `quote4` (indicated by a ' suffix) and
-- then again as a universe-based variant.
--
-- On the other hand, the universe-based variant does not need to mirror the `quote4` variant
-- exactly; we can add some additional features to it in order to produce the desired results more
-- easily. At layer 1, there is essentially just one such feature: We want to output `...Fun` (e.g.
-- `revAppFun`) instead of `...Pi` whenever we can, which is a bit tricky because some of the
-- arguments are very different. By including optional expressions that reference `HasFunctors`
-- instances, we can output either `...Fun` or `...Pi` from a single code path.



def mkHasPiType' {u v vv : Level} (α : Q(Sort u)) (V : Q(Universe.{v, vv})) (P : Q($α → $V)) :=
  ⌜HasType $V (∀ a, $P a)⌝

namespace mkHasPiType'

  section

    variable {u v vv : Level} (α : Q(Sort u)) (V : Q(Universe.{v, vv})) (P : Q($α → $V))

    def mkForAll := ⌜∀ a, $P a⌝

    def mkForAll.mkApp (f : Q(∀ a, $P a)) (a : Q($α)) : Q($P $a) := ⌜$f $a⌝
  
  end

  section

    variable {u v vv : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})} {P : Q($α → $V)}
             (h : mkHasPiType' α V P)

    def mkPi : Q($V) := ⌜Pi $P⌝

    def mkApply (F : Q(Pi $P)) : Q(∀ a, $P a) := ⌜HasPiType.apply $F⌝

    def mkDefPi (f : Q(∀ a, $P a)) : Q($V) := ⌜[∀ a, $P a | $V]_{$f}⌝

  end

  section

    def mkHasDepElim' {u u' v vv : Level} (α : Q(Sort u)) (V : Q(Universe.{v, vv})) (P : Q($α → $V))
                      (β : Q($α → Sort u')) :=
      ⌜∀ a, HasElim ($P a) ($β a)⌝

    variable {u u' v vv : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})} {P : Q($α → $V)}
             {β : Q($α → Sort u')} (h : mkHasDepElim' α V P β)

    def mkHasDepElim'.mkApp (f : Q(∀ a, $β a)) (a : Q($α)) : Q($V) :=
      ⌜[$P $a]_{$f $a}⌝

    def mkDefPi' (hP : mkHasPiType' α V P) (f : Q(∀ a, $β a)) : Q($V) :=
      ⌜HasElim.DefInst (Pi $P) $f (h := HasPiType.hasElim₂ $P)⌝

  end

  section

    variable {v vv : Level} (V : Q(Universe.{v, vv}))

    structure PiApp (u : Level) where
      α  : Q(Sort u)
      P  : Q($α → $V)
      hP : Q(HasType $V (∀ a, $P a))
      F  : Q(Pi $P)
      a  : Q($α)

    variable (Y : Q($V)) (y : Q($Y))

    def mkIsPiApp (u : Level) := ⌜IsPiApp.{u} $y⌝

    namespace mkIsPiApp

      variable {u : Level} (hApp : mkIsPiApp V Y y u)

      def mkApp : MetaM (PiApp V u) := do
        let α  : Q(Sort u)                 ← unfoldDefinitionI ⌜($hApp).α⌝
        let P  : Q($α → $V)                ← unfoldDefinitionI ⌜($hApp).P⌝
        let hP : Q(HasType $V (∀ a, $P a)) ← unfoldDefinitionI ⌜($hApp).hP⌝
        let F  : Q(Pi $P)                  ← unfoldDefinitionI ⌜($hApp).F⌝
        let a  : Q($α)                     ← unfoldDefinitionI ⌜($hApp).a⌝
        pure { α  := α,
               P  := P,
               hP := hP,
               F  := F,
               a  := a }

    end mkIsPiApp

    def mkIsPiApp₂ (u u' : Level) := ⌜IsPiApp₂.{u, u'} $y⌝

    namespace mkIsPiApp₂

      variable {u u' : Level} (hApp : mkIsPiApp₂ V Y y u u')

      def mkApp : MetaM (PiApp V u') := do
        let α     : Q(Sort u)                        ← unfoldDefinitionI ⌜($hApp).α⌝
        let β     : Q(Sort u')                       ← unfoldDefinitionI ⌜($hApp).β⌝
        let P     : Q($α → $β → $V)                  ← unfoldDefinitionI ⌜($hApp).P⌝
        let hPa   : Q(∀ a, HasType $V (∀ b, $P a b)) ← unfoldDefinitionI ⌜($hApp).hPa⌝
        let hPiPa : Q(HasType $V (∀ a, Pi ($P a)))   ← unfoldDefinitionI ⌜($hApp).hPiPa⌝
        let F     : Q(Pi₂ $P)                        ← unfoldDefinitionI ⌜($hApp).F⌝
        let a     : Q($α)                            ← unfoldDefinitionI ⌜($hApp).a⌝
        let b     : Q($β)                            ← unfoldDefinitionI ⌜($hApp).b⌝
        pure { α  := β,
               P  := ⌜$P   $a⌝,
               hP := ⌜$hPa $a⌝,
               F  := ⌜$F   $a⌝,
               a  := b }

    end mkIsPiApp₂

  end

end mkHasPiType'

def mkHasPiType {α : _sort} {v : Level} {V : _Universe v} {p : α → V} (P : [α ⥤ _[V]]_{p}) :
    ClassExpr :=
  ⟨mkHasPiType' α.α V.U P⟩

namespace mkHasPiType

  section

    variable {α : _sort} {v : Level} {V : _Universe v}

    @[reducible] def reflectProp {p : α → V} (P : [α ⥤ _[V]]_{p}) : α → V := p

    instance reflect {p : α → V} (P : [α ⥤ _[V]]_{p}) [h : mkHasPiType P] :
        HasType V (∀ a, (reflectProp P) a) where
      A     := mkHasPiType'.mkPi h.h
      hElim := ⟨λ F => mkHasPiType'.mkForAll.mkApp α.α V.U P (mkHasPiType'.mkApply h.h F)⟩

    def mkPi {p : α → V} (P : [α ⥤ _[V]]_{p}) [h : mkHasPiType P] : V := Pi (reflectProp P)

    def defSortPropFun {p : α → V} (P : [α ⥤ _[V]]_{p}) :
        [α ⥤ _sort.mkSortType v]_{λ a => _⌈(reflectProp P) a⌉.α} :=
      let P' : Q($α.α → $V.U) := P
      ⌜λ a => ⌈$P' a⌉⌝

    @[reducible] def sortProp {p : α → V} (P : [α ⥤ _[V]]_{p}) : α → _sort :=
      _sort.defFunToProp (defSortPropFun P)

    def mkApply {p : α → V} {P : [α ⥤ _[V]]_{p}} [h : mkHasPiType P] (F : mkPi P) :
        Pi (sortProp P) :=
      mkHasPiType'.mkApply h.h F

    def mkDefPi {p : α → V} (P : [α ⥤ _[V]]_{p}) [h : mkHasPiType P] (f : Pi (sortProp P)) : V :=
      mkHasPiType'.mkDefPi h.h f

  end

  section

    variable {α : _sort} {u' v : Level} {V : _Universe v} {p : α → V} (P : [α ⥤ _[V]]_{p})
             (β : α ⥤ _sort.mkSortType u')

    def mkHasDepElim' : ClassExpr := ⟨mkHasPiType'.mkHasDepElim' (u' := u') α.α V.U P β⟩

    @[reducible] def sortProp' {α : _sort} {u' : Level} (β : α ⥤ _sort.mkSortType u') :
        α → _sort :=
      _sort.funToProp β

    variable [h : mkHasDepElim' P β]

    def mkHasDepElim'.mkApp (f : Pi (sortProp' β)) (a : α) : V :=
      mkHasPiType'.mkHasDepElim'.mkApp h.h f a

    def mkDefPi' [hP : mkHasPiType P] (f : Pi (sortProp' β)) : V := mkHasPiType'.mkDefPi' h.h hP.h f

  end

  section

    variable {v : Level} {V : _Universe v} {Y : V} (y : Y)

    def mkIsPiApp (u : Level) : ClassExpr := ⟨mkHasPiType'.mkIsPiApp V.U Y y u⟩

    namespace mkIsPiApp

      variable (u : Level) [hApp : mkIsPiApp y u]

      def mkApp : MetaM (mkHasPiType'.PiApp V.U u) := mkHasPiType'.mkIsPiApp.mkApp V.U Y y hApp.h

    end mkIsPiApp

    def mkIsPiApp₂ (u u' : Level) : ClassExpr := ⟨mkHasPiType'.mkIsPiApp₂ V.U Y y u u'⟩

    namespace mkIsPiApp₂

      variable (u u' : Level) [hApp : mkIsPiApp₂ y u u']

      def mkApp : MetaM (mkHasPiType'.PiApp V.U u') := mkHasPiType'.mkIsPiApp₂.mkApp V.U Y y hApp.h

    end mkIsPiApp₂

  end

  section

    variable {u v : Level} {U : _Universe u} {A : U} {V : _Universe v}

    @[reducible] def reflectProp' {p : A → V} (P : [_⌈A⌉ ⥤ _[V]]_{p}) :
        A → V :=
      reflectProp P

    instance reflect' {p : A → V} (P : [_⌈A⌉ ⥤ _[V]]_{p}) [h : mkHasPiType P] :
        HasType V (∀ a, (reflectProp' P) a) :=
      reflect P

  end

  section

    instance {α : _sort} {v : Level} {V : _Universe v} {p : α → V} (P : [α ⥤ _[V]]_{p}) :
        HasType _sort (∀ a, _⌈(reflectProp P) a⌉) :=
      let P' : Q($α.α → $V.U) := P
      let P'' : Q($α.α → Sort v) := ⌜λ a => $P' a⌝
      _sort.hasPiType P''

    instance {α : _sort} {v w : Level} {V : _Universe v} {p : α → V} {P : [α ⥤ _[V]]_{p}}
             (W : _Universe w) :
        HasType _sort (∀ a, (_⌈(reflectProp P) a⌉ ⥤ _[W])) :=
      let P' : Q($α.α → $V.U) := P
      let Q : Q($α.α → Sort (imax v $W.uu)) := ⌜λ a => $P' a → $W.U⌝
      _sort.hasPiType' Q

  end

end mkHasPiType


def mkHasQuantPiType' {u u' v vv : Level} (α : Q(Sort u)) (β : Q($α → Sort u'))
                      (V : Q(Universe.{v, vv})) (P : Q(∀ a, $β a → $V)) :=
  ⌜∀ a, HasType $V (∀ b, $P a b)⌝

namespace mkHasQuantPiType'

  def metaProp {u u' v vv : Level} (α : Q(Sort u)) (β : Q($α → Sort u')) (V : Q(Universe.{v, vv})) :
      Q($α → Sort (imax u' vv)) :=
    ⌜λ a => $β a → $V⌝

  variable {u u' v vv : Level} {α : Q(Sort u)} {β : Q($α → Sort u')} {V : Q(Universe.{v, vv})}
           {P : Q(∀ a, $β a → $V)} (hP : mkHasQuantPiType' α β V P)

  def app (a : Q($α)) : mkHasPiType' ⌜$β $a⌝ V ⌜$P $a⌝ := ⌜$hP $a⌝

  def mkPiProp : Q($α → $V) := ⌜λ a => Pi ($P a)⌝

  variable (hPiPa : mkHasPiType' α V (mkPiProp hP))

  def mkPi₂ : Q($V) := ⌜Pi₂ $P⌝

  def mkDefPi₂ (f : Q(∀ a b, $P a b)) : Q($V) := ⌜[∀ a b, $P a b | $V]_{$f}⌝

end mkHasQuantPiType'

@[reducible] def mkHasQuantPiType.metaProp {α : _sort} {u' v : Level} {β' : α → _sort.mkSortType u'}
                                           (β : [α ⥤ _sort.mkSortType u']_{β'}) (V : _Universe v) :
    α → _sort :=
  _sort.defFunToProp (v := mkLevelIMax u' V.uu) (p := λ a => _sort.funType (β' a) _[V])
                     (mkHasQuantPiType'.metaProp (u' := u') α.α β V.U)

def mkHasQuantPiType {α : _sort} {u' v : Level} {β' : α → _sort.mkSortType u'}
                     {β : [α ⥤ _sort.mkSortType u']_{β'}} {V : _Universe v} {p : ∀ a, β' a → V}
                     {P' : ∀ a, [β' a ⥤ _[V]]_{p a}}
                     (P : [∀ a, (mkHasQuantPiType.metaProp β V) a | _sort]_{P'}) :
    ClassExpr :=
  ⟨mkHasQuantPiType' (u' := u') α.α β V.U P⟩

namespace mkHasQuantPiType

  variable {α : _sort} {u' v : Level} {β' : α → _sort.mkSortType u'}
           {β : [α ⥤ _sort.mkSortType u']_{β'}} {V : _Universe v}

  @[reducible] def reflectProp {p : ∀ a, β' a → V} {P' : ∀ a, [β' a ⥤ _[V]]_{p a}}
                               (P : [∀ a, (mkHasQuantPiType.metaProp β V) a | _sort]_{P'}) :
      ∀ a, β' a → V :=
    λ a => mkHasPiType.reflectProp (P' a)

  variable {p : ∀ a, β' a → V} {P' : ∀ a, [β' a ⥤ _[V]]_{p a}}
           (P : [∀ a, (mkHasQuantPiType.metaProp β V) a | _sort]_{P'}) [h : mkHasQuantPiType P]

  instance app (a : α) : mkHasPiType (P' a) := ⟨mkHasQuantPiType'.app h.h a⟩

  def piProp : [α ⥤ _[V]]_{λ a => Pi ((reflectProp P) a)} := mkHasQuantPiType'.mkPiProp h.h

end mkHasQuantPiType


@[reducible] def mkHasIndepQuantPiType' {u u' v vv : Level} (α : Q(Sort u)) (β : Q(Sort u'))
                                        (V : Q(Universe.{v, vv})) (P : Q($α → $β → $V)) :=
  mkHasQuantPiType' (u' := u') α ⌜λ _ => $β⌝ V P

@[reducible] def mkHasIndepQuantPiType.prop {α β : _sort} {v : Level} {V : _Universe v}
                                            {p : α → β → V} (P : [α ⥤ β ⥤ _[V]]__{p}) (a : α) :
    [β ⥤ _[V]]_{p a} :=
  P a

@[reducible] def mkHasIndepQuantPiType.prop₂ {α β : _sort} {v : Level} {V : _Universe v}
                                             {p : α → β → V} (P : [α ⥤ β ⥤ _[V]]__{p}) :
    [∀ a, (mkHasQuantPiType.metaProp (HasConstPi.defConstPi (_sort.mkSortType.fromSort β)) V) a |
     _sort]_{λ a => prop P a} :=
  P

@[reducible] def mkHasIndepQuantPiType {α β : _sort} {v : Level} {V : _Universe v} {p : α → β → V}
                                       (P : [α ⥤ β ⥤ _[V]]__{p}) :
    ClassExpr :=
  mkHasQuantPiType (mkHasIndepQuantPiType.prop₂ P)

namespace mkHasIndepQuantPiType

  @[reducible] def reflectProp {α β : _sort} {v : Level} {V : _Universe v} {p : α → β → V}
                               (P : [α ⥤ β ⥤ _[V]]__{p}) :
      α → β → V :=
    p

  variable {α β : _sort} {v : Level} {V : _Universe v} {p : α → β → V} (P : [α ⥤ β ⥤ _[V]]__{p})
           [h : mkHasIndepQuantPiType P]

  instance app (a : α) : mkHasPiType (prop P a) := mkHasQuantPiType.app (prop₂ P) a

  instance (a : α) : HasType V (∀ b, (reflectProp P) a b) := mkHasPiType.reflect (prop P a)

  def piProp : [α ⥤ _[V]]_{λ a => Pi ((reflectProp P) a)} := mkHasQuantPiType.piProp (prop₂ P)

end mkHasIndepQuantPiType


@[reducible] def mkHasUnivQuantPiType' {u v vv w ww : Level} (α : Q(Sort u))
                                       (V : Q(Universe.{v, vv})) (P : Q($α → $V))
                                       (W : Q(Universe.{w, ww})) (Q : Q(∀ a, $P a → $W)) :=
  mkHasQuantPiType' (u' := v) α ⌜λ a => $P a⌝ W Q

@[reducible] def mkHasUnivQuantPiType.metaProp {α : _sort} {v w : Level} {V : _Universe v}
                                               {p : α → _[V]} (P : [α ⥤ _[V]]_{p})
                                               (W : _Universe w) :
    α → _sort :=
  mkHasQuantPiType.metaProp (mkHasPiType.defSortPropFun P) W

@[reducible] def mkHasUnivQuantPiType {α : _sort} {v w : Level} {V : _Universe v}
                                      {p : α → _[V]} {P : [α ⥤ _[V]]_{p}} {W : _Universe w}
                                      {q : ∀ a, (mkHasPiType.reflectProp P) a → W}
                                      {Q' : ∀ a, [_⌈(mkHasPiType.reflectProp P) a⌉ ⥤ _[W]]_{q a}}
                                      (Q : [∀ a, (mkHasUnivQuantPiType.metaProp P W) a | _sort]_{Q'}) :=
  mkHasQuantPiType Q

namespace mkHasUnivQuantPiType

  variable {α : _sort} {v w : Level} {V : _Universe v} {p : α → _[V]} {P : [α ⥤ _[V]]_{p}}
           {W : _Universe w}

  @[reducible] def reflectProp {q : ∀ a, (mkHasPiType.reflectProp P) a → W}
                               {Q' : ∀ a, [_⌈(mkHasPiType.reflectProp P) a⌉ ⥤ _[W]]_{q a}}
                               (Q : [∀ a, (mkHasUnivQuantPiType.metaProp P W) a | _sort]_{Q'}) :
      ∀ a, (mkHasPiType.reflectProp P) a → W :=
    λ a => mkHasPiType.reflectProp' (Q' a)

  variable {q : ∀ a, (mkHasPiType.reflectProp P) a → W}
           {Q' : ∀ a, [_⌈(mkHasPiType.reflectProp P) a⌉ ⥤ _[W]]_{q a}}
           (Q : [∀ a, (mkHasUnivQuantPiType.metaProp P W) a | _sort]_{Q'})
           [h : mkHasUnivQuantPiType Q]

  instance app (a : α) : mkHasPiType (Q' a) := mkHasQuantPiType.app Q a

  def piProp : [α ⥤ _[W]]_{λ a => Pi ((reflectProp Q) a)} := mkHasQuantPiType.piProp Q

end mkHasUnivQuantPiType


def mkHasFunctors' {u uu : Level} (α : Q(Sort u)) (U : Q(Universe.{u, uu})) :=
  ⌜HasFunctors $α $U⌝

namespace mkHasFunctors'

  variable {u uu : Level}

  section

    variable (α : Q(Sort u)) (U : Q(Universe.{u, uu})) (Y : Q($U))

    def mkFunction := ⌜$α → $Y⌝

    def mkFunction.mkApp (f : Q($α → $Y)) (a : Q($α)) : Q($Y) := ⌜$f $a⌝
  
  end

  section

    variable {α : Q(Sort u)} {U : Q(Universe.{u, uu})} (h : mkHasFunctors' α U) (Y : Q($U))

    def toMkHasPiType' : mkHasPiType' α U ⌜λ _ => $Y⌝ := ⌜($h).hFun $Y⌝

    def mkFun : Q($U) := ⌜$α ⥤ $Y⌝

    def mkApply (F : Q($α ⥤ $Y)) : Q($α → $Y) := ⌜HasPiType.apply $F⌝

    def mkDefFun (f : Q($α → $Y)) : Q($U) := ⌜[$α ⥤ $Y]_{$f}⌝

  end

  section

    variable (U : Q(Universe.{u, uu})) (Y : Q($U))

    structure FunApp where
      α  : Q(Sort u)
      hα : Q(HasFunctors $α $U)
      F  : Q($α ⥤ $Y)
      a  : Q($α)

    def FunApp.toPiApp (app : FunApp U Y) : mkHasPiType'.PiApp U u where
      α  := app.α
      P  := ⌜λ _ => $Y⌝
      hP := ⌜$(app.hα).hFun $Y⌝
      F  := app.F
      a  := app.a

    variable (y : Q($Y))

    def mkIsFunApp := ⌜IsFunApp.{u} $y⌝

    namespace mkIsFunApp

      variable (hApp : mkIsFunApp U Y y)

      def mkApp : MetaM (FunApp U Y) := do
        let α  : Q(Sort u)            ← unfoldDefinitionI ⌜($hApp).α⌝
        let hα : Q(HasFunctors $α $U) ← unfoldDefinitionI ⌜($hApp).hα⌝
        let F  : Q($α ⥤ $Y)           ← unfoldDefinitionI ⌜($hApp).F⌝
        let a  : Q($α)                ← unfoldDefinitionI ⌜($hApp).a⌝
        pure { α  := α,
               hα := hα,
               F  := F,
               a  := a }

    end mkIsFunApp

    def mkIsFunApp₂ := ⌜IsFunApp₂ $y⌝

    namespace mkIsFunApp₂

      variable (hApp : mkIsFunApp₂ U Y y)

      def mkApp : MetaM (FunApp U Y) := do
        let α  : Q(Sort u)            ← unfoldDefinitionI ⌜($hApp).α⌝
        let β  : Q(Sort u)            ← unfoldDefinitionI ⌜($hApp).β⌝
        let hα : Q(HasFunctors $α $U) ← unfoldDefinitionI ⌜($hApp).hα⌝
        let hβ : Q(HasFunctors $β $U) ← unfoldDefinitionI ⌜($hApp).hβ⌝
        let F  : Q($α ⥤ $β ⥤ $Y)      ← unfoldDefinitionI ⌜($hApp).F⌝
        let a  : Q($α)                ← unfoldDefinitionI ⌜($hApp).a⌝
        let b  : Q($β)                ← unfoldDefinitionI ⌜($hApp).b⌝
        pure { α  := β,
               hα := hβ,
               F  := ⌜$F $a⌝,
               a  := b }

    end mkIsFunApp₂

    def mkIsFunApp₂' := ⌜IsFunApp₂' $y⌝

    namespace mkIsFunApp₂'

      variable (hApp : mkIsFunApp₂' U Y y)
    
      def mkH₂ : mkIsFunApp U Y y := ⌜($hApp).h₂⌝
      def mkIsFunApp : mkIsFunApp U Y y := ⌜($hApp).toIsFunApp⌝

    end mkIsFunApp₂'

    def mkIsFunApp₃ := ⌜IsFunApp₃ $y⌝

    namespace mkIsFunApp₃

      variable (hApp : mkIsFunApp₃ U Y y)

      def mkApp : MetaM (FunApp U Y) := do
        let α  : Q(Sort u)            ← unfoldDefinitionI ⌜($hApp).α⌝
        let β  : Q(Sort u)            ← unfoldDefinitionI ⌜($hApp).β⌝
        let γ  : Q(Sort u)            ← unfoldDefinitionI ⌜($hApp).γ⌝
        let hα : Q(HasFunctors $α $U) ← unfoldDefinitionI ⌜($hApp).hα⌝
        let hβ : Q(HasFunctors $β $U) ← unfoldDefinitionI ⌜($hApp).hβ⌝
        let hγ : Q(HasFunctors $γ $U) ← unfoldDefinitionI ⌜($hApp).hγ⌝
        let F  : Q($α ⥤ $β ⥤ $γ ⥤ $Y) ← unfoldDefinitionI ⌜($hApp).F⌝
        let a  : Q($α)                ← unfoldDefinitionI ⌜($hApp).a⌝
        let b  : Q($β)                ← unfoldDefinitionI ⌜($hApp).b⌝
        let c  : Q($γ)                ← unfoldDefinitionI ⌜($hApp).c⌝
        pure { α  := γ,
               hα := hγ,
               F  := ⌜$F $a $b⌝,
               a  := c }

    end mkIsFunApp₃

    def mkIsFunApp₃' := ⌜IsFunApp₃' $y⌝

    namespace mkIsFunApp₃'

      variable (hApp : mkIsFunApp₃' U Y y)
    
      def mkH₃ : mkIsFunApp U Y y := ⌜($hApp).h₃⌝
      def mkIsFunApp₂' : mkIsFunApp₂' U Y y := ⌜($hApp).toIsFunApp₂'⌝

    end mkIsFunApp₃'

    def mkIsFunApp₄ := ⌜IsFunApp₄ $y⌝

    namespace mkIsFunApp₄

      variable (hApp : mkIsFunApp₄ U Y y)

      def mkApp : MetaM (FunApp U Y) := do
        let α  : Q(Sort u)                             ← unfoldDefinitionI ⌜($hApp).α⌝
        let β  : Q(Sort u)                             ← unfoldDefinitionI ⌜($hApp).β⌝
        let γ  : Q(Sort u)                             ← unfoldDefinitionI ⌜($hApp).γ⌝
        let δ  : Q(Sort u)                             ← unfoldDefinitionI ⌜($hApp).δ⌝
        let hα : Q(HasFunctors $α $U)                  ← unfoldDefinitionI ⌜($hApp).hα⌝
        let hβ : Q(HasFunctors $β $U)                  ← unfoldDefinitionI ⌜($hApp).hβ⌝
        let hγ : Q(HasFunctors $γ $U)                  ← unfoldDefinitionI ⌜($hApp).hγ⌝
        let hδ : Q(HasFunctors $δ $U)                  ← unfoldDefinitionI ⌜($hApp).hδ⌝
        let F  : Q($α ⥤ $β ⥤ $γ ⥤ $δ ⥤ $Y)             ← unfoldDefinitionI ⌜($hApp).F⌝
        let a  : Q($α)                                 ← unfoldDefinitionI ⌜($hApp).a⌝
        let b  : Q($β)                                 ← unfoldDefinitionI ⌜($hApp).b⌝
        let c  : Q($γ)                                 ← unfoldDefinitionI ⌜($hApp).c⌝
        let d  : Q($δ)                                 ← unfoldDefinitionI ⌜($hApp).d⌝
        pure { α  := δ,
               hα := hδ,
               F  := ⌜$F $a $b $c⌝,
               a  := d }

    end mkIsFunApp₄

    def mkIsFunApp₄' := ⌜IsFunApp₄' $y⌝

    namespace mkIsFunApp₄'

      variable (hApp : mkIsFunApp₄' U Y y)
    
      def mkH₄ : mkIsFunApp U Y y := ⌜($hApp).h₄⌝
      def mkIsFunApp₃' : mkIsFunApp₃' U Y y := ⌜($hApp).toIsFunApp₃'⌝

    end mkIsFunApp₄'

  end

end mkHasFunctors'

def mkHasFunctors (α : _sort) (U : _Universe α.u) : ClassExpr := ⟨mkHasFunctors' α.α U.U⟩

namespace mkHasFunctors

  instance toMkHasPiType (α : _sort) {U : _Universe α.u} [h : mkHasFunctors α U] (Y : U) :
      mkHasPiType (HasConstPi.defConstPi (α := α) _(Y)) :=
    ⟨mkHasFunctors'.toMkHasPiType' h.h Y⟩

  instance reflect (α : _sort) (U : _Universe α.u) [h : mkHasFunctors α U] :
      HasFunctors α U where
    hFun Y := { A     := mkHasFunctors'.mkFun h.h Y,
                hElim := ⟨λ F => mkHasFunctors'.mkFunction.mkApp α.α U.U Y (mkHasFunctors'.mkApply h.h Y F)⟩ }

  instance reflect' {u : Level} {U : _Universe u} (A : U) (V : _Universe u)
                    [h : mkHasFunctors _⌈A⌉ V] :
      HasFunctors A V :=
    reflect _⌈A⌉ V

  def mkApply {α : _sort} {U : _Universe α.u} [h : mkHasFunctors α U] {Y : U} (F : α ⥤ Y) :
      α ⥤ _⌈Y⌉ :=
    mkHasFunctors'.mkApply h.h Y F

  def mkApply' {u : Level} {U V : _Universe u} {A : U} [h : mkHasFunctors _⌈A⌉ V] {B : V}
               (F : A ⥤ B) :
      _⌈A⌉ ⥤ _⌈B⌉ :=
    mkApply F

  section

    variable (α : _sort) {U : _Universe α.u} [h : mkHasFunctors α U] (Y : U)

    def mkDefFun (f : α ⥤ _⌈Y⌉) := mkHasFunctors'.mkDefFun h.h Y f

  end

  section

    variable {u : Level} {U : _Universe u} {Y : U} (y : Y)

    def mkIsFunApp : ClassExpr := ⟨mkHasFunctors'.mkIsFunApp U.U Y y⟩

    namespace mkIsFunApp

      variable [hApp : mkIsFunApp y]

      def mkApp : MetaM (mkHasFunctors'.FunApp U.U Y) :=
        mkHasFunctors'.mkIsFunApp.mkApp U.U Y y hApp.h

    end mkIsFunApp

    def mkIsFunApp₂ : ClassExpr := ⟨mkHasFunctors'.mkIsFunApp₂ U.U Y y⟩

    namespace mkIsFunApp₂

      variable [hApp : mkIsFunApp₂ y]

      def mkApp : MetaM (mkHasFunctors'.FunApp U.U Y) :=
        mkHasFunctors'.mkIsFunApp₂.mkApp U.U Y y hApp.h

    end mkIsFunApp₂

    def mkIsFunApp₂' : ClassExpr := ⟨mkHasFunctors'.mkIsFunApp₂' U.U Y y⟩

    namespace mkIsFunApp₂'

      variable [hApp : mkIsFunApp₂' y]
    
      def mkH₂ : mkIsFunApp y := ⟨mkHasFunctors'.mkIsFunApp₂'.mkH₂ U.U Y y hApp.h⟩
      instance : mkIsFunApp y := ⟨mkHasFunctors'.mkIsFunApp₂'.mkIsFunApp U.U Y y hApp.h⟩

    end mkIsFunApp₂'

    def mkIsFunApp₃ : ClassExpr := ⟨mkHasFunctors'.mkIsFunApp₃ U.U Y y⟩

    namespace mkIsFunApp₃

      variable [hApp : mkIsFunApp₃ y]

      def mkApp : MetaM (mkHasFunctors'.FunApp U.U Y) :=
        mkHasFunctors'.mkIsFunApp₃.mkApp U.U Y y hApp.h

    end mkIsFunApp₃

    def mkIsFunApp₃' : ClassExpr := ⟨mkHasFunctors'.mkIsFunApp₃' U.U Y y⟩

    namespace mkIsFunApp₃'

      variable [hApp : mkIsFunApp₃' y]

      def mkH₃ : mkIsFunApp y := ⟨mkHasFunctors'.mkIsFunApp₃'.mkH₃ U.U Y y hApp.h⟩
      instance : mkIsFunApp₂' y := ⟨mkHasFunctors'.mkIsFunApp₃'.mkIsFunApp₂' U.U Y y hApp.h⟩

    end mkIsFunApp₃'

    def mkIsFunApp₄ : ClassExpr := ⟨mkHasFunctors'.mkIsFunApp₄ U.U Y y⟩

    namespace mkIsFunApp₄

      variable [hApp : mkIsFunApp₄ y]

      def mkApp : MetaM (mkHasFunctors'.FunApp U.U Y) :=
        mkHasFunctors'.mkIsFunApp₄.mkApp U.U Y y hApp.h

    end mkIsFunApp₄

    def mkIsFunApp₄' : ClassExpr := ⟨mkHasFunctors'.mkIsFunApp₄' U.U Y y⟩

    namespace mkIsFunApp₄'

      variable [hApp : mkIsFunApp₄' y]

      def mkH₄ : mkIsFunApp y :=  ⟨mkHasFunctors'.mkIsFunApp₄'.mkH₄ U.U Y y hApp.h⟩
      instance : mkIsFunApp₃' y := ⟨mkHasFunctors'.mkIsFunApp₄'.mkIsFunApp₃' U.U Y y hApp.h⟩

    end mkIsFunApp₄'

  end

end mkHasFunctors


def mkHasUnivFunctors' {u uu uv : Level} (U : Q(Universe.{u, uu})) (V : Q(Universe.{u, uv})) :=
  ⌜HasUnivFunctors $U $V⌝

namespace mkHasUnivFunctors'

  variable {u uu uv : Level} {U : Q(Universe.{u, uu})} {V : Q(Universe.{u, uv})}
           (h : mkHasUnivFunctors' U V)

  def toMkHasFunctors' (A : Q($U)) : mkHasFunctors' ⌜$A⌝ V := ⌜($h).hFun $A⌝

end mkHasUnivFunctors'

def mkHasUnivFunctors {u : Level} (U V : _Universe u) : ClassExpr := ⟨mkHasUnivFunctors' U.U V.U⟩

namespace mkHasUnivFunctors

  variable {u : Level} (U V : _Universe u) [h : mkHasUnivFunctors U V]

  instance toMkHasFunctors (A : U) : mkHasFunctors _⌈A⌉ V :=
    ⟨mkHasUnivFunctors'.toMkHasFunctors' h.h A⟩

  instance reflect : HasUnivFunctors U V := ⟨⟩

end mkHasUnivFunctors



structure PiData {v : Level} (V : _Universe v) where
  {α : _sort}
  {p : α → V}
  (P : [α ⥤ _[V]]_{p})
  [h : mkHasPiType P]
  (hFun? : Option (mkHasFunctors (_sort.mk (u := v) α.α) V))

namespace PiData

  def constructPi {α : _sort} {v : Level} {V : _Universe v} {p : α → V} (P : [α ⥤ _[V]]_{p})
                  [h : mkHasPiType P] : PiData V :=
    ⟨P, none⟩

  def constructFun (α : _sort) {U : _Universe α.u} [h : mkHasFunctors α U] (Y : U) : PiData U :=
    ⟨HasConstPi.defConstPi (α := α) _(Y), some h⟩

  def mkFreshMVar {v : Level} (V : _Universe v) : MetaM (PiData V) := do
    let α ← _sort.mkFreshMVar
    let P : α ⥤ _[V] ← _sort.mkFreshInstMVar
    let P' := defAppFun P
    let h : mkHasPiType P' ← InstanceExpr.mkFreshMVar
    pure ⟨P', none⟩

  variable {v : Level} {V : _Universe v}

  def instantiate (φ : PiData V) {v' : Level} (V' : _Universe v') : MetaM (PiData V') := do
    let α ← _sort.instantiate φ.α
    let P : α ⥤ _[V'] ← _sort.instantiateInstMVars φ.P
    let P' := defAppFun P
    let h : mkHasPiType P' ← φ.h.instantiate
    pure ⟨P', none⟩

  variable (φ : PiData V)

  instance : mkHasPiType φ.P := φ.h

  @[reducible] def mkPiRaw : V := Pi (mkHasPiType.reflectProp φ.P)

  @[reducible] def mkPi : V :=
    match φ.hFun? with
    | some hFun => (_sort.mk (u := v) φ.α.α) ⥤ φ.p default
    | none      => φ.mkPiRaw

  @[reducible] def mkSortPi : _sort := Pi (mkHasPiType.sortProp φ.P)

end PiData


structure PiApp {v : Level} {V : _Universe v} {Y : V} (y : Y) extends
    PiData V where
  F : toPiData.mkPi
  a : α

namespace PiApp

  open mkHasPiType mkHasFunctors

  variable {v : Level} {V : _Universe v} {Y : V} (y : Y)

  def constructPi {u : Level} (app : mkHasPiType'.PiApp V.U u) : MetaM (PiApp y) := do
    let α : _sort := ⟨app.α⟩
    let P : α ⥤ _[V] := app.P
    let P' := defAppFun P
    let h : mkHasPiType P' := ⟨app.hP⟩
    pure ⟨PiData.constructPi P', app.F, app.a⟩

  def constructFun (app : mkHasFunctors'.FunApp V.U Y) : MetaM (PiApp y) := do
    let α : _sort.mkSortType v := app.α
    let h : mkHasFunctors α V := ⟨app.hα⟩
    pure ⟨PiData.constructFun α Y, app.F, app.a⟩

  def getLiteralPiApp : MetaM (List (PiApp y)) := do
    let φ ← PiData.mkFreshMVar V
    let F : φ.mkPiRaw ← _Universe.mkFreshInstMVar
    let a : φ.α ← _sort.mkFreshInstMVar
    if ← isDefEq y (F a) then
      let φ ← φ.instantiate V
      let F : φ.mkPiRaw ← _Universe.instantiateInstMVars F
      let a : φ.α ← _sort.instantiateInstMVars a
      return [⟨φ, F, a⟩]
    pure []

  -- `y` and `y'` must be defeq.

  def synthesizePiApps'.piApp₂ {y' : Y} : MetaM (List (PiApp y')) := do
    let u ← mkFreshLevelMVar
    let u' ← mkFreshLevelMVar
    let hApp? : Option (mkHasPiType'.mkIsPiApp₂ V.U Y y u u') ← TypedExpr.synthesize?
    match hApp? with
    | some hApp =>
      let u ← instantiateLevelMVars u
      let u' ← instantiateLevelMVars u'
      let _ : mkIsPiApp₂ y u u' := ⟨← hApp.instantiate⟩
      pure [← constructPi y' (← mkIsPiApp₂.mkApp y u u')]
    | none => pure []

  def synthesizePiApps'.piApp {y' : Y} : MetaM (List (PiApp y')) := do
    let u ← mkFreshLevelMVar
    let hApp? : Option (mkHasPiType'.mkIsPiApp V.U Y y u) ← TypedExpr.synthesize?
    match hApp? with
    | some hApp =>
      let u ← instantiateLevelMVars u
      let _ : mkIsPiApp y u := ⟨← hApp.instantiate⟩
      pure [← constructPi y' (← mkIsPiApp.mkApp y u)]
    | none => synthesizePiApps'.piApp₂ y

  def synthesizePiApps'.funApp₄ {y' : Y} : MetaM (List (PiApp y')) := do
    let hApp? : Option (mkHasFunctors'.mkIsFunApp₄ V.U Y y) ← TypedExpr.synthesize?
    match hApp? with
    | some hApp =>
      let _ : mkIsFunApp₄ y := ⟨← hApp.instantiate⟩
      pure [← constructFun y' (← mkIsFunApp₄.mkApp y)]
    | none => pure []

  def synthesizePiApps'.funApp₃ {y' : Y} : MetaM (List (PiApp y')) := do
    let hApp? : Option (mkHasFunctors'.mkIsFunApp₃ V.U Y y) ← TypedExpr.synthesize?
    match hApp? with
    | some hApp =>
      let _ : mkIsFunApp₃ y := ⟨← hApp.instantiate⟩
      pure [← constructFun y' (← mkIsFunApp₃.mkApp y)]
    | none => synthesizePiApps'.funApp₄ y

  def synthesizePiApps'.funApp₂ {y' : Y} : MetaM (List (PiApp y')) := do
    let hApp? : Option (mkHasFunctors'.mkIsFunApp₂ V.U Y y) ← TypedExpr.synthesize?
    match hApp? with
    | some hApp =>
      let _ : mkIsFunApp₂ y := ⟨← hApp.instantiate⟩
      pure [← constructFun y' (← mkIsFunApp₂.mkApp y)]
    | none => synthesizePiApps'.funApp₃ y

  def synthesizePiApps'.funApp {y' : Y} : MetaM (List (PiApp y')) := do
    let hApp? : Option (mkHasFunctors'.mkIsFunApp V.U Y y) ← TypedExpr.synthesize?
    match hApp? with
    | some hApp =>
      let _ : mkIsFunApp y := ⟨← hApp.instantiate⟩
      pure [← constructFun y' (← mkIsFunApp.mkApp y)]
    | none => synthesizePiApps'.funApp₂ y

  def synthesizePiApps'.funApp₂' {y' : Y} : MetaM (List (PiApp y')) := do
    let hApp? : Option (mkHasFunctors'.mkIsFunApp₂' V.U Y y) ← TypedExpr.synthesize?
    match hApp? with
    | some hApp =>
      let _ : mkIsFunApp₂' y := ⟨← hApp.instantiate⟩
      pure [← constructFun y' (← mkIsFunApp.mkApp y),
            ← constructFun y' (← mkIsFunApp.mkApp y (hApp := mkIsFunApp₂'.mkH₂ y))]
    | none => synthesizePiApps'.funApp y

  def synthesizePiApps'.funApp₃' {y' : Y} : MetaM (List (PiApp y')) := do
    let hApp? : Option (mkHasFunctors'.mkIsFunApp₃' V.U Y y) ← TypedExpr.synthesize?
    match hApp? with
    | some hApp =>
      let _ : mkIsFunApp₃' y := ⟨← hApp.instantiate⟩
      pure [← constructFun y' (← mkIsFunApp.mkApp y),
            ← constructFun y' (← mkIsFunApp.mkApp y (hApp := mkIsFunApp₂'.mkH₂ y)),
            ← constructFun y' (← mkIsFunApp.mkApp y (hApp := mkIsFunApp₃'.mkH₃ y))]
    | none => synthesizePiApps'.funApp₂' y

  def synthesizePiApps'.funApp₄' {y' : Y} : MetaM (List (PiApp y')) := do
    let hApp? : Option (mkHasFunctors'.mkIsFunApp₄' V.U Y y) ← TypedExpr.synthesize?
    match hApp? with
    | some hApp =>
      let _ : mkIsFunApp₄' y := ⟨← hApp.instantiate⟩
      pure [← constructFun y' (← mkIsFunApp.mkApp y),
            ← constructFun y' (← mkIsFunApp.mkApp y (hApp := mkIsFunApp₂'.mkH₂ y)),
            ← constructFun y' (← mkIsFunApp.mkApp y (hApp := mkIsFunApp₃'.mkH₃ y)),
            ← constructFun y' (← mkIsFunApp.mkApp y (hApp := mkIsFunApp₄'.mkH₄ y))]
    | none => synthesizePiApps'.funApp₃' y

  def synthesizePiApps' {y' : Y} : MetaM (List (PiApp y')) := do
    let piApps: List (PiApp y') ← synthesizePiApps'.piApp y
    let funApps: List (PiApp y') ← synthesizePiApps'.funApp₄' y
    pure (funApps ++ piApps)

  def synthesizePiApps : MetaM (List (PiApp y)) := do
    -- First, check whether we can find an instance of `IsFunApp` and/or `IsPiApp`.
    match ← synthesizePiApps' y with
    | List.nil =>
      -- If none was found, unfold `y` once and try again, to support the use of definitions in
      -- `Λ` bodies.
      if let some (y' : Y) ← TypedExpr.unfold_def? y then
        match ← synthesizePiApps' y' with
        | List.nil => pure ()
        | result => return result
      -- Finally, check whether `y` is literally a functor application.
      -- This sees through some definitions that are opaque to type class synthesis.
      -- (We do not do this unconditionally because we want to return all alternatives if multiple
      -- exist.)
      getLiteralPiApp y
    | result => pure result

end PiApp



def mkHasIdFun' {u uu : Level} {U : Q(Universe.{u, uu})} (hUU : mkHasUnivFunctors' U U)
                (A : Q($U)) :=
  ⌜HasIdFun $A⌝

namespace mkHasIdFun'

  variable {u uu : Level} {U : Q(Universe.{u, uu})} {hUU : mkHasUnivFunctors' U U} {A : Q($U)}
           (h : mkHasIdFun' hUU A)

  def mkIdFun : Q($A ⥤ $A) := ⌜HasIdFun.idFun $A⌝

end mkHasIdFun'

def mkHasIdFun {u : Level} {U : _Universe u} [hUU : mkHasUnivFunctors U U] (A : U) : ClassExpr :=
  ⟨mkHasIdFun' (U := U.U) (A := A) hUU.h⟩

namespace mkHasIdFun

  variable {u : Level} {U : _Universe u} [hUU : mkHasUnivFunctors U U] (A : U) [h : mkHasIdFun A]

  def mkIdFun : A ⥤ A := mkHasIdFun'.mkIdFun h.h

  instance reflect : HasIdFun A := ⟨mkIdFun A⟩

end mkHasIdFun


def mkHasPiAppFun' {u v vv : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})}
                   (hV : mkHasUnivFunctors' V V) {P : Q($α → $V)} (hP : mkHasPiType' α V P) :=
  ⌜HasPiAppFun $P⌝

namespace mkHasPiAppFun'

  variable {u v vv : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})} {hV : mkHasUnivFunctors' V V}
           {P : Q($α → $V)} {hP : mkHasPiType' α V P} (h : mkHasPiAppFun' hV hP)

  def mkPiAppFun (a : Q($α)) : Q(Pi $P ⥤ $P $a) := ⌜HasPiAppFun.piAppFun $P $a⌝

end mkHasPiAppFun'

def mkHasPiAppFun {α : _sort} {v : Level} {V : _Universe v} [hV : mkHasUnivFunctors V V]
                  {p : α → V} (P : [α ⥤ _[V]]_{p}) [hP : mkHasPiType P] :
    ClassExpr :=
  ⟨mkHasPiAppFun' hV.h hP.h⟩

namespace mkHasPiAppFun

  variable {α : _sort} {v : Level} {V : _Universe v} [hV : mkHasUnivFunctors V V] {p : α → V}
           (P : [α ⥤ _[V]]_{p}) [hP : mkHasPiType P] [h : mkHasPiAppFun P]

  def mkPiAppFun (a : α) : Pi (mkHasPiType.reflectProp P) ⥤ p a :=
    mkHasPiAppFun'.mkPiAppFun h.h a

  instance reflect : HasPiAppFun (mkHasPiType.reflectProp P) := ⟨mkPiAppFun P⟩

end mkHasPiAppFun


def mkHasSwapPi' {u u' v vv : Level} {α : Q(Sort u)} {β : Q(Sort u')} {V : Q(Universe.{v, vv})}
                 {P : Q($α → $β → $V)} (hPa : mkHasIndepQuantPiType' α β V P)
                 (hPiPa : mkHasPiType' α V ⌜λ a => Pi ($P a)⌝)
                 (hPab : mkHasIndepQuantPiType' β α V ⌜λ b a => $P a b⌝) :=
  ⌜HasSwapPi $P⌝

namespace mkHasSwapPi'

  def prop {u u' v vv : Level} (α : Q(Sort u)) (β : Q(Sort u')) (V : Q(Universe.{v, vv}))
           (P : Q($α → $β → $V)) :
      Q($β → $α → $V) :=
    ⌜λ b a => $P a b⌝

  variable {u u' v vv : Level} {α : Q(Sort u)} {β : Q(Sort u')} {V : Q(Universe.{v, vv})}
           {P : Q($α → $β → $V)} {hPa : mkHasIndepQuantPiType' α β V P}
           {hPiPa : mkHasPiType' α V ⌜λ a => Pi ($P a)⌝}
           {hPab : mkHasIndepQuantPiType' β α V ⌜λ b a => $P a b⌝} (h : mkHasSwapPi' hPa hPiPa hPab)

  def mkSwapPi (F : Q(Pi₂ $P)) (b : Q($β)) : Q([∀ a, $P a $b | $V]) := ⌜HasSwapPi.swapPi $F $b⌝

end mkHasSwapPi'

def mkHasSwapPi.prop {α β : _sort} {v : Level} {V : _Universe v} {p : α → β → V}
                     (P : [α ⥤ β ⥤ _[V]]__{p}) [hPa : mkHasIndepQuantPiType P] :
    [β ⥤ α ⥤ _[V]]__{λ b a => p a b} :=
  mkHasSwapPi'.prop α.α β.α V.U P

def mkHasSwapPi {α β : _sort} {v : Level} {V : _Universe v} {p : α → β → V}
                (P : [α ⥤ β ⥤ _[V]]__{p}) [hPa : mkHasIndepQuantPiType P]
                [hPiPa : mkHasPiType (mkHasIndepQuantPiType.piProp P)]
                [hPab : mkHasIndepQuantPiType (mkHasSwapPi.prop P)] :
    ClassExpr :=
  ⟨mkHasSwapPi' hPa.h hPiPa.h hPab.h⟩

namespace mkHasSwapPi

  variable {α β : _sort} {v : Level} {V : _Universe v} {p : α → β → V} {P : [α ⥤ β ⥤ _[V]]__{p}}
           [hPa : mkHasIndepQuantPiType P]
           [hPiPa : mkHasPiType (mkHasIndepQuantPiType.piProp P)]
           [hPab : mkHasIndepQuantPiType (prop P)] [h : mkHasSwapPi P]

  instance (a : α) : HasType V (∀ b, (mkHasIndepQuantPiType.reflectProp P) a b) :=
    mkHasPiType.reflect (mkHasIndepQuantPiType.prop P a)

  instance : HasType V (∀ a, Pi ((mkHasIndepQuantPiType.reflectProp P) a)) :=
    mkHasPiType.reflect (mkHasIndepQuantPiType.piProp P)

  instance (b : β) : HasType V (∀ a, (mkHasIndepQuantPiType.reflectProp P) a b) :=
    mkHasPiType.reflect ((prop P) b)

  def mkSwapPi (F : Pi₂ (mkHasIndepQuantPiType.reflectProp P)) (b : β) :
      [∀ a, (mkHasIndepQuantPiType.reflectProp P) a b | V] :=
    mkHasSwapPi'.mkSwapPi h.h F b

  instance reflect : HasSwapPi (mkHasIndepQuantPiType.reflectProp P) := ⟨mkSwapPi⟩

end mkHasSwapPi


def mkHasCompFunPi' {u uv w ww : Level} {α : Q(Sort u)} {V : Q(Universe.{u, uv})}
                    (hαV : mkHasFunctors' α V) (B : Q($V)) {W : Q(Universe.{w, ww})}
                    (Q : Q($B → $W)) (hQ : mkHasPiType' ⌜$B⌝ W Q)
                    (hQFa : mkHasIndepQuantPiType' ⌜$α ⥤ $B⌝ α W ⌜λ F a => $Q (F a)⌝) :=
  ⌜HasCompFunPi $α $Q⌝

namespace mkHasCompFunPi'

  def prop {u uv w ww : Level} {α : Q(Sort u)} {V : Q(Universe.{u, uv})} (hαV : mkHasFunctors' α V)
           (B : Q($V)) (W : Q(Universe.{w, ww})) (Q : Q($B → $W)) :
      Q(($α ⥤ $B) → $α → $W) :=
    ⌜λ F a => $Q (F a)⌝

  variable {u uv w ww : Level} {α : Q(Sort u)} {V : Q(Universe.{u, uv})} {hαV : mkHasFunctors' α V}
           {B : Q($V)} {W : Q(Universe.{w, ww})} {Q : Q($B → $W)} {hQ : mkHasPiType' ⌜$B⌝ W Q}
           {hQFa : mkHasIndepQuantPiType' ⌜$α ⥤ $B⌝ α W ⌜λ F a => $Q (F a)⌝}
           (h : mkHasCompFunPi' hαV B Q hQ hQFa)

  def mkRevCompFunPi (G : Q(Pi $Q)) (F : Q($α ⥤ $B)) : Q([∀ a, $Q ($F a) | $W]) :=
    ⌜HasCompFunPi.revCompFunPi $G $F⌝

end mkHasCompFunPi'

def mkHasCompFunPi.prop (α : _sort) {V : _Universe α.u} [hαV : mkHasFunctors α V] {B : V}
                        {w : Level} {W : _Universe w} {q : B → W} (Q : [_⌈B⌉ ⥤ _[W]]_{q})
                        [hQ : mkHasPiType Q] :
    [_⌈α ⥤ B⌉ ⥤ α ⥤ _[W]]__{λ (F : α ⥤ B) a => q (F a)} :=
  mkHasCompFunPi'.prop hαV.h B W.U Q

def mkHasCompFunPi (α : _sort) {V : _Universe α.u} [hαV : mkHasFunctors α V] {B : V} {w : Level}
                   {W : _Universe w} {q : B → W} (Q : [_⌈B⌉ ⥤ _[W]]_{q})
                   [hQ : mkHasPiType Q] [hQFa : mkHasIndepQuantPiType (mkHasCompFunPi.prop α Q)] :
    ClassExpr :=
  ⟨mkHasCompFunPi' (W := W.U) hαV.h B Q hQ.h hQFa.h⟩

namespace mkHasCompFunPi

  variable {α : _sort} {V : _Universe α.u} [hαV : mkHasFunctors α V] {B : V} {w : Level}
           {W : _Universe w} {q : B → W} {Q : [_⌈B⌉ ⥤ _[W]]_{q}} [hQ : mkHasPiType Q]
           [hQFa : mkHasIndepQuantPiType (prop α Q)] [h : mkHasCompFunPi α Q]

  instance (F : α ⥤ B) : HasType W (∀ a, (mkHasPiType.reflectProp' Q) (F a)) :=
    mkHasPiType.reflect ((prop α Q) F)

  def mkRevCompFunPi (G : Pi (mkHasPiType.reflectProp' Q)) (F : α ⥤ B) :
      [∀ a, (mkHasPiType.reflectProp' Q) (F a) | W] :=
    mkHasCompFunPi'.mkRevCompFunPi h.h G F

  instance reflect : HasCompFunPi α (B := B) (mkHasPiType.reflectProp' Q) :=
    ⟨λ F G => mkRevCompFunPi G F⟩

end mkHasCompFunPi


def mkHasConstPi' {u v vv : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})} {B : Q($V)}
                  (hαB : mkHasPiType' α V ⌜λ _ => $B⌝) :=
  ⌜HasConstPi $α $B⌝

namespace mkHasConstPi'

  variable {u v vv : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})} {B : Q($V)}
           {hαB : mkHasPiType' α V ⌜λ _ => $B⌝} (h : mkHasConstPi' hαB)

  def mkConstPi (b : Q($B)) : Q([$α → $B | $V]) := ⌜HasConstPi.constPi $α $b⌝

end mkHasConstPi'

def mkHasConstPi (α : _sort) {v : Level} {V : _Universe v} (B : V)
                 [hαB : mkHasPiType (HasConstPi.defConstPi (α := α) _(B))] :
    ClassExpr :=
  ⟨mkHasConstPi' (α := α.α) (V := V.U) (B := B) hαB.h⟩

namespace mkHasConstPi

  variable (α : _sort) {v : Level} {V : _Universe v} {B : V}
           [hαB : mkHasPiType (HasConstPi.defConstPi (α := α) _(B))] [h : mkHasConstPi α B]

  def mkConstPi (b : B) : [α → B | V] := mkHasConstPi'.mkConstPi h.h b

  instance reflect : HasConstPi α B := ⟨mkConstPi α⟩

end mkHasConstPi


def mkHasDupPi' {u v vv : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})} (P : Q($α → $α → $V))
                (hPa : mkHasIndepQuantPiType' α α V P) (hPiPa : mkHasPiType' α V ⌜λ a => Pi ($P a)⌝)
                (hP : mkHasPiType' α V ⌜λ a => $P a a⌝) :=
  ⌜HasDupPi $P⌝

namespace mkHasDupPi'

  def prop {u v vv : Level} (α : Q(Sort u)) (V : Q(Universe.{v, vv})) (P : Q($α → $α → $V)) :
      Q($α → $V) :=
    ⌜λ a => $P a a⌝

  variable {u v vv : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})} {P : Q($α → $α → $V)}
           {hPa : mkHasIndepQuantPiType' α α V P} {hPiPa : mkHasPiType' α V ⌜λ a => Pi ($P a)⌝}
           {hP : mkHasPiType' α V ⌜λ a => $P a a⌝} (h : mkHasDupPi' P hPa hPiPa hP)

  def mkDupPi (F : Q(Pi₂ $P)) : Q([∀ a, $P a a | $V]) := ⌜HasDupPi.dupPi $F⌝

end mkHasDupPi'

def mkHasDupPi.prop {α : _sort} {v : Level} {V : _Universe v} {p : α → α → V}
                    (P : [α ⥤ α ⥤ _[V]]__{p}) [hPa : mkHasIndepQuantPiType P] :
    [α ⥤ _[V]]_{λ a => p a a} :=
  mkHasDupPi'.prop α.α V.U P

def mkHasDupPi {α : _sort} {v : Level} {V : _Universe v} {p : α → α → V} (P : [α ⥤ α ⥤ _[V]]__{p})
               [hPa : mkHasIndepQuantPiType P]
               [hPiPa : mkHasPiType (mkHasIndepQuantPiType.piProp P)]
               [hP : mkHasPiType (mkHasDupPi.prop P)] :
    ClassExpr :=
  ⟨mkHasDupPi' P hPa.h hPiPa.h hP.h⟩

namespace mkHasDupPi

  variable {α : _sort} {v : Level} {V : _Universe v} {p : α → α → V} {P : [α ⥤ α ⥤ _[V]]__{p}}
           [hPa : mkHasIndepQuantPiType P] [hPiPa : mkHasPiType (mkHasIndepQuantPiType.piProp P)]
           [hP : mkHasPiType (prop P)] [h : mkHasDupPi P]

  def mkDupPi (F : Pi₂ (mkHasIndepQuantPiType.reflectProp P)) :
      Pi (mkHasPiType.reflectProp (prop P)) :=
    mkHasDupPi'.mkDupPi h.h F

  instance reflect : HasDupPi (mkHasIndepQuantPiType.reflectProp P) := ⟨mkDupPi⟩

end mkHasDupPi


def mkHasPiSelfAppPi' {u uu uv : Level} {U : Q(Universe.{u, uu})} {V : Q(Universe.{u, uv})}
                      (hVU : mkHasUnivFunctors' V U) (A : Q($U)) (Q : Q($A → $V))
                      (hQ : mkHasPiType' (u := u) ⌜$A⌝ V Q)
                      (hQF : mkHasIndepQuantPiType' ⌜Pi $Q ⥤ $A⌝ ⌜Pi $Q⌝ V ⌜λ F G => $Q (F G)⌝) :=
  ⌜HasPiSelfAppPi $Q⌝

namespace mkHasPiSelfAppPi'

  def prop {u uu uv : Level} {U : Q(Universe.{u, uu})} {V : Q(Universe.{u, uv})}
           (hVU : mkHasUnivFunctors' V U) (A : Q($U)) (Q : Q($A → $V))
           (hQ : mkHasPiType' (u := u) ⌜$A⌝ V Q) :
      Q((Pi $Q ⥤ $A) → Pi $Q → $V) :=
    ⌜λ F G => $Q (F G)⌝

  variable {u uu uv : Level} {U : Q(Universe.{u, uu})} {V : Q(Universe.{u, uv})}
           {hVU : mkHasUnivFunctors' V U} {A : Q($U)} {Q : Q($A → $V)}
           {hQ : mkHasPiType' (u := u) ⌜$A⌝ V Q}
           {hQF : mkHasIndepQuantPiType' ⌜Pi $Q ⥤ $A⌝ ⌜Pi $Q⌝ V ⌜λ F G => $Q (F G)⌝}
           (h : mkHasPiSelfAppPi' hVU A Q hQ hQF)

  def mkPiSelfAppPi (F : Q(Pi $Q ⥤ $A)) : Q([∀ G, $Q ($F G) | $V]) :=
    ⌜HasPiSelfAppPi.piSelfAppPi $F⌝

end mkHasPiSelfAppPi'

def mkHasPiSelfAppPi.prop {u : Level} {U V : _Universe u} [hVU : mkHasUnivFunctors V U] {A : U}
                          {q : A → V} (Q : [_⌈A⌉ ⥤ _[V]]_{q}) [hQ : mkHasPiType Q] :
    [_⌈Pi (mkHasPiType.reflectProp Q) ⥤ A⌉ ⥤ _⌈Pi (mkHasPiType.reflectProp Q)⌉ ⥤ _[V]]__{
     λ (F : Pi (mkHasPiType.reflectProp Q) ⥤ A) (G : Pi (mkHasPiType.reflectProp Q)) => q (F G)} :=
  mkHasPiSelfAppPi'.prop hVU.h A Q hQ.h

def mkHasPiSelfAppPi {u : Level} {U V : _Universe u} [hVU : mkHasUnivFunctors V U] {A : U}
                     {q : A → V} (Q : [_⌈A⌉ ⥤ _[V]]_{q}) [hQ : mkHasPiType Q]
                     [hQF : mkHasIndepQuantPiType (mkHasPiSelfAppPi.prop Q)] :
    ClassExpr :=
  ⟨mkHasPiSelfAppPi' hVU.h A Q hQ.h hQF.h⟩

namespace mkHasPiSelfAppPi

  variable {u : Level} {U V : _Universe u} [hVU : mkHasUnivFunctors V U] {A : U} {q : A → V}
           {Q : [_⌈A⌉ ⥤ _[V]]_{q}} [hQ : mkHasPiType Q]
           [hQF : mkHasIndepQuantPiType (mkHasPiSelfAppPi.prop Q)] [h : mkHasPiSelfAppPi Q]

  instance (F : Pi (mkHasPiType.reflectProp' Q) ⥤ A) :
      HasType V (∀ G, (mkHasPiType.reflectProp' Q) (F G)) :=
    mkHasPiType.reflect' ((prop Q) F)

  def mkPiSelfAppPi (F : Pi (mkHasPiType.reflectProp' Q) ⥤ A) :
      [∀ G, (mkHasPiType.reflectProp' Q) (F G) | V] :=
    mkHasPiSelfAppPi'.mkPiSelfAppPi h.h F

  instance reflect : HasPiSelfAppPi (mkHasPiType.reflectProp' Q) := ⟨mkPiSelfAppPi⟩

end mkHasPiSelfAppPi


def mkHasSubstPi' {u v vv w ww : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})}
                  {P : Q($α → $V)} (hP : mkHasPiType' α V P) (W : Q(Universe.{w, ww}))
                  (Q : Q(∀ a, $P a → $W)) (hQa : mkHasUnivQuantPiType' α V P W Q)
                  (hPiQa : mkHasPiType' α W ⌜λ a => Pi ($Q a)⌝)
                  (hQaFa : mkHasIndepQuantPiType' ⌜Pi $P⌝ α W ⌜λ F a => $Q a (F a)⌝) :=
  ⌜HasSubstPi $Q⌝

namespace mkHasSubstPi'

  def prop {u v vv w ww : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})} {P : Q($α → $V)}
           (hP : mkHasPiType' α V P) (W : Q(Universe.{w, ww})) (Q : Q(∀ a, $P a → $W)) :
      Q((Pi $P) → $α → $W) :=
    ⌜λ F a => $Q a (F a)⌝

  variable {u v vv w ww : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})}
           {P : Q($α → $V)} {hP : mkHasPiType' α V P} {W : Q(Universe.{w, ww})}
           {Q : Q(∀ a, $P a → $W)} {hQa : mkHasUnivQuantPiType' α V P W Q}
           {hPiQa : mkHasPiType' α W ⌜λ a => Pi ($Q a)⌝}
           {hQaFa : mkHasIndepQuantPiType' ⌜Pi $P⌝ α W ⌜λ F a => $Q a (F a)⌝}
           (h : mkHasSubstPi' hP W Q hQa hPiQa hQaFa)

  def mkRevSubstPi (G : Q([∀ a, Pi ($Q a) | $W])) (F : Q(Pi $P)) : Q([∀ a, $Q a ($F a) | $W]) :=
    ⌜HasSubstPi.revSubstPi $G $F⌝

end mkHasSubstPi'

def mkHasSubstPi.prop {α : _sort} {v w : Level} {V : _Universe v} {p : α → V} {P : [α ⥤ _[V]]_{p}}
                      [hP : mkHasPiType P] {W : _Universe w} {q : ∀ a, p a → W}
                      {Q' : ∀ a, [_⌈p a⌉ ⥤ _[W]]_{q a}}
                      (Q : [∀ a, (mkHasUnivQuantPiType.metaProp P W) a | _sort]_{Q'})
                      [hQ : mkHasUnivQuantPiType Q] :
    [_⌈Pi (mkHasPiType.reflectProp P)⌉ ⥤ α ⥤ _[W]]__{
     λ (F : Pi (mkHasPiType.reflectProp P)) a => q a (F a)} :=
  mkHasSubstPi'.prop hP.h W.U Q

def mkHasSubstPi {α : _sort} {v w : Level} {V : _Universe v} {p : α → V} {P : [α ⥤ _[V]]_{p}}
                 [hP : mkHasPiType P] {W : _Universe w} {q : ∀ a, p a → W}
                 {Q' : ∀ a, [_⌈p a⌉ ⥤ _[W]]_{q a}}
                 (Q : [∀ a, (mkHasUnivQuantPiType.metaProp P W) a | _sort]_{Q'})
                 [hQa : mkHasUnivQuantPiType Q]
                 [hPiQa : mkHasPiType (mkHasUnivQuantPiType.piProp Q)]
                 [hQaFa : mkHasIndepQuantPiType (mkHasSubstPi.prop Q)] :
    ClassExpr :=
  ⟨mkHasSubstPi' hP.h W.U Q hQa.h hPiQa.h hQaFa.h⟩

namespace mkHasSubstPi

  variable {α : _sort} {v w : Level} {V : _Universe v} {p : α → V} {P : [α ⥤ _[V]]_{p}}
           [hP : mkHasPiType P] {W : _Universe w} {q : ∀ a, p a → W}
           {Q' : ∀ a, [_⌈p a⌉ ⥤ _[W]]_{q a}}
           {Q : [∀ a, (mkHasUnivQuantPiType.metaProp P W) a | _sort]_{Q'}}
           [hQa : mkHasUnivQuantPiType Q] [hPiQa : mkHasPiType (mkHasUnivQuantPiType.piProp Q)]
           [hQaFa : mkHasIndepQuantPiType (mkHasSubstPi.prop Q)] [h : mkHasSubstPi Q]

  instance (F : Pi (mkHasPiType.reflectProp P)) :
      HasType W (∀ a, (mkHasUnivQuantPiType.reflectProp Q) a (F a)) :=
    mkHasPiType.reflect ((prop Q) F)

  def mkRevSubstPi (G : Pi (mkHasPiType.reflectProp (mkHasUnivQuantPiType.piProp Q)))
                   (F : Pi (mkHasPiType.reflectProp P)) :
      [∀ a, (mkHasUnivQuantPiType.reflectProp Q) a (F a) | W] :=
    mkHasSubstPi'.mkRevSubstPi h.h G F

  instance reflect : HasSubstPi (mkHasUnivQuantPiType.reflectProp Q) := ⟨λ F G => mkRevSubstPi G F⟩

end mkHasSubstPi



def mkHasLinearLogic' {u uu : Level} (U : Q(Universe.{u, uu})) := ⌜HasLinearLogic $U⌝

namespace mkHasLinearLogic'

  variable {u uu : Level} {U : Q(Universe.{u, uu})} (h : mkHasLinearLogic' U)

  def toMkHasUnivFunctors' : mkHasUnivFunctors' U U := ⌜($h).toHasUnivFunctors⌝

  def mkIdFun (A : Q($U)) : Q($A ⥤ $A) := ⌜HasLinearLogic.idFun $A⌝

end mkHasLinearLogic'

def mkHasExternalLinearLogic' {u uu : Level} (α : Q(Sort u)) {U : Q(Universe.{u, uu})}
                              (hUU : mkHasUnivFunctors' U U) :=
  ⌜HasExternalLinearLogic $α $U⌝

namespace mkHasExternalLinearLogic'

  section

    variable {u uu : Level} {α : Q(Sort u)} {U : Q(Universe.{u, uu})} {hUU : mkHasUnivFunctors' U U}
             (h : mkHasExternalLinearLogic' α hUU)

    def toMkHasFunctors' : mkHasFunctors' α U := ⌜($h).toHasFunctors⌝

    def mkRevAppFun (a : Q($α)) (B : Q($U)) : Q(($α ⥤ $B) ⥤ $B) :=
      ⌜HasExternalLinearLogic.revAppFun $a $B⌝

    def mkRevAppFun₂ (B : Q($U)) : Q($α ⥤ ($α ⥤ $B) ⥤ $B) :=
      ⌜HasExternalLinearLogic.revAppFun₂ $α $B⌝

    def mkRevCompFun (B C : Q($U)) (G : Q($B ⥤ $C)) (F : Q($α ⥤ $B)) : Q($α ⥤ $C) :=
      ⌜HasExternalLinearLogic.revCompFun $G $F⌝

    def mkRevCompFun₃ (B C : Q($U)) : Q(($B ⥤ $C) ⥤ ($α ⥤ $B) ⥤ ($α ⥤ $C)) :=
      ⌜HasExternalLinearLogic.revCompFun₃ $α $B $C⌝

  end

  section

    variable {u uu : Level} {α β : Q(Sort u)} {U : Q(Universe.{u, uu})}
             {hU : mkHasLinearLogic' U}
             (hα : mkHasExternalLinearLogic' α (mkHasLinearLogic'.toMkHasUnivFunctors' hU))
             (hβ : mkHasExternalLinearLogic' β (mkHasLinearLogic'.toMkHasUnivFunctors' hU))

    def mkSwapFun (C : Q($U)) (F : Q($α ⥤ $β ⥤ $C)) (b : Q($β)) : Q($α ⥤ $C) :=
      ⌜HasExternalLinearLogic.swapFun $F $b⌝

  end

end mkHasExternalLinearLogic'

namespace mkHasLinearLogic'

  variable {u uu : Level} {U : Q(Universe.{u, uu})} (h : mkHasLinearLogic' U)

  def toMkHasExternalLinearLogic' (A : Q($U)) :
      mkHasExternalLinearLogic' ⌜$A⌝ (toMkHasUnivFunctors' h) :=
    ⌜($h).hasExternalLinearLogic $A⌝

end mkHasLinearLogic'

def mkHasLinearLogic {u : Level} (U : _Universe u) : ClassExpr := ⟨mkHasLinearLogic' U.U⟩

namespace mkHasLinearLogic

  instance toMkHasUnivFunctors {u : Level} (U : _Universe u) [h : mkHasLinearLogic U] :
      mkHasUnivFunctors U U :=
    ⟨mkHasLinearLogic'.toMkHasUnivFunctors' h.h⟩

end mkHasLinearLogic

def mkHasExternalLinearLogic (α : _sort) (U : _Universe α.u) [hUU : mkHasUnivFunctors U U] :
    ClassExpr :=
  ⟨mkHasExternalLinearLogic' α.α hUU.h⟩

namespace mkHasExternalLinearLogic

  instance toMkHasFunctors (α : _sort) (U : _Universe α.u) [hUU : mkHasUnivFunctors U U]
                           [h : mkHasExternalLinearLogic α U] :
      mkHasFunctors α U :=
    ⟨mkHasExternalLinearLogic'.toMkHasFunctors' h.h⟩

  section

    variable {α : _sort} {U : _Universe α.u} [hUU : mkHasUnivFunctors U U]
             [h : mkHasExternalLinearLogic α U]

    def mkRevAppFun (a : α) (B : U) : (α ⥤ B) ⥤ B := mkHasExternalLinearLogic'.mkRevAppFun h.h a B

    def mkRevCompFun {B C : U} (G : B ⥤ C) (F : α ⥤ B) : α ⥤ C :=
      mkHasExternalLinearLogic'.mkRevCompFun h.h B C G F

  end

  section

    variable (α : _sort) {U : _Universe α.u} [hUU : mkHasUnivFunctors U U]
             [h : mkHasExternalLinearLogic α U]

    def mkRevAppFun₂ (B : U) : α ⥤ (α ⥤ B) ⥤ B := mkHasExternalLinearLogic'.mkRevAppFun₂ h.h B

    def mkRevCompFun₃ (B C : U) : (B ⥤ C) ⥤ (α ⥤ B) ⥤ (α ⥤ C) :=
      mkHasExternalLinearLogic'.mkRevCompFun₃ h.h B C

    instance reflect : HasExternalLinearLogic α U where
      defRevAppFun₂  := mkRevAppFun₂  α
      defRevCompFun₃ := mkRevCompFun₃ α

  end

  section

    variable {u : Level} {α β : _sort.mkSortType u} {U : _Universe u} [mkHasLinearLogic U]
             [hα : mkHasExternalLinearLogic α U] [hβ : mkHasExternalLinearLogic β U]

    def mkSwapFun {C : U} (F : α ⥤ β ⥤ C) (b : β) : α ⥤ C :=
      mkHasExternalLinearLogic'.mkSwapFun hα.h hβ.h C F b

  end

end mkHasExternalLinearLogic

namespace mkHasLinearLogic

  section

    variable {u : Level} {U : _Universe u} [h : mkHasLinearLogic U]

    instance toMkHasExternalLinearLogic (A : U) : mkHasExternalLinearLogic _⌈A⌉ U :=
      ⟨mkHasLinearLogic'.toMkHasExternalLinearLogic' h.h A⟩

    def mkIdFun (A : U) : A ⥤ A := mkHasLinearLogic'.mkIdFun h.h A

    def mkRevAppFun₂ (A B : U) : A ⥤ (A ⥤ B) ⥤ B :=
      mkHasExternalLinearLogic'.mkRevAppFun₂ (mkHasLinearLogic'.toMkHasExternalLinearLogic' h.h A) B

    def mkRevCompFun₃ (A B C : U) : (B ⥤ C) ⥤ (A ⥤ B) ⥤ (A ⥤ C) :=
      mkHasExternalLinearLogic'.mkRevCompFun₃ (mkHasLinearLogic'.toMkHasExternalLinearLogic' h.h A)
                                              B C

  end

  instance reflect {u : Level} (U : _Universe u) [mkHasLinearLogic U] : HasLinearLogic U where
    defIdFun       := mkIdFun
    defRevAppFun₂  := mkRevAppFun₂
    defRevCompFun₃ := mkRevCompFun₃

end mkHasLinearLogic


def mkHasExternalSubLinearLogic' {u uu : Level} (α : Q(Sort u)) {U : Q(Universe.{u, uu})}
                                 (hUU : mkHasUnivFunctors' U U) (hαU : mkHasFunctors' α U) :=
  ⌜HasExternalSubLinearLogic $α $U⌝

namespace mkHasExternalSubLinearLogic'

  variable {u uu : Level} {α : Q(Sort u)} {U : Q(Universe.{u, uu})} {hUU : mkHasUnivFunctors' U U}
           {hαU : mkHasFunctors' α U} (h : mkHasExternalSubLinearLogic' α hUU hαU)

  def mkConstFun (B : Q($U)) (b : Q($B)) : Q($α ⥤ $B) := ⌜HasExternalSubLinearLogic.constFun $α $b⌝

  def mkConstFun₂ (B : Q($U)) : Q($B ⥤ ($α ⥤ $B)) := ⌜HasExternalSubLinearLogic.constFun₂ $α $B⌝

end mkHasExternalSubLinearLogic'

def mkHasSubLinearLogic' {u uu : Level} {U : Q(Universe.{u, uu})} (hUU : mkHasUnivFunctors' U U) :=
  ⌜HasSubLinearLogic $U⌝

namespace mkHasSubLinearLogic'

  variable {u uu : Level} {U : Q(Universe.{u, uu})} {hU : mkHasLinearLogic' U}
           (h : mkHasSubLinearLogic' (mkHasLinearLogic'.toMkHasUnivFunctors' hU))

  def toMkHasExternalSubLinearLogic' (A : Q($U)) :
      mkHasExternalSubLinearLogic' ⌜$A⌝ (mkHasLinearLogic'.toMkHasUnivFunctors' hU)
        (mkHasUnivFunctors'.toMkHasFunctors' (mkHasLinearLogic'.toMkHasUnivFunctors' hU) A) :=
    ⌜($h).hasExternalSubLinearLogic $A⌝

end mkHasSubLinearLogic'

def mkHasExternalSubLinearLogic (α : _sort) (U : _Universe α.u) [hUU : mkHasUnivFunctors U U]
                                [hαU : mkHasFunctors α U] :
    ClassExpr :=
  ⟨mkHasExternalSubLinearLogic' α.α hUU.h hαU.h⟩

namespace mkHasExternalSubLinearLogic

  variable (α : _sort) {U : _Universe α.u} [hUU : mkHasUnivFunctors U U] [hαU : mkHasFunctors α U]
           [h : mkHasExternalSubLinearLogic α U]

  def mkConstFun {B : U} (b : B) : α ⥤ B := mkHasExternalSubLinearLogic'.mkConstFun h.h B b

  def mkConstFun₂ (B : U) : B ⥤ (α ⥤ B) := mkHasExternalSubLinearLogic'.mkConstFun₂ h.h B

  instance reflect : HasExternalSubLinearLogic α U where
    defConstFun₂ := mkConstFun₂ α

end mkHasExternalSubLinearLogic

def mkHasSubLinearLogic {u : Level} (U : _Universe u) [hUU : mkHasUnivFunctors U U] : ClassExpr :=
  ⟨mkHasSubLinearLogic' hUU.h⟩

namespace mkHasSubLinearLogic

  section

    variable {u : Level} {U : _Universe u} [mkHasLinearLogic U] [h : mkHasSubLinearLogic U]

    instance toMkHasExternalSubLinearLogic (A : U) : mkHasExternalSubLinearLogic _⌈A⌉ U :=
      ⟨mkHasSubLinearLogic'.toMkHasExternalSubLinearLogic' h.h A⟩

    def mkConstFun₂ (A B : U) : B ⥤ (A ⥤ B) :=
      mkHasExternalSubLinearLogic'.mkConstFun₂
        (mkHasSubLinearLogic'.toMkHasExternalSubLinearLogic' h.h A) B

  end

  instance reflect {u : Level} (U : _Universe u) [mkHasLinearLogic U] [mkHasSubLinearLogic U] :
      HasSubLinearLogic U where
    defConstFun₂ := mkConstFun₂

end mkHasSubLinearLogic


def mkHasExternalNonLinearLogic' {u uu : Level} (α : Q(Sort u)) {U : Q(Universe.{u, uu})}
                                 (hUU : mkHasUnivFunctors' U U) (hαU : mkHasFunctors' α U) :=
  ⌜HasExternalNonLinearLogic $α $U⌝

namespace mkHasExternalNonLinearLogic'

  section

    variable {u uu : Level} {α : Q(Sort u)} {U : Q(Universe.{u, uu})} {hUU : mkHasUnivFunctors' U U}
             {hαU : mkHasFunctors' α U} (h : mkHasExternalNonLinearLogic' α hUU hαU)

    def mkDupFun (B : Q($U)) (F : Q($α ⥤ $α ⥤ $B)) : Q($α ⥤ $B) :=
      ⌜HasExternalNonLinearLogic.dupFun $F⌝

    def mkDupFun₂ (B : Q($U)) : Q(($α ⥤ $α ⥤ $B) ⥤ ($α ⥤ $B)) :=
      ⌜HasExternalNonLinearLogic.dupFun₂ $α $B⌝

  end

  section

    variable {u uu : Level} {α : Q(Sort u)} {U : Q(Universe.{u, uu})} {hU : mkHasLinearLogic' U}
             {hαU : mkHasExternalLinearLogic' α (mkHasLinearLogic'.toMkHasUnivFunctors' hU)}
             (h : mkHasExternalNonLinearLogic' α (mkHasLinearLogic'.toMkHasUnivFunctors' hU)
                                               (mkHasExternalLinearLogic'.toMkHasFunctors' hαU))

    def mkRevSubstFun (B C : Q($U)) (G : Q($α ⥤ $B ⥤ $C)) (F : Q($α ⥤ $B)) : Q($α ⥤ $C) :=
      ⌜HasExternalNonLinearLogic.revSubstFun $G $F⌝

  end

end mkHasExternalNonLinearLogic'

def mkHasNonLinearLogic' {u uu : Level} {U : Q(Universe.{u, uu})} (hUU : mkHasUnivFunctors' U U) :=
  ⌜HasNonLinearLogic $U⌝

namespace mkHasNonLinearLogic'

  variable {u uu : Level} {U : Q(Universe.{u, uu})} {hU : mkHasLinearLogic' U}
           (h : mkHasNonLinearLogic' (mkHasLinearLogic'.toMkHasUnivFunctors' hU))

  def toMkHasExternalNonLinearLogic' (A : Q($U)) :
      mkHasExternalNonLinearLogic' ⌜$A⌝ (mkHasLinearLogic'.toMkHasUnivFunctors' hU)
        (mkHasUnivFunctors'.toMkHasFunctors' (mkHasLinearLogic'.toMkHasUnivFunctors' hU) A) :=
    ⌜($h).hasExternalNonLinearLogic $A⌝

  def mkRevSelfAppFun (A B : Q($U)) (F : Q(($A ⥤ $B) ⥤ $A)) : Q(($A ⥤ $B) ⥤ $B) :=
    ⌜HasNonLinearLogic.revSelfAppFun $F⌝

end mkHasNonLinearLogic'

def mkHasExternalNonLinearLogic (α : _sort) (U : _Universe α.u) [hUU : mkHasUnivFunctors U U]
                                [hαU : mkHasFunctors α U] :
    ClassExpr :=
  ⟨mkHasExternalNonLinearLogic' α.α hUU.h hαU.h⟩

namespace mkHasExternalNonLinearLogic

  section

    variable {α : _sort} {U : _Universe α.u} [hUU : mkHasUnivFunctors U U] [hαU : mkHasFunctors α U]
             [h : mkHasExternalNonLinearLogic α U]

    def mkDupFun {B : U} (F : α ⥤ α ⥤ B) : α ⥤ B := mkHasExternalNonLinearLogic'.mkDupFun h.h B F

  end

  section

    variable (α : _sort) {U : _Universe α.u} [hUU : mkHasUnivFunctors U U] [hαU : mkHasFunctors α U]
             [h : mkHasExternalNonLinearLogic α U]

    def mkDupFun₂ (B : U) : (α ⥤ α ⥤ B) ⥤ (α ⥤ B) := mkHasExternalNonLinearLogic'.mkDupFun₂ h.h B

    instance reflect : HasExternalNonLinearLogic α U where
      defDupFun₂ := mkDupFun₂ α

  end

  section

    variable {α : _sort} {U : _Universe α.u} [mkHasLinearLogic U]
             [hαU : mkHasExternalLinearLogic α U] [h : mkHasExternalNonLinearLogic α U]

    def mkRevSubstFun {B C : U} (G : α ⥤ B ⥤ C) (F : α ⥤ B) : α ⥤ C :=
      mkHasExternalNonLinearLogic'.mkRevSubstFun h.h B C G F

  end

end mkHasExternalNonLinearLogic

def mkHasNonLinearLogic {u : Level} (U : _Universe u) [hUU : mkHasUnivFunctors U U] : ClassExpr :=
  ⟨mkHasNonLinearLogic' hUU.h⟩

namespace mkHasNonLinearLogic

  section

    variable {u : Level} {U : _Universe u} [mkHasLinearLogic U] [h : mkHasNonLinearLogic U]

    instance toMkHasExternalNonLinearLogic (A : U) : mkHasExternalNonLinearLogic _⌈A⌉ U :=
      ⟨mkHasNonLinearLogic'.toMkHasExternalNonLinearLogic' h.h A⟩

    def mkDupFun₂ (A B : U) : (A ⥤ A ⥤ B) ⥤ (A ⥤ B) :=
      mkHasExternalNonLinearLogic'.mkDupFun₂ (mkHasNonLinearLogic'.toMkHasExternalNonLinearLogic' h.h A) B

    def mkRevSelfAppFun {A B : U} (F : (A ⥤ B) ⥤ A) : (A ⥤ B) ⥤ B :=
      mkHasNonLinearLogic'.mkRevSelfAppFun h.h A B F

  end

  instance reflect {u : Level} (U : _Universe u) [mkHasLinearLogic U] [mkHasNonLinearLogic U] :
      HasNonLinearLogic U where
    defDupFun₂ := mkDupFun₂

end mkHasNonLinearLogic
