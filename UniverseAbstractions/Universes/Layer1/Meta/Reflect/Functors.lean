import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedFunctors
import UniverseAbstractions.Universes.Layer1.Meta.Reflect.Universes



namespace UniverseAbstractions.Layer1.Meta

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 10000
set_option linter.unusedVariables false

open Lean Lean.Meta Qq UniverseAbstractions.Meta
     HasPiType HasFunctors



def mkHasPiType' {u v vv : Level} (α : Q(Sort u)) (V : Q(Universe.{v, vv})) (P : Q($α → $V)) :=
  ⌜HasPiType $P⌝

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

    def mkDefPi (f : Q(∀ a, $P a)) := ⌜DefPi $P $f⌝

    namespace mkDefPi

      variable (f : Q(∀ a, $P a))

      def mkMk (F : Q(Pi $P)) : mkDefPi h f := ⌜DefPi.mk (f := $f) $F⌝

      variable (F : mkDefPi h f)

      def mkInst : Q(Pi $P) := ⌜($F).inst⌝

    end mkDefPi

  end

  section

    variable {v vv : Level} (V : Q(Universe.{v, vv}))

    structure PiApp (u : Level) where
      α  : Q(Sort u)
      P  : Q($α → $V)
      hP : Q(HasPiType $P)
      F  : Q(Pi $P)
      a  : Q($α)

    variable (Y : Q($V)) (y : Q($Y))

    def mkIsPiApp (u : Level) := ⌜IsPiApp.{u} $y⌝

    namespace mkIsPiApp

      variable {u : Level} (hApp : mkIsPiApp V Y y u)

      def mkApp : MetaM (PiApp V u) := do
        let α  : Q(Sort u)       ← unfoldOnce ⌜($hApp).α⌝
        let P  : Q($α → $V)      ← unfoldOnce ⌜($hApp).P⌝
        let hP : Q(HasPiType $P) ← unfoldOnce ⌜($hApp).hP⌝
        let F  : Q(Pi $P)        ← unfoldOnce ⌜($hApp).F⌝
        let a  : Q($α)           ← unfoldOnce ⌜($hApp).a⌝
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
        let α     : Q(Sort u)                       ← unfoldOnce ⌜($hApp).α⌝
        let β     : Q(Sort u')                      ← unfoldOnce ⌜($hApp).β⌝
        let P     : Q($α → $β → $V)                 ← unfoldOnce ⌜($hApp).P⌝
        let hPa   : Q(∀ a, HasPiType ($P a))        ← unfoldOnce ⌜($hApp).hPa⌝
        let hPiPa : Q(HasPiType (λ a => Pi ($P a))) ← unfoldOnce ⌜($hApp).hPiPa⌝
        let F     : Q(Pi₂ $P)                       ← unfoldOnce ⌜($hApp).F⌝
        let a     : Q($α)                           ← unfoldOnce ⌜($hApp).a⌝
        let b     : Q($β)                           ← unfoldOnce ⌜($hApp).b⌝
        pure { α  := β,
               P  := ⌜$P   $a⌝,
               hP := ⌜$hPa $a⌝,
               F  := ⌜$F   $a⌝,
               a  := b }

    end mkIsPiApp₂

    def mkIsPiApp₂' (u u' : Level) := ⌜IsPiApp₂'.{u, u'} $y⌝

    namespace mkIsPiApp₂'

      variable {u u' : Level} (hApp : mkIsPiApp₂' V Y y u u')
    
      def mkH₂ : mkIsPiApp V Y y u' := ⌜($hApp).h₂⌝
      def mkIsPiApp : mkIsPiApp V Y y u := ⌜($hApp).toIsPiApp⌝

    end mkIsPiApp₂'

    def mkIsPiApp₃ (u u' u'' : Level) := ⌜IsPiApp₃.{u, u', u''} $y⌝

    namespace mkIsPiApp₃

      variable {u u' u'' : Level} (hApp : mkIsPiApp₃ V Y y u u' u'')

      def mkApp : MetaM (PiApp V u'') := do
        let α      : Q(Sort u)                              ← unfoldOnce ⌜($hApp).α⌝
        let β      : Q(Sort u')                             ← unfoldOnce ⌜($hApp).β⌝
        let γ      : Q(Sort u'')                            ← unfoldOnce ⌜($hApp).γ⌝
        let P      : Q($α → $β → $γ → $V)                   ← unfoldOnce ⌜($hApp).P⌝
        let hPab   : Q(∀ a b, HasPiType ($P a b))           ← unfoldOnce ⌜($hApp).hPab⌝
        let hPiPab : Q(∀ a, HasPiType (λ b => Pi ($P a b))) ← unfoldOnce ⌜($hApp).hPiPab⌝
        let hPiPa  : Q(HasPiType (λ a => Pi₂ ($P a)))       ← unfoldOnce ⌜($hApp).hPiPa⌝
        let F      : Q(Pi₃ $P)                              ← unfoldOnce ⌜($hApp).F⌝
        let a      : Q($α)                                  ← unfoldOnce ⌜($hApp).a⌝
        let b      : Q($β)                                  ← unfoldOnce ⌜($hApp).b⌝
        let c      : Q($γ)                                  ← unfoldOnce ⌜($hApp).c⌝
        pure { α  := γ,
               P  := ⌜$P    $a $b⌝,
               hP := ⌜$hPab $a $b⌝,
               F  := ⌜$F    $a $b⌝,
               a  := c }

    end mkIsPiApp₃

    def mkIsPiApp₃' (u u' u'' : Level) := ⌜IsPiApp₃'.{u, u', u''} $y⌝

    namespace mkIsPiApp₃'

      variable {u u' u'' : Level} (hApp : mkIsPiApp₃' V Y y u u' u'')
    
      def mkH₃ : mkIsPiApp V Y y u'' := ⌜($hApp).h₃⌝
      def mkIsPiApp₂' : mkIsPiApp₂' V Y y u u' := ⌜($hApp).toIsPiApp₂'⌝

    end mkIsPiApp₃'

    def mkIsPiApp₄ (u u' u'' u''' : Level) := ⌜IsPiApp₄.{u, u', u'', u'''} $y⌝

    namespace mkIsPiApp₄

      variable {u u' u'' u''' : Level} (hApp : mkIsPiApp₄ V Y y u u' u'' u''')

      def mkApp : MetaM (PiApp V u''') := do
        let α       : Q(Sort u)                                  ← unfoldOnce ⌜($hApp).α⌝
        let β       : Q(Sort u')                                 ← unfoldOnce ⌜($hApp).β⌝
        let γ       : Q(Sort u'')                                ← unfoldOnce ⌜($hApp).γ⌝
        let δ       : Q(Sort u''')                               ← unfoldOnce ⌜($hApp).δ⌝
        let P       : Q($α → $β → $γ → $δ → $V)                  ← unfoldOnce ⌜($hApp).P⌝
        let hPabc   : Q(∀ a b c, HasPiType ($P a b c))           ← unfoldOnce ⌜($hApp).hPabc⌝
        let hPiPabc : Q(∀ a b, HasPiType (λ c => Pi ($P a b c))) ← unfoldOnce ⌜($hApp).hPiPabc⌝
        let hPiPab  : Q(∀ a, HasPiType (λ b => Pi₂ ($P a b)))    ← unfoldOnce ⌜($hApp).hPiPab⌝
        let hPiPa   : Q(HasPiType (λ a => Pi₃ ($P a)))           ← unfoldOnce ⌜($hApp).hPiPa⌝
        let F       : Q(Pi₄ $P)                                  ← unfoldOnce ⌜($hApp).F⌝
        let a       : Q($α)                                      ← unfoldOnce ⌜($hApp).a⌝
        let b       : Q($β)                                      ← unfoldOnce ⌜($hApp).b⌝
        let c       : Q($γ)                                      ← unfoldOnce ⌜($hApp).c⌝
        let d       : Q($δ)                                      ← unfoldOnce ⌜($hApp).d⌝
        pure { α  := δ,
               P  := ⌜$P     $a $b $c⌝,
               hP := ⌜$hPabc $a $b $c⌝,
               F  := ⌜$F     $a $b $c⌝,
               a  := d }

    end mkIsPiApp₄

    def mkIsPiApp₄' (u u' u'' u''' : Level) := ⌜IsPiApp₄'.{u, u', u'', u'''} $y⌝

    namespace mkIsPiApp₄'

      variable {u u' u'' u''' : Level} (hApp : mkIsPiApp₄' V Y y u u' u'' u''')
    
      def mkH₄ : mkIsPiApp V Y y u''' := ⌜($hApp).h₄⌝
      def mkIsPiApp₃' : mkIsPiApp₃' V Y y u u' u'' := ⌜($hApp).toIsPiApp₃'⌝

    end mkIsPiApp₄'

  end

end mkHasPiType'


def mkHasQuantPiType' {u u' v vv : Level} (α : Q(Sort u)) (β : Q(Sort u')) (V : Q(Universe.{v, vv}))
                      (P : Q($α → $β → $V)) :=
  ⌜∀ a, HasPiType ($P a)⌝

namespace mkHasQuantPiType'

  variable {u u' v vv : Level} {α : Q(Sort u)} {β : Q(Sort u')} {V : Q(Universe.{v, vv})}
           {P : Q($α → $β → $V)} (hP : mkHasQuantPiType' α β V P)

  def app (a : Q($α)) : mkHasPiType' β V ⌜$P $a⌝ := ⌜$hP $a⌝

  def mkPiProp : Q($α → $V) := ⌜λ a => Pi ($P a)⌝

end mkHasQuantPiType'


def mkHasQuantDepPiType' {u v vv w ww : Level} (α : Q(Sort u)) (V : Q(Universe.{v, vv}))
                         (P : Q($α → $V)) (W : Q(Universe.{w, ww})) (Q : Q(∀ a, $P a → $W)) :=
  ⌜∀ a, HasPiType ($Q a)⌝

namespace mkHasQuantDepPiType'

  variable {u v vv w ww : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})} {P : Q($α → $V)}
           {W : Q(Universe.{w, ww})} {Q : Q(∀ a, $P a → $W)} (hQ : mkHasQuantDepPiType' α V P W Q)

  def app (a : Q($α)) : mkHasPiType' ⌜$P $a⌝ W ⌜$Q $a⌝ := ⌜$hQ $a⌝

  def mkPiProp : Q($α → $W) := ⌜λ a => Pi ($Q a)⌝

end mkHasQuantDepPiType'


def mkHasFunctors' {u uu : Level} (α : Q(Sort u)) (U : Q(Universe.{u, uu})) (Y : Q($U)) :=
  ⌜HasFunctors $α $Y⌝

namespace mkHasFunctors'

  variable {u uu : Level}

  section

    variable (α : Q(Sort u)) (U : Q(Universe.{u, uu})) (Y : Q($U))

    def mkFunction := ⌜$α → $Y⌝

    def mkFunction.mkApp (f : Q($α → $Y)) (a : Q($α)) : Q($Y) := ⌜$f $a⌝
  
  end

  section

    variable {α : Q(Sort u)} {U : Q(Universe.{u, uu})} {Y : Q($U)} (h : mkHasFunctors' α U Y)

    def toMkHasPiType' : mkHasPiType' α U ⌜Function.const $α $Y⌝ := ⌜($h).toHasPiType⌝

    def mkFun : Q($U) := ⌜$α ⥤ $Y⌝

    def mkApply (F : Q($α ⥤ $Y)) : Q($α → $Y) := ⌜HasFunctors.apply $F⌝

    def mkDefFun (f : Q($α → $Y)) := ⌜$α ⥤{$f} $Y⌝

    namespace mkDefFun

      variable (f : Q($α → $Y))

      def mkMk (F : Q($α ⥤ $Y)) : mkDefFun h f := ⌜DefFun.mk (f := $f) $F⌝

      variable (F : mkDefFun h f)

      def mkInst : Q($α ⥤ $Y) := ⌜($F).inst⌝

    end mkDefFun

  end

  section

    variable (U : Q(Universe.{u, uu})) (Y : Q($U))

    structure FunApp where
      α  : Q(Sort u)
      hα : Q(HasFunctors $α $Y)
      F  : Q($α ⥤ $Y)
      a  : Q($α)

    def FunApp.toPiApp (app : FunApp U Y) : mkHasPiType'.PiApp U u where
      α  := app.α
      P  := ⌜Function.const _ $Y⌝
      hP := ⌜$(app.hα).toHasPiType⌝
      F  := app.F
      a  := app.a

    variable (y : Q($Y))

    def mkIsFunApp := ⌜IsFunApp.{u} $y⌝

    namespace mkIsFunApp

      variable (hApp : mkIsFunApp U Y y)

      def mkApp : MetaM (FunApp U Y) := do
        let α  : Q(Sort u)            ← unfoldOnce ⌜($hApp).α⌝
        let hα : Q(HasFunctors $α $Y) ← unfoldOnce ⌜($hApp).hα⌝
        let F  : Q($α ⥤ $Y)           ← unfoldOnce ⌜($hApp).F⌝
        let a  : Q($α)                ← unfoldOnce ⌜($hApp).a⌝
        pure { α  := α,
               hα := hα,
               F  := F,
               a  := a }

    end mkIsFunApp

    def mkIsFunApp₂ := ⌜IsFunApp₂ $y⌝

    namespace mkIsFunApp₂

      variable (hApp : mkIsFunApp₂ U Y y)

      def mkApp : MetaM (FunApp U Y) := do
        let α  : Q(Sort u)                   ← unfoldOnce ⌜($hApp).α⌝
        let β  : Q(Sort u)                   ← unfoldOnce ⌜($hApp).β⌝
        let hβ : Q(HasFunctors $β $Y)        ← unfoldOnce ⌜($hApp).hβ⌝
        let hα : Q(HasFunctors $α ($β ⥤ $Y)) ← unfoldOnce ⌜($hApp).hα⌝
        let F  : Q($α ⥤ $β ⥤ $Y)             ← unfoldOnce ⌜($hApp).F⌝
        let a  : Q($α)                       ← unfoldOnce ⌜($hApp).a⌝
        let b  : Q($β)                       ← unfoldOnce ⌜($hApp).b⌝
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
        let α  : Q(Sort u)                        ← unfoldOnce ⌜($hApp).α⌝
        let β  : Q(Sort u)                        ← unfoldOnce ⌜($hApp).β⌝
        let γ  : Q(Sort u)                        ← unfoldOnce ⌜($hApp).γ⌝
        let hγ : Q(HasFunctors $γ $Y)             ← unfoldOnce ⌜($hApp).hγ⌝
        let hβ : Q(HasFunctors $β ($γ ⥤ $Y))      ← unfoldOnce ⌜($hApp).hβ⌝
        let hα : Q(HasFunctors $α ($β ⥤ $γ ⥤ $Y)) ← unfoldOnce ⌜($hApp).hα⌝
        let F  : Q($α ⥤ $β ⥤ $γ ⥤ $Y)             ← unfoldOnce ⌜($hApp).F⌝
        let a  : Q($α)                            ← unfoldOnce ⌜($hApp).a⌝
        let b  : Q($β)                            ← unfoldOnce ⌜($hApp).b⌝
        let c  : Q($γ)                            ← unfoldOnce ⌜($hApp).c⌝
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
        let α  : Q(Sort u)                             ← unfoldOnce ⌜($hApp).α⌝
        let β  : Q(Sort u)                             ← unfoldOnce ⌜($hApp).β⌝
        let γ  : Q(Sort u)                             ← unfoldOnce ⌜($hApp).γ⌝
        let δ  : Q(Sort u)                             ← unfoldOnce ⌜($hApp).δ⌝
        let hδ : Q(HasFunctors $δ $Y)                  ← unfoldOnce ⌜($hApp).hδ⌝
        let hγ : Q(HasFunctors $γ ($δ ⥤ $Y))           ← unfoldOnce ⌜($hApp).hγ⌝
        let hβ : Q(HasFunctors $β ($γ ⥤ $δ ⥤ $Y))      ← unfoldOnce ⌜($hApp).hβ⌝
        let hα : Q(HasFunctors $α ($β ⥤ $γ ⥤ $δ ⥤ $Y)) ← unfoldOnce ⌜($hApp).hα⌝
        let F  : Q($α ⥤ $β ⥤ $γ ⥤ $δ ⥤ $Y)             ← unfoldOnce ⌜($hApp).F⌝
        let a  : Q($α)                                 ← unfoldOnce ⌜($hApp).a⌝
        let b  : Q($β)                                 ← unfoldOnce ⌜($hApp).b⌝
        let c  : Q($γ)                                 ← unfoldOnce ⌜($hApp).c⌝
        let d  : Q($δ)                                 ← unfoldOnce ⌜($hApp).d⌝
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


def mkHasUnivTypeFunctors' {u uu uv : Level} (U : Q(Universe.{u, uu})) (V : Q(Universe.{u, uv}))
                           (A : Q($U)) (B : Q($V)) :=
  ⌜HasFunctors $A $B⌝

namespace mkHasUnivTypeFunctors'

  instance {u uu uv : Level} (U : Q(Universe.{u, uu})) (V : Q(Universe.{u, uv})) (A : Q($U))
           (B : Q($V)) :
      Coe (mkHasUnivTypeFunctors' U V A B) (mkHasFunctors' ⌜$A⌝ V B) :=
    ⟨id⟩

end mkHasUnivTypeFunctors'


def mkHasUnivFunctors' {u uu uv : Level} (U : Q(Universe.{u, uu})) (V : Q(Universe.{u, uv})) :=
  ⌜HasUnivFunctors $U $V⌝

namespace mkHasUnivFunctors'

  variable {u uu uv : Level} {U : Q(Universe.{u, uu})} {V : Q(Universe.{u, uv})}
           (h : mkHasUnivFunctors' U V)

  def mkHasUnivTypeFunctors' (A : Q($U)) (B : Q($V)) : mkHasUnivTypeFunctors' U V A B :=
    ⌜inferInstance⌝

end mkHasUnivFunctors'



class mkHasPiType {α : _sort} {v : Level} {V : _Universe v} {p : α → V} (P : α ⥤{p} _[V]) where
  h    : mkHasPiType' α.α V.U P.inst
  -- Optional `HasFunctors` instance, to output better terms if `P` is known to be constant, i.e. if
  -- `p` is a constant function at the meta level.
  hFun : Option (mkHasFunctors' (u := v) α.α V.U (p default))

namespace mkHasPiType

  section

    variable {α : _sort} {v : Level} {V : _Universe v}

    def mkFreshMVar {p : α → V} {P : α ⥤{p} _[V]} : MetaM (mkHasPiType P) := do
      pure { h    := ← TypedExpr.mkFreshMVar,
             hFun := none }

    def instantiate {p : α → V} {P : α ⥤{p} _[V]} (hP : mkHasPiType P) {α' : _sort} {v' : Level}
                    {V' : _Universe v'} {p' : α' → V'} (P' : α' ⥤{p'} _[V']) :
        MetaM (Σ (p' : α' → V') (P' : α' ⥤{p'} _[V']), mkHasPiType P') := do
      let Y : V' ← _Universe.mkFreshTypeMVar
      let P'const := HasConstPi.defConstFun α _(Y)
      if ← isDefEq P'.inst P'const.inst then
        let Y : V' ← _Universe.instantiateTypeMVars Y
        let P'const := HasConstPi.defConstFun α' _(Y)
        let hP' : mkHasPiType P'const := { h    := ← hP.h.instantiate,
                                           hFun := ← TypedExpr.synthesize? }
        return ⟨Function.const α' Y, P'const, hP'⟩
      let hP' : mkHasPiType P' := { h    := ← hP.h.instantiate,
                                    hFun := none }
      return ⟨p', P', hP'⟩

    def synthesize {p : α → V} (P : α ⥤{p} _[V]) :
        MetaM (Σ (p : α → V) (P : α ⥤{p} _[V]), mkHasPiType P) := do
      let Y : V ← _Universe.mkFreshTypeMVar
      let Pconst := HasConstPi.defConstFun α _(Y)
      if ← isDefEq P.inst Pconst.inst then
        let Y : V ← _Universe.instantiateTypeMVars Y
        let Pconst := HasConstPi.defConstFun α _(Y)
        let hP : mkHasPiType Pconst := { h    := ← TypedExpr.synthesize,
                                         hFun := ← TypedExpr.synthesize? }
        return ⟨Function.const α Y, Pconst, hP⟩
      let hP : mkHasPiType P := { h    := ← TypedExpr.synthesize,
                                  hFun := none }
      return ⟨p, P, hP⟩

    @[reducible] def reflectProp {p : α → V} (P : α ⥤{p} _[V]) : α → V := p

    instance reflect {p : α → V} (P : α ⥤{p} _[V]) [h : mkHasPiType P] :
        HasPiType (reflectProp P) where
      defPiType := match h.hFun with
                   | some hFun =>
                     { A    := mkHasFunctors'.mkFun hFun,
                       elim := λ F => mkHasFunctors'.mkFunction.mkApp (u := v) α.α V.U (p default)
                                                                      (mkHasFunctors'.mkApply hFun F) }
                   | none =>
                     { A    := mkHasPiType'.mkPi h.h,
                       elim := λ F => mkHasPiType'.mkForAll.mkApp α.α V.U P.inst
                                                                  (mkHasPiType'.mkApply h.h F) }

    def defSortPropFun {p : α → V} (P : α ⥤{p} _[V]) :
        α ⥤{λ a => _⌈(reflectProp P) a⌉.α} _sort.mkSortType v :=
      ⟨_Universe.instInstFun V ⊙ P.inst⟩

    @[reducible] def sortProp {p : α → V} (P : α ⥤{p} _[V]) :=
      _sort.defFunToProp (defSortPropFun P)

    def mkApply {p : α → V} {P : α ⥤{p} _[V]} [h : mkHasPiType P] (F : Pi (reflectProp P)) :
        Pi (sortProp P) :=
      match h.hFun with
      | some hFun => mkHasFunctors'.mkApply hFun F
      | none => mkHasPiType'.mkApply h.h F

    def mkDefPi {p : α → V} (P : α ⥤{p} _[V]) [h : mkHasPiType P] (f : Pi (sortProp P)) :=
      match h.hFun with
      | some hFun => mkHasFunctors'.mkDefFun hFun f
      | none => mkHasPiType'.mkDefPi h.h f

    namespace mkDefPi

      variable {p : α → V} (P : α ⥤{p} _[V]) [h : mkHasPiType P] (f : Pi (sortProp P))

      def mkMk (F : Pi (reflectProp P)) : mkDefPi P f := mkHasPiType'.mkDefPi.mkMk h.h f F

      variable (F : mkDefPi P f)

      def mkInst : Pi (reflectProp P) := mkHasPiType'.mkDefPi.mkInst h.h f F

    end mkDefPi

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

    def mkIsPiApp₂' (u u' : Level) : ClassExpr := ⟨mkHasPiType'.mkIsPiApp₂' V.U Y y u u'⟩

    namespace mkIsPiApp₂'

      variable (u u' : Level) [hApp : mkIsPiApp₂' y u u']
    
      instance : mkIsPiApp y u' := ⟨mkHasPiType'.mkIsPiApp₂'.mkH₂ V.U Y y hApp.h⟩
      instance : mkIsPiApp y u := ⟨mkHasPiType'.mkIsPiApp₂'.mkIsPiApp V.U Y y hApp.h⟩

    end mkIsPiApp₂'

    def mkIsPiApp₃ (u u' u'' : Level) : ClassExpr := ⟨mkHasPiType'.mkIsPiApp₃ V.U Y y u u' u''⟩

    namespace mkIsPiApp₃

      variable (u u' u'' : Level) [hApp : mkIsPiApp₃ y u u' u'']

      def mkApp : MetaM (mkHasPiType'.PiApp V.U u'') := mkHasPiType'.mkIsPiApp₃.mkApp V.U Y y hApp.h

    end mkIsPiApp₃

    def mkIsPiApp₃' (u u' u'' : Level) : ClassExpr := ⟨mkHasPiType'.mkIsPiApp₃' V.U Y y u u' u''⟩

    namespace mkIsPiApp₃'

      variable (u u' u'' : Level) [hApp : mkIsPiApp₃' y u u' u'']

      instance : mkIsPiApp y u'' := ⟨mkHasPiType'.mkIsPiApp₃'.mkH₃ V.U Y y hApp.h⟩
      instance : mkIsPiApp₂' y u u' := ⟨mkHasPiType'.mkIsPiApp₃'.mkIsPiApp₂' V.U Y y hApp.h⟩

    end mkIsPiApp₃'

    def mkIsPiApp₄ (u u' u'' u''' : Level) : ClassExpr :=
      ⟨mkHasPiType'.mkIsPiApp₄ V.U Y y u u' u'' u'''⟩

    namespace mkIsPiApp₄

      variable (u u' u'' u''' : Level) [hApp : mkIsPiApp₄ y u u' u'' u''']

      def mkApp : MetaM (mkHasPiType'.PiApp V.U u''') :=
        mkHasPiType'.mkIsPiApp₄.mkApp V.U Y y hApp.h

    end mkIsPiApp₄

    def mkIsPiApp₄' (u u' u'' u''' : Level) : ClassExpr :=
      ⟨mkHasPiType'.mkIsPiApp₄' V.U Y y u u' u'' u'''⟩

    namespace mkIsPiApp₄'

      variable (u u' u'' u''' : Level) [hApp : mkIsPiApp₄' y u u' u'' u''']

      instance : mkIsPiApp y u''' :=  ⟨mkHasPiType'.mkIsPiApp₄'.mkH₄ V.U Y y hApp.h⟩
      instance : mkIsPiApp₃' y u u' u'' := ⟨mkHasPiType'.mkIsPiApp₄'.mkIsPiApp₃' V.U Y y hApp.h⟩

    end mkIsPiApp₄'

  end

  section

    variable {u v : Level} {U : _Universe u} {A : U} {V : _Universe v}

    @[reducible] def reflectProp' {p : A → V} (P : _⌈A⌉ ⥤{p} _[V]) :
        A → V :=
      reflectProp P

    instance reflect' {p : A → V} (P : _⌈A⌉ ⥤{p} _[V]) [h : mkHasPiType P] :
        HasPiType (reflectProp' P) :=
      reflect P

  end

  section

    instance {α : _sort} {v : Level} {V : _Universe v} {p : α → V} (P : α ⥤{p} _[V]) :
        HasPiType (λ a => _⌈(reflectProp P) a⌉) :=
      _sort.hasPiType (HasCompFunPi.defCompDefFun P (_Universe.defInstInstFun V))

    instance {α : _sort} {v w : Level} {V : _Universe v} {p : α → V} {P : α ⥤{p} _[V]}
             (W : _Universe w) :
        HasPiType (λ a => (_⌈(reflectProp P) a⌉ ⥤ _[W])) :=
      _sort.hasPiType
        (HasCompFunPi.defCompDefFun (HasCompFunPi.defCompDefFun P (_Universe.defInstInstFun V))
                                    (_sort.defInFunCtorFun v _[W]))

  end

end mkHasPiType


def mkHasQuantPiType {α β : _sort} {v : Level} {V : _Universe v} {p : α → β → V}
                     (P : α ⥤ β ⥤{p} _[V]) :
    ClassExpr :=
  ⟨mkHasQuantPiType' α.α β.α V.U P.inst⟩

namespace mkHasQuantPiType

  variable {α β : _sort} {v : Level} {V : _Universe v}

  @[reducible] def reflectAppProp {p : α → β → V} (P : α ⥤ β ⥤{p} _[V]) (a : α) :
      β → V :=
    mkHasPiType.reflectProp (P.app a)

  @[reducible] def reflectProp₂ {p : α → β → V} (P : α ⥤ β ⥤{p} _[V]) :
      α → β → V :=
    p

  variable {p : α → β → V} (P : α ⥤ β ⥤{p} _[V]) [h : mkHasQuantPiType P]

  instance app (a : α) : mkHasPiType (P.app a) where
    h    := mkHasQuantPiType'.app h.h a
    hFun := none -- TODO

  def piProp : α ⥤{λ a => Pi (reflectAppProp P a)} _[V] := ⟨mkHasQuantPiType'.mkPiProp h.h⟩

end mkHasQuantPiType


def mkHasQuantDepPiType {α : _sort} {v w : Level} {V : _Universe v} {p : α → V} {P : α ⥤{p} _[V]}
                        {W : _Universe w} {q : ∀ a, _⌈p a⌉ ⥤ _[W]}
                        (Q : DefPi (λ a => (_⌈(mkHasPiType.reflectProp P) a⌉ ⥤ _[W])) q) :
    ClassExpr :=
  ⟨mkHasQuantDepPiType' α.α V.U P.inst W.U Q.inst⟩

namespace mkHasQuantDepPiType

  variable {α : _sort} {v w : Level} {V : _Universe v} {p : α → V} {P : α ⥤{p} _[V]}
           {W : _Universe w}

  def appProp {q : ∀ a, _⌈p a⌉ ⥤ _[W]}
              (Q : DefPi (λ a => (_⌈(mkHasPiType.reflectProp P) a⌉ ⥤ _[W])) q) (a : α) :
      _⌈(mkHasPiType.reflectProp P) a⌉ ⥤{λ b => q a b} _[W] :=
    DefFun.defAppFun (q a)

  @[reducible] def reflectAppProp {q : ∀ a, _⌈p a⌉ ⥤ _[W]}
                                  (Q : DefPi (λ a => (_⌈(mkHasPiType.reflectProp P) a⌉ ⥤ _[W])) q)
                                  (a : α) :
      (mkHasPiType.reflectProp P) a → W :=
    mkHasPiType.reflectProp (appProp Q a)

  @[reducible] def reflectProp₂ {q : ∀ a, _⌈p a⌉ ⥤ _[W]}
                                (Q : DefPi (λ a => (_⌈(mkHasPiType.reflectProp P) a⌉ ⥤ _[W])) q) :
      ∀ a, p a → W :=
    λ a b => q a b

  variable {q : ∀ a, _⌈p a⌉ ⥤ _[W]}
           (Q : DefPi (λ a => (_⌈(mkHasPiType.reflectProp P) a⌉ ⥤ _[W])) q)
           [h : mkHasQuantDepPiType Q]

  instance app (a : α) : mkHasPiType (appProp Q a) where
    h    := mkHasQuantDepPiType'.app h.h a
    hFun := none -- TODO

  def piProp : α ⥤{λ a => Pi (reflectAppProp Q a)} _[W] := ⟨mkHasQuantPiType'.mkPiProp h.h⟩

end mkHasQuantDepPiType


def mkHasFunctors (α : _sort) {U : _Universe α.u} (Y : U) : ClassExpr :=
  ⟨mkHasFunctors' α.α U.U Y⟩

namespace mkHasFunctors

  instance toMkHasPiType (α : _sort) {U : _Universe α.u} (Y : U) [h : mkHasFunctors α Y] :
      mkHasPiType (HasConstPi.defConstFun α _(Y)) where
    h    := mkHasFunctors'.toMkHasPiType' h.h
    hFun := some h.h

  instance reflect (α : _sort) {U : _Universe α.u} (Y : U) [h : mkHasFunctors α Y] :
    HasFunctors α Y := ⟨⟩

  instance reflect' {u : Level} {U V : _Universe u} (A : U) (B : V) [h : mkHasFunctors _⌈A⌉ B] :
      HasFunctors A B :=
    reflect _⌈A⌉ B

  def toPi {α : _sort} {U : _Universe α.u} {Y : U} [h : mkHasFunctors α Y] (F : α ⥤ Y) :
      Pi (mkHasPiType.reflectProp (HasConstPi.defConstFun α _(Y))) :=
    F

  def mkApply {α : _sort} {U : _Universe α.u} {Y : U} [h : mkHasFunctors α Y] (F : α ⥤ Y) :
      α ⥤ _⌈Y⌉ :=
    mkHasPiType.mkApply (toPi F)

  section

    variable (α : _sort) {U : _Universe α.u} (Y : U) [h : mkHasFunctors α Y]

    def mkDefFun (f : α ⥤ _⌈Y⌉) := mkHasFunctors'.mkDefFun h.h f

    namespace mkDefFun

      variable (f : α ⥤ _⌈Y⌉)

      def mkMk (F : α ⥤ Y) : mkDefFun α Y f :=
        mkHasFunctors'.mkDefFun.mkMk h.h f F

      variable (F : mkDefFun α Y f)

      def mkInst : α ⥤ Y := mkHasFunctors'.mkDefFun.mkInst h.h f F

    end mkDefFun

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


def mkHasUnivFunctors {u : Level} (U V : _Universe u) : ClassExpr := ⟨mkHasUnivFunctors' U.U V.U⟩

namespace mkHasUnivFunctors

  variable {u : Level} (U V : _Universe u) [h : mkHasUnivFunctors U V]

  instance toMkHasFunctors (A : U) (B : V) : mkHasFunctors _⌈A⌉ B :=
    ⟨mkHasUnivFunctors'.mkHasUnivTypeFunctors' h.h A B⟩

  instance reflect : HasUnivFunctors U V := ⟨⟩

end mkHasUnivFunctors



structure PiData {v : Level} (V : _Universe v) where
  {α : _sort}
  {p : α → V}
  (P : α ⥤{p} _[V])
  [h : mkHasPiType P]

namespace PiData

  def mkFreshMVar {v : Level} (V : _Universe v) : MetaM (PiData V) := do
    let α ← _sort.mkFreshMVar
    let P : α ⥤ _[V] ← _sort.mkFreshInstMVar
    let P' := DefFun.defAppFun P
    let h : mkHasPiType P' ← mkHasPiType.mkFreshMVar
    pure ⟨P'⟩

  variable {v : Level} {V : _Universe v}

  def instantiate (φ : PiData V) {v' : Level} (V' : _Universe v') : MetaM (PiData V') := do
    let α ← _sort.instantiate φ.α
    let P : α ⥤ _[V'] ← _sort.instantiateInstMVars φ.P.inst
    let P' := DefFun.defAppFun P
    let ⟨p, P', h⟩ ← φ.h.instantiate P'
    pure ⟨P'⟩

  variable (φ : PiData V)

  instance : mkHasPiType φ.P := φ.h

  @[reducible] def mkPi     : V     := Pi (mkHasPiType.reflectProp φ.P)
  @[reducible] def mkSortPi : _sort := Pi (mkHasPiType.sortProp    φ.P)

end PiData


structure PiApp {v : Level} {V : _Universe v} {Y : V} (y : Y) extends
    PiData V where
  F : Pi (mkHasPiType.reflectProp P)
  a : α

namespace PiApp

  open mkHasPiType mkHasFunctors

  variable {v : Level} {V : _Universe v} {Y : V} (y : Y)

  def constructPi {u : Level} (app : mkHasPiType'.PiApp V.U u) : MetaM (PiApp y) := do
    let α : _sort := ⟨app.α⟩
    let P : α ⥤ _[V] := app.P
    let P' := DefFun.defAppFun P
    let h : mkHasPiType P' := { h := app.hP, hFun := none }
    pure ⟨⟨P'⟩, app.F, app.a⟩

  def constructFun (app : mkHasFunctors'.FunApp V.U Y) : MetaM (PiApp y) := do
    let α : _sort := ⟨app.α⟩
    let h : mkHasFunctors α Y := { h := app.hα }
    pure ⟨⟨HasConstPi.defConstFun α _(Y)⟩, app.F, app.a⟩

  def getLiteralPiApp : MetaM (List (PiApp y)) := do
    let φ ← PiData.mkFreshMVar V
    let F : φ.mkPi ← _Universe.mkFreshInstMVar
    let a : φ.α ← _sort.mkFreshInstMVar
    if ← isDefEq y (F a) then
      let φ ← φ.instantiate V
      let F : φ.mkPi ← _Universe.instantiateInstMVars F
      let a : φ.α ← _sort.instantiateInstMVars a
      return [⟨φ, F, a⟩]
    pure []

  -- `y` and `y'` must be defeq.

  def synthesizePiApps'.app₄ {y' : Y} : MetaM (List (PiApp y')) := do
    let hApp? : Option (mkHasFunctors'.mkIsFunApp₄ V.U Y y) ← TypedExpr.synthesize?
    match hApp? with
    | some hApp =>
      let _ : mkIsFunApp₄ y := { h := ← hApp.instantiate }
      pure [← constructFun y' (← mkIsFunApp₄.mkApp y)]
    | none => do
      let u ← mkFreshLevelMVar
      let u' ← mkFreshLevelMVar
      let u'' ← mkFreshLevelMVar
      let u''' ← mkFreshLevelMVar
      let hApp? : Option (mkHasPiType'.mkIsPiApp₄ V.U Y y u u' u'' u''') ← TypedExpr.synthesize?
      match hApp? with
      | some hApp =>
        let u ← instantiateLevelMVars u
        let u' ← instantiateLevelMVars u'
        let u'' ← instantiateLevelMVars u''
        let u''' ← instantiateLevelMVars u'''
        let _ : mkIsPiApp₄ y u u' u'' u''' := { h := ← hApp.instantiate }
        pure [← constructPi y' (← mkIsPiApp₄.mkApp y u u' u'' u''')]
      | none => pure []

  def synthesizePiApps'.app₃ {y' : Y} : MetaM (List (PiApp y')) := do
    let hApp? : Option (mkHasFunctors'.mkIsFunApp₃ V.U Y y) ← TypedExpr.synthesize?
    match hApp? with
    | some hApp =>
      let _ : mkIsFunApp₃ y := { h := ← hApp.instantiate }
      pure [← constructFun y' (← mkIsFunApp₃.mkApp y)]
    | none => do
      let u ← mkFreshLevelMVar
      let u' ← mkFreshLevelMVar
      let u'' ← mkFreshLevelMVar
      let hApp? : Option (mkHasPiType'.mkIsPiApp₃ V.U Y y u u' u'') ← TypedExpr.synthesize?
      match hApp? with
      | some hApp =>
        let u ← instantiateLevelMVars u
        let u' ← instantiateLevelMVars u'
        let u'' ← instantiateLevelMVars u''
        let _ : mkIsPiApp₃ y u u' u'' := { h := ← hApp.instantiate }
        pure [← constructPi y' (← mkIsPiApp₃.mkApp y u u' u'')]
      | none => synthesizePiApps'.app₄ y

  def synthesizePiApps'.app₂ {y' : Y} : MetaM (List (PiApp y')) := do
    let hApp? : Option (mkHasFunctors'.mkIsFunApp₂ V.U Y y) ← TypedExpr.synthesize?
    match hApp? with
    | some hApp =>
      let _ : mkIsFunApp₂ y := { h := ← hApp.instantiate }
      pure [← constructFun y' (← mkIsFunApp₂.mkApp y)]
    | none => do
      let u ← mkFreshLevelMVar
      let u' ← mkFreshLevelMVar
      let hApp? : Option (mkHasPiType'.mkIsPiApp₂ V.U Y y u u') ← TypedExpr.synthesize?
      match hApp? with
      | some hApp =>
        let u ← instantiateLevelMVars u
        let u' ← instantiateLevelMVars u'
        let _ : mkIsPiApp₂ y u u' := { h := ← hApp.instantiate }
        pure [← constructPi y' (← mkIsPiApp₂.mkApp y u u')]
      | none => synthesizePiApps'.app₃ y

  def synthesizePiApps'.app {y' : Y} : MetaM (List (PiApp y')) := do
    let hApp? : Option (mkHasFunctors'.mkIsFunApp V.U Y y) ← TypedExpr.synthesize?
    match hApp? with
    | some hApp =>
      let _ : mkIsFunApp y := { h := ← hApp.instantiate }
      pure [← constructFun y' (← mkIsFunApp.mkApp y)]
    | none => do
      let u ← mkFreshLevelMVar
      let hApp? : Option (mkHasPiType'.mkIsPiApp V.U Y y u) ← TypedExpr.synthesize?
      match hApp? with
      | some hApp =>
        let u ← instantiateLevelMVars u
        let _ : mkIsPiApp y u := { h := ← hApp.instantiate }
        pure [← constructPi y' (← mkIsPiApp.mkApp y u)]
      | none => synthesizePiApps'.app₂ y

  def synthesizePiApps'.app₂' {y' : Y} : MetaM (List (PiApp y')) := do
    let hApp? : Option (mkHasFunctors'.mkIsFunApp₂' V.U Y y) ← TypedExpr.synthesize?
    match hApp? with
    | some hApp =>
      let _ : mkIsFunApp₂' y := { h := ← hApp.instantiate }
      pure [← constructFun y' (← mkIsFunApp.mkApp y),
            ← constructFun y' (← mkIsFunApp.mkApp y (hApp := mkIsFunApp₂'.mkH₂ y))]
    | none => do
      let u ← mkFreshLevelMVar
      let u' ← mkFreshLevelMVar
      let hApp? : Option (mkHasPiType'.mkIsPiApp₂' V.U Y y u u') ← TypedExpr.synthesize?
      match hApp? with
      | some hApp =>
        let u ← instantiateLevelMVars u
        let u' ← instantiateLevelMVars u'
        let _ : mkIsPiApp₂' y u u' := { h := ← hApp.instantiate }
        pure [← constructPi y' (← mkIsPiApp.mkApp y u),
              ← constructPi y' (← mkIsPiApp.mkApp y u')]
      | none => synthesizePiApps'.app y

  def synthesizePiApps'.app₃' {y' : Y} : MetaM (List (PiApp y')) := do
    let hApp? : Option (mkHasFunctors'.mkIsFunApp₃' V.U Y y) ← TypedExpr.synthesize?
    match hApp? with
    | some hApp =>
      let _ : mkIsFunApp₃' y := { h := ← hApp.instantiate }
      pure [← constructFun y' (← mkIsFunApp.mkApp y),
            ← constructFun y' (← mkIsFunApp.mkApp y (hApp := mkIsFunApp₂'.mkH₂ y)),
            ← constructFun y' (← mkIsFunApp.mkApp y (hApp := mkIsFunApp₃'.mkH₃ y))]
    | none => do
      let u ← mkFreshLevelMVar
      let u' ← mkFreshLevelMVar
      let u'' ← mkFreshLevelMVar
      let hApp? : Option (mkHasPiType'.mkIsPiApp₃' V.U Y y u u' u'') ← TypedExpr.synthesize?
      match hApp? with
      | some hApp =>
        let u ← instantiateLevelMVars u
        let u' ← instantiateLevelMVars u'
        let u'' ← instantiateLevelMVars u''
        let _ : mkIsPiApp₃' y u u' u'' := { h := ← hApp.instantiate }
        pure [← constructPi y' (← mkIsPiApp.mkApp y u),
              ← constructPi y' (← mkIsPiApp.mkApp y u'),
              ← constructPi y' (← mkIsPiApp.mkApp y u'')]
      | none => synthesizePiApps'.app₂' y

  def synthesizePiApps'.app₄' {y' : Y} : MetaM (List (PiApp y')) := do
    let hApp? : Option (mkHasFunctors'.mkIsFunApp₄' V.U Y y) ← TypedExpr.synthesize?
    match hApp? with
    | some hApp =>
      let _ : mkIsFunApp₄' y := { h := ← hApp.instantiate }
      pure [← constructFun y' (← mkIsFunApp.mkApp y),
            ← constructFun y' (← mkIsFunApp.mkApp y (hApp := mkIsFunApp₂'.mkH₂ y)),
            ← constructFun y' (← mkIsFunApp.mkApp y (hApp := mkIsFunApp₃'.mkH₃ y)),
            ← constructFun y' (← mkIsFunApp.mkApp y (hApp := mkIsFunApp₄'.mkH₄ y))]
    | none => do
      let u ← mkFreshLevelMVar
      let u' ← mkFreshLevelMVar
      let u'' ← mkFreshLevelMVar
      let u''' ← mkFreshLevelMVar
      let hApp? : Option (mkHasPiType'.mkIsPiApp₄' V.U Y y u u' u'' u''') ← TypedExpr.synthesize?
      match hApp? with
      | some hApp =>
        let u ← instantiateLevelMVars u
        let u' ← instantiateLevelMVars u'
        let u'' ← instantiateLevelMVars u''
        let u''' ← instantiateLevelMVars u'''
        let _ : mkIsPiApp₄' y u u' u'' u''' := { h := ← hApp.instantiate }
        pure [← constructPi y' (← mkIsPiApp.mkApp y u),
              ← constructPi y' (← mkIsPiApp.mkApp y u'),
              ← constructPi y' (← mkIsPiApp.mkApp y u''),
              ← constructPi y' (← mkIsPiApp.mkApp y u''')]
      | none => synthesizePiApps'.app₃' y

  def synthesizePiApps' {y' : Y} : MetaM (List (PiApp y')) :=
    synthesizePiApps'.app₄' y

  def synthesizePiApps : MetaM (List (PiApp y)) := do
    -- First, check whether we can find an instance of `IsPiApp`.
    match ← synthesizePiApps' y with
    | List.nil => do
      -- If none was found, check if `y` is an application of `DefPi.inst`. If it is, pass that to
      -- `IsPiApp` instead of the original value of `y`, as `IsPiApp` is usually defined on such
      -- terms.
      let ψ ← PiData.mkFreshMVar V
      let f_y : ψ.mkSortPi ← _sort.mkFreshInstMVar
      let F_y : mkHasPiType.mkDefPi ψ.P f_y ← TypedExpr.mkFreshMVar
      let y' : ψ.mkPi := mkHasPiType.mkDefPi.mkInst ψ.P f_y F_y
      if ← isDefEq y y' then
        let ψ ← ψ.instantiate V
        let f_y : ψ.mkSortPi ← _sort.instantiateInstMVars f_y
        let F_y : ψ.mkPi ← _Universe.instantiateInstMVars F_y
        let y' : Y := mkHasPiType.mkDefPi.mkInst ψ.P f_y F_y
        -- However, if that is in turn reducibly an application of `DefPi.mk`, then use the
        -- argument of that.
        let y'' : Y ← _Universe.mkFreshInstMVar
        let F_y' := mkHasPiType.mkDefPi.mkMk ψ.P f_y y''
        if ← withReducible (isDefEq F_y F_y') then
          let y'' : Y ← _Universe.instantiateInstMVars y''
          return ← synthesizePiApps' y''
        return ← synthesizePiApps' y'
      -- Lastly, check whether `y` is literally a functor application.
      -- This sees through some definitions that are opaque to type class synthesis.
      -- Only do this if all else fails, as we want to return all alternatives if multiple exist.
      getLiteralPiApp y
    | result => pure result

end PiApp



def mkHasIdFun' {u uu : Level} {U : Q(Universe.{u, uu})} {A : Q($U)}
                (hAA : mkHasUnivTypeFunctors' U U A A) :=
  ⌜HasIdFun $A⌝

namespace mkHasIdFun'

  variable {u uu : Level} {U : Q(Universe.{u, uu})} {A : Q($U)}
           {hAA : mkHasUnivTypeFunctors' U U A A} (h : ⌜HasIdFun $A⌝)

  def mkIdFun : Q($A ⥤ $A) := ⌜HasIdFun.idFun $A⌝

end mkHasIdFun'

def mkHasIdFun {u : Level} {U : _Universe u} (A : U) [hAA : mkHasFunctors _⌈A⌉ A] : ClassExpr :=
  ⟨mkHasIdFun' (U := U.U) (A := A) hAA.h⟩

namespace mkHasIdFun

  variable {u : Level} {U : _Universe u} (A : U) [mkHasFunctors _⌈A⌉ A] [h : mkHasIdFun A]

  def mkIdFun : A ⥤ A := mkHasIdFun'.mkIdFun h.h

  instance reflect : HasIdFun A := ⟨⟨mkIdFun A⟩⟩

end mkHasIdFun


def mkHasPiAppFun' {u v vv : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})}
                   (hV : mkHasUnivFunctors' V V) {P : Q($α → $V)} (hP : mkHasPiType' α V P) :=
  ⌜HasPiAppFun $P⌝

namespace mkHasPiAppFun'

  section

    variable {u v vv : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})} {hV : mkHasUnivFunctors' V V}
             {P : Q($α → $V)} {hP : mkHasPiType' α V P} (h : mkHasPiAppFun' hV hP)

    def mkPiAppFun (a : Q($α)) : Q(Pi $P ⥤ $P $a) := ⌜HasPiAppFun.piAppFun $P $a⌝

  end

  section

    variable {u uu : Level} {α : Q(Sort u)} {U : Q(Universe.{u, uu})} {hU : mkHasUnivFunctors' U U}
             {B : Q($U)} {hαB : mkHasFunctors' α U B}
             (h : mkHasPiAppFun' hU (mkHasFunctors'.toMkHasPiType' hαB))

    def mkRevAppFun (a : Q($α)) : Q(($α ⥤ $B) ⥤ $B) := ⌜HasPiAppFun.revAppFun $a $B⌝

  end

end mkHasPiAppFun'

def mkHasPiAppFun {α : _sort} {v : Level} {V : _Universe v} [hV : mkHasUnivFunctors V V]
                  {p : α → V} (P : α ⥤{p} _[V]) [hP : mkHasPiType P] :
    ClassExpr :=
  ⟨mkHasPiAppFun' hV.h hP.h⟩

namespace mkHasPiAppFun

  variable {α : _sort} {v : Level} {V : _Universe v} [hV : mkHasUnivFunctors V V] {p : α → V}
           (P : α ⥤{p} _[V]) [hP : mkHasPiType P] [h : mkHasPiAppFun P]

  def mkPiAppFun (a : α) : Pi (mkHasPiType.reflectProp P) ⥤ p a :=
    match hP.hFun with
    | some hFun => mkHasPiAppFun'.mkRevAppFun (hU := hV.h) (hαB := hFun) h.h a
    | none => mkHasPiAppFun'.mkPiAppFun h.h a

  instance reflect : HasPiAppFun (mkHasPiType.reflectProp P) := ⟨λ a => ⟨mkPiAppFun P a⟩⟩

end mkHasPiAppFun


def mkHasSwapPi' {u u' v vv : Level} {α : Q(Sort u)} {β : Q(Sort u')} {V : Q(Universe.{v, vv})}
                 {P : Q($α → $β → $V)} (hPa : mkHasQuantPiType' α β V P)
                 (hPiPa : mkHasPiType' α V ⌜λ a => Pi ($P a)⌝)
                 (hPab : mkHasQuantPiType' β α V ⌜λ b a => $P a b⌝) :=
  ⌜HasSwapPi $P⌝

namespace mkHasSwapPi'

  def prop {u u' v vv : Level} (α : Q(Sort u)) (β : Q(Sort u')) (V : Q(Universe.{v, vv}))
           (P : Q($α → $β → $V)) (b : Q($β)) :
      Q($α → $V) :=
    ⌜λ a => $P a $b⌝

  def prop₂ {u u' v vv : Level} (α : Q(Sort u)) (β : Q(Sort u')) (V : Q(Universe.{v, vv}))
            (P : Q($α → $β → $V)) :
      Q($β → $α → $V) :=
    ⌜λ b a => $P a b⌝

  variable {u u' v vv : Level} {α : Q(Sort u)} {β : Q(Sort u')} {V : Q(Universe.{v, vv})}
           {P : Q($α → $β → $V)} {hPa : Q(∀ a, HasPiType ($P a))}
           {hPiPa : Q(HasPiType (λ a => Pi ($P a)))} {hPab : Q(∀ b, HasPiType (λ a => $P a b))}
           (h : mkHasSwapPi' hPa hPiPa hPab)

  def mkSwapPi (F : Q(Pi₂ $P)) (b : Q($β)) : Q(Pi (λ a => $P a $b)) := ⌜HasSwapPi.swapPi $F $b⌝

end mkHasSwapPi'

def mkHasSwapPi.prop {α β : _sort} {v : Level} {V : _Universe v} {p : α → β → V}
                     (P : α ⥤ β ⥤{p} _[V]) :
    β ⥤ α ⥤{λ b a => p a b} _[V] :=
  DefFun₂.mk (λ b => ⟨mkHasSwapPi'.prop α.α β.α V.U P.inst b⟩)
             (DefFun.mk (mkHasSwapPi'.prop₂ α.α β.α V.U P.inst))

def mkHasSwapPi {α β : _sort} {v : Level} {V : _Universe v} {p : α → β → V}
                (P : α ⥤ β ⥤{p} _[V]) [hPa : mkHasQuantPiType P]
                [hPiPa : mkHasPiType (mkHasQuantPiType.piProp P)]
                [hPab : mkHasQuantPiType (mkHasSwapPi.prop P)] :
    ClassExpr :=
  ⟨mkHasSwapPi' hPa.h hPiPa.h hPab.h⟩

namespace mkHasSwapPi

  variable {α β : _sort} {v : Level} {V : _Universe v} {p : α → β → V} {P : α ⥤ β ⥤{p} _[V]}
           [hPa : mkHasQuantPiType P] [hPiPa : mkHasPiType (mkHasQuantPiType.piProp P)]
           [hPab : mkHasQuantPiType (prop P)] [h : mkHasSwapPi P]

  instance (b : β) : mkHasPiType (DefFun₂.app (prop P) b) := inferInstance

  instance : HasPiType (λ a => Pi ((mkHasQuantPiType.reflectProp₂ P) a)) :=
    mkHasPiType.reflect (mkHasQuantPiType.piProp P)

  def mkSwapPi (F : Pi₂ (mkHasQuantPiType.reflectProp₂ P)) (b : β) :
      Pi (mkHasPiType.reflectProp (DefFun₂.app (prop P) b)) :=
    mkHasSwapPi'.mkSwapPi h.h F b

  instance reflect : HasSwapPi (mkHasQuantPiType.reflectProp₂ P) := ⟨λ F b => ⟨mkSwapPi F b⟩⟩

end mkHasSwapPi


def mkHasCompFunPi' {u uv w ww : Level} {α : Q(Sort u)} {V : Q(Universe.{u, uv})}
                    {B : Q($V)} (hαB : mkHasFunctors' α V B) {W : Q(Universe.{w, ww})}
                    (Q : Q($B → $W)) (hQ : mkHasPiType' ⌜$B⌝ W Q)
                    (hQFa : mkHasQuantPiType' ⌜$α ⥤ $B⌝ α W ⌜λ F a => $Q (F a)⌝) :=
  ⌜HasCompFunPi $α $Q⌝

namespace mkHasCompFunPi'

  def prop {u uv w ww : Level} {α : Q(Sort u)} {V : Q(Universe.{u, uv})} {B : Q($V)}
           (hαB : mkHasFunctors' α V B) (W : Q(Universe.{w, ww})) (Q : Q($B → $W)) (F : Q($α ⥤ $B)) :
      Q($α → $W) :=
    ⌜λ a => $Q ($F a)⌝

  def prop₂ {u uv w ww : Level} {α : Q(Sort u)} {V : Q(Universe.{u, uv})} {B : Q($V)}
            (hαB : mkHasFunctors' α V B) (W : Q(Universe.{w, ww})) (Q : Q($B → $W)) :
      Q(($α ⥤ $B) → $α → $W) :=
    ⌜λ F a => $Q (F a)⌝

  variable {u uv w ww : Level} {α : Q(Sort u)} {V : Q(Universe.{u, uv})} {B : Q($V)}
           {hαB : mkHasFunctors' α V B} {W : Q(Universe.{w, ww})} {Q : Q($B → $W)}
           {hQ : mkHasPiType' ⌜$B⌝ W Q} {hQFa : mkHasQuantPiType' ⌜$α ⥤ $B⌝ α W ⌜λ F a => $Q (F a)⌝}
           (h : mkHasCompFunPi' hαB Q hQ hQFa)

  def mkRevCompFunPi (G : Q(Pi $Q)) (F : Q($α ⥤ $B)) : Q(Pi (λ a => $Q ($F a))) :=
    ⌜HasCompFunPi.revCompFunPi $G $F⌝

end mkHasCompFunPi'

def mkHasCompFunPi.prop (α : _sort) {V : _Universe α.u} {B : V} [hαB : mkHasFunctors α B]
                        {w : Level} {W : _Universe w} {q : B → W} (Q : _⌈B⌉ ⥤{q} _[W]) :
    _⌈α ⥤ B⌉ ⥤ α ⥤{λ (F : α ⥤ B) a => q (F a)} _[W] :=
  DefFun₂.mk (λ F => ⟨mkHasCompFunPi'.prop hαB.h W.U Q.inst F⟩)
             (DefFun.mk (mkHasCompFunPi'.prop₂ hαB.h W.U Q.inst))

def mkHasCompFunPi (α : _sort) {V : _Universe α.u} {B : V} [hαB : mkHasFunctors α B] {w : Level}
                   {W : _Universe w} {q : B → W} (Q : _⌈B⌉ ⥤{q} _[W])
                   [hQ : mkHasPiType Q] [hQFa : mkHasQuantPiType (mkHasCompFunPi.prop α Q)] :
    ClassExpr :=
  ⟨mkHasCompFunPi' (W := W.U) hαB.h Q.inst hQ.h hQFa.h⟩

namespace mkHasCompFunPi

  variable {α : _sort} {V : _Universe α.u} {B : V} [hαB : mkHasFunctors α B] {w : Level}
           {W : _Universe w} {q : B → W} {Q : _⌈B⌉ ⥤{q} _[W]} [hQ : mkHasPiType Q]
           [hQFa : mkHasQuantPiType (prop α Q)] [h : mkHasCompFunPi α Q]

  instance (F : α ⥤ B) : mkHasPiType (DefFun₂.app (prop α Q) F) := inferInstance

  def mkRevCompFunPi (G : Pi (mkHasPiType.reflectProp' Q)) (F : α ⥤ B) :
      Pi (mkHasPiType.reflectProp (DefFun₂.app (prop α Q) F)) :=
    mkHasCompFunPi'.mkRevCompFunPi h.h G F

  instance reflect : HasCompFunPi α (B := B) (mkHasPiType.reflectProp' Q) :=
    ⟨λ F G => ⟨mkRevCompFunPi G F⟩⟩

end mkHasCompFunPi


def mkHasConstPi' {u v vv : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})} {B : Q($V)}
                  (hαB : mkHasPiType' α V ⌜Function.const $α $B⌝) :=
  ⌜HasConstPi $α $B⌝

namespace mkHasConstPi'

  section

    variable {u v vv : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})} {B : Q($V)}
             {hαB : mkHasPiType' α V ⌜Function.const $α $B⌝} (h : mkHasConstPi' hαB)

    def mkConstPi (b : Q($B)) : Q(Pi (Function.const $α $B)) := ⌜HasConstPi.constPi $α $b⌝

  end

  section

    variable {u uu : Level} {α : Q(Sort u)} {U : Q(Universe.{u, uu})} {B : Q($U)}
             {hαB : mkHasFunctors' α U B} (h : mkHasConstPi' (mkHasFunctors'.toMkHasPiType' hαB))

    def mkConstFun (b : Q($B)) : Q($α ⥤ $B) := ⌜HasConstPi.constFun $α $b⌝

  end

end mkHasConstPi'

def mkHasConstPi (α : _sort) {v : Level} {V : _Universe v} (B : V)
                 [hαB : mkHasPiType (HasConstPi.defConstFun α _(B))] :
    ClassExpr :=
  ⟨mkHasConstPi' (α := α.α) (V := V.U) (B := B) hαB.h⟩

namespace mkHasConstPi

  variable (α : _sort) {v : Level} {V : _Universe v} {B : V}
           [hαB : mkHasPiType (HasConstPi.defConstFun α _(B))] [h : mkHasConstPi α B]

  def mkConstPi (b : B) : Pi (Function.const α B) :=
    match hαB.hFun with
    | some hFun => mkHasConstPi'.mkConstFun (hαB := hFun) h.h b
    | none => mkHasConstPi'.mkConstPi h.h b

  instance reflect : HasConstPi α B := ⟨λ b => ⟨mkConstPi α b⟩⟩

end mkHasConstPi


def mkHasDupPi' {u v vv : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})} (P : Q($α → $α → $V))
                (hPa : mkHasQuantPiType' α α V P) (hPiPa : mkHasPiType' α V ⌜λ a => Pi ($P a)⌝)
                (hP : mkHasPiType' α V ⌜λ a => $P a a⌝) :=
  ⌜HasDupPi $P⌝

namespace mkHasDupPi'

  def prop {u v vv : Level} (α : Q(Sort u)) (V : Q(Universe.{v, vv})) (P : Q($α → $α → $V)) :
      Q($α → $V) :=
    ⌜λ a => $P a a⌝

  variable {u v vv : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})} {P : Q($α → $α → $V)}
           {hPa : mkHasQuantPiType' α α V P} {hPiPa : mkHasPiType' α V ⌜λ a => Pi ($P a)⌝}
           {hP : mkHasPiType' α V ⌜λ a => $P a a⌝} (h : mkHasDupPi' P hPa hPiPa hP)

  def mkDupPi (F : Q(Pi₂ $P)) : Q(Pi (λ a => $P a a)) := ⌜HasDupPi.dupPi $F⌝

end mkHasDupPi'

def mkHasDupPi.prop {α : _sort} {v : Level} {V : _Universe v} {p : α → α → V}
                    (P : α ⥤ α ⥤{p} _[V]) :
    α ⥤{λ a => p a a} _[V] :=
  DefFun.mk (mkHasDupPi'.prop α.α V.U P.inst)

def mkHasDupPi {α : _sort} {v : Level} {V : _Universe v} {p : α → α → V} (P : α ⥤ α ⥤{p} _[V])
               [hPa : mkHasQuantPiType P] [hPiPa : mkHasPiType (mkHasQuantPiType.piProp P)]
               [hP : mkHasPiType (mkHasDupPi.prop P)] :
    ClassExpr :=
  ⟨mkHasDupPi' P.inst hPa.h hPiPa.h hP.h⟩

namespace mkHasDupPi

  variable {α : _sort} {v : Level} {V : _Universe v} {p : α → α → V} {P : α ⥤ α ⥤{p} _[V]}
           [hPa : mkHasQuantPiType P] [hPiPa : mkHasPiType (mkHasQuantPiType.piProp P)]
           [hP : mkHasPiType (prop P)] [h : mkHasDupPi P]

  def mkDupPi (F : Pi₂ (mkHasQuantPiType.reflectProp₂ P)) :
      Pi (mkHasPiType.reflectProp (prop P)) :=
    mkHasDupPi'.mkDupPi h.h F

  instance reflect : HasDupPi (mkHasQuantPiType.reflectProp₂ P) := ⟨λ F => ⟨mkDupPi F⟩⟩

end mkHasDupPi


def mkHasPiSelfAppPi' {u uu uv : Level} {U : Q(Universe.{u, uu})} {V : Q(Universe.{u, uv})}
                      (hVU : mkHasUnivFunctors' V U) (A : Q($U)) (Q : Q($A → $V))
                      (hQ : mkHasPiType' (u := u) ⌜$A⌝ V Q)
                      (hQF : mkHasQuantPiType' ⌜Pi $Q ⥤ $A⌝ ⌜Pi $Q⌝ V ⌜λ F G => $Q (F G)⌝) :=
  ⌜HasPiSelfAppPi $Q⌝

namespace mkHasPiSelfAppPi'

  def prop {u uu uv : Level} {U : Q(Universe.{u, uu})} {V : Q(Universe.{u, uv})}
           (hVU : mkHasUnivFunctors' V U) (A : Q($U)) (Q : Q($A → $V))
           (hQ : mkHasPiType' (u := u) ⌜$A⌝ V Q) (F : Q(Pi $Q ⥤ $A)) :
      Q(Pi $Q → $V) :=
    ⌜λ G => $Q ($F G)⌝

  def prop₂ {u uu uv : Level} {U : Q(Universe.{u, uu})} {V : Q(Universe.{u, uv})}
            (hVU : mkHasUnivFunctors' V U) (A : Q($U)) (Q : Q($A → $V))
            (hQ : mkHasPiType' (u := u) ⌜$A⌝ V Q) :
      Q((Pi $Q ⥤ $A) → Pi $Q → $V) :=
    ⌜λ F G => $Q (F G)⌝

  variable {u uu uv : Level} {U : Q(Universe.{u, uu})} {V : Q(Universe.{u, uv})}
           {hVU : mkHasUnivFunctors' V U} {A : Q($U)} {Q : Q($A → $V)}
           {hQ : mkHasPiType' (u := u) ⌜$A⌝ V Q}
           {hQF : mkHasQuantPiType' ⌜Pi $Q ⥤ $A⌝ ⌜Pi $Q⌝ V ⌜λ F G => $Q (F G)⌝}
           (h : mkHasPiSelfAppPi' hVU A Q hQ hQF)

  def mkPiSelfAppPi (F : Q(Pi $Q ⥤ $A)) : Q(Pi (λ G => $Q ($F G))) :=
    ⌜HasPiSelfAppPi.piSelfAppPi $F⌝

end mkHasPiSelfAppPi'

def mkHasPiSelfAppPi.prop {u : Level} {U V : _Universe u} [hVU : mkHasUnivFunctors V U] {A : U}
                          {q : A → V} (Q : _⌈A⌉ ⥤{q} _[V]) [hQ : mkHasPiType Q] :
    _⌈Pi (mkHasPiType.reflectProp Q) ⥤ A⌉ ⥤ _⌈Pi (mkHasPiType.reflectProp Q)⌉
    ⥤{λ (F : Pi (mkHasPiType.reflectProp Q) ⥤ A) (G : Pi (mkHasPiType.reflectProp Q)) => q (F G)}
    _[V] :=
  DefFun₂.mk (λ F => ⟨mkHasPiSelfAppPi'.prop hVU.h A Q.inst hQ.h F⟩)
             (DefFun.mk (mkHasPiSelfAppPi'.prop₂ hVU.h A Q.inst hQ.h))

def mkHasPiSelfAppPi {u : Level} {U V : _Universe u} [hVU : mkHasUnivFunctors V U] {A : U}
                     {q : A → V} (Q : _⌈A⌉ ⥤{q} _[V]) [hQ : mkHasPiType Q]
                     [hQF : mkHasQuantPiType (mkHasPiSelfAppPi.prop Q)] :
    ClassExpr :=
  ⟨mkHasPiSelfAppPi' hVU.h A Q.inst hQ.h hQF.h⟩

namespace mkHasPiSelfAppPi

  variable {u : Level} {U V : _Universe u} [hVU : mkHasUnivFunctors V U] {A : U} {q : A → V}
           {Q : _⌈A⌉ ⥤{q} _[V]} [hQ : mkHasPiType Q]
           [hQF : mkHasQuantPiType (mkHasPiSelfAppPi.prop Q)] [h : mkHasPiSelfAppPi Q]

  instance (F : Pi (mkHasPiType.reflectProp' Q) ⥤ A) : mkHasPiType (DefFun₂.app (prop Q) F) :=
    inferInstance

  def mkPiSelfAppPi (F : Pi (mkHasPiType.reflectProp' Q) ⥤ A) :
      Pi (mkHasPiType.reflectProp' (DefFun₂.app (prop Q) F)) :=
    mkHasPiSelfAppPi'.mkPiSelfAppPi h.h F

  instance reflect : HasPiSelfAppPi (mkHasPiType.reflectProp' Q) :=
    ⟨λ F => ⟨mkPiSelfAppPi F⟩⟩

end mkHasPiSelfAppPi


def mkHasSubstPi' {u v vv w ww : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})}
                  {W : Q(Universe.{w, ww})} {P : Q($α → $V)} (hP : mkHasPiType' α V P)
                  (Q : Q(∀ a, $P a → $W)) (hQa : mkHasQuantDepPiType' α V P W Q)
                  (hPiQa : mkHasPiType' α W ⌜λ a => Pi ($Q a)⌝)
                  (hQaFa : mkHasQuantPiType' ⌜Pi $P⌝ α W ⌜λ F a => $Q a (F a)⌝) :=
  ⌜HasSubstPi $Q⌝

namespace mkHasSubstPi'

  def prop {u v vv w ww : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})} {P : Q($α → $V)}
           (hP : mkHasPiType' α V P) (W : Q(Universe.{w, ww})) (Q : Q(∀ a, $P a → $W))
           (F : Q(Pi $P)) :
      Q($α → $W) :=
    ⌜λ a => $Q a ($F a)⌝

  def prop₂ {u v vv w ww : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})} {P : Q($α → $V)}
            (hP : mkHasPiType' α V P) (W : Q(Universe.{w, ww})) (Q : Q(∀ a, $P a → $W)) :
      Q((Pi $P) → $α → $W) :=
    ⌜λ F a => $Q a (F a)⌝

  variable {u v vv w ww : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})}
           {W : Q(Universe.{w, ww})} {P : Q($α → $V)} {hP : mkHasPiType' α V P}
           {Q : Q(∀ a, $P a → $W)} {hQa : mkHasQuantDepPiType' α V P W Q}
           {hPiQa : mkHasPiType' α W ⌜λ a => Pi ($Q a)⌝}
           {hQaFa : mkHasQuantPiType' ⌜Pi $P⌝ α W ⌜λ F a => $Q a (F a)⌝}
           (h : mkHasSubstPi' hP Q hQa hPiQa hQaFa)

  def mkRevSubstPi (G : Q(Pi (λ a => Pi ($Q a)))) (F : Q(Pi $P)) : Q(Pi (λ a => $Q a ($F a))) :=
    ⌜HasSubstPi.revSubstPi $G $F⌝

end mkHasSubstPi'

def mkHasSubstPi.prop {α : _sort} {v w : Level} {V : _Universe v} {p : α → V} {P : α ⥤{p} _[V]}
                      [hP : mkHasPiType P] {W : _Universe w} {q : ∀ a, _⌈p a⌉ ⥤ _[W]}
                      (Q : DefPi (α := α) (V := _sort)
                                 (λ a => (_⌈(mkHasPiType.reflectProp P) a⌉ ⥤ _[W])) q) :
    _⌈Pi (mkHasPiType.reflectProp P)⌉ ⥤ α
    ⥤{λ (F : Pi (mkHasPiType.reflectProp P)) a => q a (F a)}
    _[W] :=
  DefFun₂.mk (λ F => ⟨mkHasSubstPi'.prop hP.h W.U Q.inst F⟩)
             (DefFun.mk (mkHasSubstPi'.prop₂ hP.h W.U Q.inst))

def mkHasSubstPi {α : _sort} {v w : Level} {V : _Universe v} {p : α → V} {P : α ⥤{p} _[V]}
                 [hP : mkHasPiType P] {W : _Universe w} {q : ∀ a, _⌈p a⌉ ⥤ _[W]}
                 (Q : DefPi (λ a => (_⌈(mkHasPiType.reflectProp P) a⌉ ⥤ _[W])) q)
                 [hQa : mkHasQuantDepPiType Q] [hPiQa : mkHasPiType (mkHasQuantDepPiType.piProp Q)]
                 [hQaFa : mkHasQuantPiType (mkHasSubstPi.prop Q)] :
    ClassExpr :=
  ⟨mkHasSubstPi' hP.h Q.inst hQa.h hPiQa.h hQaFa.h⟩

namespace mkHasSubstPi

  variable {α : _sort} {v w : Level} {V : _Universe v} {p : α → V} {P : α ⥤{p} _[V]}
           [hP : mkHasPiType P] {W : _Universe w} {q : ∀ a, _⌈p a⌉ ⥤ _[W]}
           {Q : DefPi (λ a => (_⌈(mkHasPiType.reflectProp P) a⌉ ⥤ _[W])) q}
           [hQa : mkHasQuantDepPiType Q] [hPiQa : mkHasPiType (mkHasQuantDepPiType.piProp Q)]
           [hQaFa : mkHasQuantPiType (mkHasSubstPi.prop Q)] [h : mkHasSubstPi Q]

  instance (F : Pi (mkHasPiType.reflectProp P)) : mkHasPiType (DefFun₂.app (prop Q) F) :=
    inferInstance

  instance (a : α) : HasPiType ((mkHasQuantDepPiType.reflectProp₂ Q) a) :=
    mkHasPiType.reflect (mkHasQuantDepPiType.appProp Q a)

  -- This somehow confuses type class instance search. So at the moment we need to omit the
  -- `HasSubstPi` instance and just use `mkRevSubstPi` directly.
  --instance : HasPiType (λ a => Pi ((mkHasQuantDepPiType.reflectProp₂ Q) a)) :=
  --  mkHasPiType.reflect (mkHasQuantDepPiType.piProp Q)

  def mkRevSubstPi (G : Pi (mkHasPiType.reflectProp (mkHasQuantDepPiType.piProp Q)))
                   (F : Pi (mkHasPiType.reflectProp P)) :
      Pi (mkHasPiType.reflectProp (DefFun₂.app (prop Q) F)) :=
    mkHasSubstPi'.mkRevSubstPi h.h G F

  --instance reflect : HasSubstPi (P := mkHasPiType.reflectProp P)
  --                              (mkHasQuantDepPiType.reflectProp₂ Q) where
  --  defSubstPi F G := ⟨mkRevSubstPi G F⟩

end mkHasSubstPi
