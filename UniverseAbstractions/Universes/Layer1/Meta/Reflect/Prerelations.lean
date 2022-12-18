import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations
import UniverseAbstractions.Universes.Layer1.Meta.Reflect.Universes
import UniverseAbstractions.Universes.Layer1.Meta.Reflect.Functors



namespace UniverseAbstractions.Layer1.Meta

set_option autoImplicit false

open Lean Lean.Meta Qq UniverseAbstractions.Meta Prerelation



def _Prerelation {u v : Level} (α : ⌜Sort u⌝) (V : _Universe v) := ⌜Prerelation $α $V.U⌝

namespace _Prerelation

  variable {u v : Level} {α : ⌜Sort u⌝} {V : _Universe v} [hV : mkHasLinearLogic V]
           (R : _Prerelation α V)

  def reflect : Prerelation α V := λ a b => ⌜$R $a $b⌝

  def mkHasRefl  : ClassExpr := let _ := hV.h; ⟨⌜HasRefl  $R⌝⟩
  def mkHasSymm  : ClassExpr := let _ := hV.h; ⟨⌜HasSymm  $R⌝⟩
  def mkHasTrans : ClassExpr := let _ := hV.h; ⟨⌜HasTrans $R⌝⟩

  instance mkHasRefl.reflect [h : mkHasRefl R] : HasRefl (reflect R) :=
    let _ := h.h
    ⟨λ a => ⌜HasRefl.refl (R := $R) $a⌝⟩

  instance mkHasSymm.reflect [h : mkHasSymm R] : HasSymm (reflect R) :=
    let _ := h.h
    ⟨λ a b => ⌜HasSymm.symmFun (R := $R) $a $b⌝⟩

  instance mkHasTrans.reflect [h : mkHasTrans R] : HasTrans (reflect R) :=
    let _ := h.h
    ⟨λ a b c => ⌜HasTrans.transFun₂ (R := $R) $a $b $c⌝⟩

  def mkIsPreorder : ClassExpr := let _ := hV.h; ⟨⌜IsPreorder $R⌝⟩

  namespace mkIsPreorder

    variable [h : mkIsPreorder R]

    instance : mkHasRefl  R := let _ := h.h; ⟨⌜IsPreorder.toHasRefl⌝⟩
    instance : mkHasTrans R := let _ := h.h; ⟨⌜IsPreorder.toHasTrans⌝⟩

    instance reflect : IsPreorder (reflect R) := ⟨⟩

  end mkIsPreorder

  def mkIsEquivalence : ClassExpr := let _ := hV.h; ⟨⌜IsEquivalence $R⌝⟩

  namespace mkIsEquivalence

    variable [h : mkIsEquivalence R]

    instance : mkIsPreorder R := let _ := h.h; ⟨⌜IsEquivalence.toIsPreorder⌝⟩
    instance : mkHasSymm    R := let _ := h.h; ⟨⌜IsEquivalence.toHasSymm⌝⟩

    instance reflect : IsEquivalence (reflect R) := ⟨⟩

  end mkIsEquivalence

end _Prerelation
