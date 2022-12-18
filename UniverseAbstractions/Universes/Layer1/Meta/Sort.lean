import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedFunctors
import UniverseAbstractions.Meta.Helpers
import UniverseAbstractions.Universes.Layer1.Meta.ExprUniverse



namespace UniverseAbstractions.Layer1.Meta

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 20000
set_option linter.unusedVariables false

open Lean Elab Tactic Qq UniverseAbstractions.Meta
     HasPiType HasFunctors



-- A meta-level universe of all object-level types and instances. This mostly just provides an
-- overly complicated mechanism for defining object-level (dependent) functions as functors on the
-- meta level.
--
-- In theory, we can compose these meta-level functors to build complex object-level functions from
-- simpler ones, but in practice we avoid this because the resulting functions tend to look ugly
-- (e.g. when looking at them in the infoview).
--
-- A useful use case, though, is to attach a meta-level function to an object-level function via
-- `DefInst`. This way, we can easily specify that the result of a particular object-level
-- function application should always be defeq to the result of executing a specific meta-level
-- function. We extensively make use of this both in this file and in `Meta/Reflect/Functors.lean`,
-- by reflecting object-level properties as meta-level functors with an attached meta-level
-- function/property.

def _sort := exprUniverse id

namespace _sort

  def mk {u : Level} (α : ⌜Sort u⌝) : _sort := ⟨α⟩

  instance inhabited (α : _sort) : Inhabited α := _Sort.inhabited α

  def mkFreshMVar : MetaM _sort := _Sort.mkFreshMVar
  def instantiate (α : _sort) : MetaM _sort := _Sort.instantiate α
  def mkFreshInstMVar {α : _sort} : MetaM α := _Sort.mkFreshInstMVar (α := α)
  def instantiateInstMVars {α α' : _sort} (a : α) : MetaM α' :=
    _Sort.instantiateInstMVars (α := α) (α' := α') a

  def elaborate' {α : _sort} (a : Syntax) : TermElabM α := _Sort.elaborate' (α := α) a
  def elaborate  {α : _sort} (a : Syntax) : TacticM α := _Sort.elaborate (α := α) a

  def mkSortType (u : Level) : _sort := mk (u := mkLevelSucc u) ⌜Sort u⌝
  def mkSortType.fromSort (α : _sort) : mkSortType α.u := α.α
  def mkSortType.toSort {u : Level} (α : mkSortType u) : _sort := mk (u := u) α
  instance (α : _sort) : CoeDep _sort α (mkSortType α.u) := ⟨mkSortType.fromSort α⟩
  instance {u : Level} : Coe (mkSortType u) _sort := ⟨mkSortType.toSort⟩
  instance {u : Level} : CoeSort (mkSortType u) Type := ⟨λ α => α⟩

  def hasPiType'' {α : _sort} {v : Level} {p : α → _sort} (P : Q($α.α → Sort v)) :
      HasType _sort (∀ a, p a) where
    A     := ⟨mkForAll       α.α P⟩
    hElim := ⟨mkForAll.mkApp α.α P⟩

  def hasPiType' {α : _sort} {v : Level} {p : α → mkSortType v} (P : Q($α.α → Sort v)) :
      HasType _sort (∀ a, mkSortType.toSort (p a)) :=
    hasPiType'' P

  def funProp (α β : _sort) : Q($α.α → Sort $β.u) := ⌜λ _ => $β.α⌝
  def funProp₂ (α β γ : _sort) : Q($α.α → $β.α → Sort $γ.u) := ⌜λ _ _ => $γ.α⌝

  instance hasFunType (α β : _sort) : HasType _sort (α → β) := hasPiType' (funProp α β)

  instance hasFunctors (α : _sort) : HasFunctors α _sort := ⟨⟩

  def funType (α β : _sort) : mkSortType (mkLevelIMax α.u β.u) := mkSortType.fromSort (α ⥤ β)
  def funType' {u v : Level} (α : mkSortType u) (β : mkSortType v) : mkSortType (mkLevelIMax u v) :=
    funType α β

  instance hasUnivFunctors : HasUnivFunctors _sort _sort := ⟨⟩

  def defFunToProp {α : _sort} {v : Level} {p : α → mkSortType v} (P : [α ⥤ mkSortType v]_{p}) :
      α → _sort :=
    λ a => p a

  @[reducible] def funToProp {α : _sort} {v : Level} (P : α ⥤ mkSortType v) :
      α → _sort :=
    defFunToProp (HasFunctors.defAppFun P)

  def defFunToProp₂ {α β : _sort} {v : Level} {p : α → β → mkSortType v}
                    (P : [α ⥤ β ⥤ mkSortType v]__{p}) :
      α → β → _sort :=
    λ a b => p a b

  def funToProp₂ {α β : _sort} {v : Level} (P : α ⥤ β ⥤ mkSortType v) :
      α → β → _sort :=
    defFunToProp₂ (HasFunctors.defAppFun₂ P)

  instance hasPiType {α : _sort} {v : Level} {p : α → mkSortType v} (P : [α ⥤ mkSortType v]_{p}) :
      HasType _sort (∀ a, (defFunToProp P) a) :=
    hasPiType' P

  instance {α β : _sort} {v : Level} {p : α → β → mkSortType v} (P : [α ⥤ β ⥤ mkSortType v]__{p})
           (a : α) :
      HasType _sort (∀ b, (defFunToProp₂ P) a b) :=
    hasPiType (P a)

  instance {α β : _sort} {v : Level} {p : α → β → mkSortType v} (P : [α ⥤ β ⥤ mkSortType v]__{p}) :
      HasType _sort (∀ a, Pi ((defFunToProp₂ P) a)) :=
    let P' : Q($α.α → $β.α → Sort v) := P
    hasPiType ⌜λ a => ∀ b, $P' a b⌝

  instance {α β : _sort} {v : Level} {p : α → β → mkSortType v} (P : [α ⥤ β ⥤ mkSortType v]__{p})
           (b : β) :
      HasType _sort (∀ a, (defFunToProp₂ P) a b) :=
    let P' : Q($α.α → $β.α → Sort v) := P
    let b' : Q($β.α) := b
    hasPiType ⌜λ a => $P' a $b'⌝

  instance {α β : _sort} {v : Level} {p : α → β → mkSortType v} (P : [α ⥤ β ⥤ mkSortType v]__{p}) :
      HasType _sort (∀ b, [∀ a, (defFunToProp₂ P) a b | _sort]) :=
    let P' : Q($α.α → $β.α → Sort v) := P
    hasPiType ⌜λ b => ∀ a, $P' a b⌝

  instance {α : _sort} {v w : Level} {p : α → mkSortType v} (P : [α ⥤ mkSortType v]_{p}) :
      HasType _sort (∀ a, (defFunToProp P) a ⥤ mkSortType w) :=
    let P' : Q($α.α → Sort v) := P
    let Q : Q($α.α → Sort (max v (w + 1))) := ⌜λ a => ($P' a → Sort w)⌝
    hasPiType'' Q

  def defPiToProp {α : _sort} {v w : Level} {p : α → mkSortType v} {P : [α ⥤ mkSortType v]_{p}}
                  {q : ∀ a, p a → mkSortType w} {qa : ∀ a, [p a ⥤ mkSortType w]_{q a}}
                  (Q : [∀ a, (defFunToProp P) a ⥤ mkSortType w | _sort]_{qa}) :
      ∀ a, (defFunToProp P) a → _sort :=
    λ a b => q a b

  instance hasIdFun (α : _sort) : HasIdFun α := ⟨mkIdFun α.α⟩

  instance hasPiAppFun {α : _sort} {v : Level} {p : α → mkSortType v} (P : [α ⥤ mkSortType v]_{p}) :
      HasPiAppFun (defFunToProp P) :=
    ⟨mkPiAppFun (v := v) α.α P⟩

  local instance {α : _sort} {v : Level} {p : α → mkSortType v} (P : [α ⥤ mkSortType v]_{p}) :
      HasType _sort (∀ a, Pi (defFunToProp P) ⥤ (defFunToProp P) a) :=
    let P' : Q($α.α → Sort v) := P
    let Q : Q($α.α → Sort (imax (imax $α.u v) v)) := ⌜λ a => ((∀ a', $P' a') → $P' a)⌝
    hasPiType' Q

  instance hasPiAppFunPi {α : _sort} {v : Level} {p : α → mkSortType v} (P : [α ⥤ mkSortType v]_{p}) :
      HasPiAppFunPi (defFunToProp P) :=
    ⟨mkPiAppFunPi (v := v) α.α P⟩

  instance hasSwapPi {α β : _sort} {v : Level} {p : α → β → mkSortType v}
                     (P : [α ⥤ β ⥤ mkSortType v]__{p}) :
      HasSwapPi (defFunToProp₂ P) :=
    ⟨mkSwapPi (v := v) α.α β.α P⟩

  instance hasSwapPi₂ {α β : _sort} {v : Level} {p : α → β → mkSortType v}
                      (P : [α ⥤ β ⥤ mkSortType v]__{p}) :
      HasSwapPi₂ (defFunToProp₂ P) :=
    ⟨mkSwapPi₂ (v := v) α.α β.α P⟩

  instance hasSwapPiFun {α β : _sort} {v : Level} {p : α → β → mkSortType v}
                        (P : [α ⥤ β ⥤ mkSortType v]__{p}) :
      HasSwapPiFun (defFunToProp₂ P) :=
    ⟨mkSwapPiFun (v := v) α.α β.α P⟩

  instance (α β : _sort) {w : Level} {q : β → mkSortType w} (Q : [β ⥤ mkSortType w]_{q}) (f : α ⥤ β) :
      HasType _sort (∀ a, (defFunToProp Q) (f a)) :=
    let Q' : Q($β.α → Sort w) := Q
    let f' : Q($α.α → $β.α) := f
    hasPiType ⌜λ a => $Q' ($f' a)⌝

  instance hasCompFunPi (α β : _sort) {w : Level} {q : β → mkSortType w} (Q : [β ⥤ mkSortType w]_{q}) :
      HasCompFunPi α (defFunToProp Q) :=
    ⟨mkCompFunPi (w := w) α.α β.α Q⟩

  instance (α β : _sort) {w : Level} {q : β → mkSortType w} (Q : [β ⥤ mkSortType w]_{q}) :
      HasType _sort (∀ f : α ⥤ β, [∀ a, (defFunToProp Q) (f a) | _sort]) :=
    let Q' : Q($β.α → Sort w) := Q
    let R : Q(($α.α → $β.α) → Sort (imax $α.u w)) := ⌜λ f => ∀ a, $Q' (f a)⌝
    hasPiType R

  instance hasRevCompFunPi₂ (α β : _sort) {w : Level} {q : β → mkSortType w}
                            (Q : [β ⥤ mkSortType w]_{q}) :
      HasRevCompFunPi₂ α (defFunToProp Q) :=
    ⟨mkRevCompFunPi₂ (w := w) α.α β.α Q⟩

  instance hasRevCompFunPiFun (α β : _sort) {w : Level} {q : β → mkSortType w}
                              (Q : [β ⥤ mkSortType w]_{q}) :
      HasRevCompFunPiFun α (defFunToProp Q) :=
    ⟨mkRevCompFunPiFun (w := w) α.α β.α Q⟩

  instance hasConstPi (α β : _sort) : HasConstPi α β :=
    ⟨mkConstPi α.α β.α⟩

  instance hasConstPiFun (α β : _sort) : HasConstPiFun α β :=
    ⟨mkConstPiFun α.α β.α⟩

  instance {α : _sort} {v : Level} {p : α → α → mkSortType v} (P : [α ⥤ α ⥤ mkSortType v]__{p}) :
      HasType _sort (∀ a, (defFunToProp₂ P) a a) :=
    let P' : Q($α.α → $α.α → Sort v) := P
    hasPiType ⌜λ a => $P' a a⌝

  instance hasDupPi {α : _sort} {v : Level} {p : α → α → mkSortType v}
                    (P : [α ⥤ α ⥤ mkSortType v]__{p}) :
      HasDupPi (defFunToProp₂ P) :=
    ⟨mkDupPi (v := v) α.α P⟩

  instance hasDupPiFun {α : _sort} {v : Level} {p : α → α → mkSortType v}
                       (P : [α ⥤ α ⥤ mkSortType v]__{p}) :
      HasDupPiFun (defFunToProp₂ P) :=
    ⟨mkDupPiFun (v := v) α.α P⟩

  instance hasPiSelfAppPi {α : _sort} {v : Level} {q : α → mkSortType v}
                          (Q : [α ⥤ mkSortType v]_{q}) :
      HasPiSelfAppPi (defFunToProp Q) :=
    ⟨mkPiSelfAppPi (v := v) α.α Q⟩

  instance hasPiSelfAppPi₂ {α : _sort} {v : Level} {q : α → mkSortType v}
                           (Q : [α ⥤ mkSortType v]_{q}) :
      HasPiSelfAppPi₂ (defFunToProp Q) :=
    ⟨mkPiSelfAppPi₂ (v := v) α.α Q⟩

  instance {α : _sort} {v w : Level} {p : α → mkSortType v} (P : [α ⥤ mkSortType v]_{p})
           {q : ∀ a, p a → mkSortType w} {qa : ∀ a, [p a ⥤ mkSortType w]_{q a}}
           (Q : [∀ a, (defFunToProp P) a ⥤ mkSortType w | _sort]_{qa}) (a : α) :
      HasType _sort (∀ b, (defPiToProp Q) a b) :=
    hasPiType (qa a)

  def substProp₁' {u v w : Level} (α : Q(Sort u)) (P : Q($α → Sort v)) (Q : Q(∀ a, $P a → Sort w)) :
      Q($α → Sort (imax v w)) :=
    ⌜λ a => ∀ b, $Q a b⌝

  def defSubstProp₁ {α : _sort} {v w : Level} {p : α → mkSortType v} {P : [α ⥤ mkSortType v]_{p}}
                    {q : ∀ a, p a → mkSortType w} {qa : ∀ a, [p a ⥤ mkSortType w]_{q a}}
                    (Q : [∀ a, (defFunToProp P) a ⥤ mkSortType w | _sort]_{qa}) :
      [α ⥤ mkSortType (mkLevelIMax v w)]_{λ a => (Pi ((defPiToProp Q) a)).α} :=
    substProp₁' (v := v) (w := w) α.α P Q

  instance {α : _sort} {v w : Level} {p : α → mkSortType v} {P : [α ⥤ mkSortType v]_{p}}
           {q : ∀ a, p a → mkSortType w} {qa : ∀ a, [p a ⥤ mkSortType w]_{q a}}
           (Q : [∀ a, (defFunToProp P) a ⥤ mkSortType w | _sort]_{qa}) :
      HasType _sort (∀ a, Pi ((defPiToProp Q) a)) :=
    hasPiType (defSubstProp₁ Q)

  def substProp₂' {u v w : Level} (α : Q(Sort u)) (P : Q($α → Sort v)) (Q : Q(∀ a, $P a → Sort w))
                  (f : Q(∀ a, $P a)) :
      Q($α → Sort w) :=
    ⌜λ a => $Q a ($f a)⌝

  def defSubstProp₂ {α : _sort} {v w : Level} {p : α → mkSortType v} {P : [α ⥤ mkSortType v]_{p}}
                    {q : ∀ a, p a → mkSortType w} {qa : ∀ a, [p a ⥤ mkSortType w]_{q a}}
                    (Q : [∀ a, (defFunToProp P) a ⥤ mkSortType w | _sort]_{qa})
                    (f : Pi (defFunToProp P)) :
      [α ⥤ mkSortType w]_{λ a => q a (f a)} :=
    substProp₂' (v := v) (w := w) α.α P Q f

  instance {α : _sort} {v w : Level} {p : α → mkSortType v} {P : [α ⥤ mkSortType v]_{p}}
           {q : ∀ a, p a → mkSortType w} {qa : ∀ a, [p a ⥤ mkSortType w]_{q a}}
           (Q : [∀ a, (defFunToProp P) a ⥤ mkSortType w | _sort]_{qa})
           (f : Pi (defFunToProp P)) :
      HasType _sort (∀ a, (defPiToProp Q) a (f a)) :=
    hasPiType (defSubstProp₂ Q f)

  instance hasSubstPi {α : _sort} {v w : Level} {p : α → mkSortType v} {P : [α ⥤ mkSortType v]_{p}}
                      {q : ∀ a, p a → mkSortType w} {qa : ∀ a, [p a ⥤ mkSortType w]_{q a}}
                      (Q : [∀ a, (defFunToProp P) a ⥤ mkSortType w | _sort]_{qa}) :
      HasSubstPi (defPiToProp Q) :=
    ⟨mkSubstPi (v := v) (w := w) α.α P Q⟩

  def substProp₃' {u v w : Level} (α : Q(Sort u)) (P : Q($α → Sort v)) (Q : Q(∀ a, $P a → Sort w)) :
      Q((∀ a, $P a) → Sort (imax u w)) :=
    ⌜λ f => ∀ a, $Q a (f a)⌝

  def defSubstProp₃ {α : _sort} {v w : Level} {p : α → mkSortType v} {P : [α ⥤ mkSortType v]_{p}}
                    {q : ∀ a, p a → mkSortType w} {qa : ∀ a, [p a ⥤ mkSortType w]_{q a}}
                    (Q : [∀ a, (defFunToProp P) a ⥤ mkSortType w | _sort]_{qa}) :
      [Pi (defFunToProp P) ⥤ mkSortType (mkLevelIMax α.u w)]_{
       λ f : Pi (defFunToProp P) => [∀ a, (defPiToProp Q) a (f a) | _sort].α} :=
    substProp₃' (v := v) (w := w) α.α P Q

  instance {α : _sort} {v w : Level} {p : α → mkSortType v} {P : [α ⥤ mkSortType v]_{p}}
           {q : ∀ a, p a → mkSortType w} {qa : ∀ a, [p a ⥤ mkSortType w]_{q a}}
           (Q : [∀ a, (defFunToProp P) a ⥤ mkSortType w | _sort]_{qa}) :
      HasType _sort (∀ f : Pi (defFunToProp P), [∀ a, (defPiToProp Q) a (f a) | _sort]) :=
    hasPiType (defSubstProp₃ Q)

  instance hasRevSubstPi₂ {α : _sort} {v w : Level} {p : α → mkSortType v} {P : [α ⥤ mkSortType v]_{p}}
                          {q : ∀ a, p a → mkSortType w} {qa : ∀ a, [p a ⥤ mkSortType w]_{q a}}
                          (Q : [∀ a, (defFunToProp P) a ⥤ mkSortType w | _sort]_{qa}) :
      HasRevSubstPi₂ (defPiToProp Q) :=
    ⟨mkRevSubstPi₂ (v := v) (w := w) α.α P Q⟩

  instance hasRevSubstPiFun {α : _sort} {v w : Level} {p : α → mkSortType v}
                            {P : [α ⥤ mkSortType v]_{p}} {q : ∀ a, p a → mkSortType w}
                            {qa : ∀ a, [p a ⥤ mkSortType w]_{q a}}
                            (Q : [∀ a, (defFunToProp P) a ⥤ mkSortType w | _sort]_{qa}) :
      HasRevSubstPiFun (defPiToProp Q) :=
    ⟨mkRevSubstPiFun (v := v) (w := w) α.α P Q⟩

  instance hasExternalLinearLogic (α : _sort) : HasExternalLinearLogic α _sort where
    defRevAppFun₂  β   := mkPiAppFunPi α.α (funProp α β)
    defRevCompFun₃ β γ := mkRevCompFunPiFun α.α β.α (funProp β γ)

  instance hasExternalSubLinearLogic (α : _sort) : HasExternalSubLinearLogic α _sort where
    defConstFun₂ β := mkConstPiFun α.α β.α

  instance hasExternalAffineLogic (α : _sort) : HasExternalAffineLogic α _sort := ⟨⟩

  instance hasExternalNonLinearLogic (α : _sort) : HasExternalNonLinearLogic α _sort where
    defDupFun₂ β := mkDupPiFun α.α (funProp₂ α α β)

  instance hasExternalFullLogic (α : _sort) : HasExternalFullLogic α _sort := ⟨⟩

  instance hasLinearLogic : HasLinearLogic _sort where
    defIdFun       α     := mkIdFun α.α
    defRevAppFun₂  α β   := mkPiAppFunPi α.α (funProp α β)
    defRevCompFun₃ α β γ := mkRevCompFunPiFun α.α β.α (funProp β γ)

  instance hasSubLinearLogic : HasSubLinearLogic _sort where
    defConstFun₂ α β := mkConstPiFun α.α β.α

  instance hasAffineLogic : HasAffineLogic _sort := ⟨⟩

  instance hasNonLinearLogic : HasNonLinearLogic _sort where
    defDupFun₂ α β := mkDupPiFun α.α (funProp₂ α α β)

  instance hasFullLogic : HasFullLogic _sort := ⟨⟩

end _sort
