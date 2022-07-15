import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedFunctors
import UniverseAbstractions.Meta.Helpers
import UniverseAbstractions.Universes.Layer1.Meta.ExprUniverse



namespace UniverseAbstractions.Layer1.Meta

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 5000
set_option linter.unusedVariables false

open Lean Elab Tactic Qq UniverseAbstractions.Meta
     Universe HasPiType HasFunctors



-- A meta-level universe of all object-level types and instances. This mostly just provides an
-- overly complicated mechanism for defining object-level (dependent) functions as functors on the
-- meta level.
--
-- In theory, we can compose these meta-level functors to build complex object-level functions from
-- simpler ones, but in practice we avoid this because the resulting functions tend to look ugly
-- (e.g. when looking at them in the infoview).
--
-- A useful use case, though, is to attach a meta-level function to an object-level function via
-- `DefPi`/`DefFun`. This way, we can easily specify that the result of a particular object-level
-- function application should always be defeq to the result of executing a specific meta-level
-- function. We extensively make use of this both in this file and in `Meta/Reflect/Functors.lean`,
-- by reflecting object-level properties as meta-level `DefFun`s, which in turn enables us to
-- interpret the meta-level function belonging to the `DefFun` as a meta-level property.

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

  -- When using this, make sure that `a` is defeq to what `a'` specifies.
  def defInst {α : Type} {A : DefType _sort α} {a' : α} (a : A.A) : DefType.DefInst A a' := ⟨a⟩

  def mkSortType (u : Level) : _sort := mk (u := mkLevelSucc u) ⌜Sort u⌝
  def mkSortType.fromSort (α : _sort) : mkSortType α.u := α.α
  def mkSortType.toSort {u : Level} (α : mkSortType u) : _sort := mk (u := u) α
  instance (α : _sort) : CoeDep _sort α (mkSortType α.u) := ⟨mkSortType.fromSort α⟩
  instance {u : Level} : Coe (mkSortType u) _sort := ⟨mkSortType.toSort⟩
  instance {u : Level} : CoeSort (mkSortType u) Type := ⟨λ α => α⟩

  def hasPiType'' {α : _sort} {v : Level} {p : α → _sort} (P : Q($α.α → Sort v)) :
      HasPiType p where
    defPiType := { A    := ⟨mkForAll α.α P⟩,
                   elim := λ f a => mkForAll.mkApp α.α P f a }

  def hasPiType' {α : _sort} {v : Level} {p : α → mkSortType v} (P : Q($α.α → Sort v)) :
      HasPiType (λ a => mkSortType.toSort (p a)) :=
    hasPiType'' P

  instance hasFunPi (α β : _sort) : HasPiType (Function.const α β) :=
    hasPiType' ⌜λ _ => $β.α⌝

  instance hasFunctors (α β : _sort) : HasFunctors α β := ⟨⟩

  def funType (α β : _sort) : mkSortType (mkLevelIMax α.u β.u) := mkSortType.fromSort (α ⥤ β)
  def funType' {u v : Level} (α : mkSortType u) (β : mkSortType v) : mkSortType (mkLevelIMax u v) :=
    funType α β

  instance hasUnivFunctors : HasUnivFunctors _sort _sort := ⟨⟩

  def defFunToProp {α : _sort} {v : Level} {p : α → mkSortType v} (P : α ⥤{p} mkSortType v) :
      α → _sort :=
    λ a => p a

  @[reducible] def funToProp {α : _sort} {v : Level} (P : α ⥤ mkSortType v) : α → _sort :=
    defFunToProp (DefFun.defAppFun P)

  def defFunToProp₂ {α β : _sort} {v : Level} {p : α → β → mkSortType v}
                    (P : α ⥤ β ⥤{p} mkSortType v) :
      α → β → _sort :=
    λ a b => p a b

  @[reducible] def funToProp₂ {α β : _sort} {v : Level} {p : α → β → mkSortType v}
                              (P : α ⥤ β ⥤ mkSortType v) :
      α → β → _sort :=
    defFunToProp₂ (DefFun₂.defAppFun P)

  instance hasPiType {α : _sort} {v : Level} {p : α → mkSortType v} (P : α ⥤{p} mkSortType v) :
      HasPiType (defFunToProp P) :=
    hasPiType' P.inst

  instance {α : _sort} {v : Level} {p : α → mkSortType v} (P : α ⥤{p} mkSortType v) :
      HasPiType (λ a => (defFunToProp P) a) :=
    hasPiType P

  instance {α β : _sort} {v : Level} {p : α → β → mkSortType v} (P : α ⥤ β ⥤{p} mkSortType v)
           (a : α) :
      HasPiType ((defFunToProp₂ P) a) :=
    hasPiType (P.app a)

  instance {α β : _sort} {v : Level} {p : α → β → mkSortType v} (P : α ⥤ β ⥤{p} mkSortType v) :
      HasPiType (λ a => Pi ((defFunToProp₂ P) a)) :=
    let P' : Q($α.α → $β.α → Sort v) := P.inst
    hasPiType ⟨⌜λ a => ∀ b, $P' a b⌝⟩

  instance {α β : _sort} {v : Level} {p : α → β → mkSortType v} (P : α ⥤ β ⥤{p} mkSortType v)
           (b : β) :
      HasPiType (λ a => (defFunToProp₂ P) a b) :=
    let P' : Q($α.α → $β.α → Sort v) := P.inst
    let b' : Q($β.α) := b
    hasPiType ⟨⌜λ a => $P' a $b'⌝⟩

  instance {α β : _sort} {v : Level} {p : α → β → mkSortType v} (P : α ⥤ β ⥤{p} mkSortType v) :
      HasPiType (λ b => Pi (λ a => (defFunToProp₂ P) a b)) :=
    let P' : Q($α.α → $β.α → Sort v) := P.inst
    hasPiType ⟨⌜λ b => ∀ a, $P' a b⌝⟩

  instance {α : _sort} {v w : Level} {p : α → mkSortType v} (P : α ⥤{p} mkSortType v) :
      HasPiType (λ a => ((defFunToProp P) a ⥤ mkSortType w)) :=
    let P' : Q($α.α → Sort v) := P.inst
    let Q : Q($α.α → Sort (max v (w + 1))) := ⌜λ a => ($P' a → Sort w)⌝
    hasPiType'' Q

  def defPiToProp {α : _sort} {v w : Level} {p : α → mkSortType v} {P : α ⥤{p} mkSortType v}
                  {q : ∀ a, p a → mkSortType w} {qa : ∀ a, p a ⥤{q a} mkSortType w}
                  (Q : DefPi (λ a => ((defFunToProp P) a ⥤ mkSortType w)) (λ a => qa a)) :
      ∀ a, (defFunToProp P) a → _sort :=
    λ a b => q a b

  instance hasIdFun (α : _sort) : HasIdFun α := ⟨⟨mkIdFun α.α⟩⟩

  instance hasPiAppFun {α : _sort} {v : Level} {p : α → mkSortType v} (P : α ⥤{p} mkSortType v) :
      HasPiAppFun (defFunToProp P) :=
    ⟨λ a => ⟨mkPiAppFun (v := v) α.α P.inst a⟩⟩

  instance {α : _sort} {v : Level} {p : α → mkSortType v} (P : α ⥤{p} mkSortType v) :
      HasPiType (λ a => (Pi (defFunToProp P) ⥤ (defFunToProp P) a)) :=
    let P' : Q($α.α → Sort v) := P.inst
    let Q : Q($α.α → Sort (imax (imax $α.u v) v)) := ⌜λ a => ((∀ a', $P' a') → $P' a)⌝
    hasPiType' Q

  instance hasPiAppFunPi {α : _sort} {v : Level} {p : α → mkSortType v} (P : α ⥤{p} mkSortType v) :
      HasPiAppFunPi (defFunToProp P) :=
    ⟨⟨mkPiAppFunPi (v := v) α.α P.inst⟩⟩

  instance hasSwapPi {α β : _sort} {v : Level} {p : α → β → mkSortType v}
                     (P : α ⥤ β ⥤{p} mkSortType v) :
      HasSwapPi (defFunToProp₂ P) :=
    ⟨λ f b => ⟨mkSwapPi (v := v) α.α β.α P.inst f b⟩⟩

  instance hasSwapPi₂ {α β : _sort} {v : Level} {p : α → β → mkSortType v}
                      (P : α ⥤ β ⥤{p} mkSortType v) :
      HasSwapPi₂ (defFunToProp₂ P) :=
    ⟨λ f => ⟨mkSwapPi₂ (v := v) α.α β.α P.inst f⟩⟩

  instance hasSwapPiFun {α β : _sort} {v : Level} {p : α → β → mkSortType v}
                        (P : α ⥤ β ⥤{p} mkSortType v) :
      HasSwapPiFun (defFunToProp₂ P) :=
    ⟨⟨mkSwapPiFun (v := v) α.α β.α P.inst⟩⟩

  instance (α β : _sort) {w : Level} {q : β → mkSortType w} (Q : β ⥤{q} mkSortType w) (f : α ⥤ β) :
      HasPiType (λ a => (defFunToProp Q) (f a)) :=
    let Q' : Q($β.α → Sort w) := Q.inst
    let f' : Q($α.α → $β.α) := f
    hasPiType ⟨⌜λ a => $Q' ($f' a)⌝⟩

  instance hasCompFunPi (α β : _sort) {w : Level} {q : β → mkSortType w} (Q : β ⥤{q} mkSortType w) :
      HasCompFunPi α (defFunToProp Q) :=
    ⟨λ f g => ⟨mkCompFunPi (w := w) α.α β.α Q.inst f g⟩⟩

  instance (α β : _sort) {w : Level} {q : β → mkSortType w} (Q : β ⥤{q} mkSortType w) :
      HasPiType (λ (f : α ⥤ β) => Pi (λ a => (defFunToProp Q) (f a))) :=
    let Q' : Q($β.α → Sort w) := Q.inst
    let R : Q(($α.α → $β.α) → Sort (imax $α.u w)) := ⌜λ f => ∀ a, $Q' (f a)⌝
    hasPiType ⟨R⟩

  instance hasRevCompFunPi₂ (α β : _sort) {w : Level} {q : β → mkSortType w}
                            (Q : β ⥤{q} mkSortType w) :
      HasRevCompFunPi₂ α (defFunToProp Q) :=
    ⟨λ g => ⟨mkRevCompFunPi₂ (w := w) α.α β.α Q.inst g⟩⟩

  instance hasRevCompFunPiFun (α β : _sort) {w : Level} {q : β → mkSortType w}
                              (Q : β ⥤{q} mkSortType w) :
      HasRevCompFunPiFun α (defFunToProp Q) :=
    ⟨⟨mkRevCompFunPiFun (w := w) α.α β.α Q.inst⟩⟩

  instance hasConstPi (α β : _sort) : HasConstPi α β :=
    ⟨λ b => ⟨mkConstFun α.α β.α b⟩⟩

  instance hasConstPiFun (α β : _sort) : HasConstPiFun α β :=
    ⟨⟨mkConstFun₂ α.α β.α⟩⟩

  instance {α : _sort} {v : Level} {p : α → α → mkSortType v} (P : α ⥤ α ⥤{p} mkSortType v) :
      HasPiType (λ a => (defFunToProp₂ P) a a) :=
    let P' : Q($α.α → $α.α → Sort v) := P.inst
    hasPiType ⟨⌜λ a => $P' a a⌝⟩

  instance hasDupPi {α : _sort} {v : Level} {p : α → α → mkSortType v}
                    (P : α ⥤ α ⥤{p} mkSortType v) :
      HasDupPi (defFunToProp₂ P) :=
    ⟨λ f => ⟨mkDupPi (v := v) α.α P.inst f⟩⟩

  instance hasDupPiFun {α : _sort} {v : Level} {p : α → α → mkSortType v}
                       (P : α ⥤ α ⥤{p} mkSortType v) :
      HasDupPiFun (defFunToProp₂ P) :=
    ⟨⟨mkDupPiFun (v := v) α.α P.inst⟩⟩

  instance hasPiSelfAppPi {α : _sort} {v : Level} {q : α → mkSortType v} (Q : α ⥤{q} mkSortType v) :
      HasPiSelfAppPi (defFunToProp Q) :=
    ⟨λ f => ⟨mkPiSelfAppPi (v := v) α.α Q.inst f⟩⟩

  instance hasPiSelfAppPi₂ {α : _sort} {v : Level} {q : α → mkSortType v} (Q : α ⥤{q} mkSortType v) :
      HasPiSelfAppPi₂ (defFunToProp Q) :=
    ⟨⟨mkPiSelfAppPi₂ (v := v) α.α Q.inst⟩⟩

  instance {α : _sort} {v w : Level} {p : α → mkSortType v} (P : α ⥤{p} mkSortType v)
           {q : ∀ a, p a → mkSortType w} {qa : ∀ a, p a ⥤{q a} mkSortType w}
           (Q : DefPi (λ a => ((defFunToProp P) a ⥤ mkSortType w)) (λ a => qa a)) (a : α) :
      HasPiType ((defPiToProp Q) a) :=
    hasPiType (qa a)

  def substProp₁' {u v w : Level} (α : Q(Sort u)) (P : Q($α → Sort v)) (Q : Q(∀ a, $P a → Sort w)) :
      Q($α → Sort (imax v w)) :=
    ⌜λ a => ∀ b, $Q a b⌝

  def defSubstProp₁ {α : _sort} {v w : Level} {p : α → mkSortType v} {P : α ⥤{p} mkSortType v}
                    {q : ∀ a, p a → mkSortType w} {qa : ∀ a, p a ⥤{q a} mkSortType w}
                    (Q : DefPi (λ a => ((defFunToProp P) a ⥤ mkSortType w)) (λ a => qa a)) :
      α ⥤{λ a => (Pi ((defPiToProp Q) a)).α} mkSortType (mkLevelIMax v w) :=
    ⟨substProp₁' (v := v) (w := w) α.α P.inst Q.inst⟩

  instance {α : _sort} {v w : Level} {p : α → mkSortType v} {P : α ⥤{p} mkSortType v}
           {q : ∀ a, p a → mkSortType w} {qa : ∀ a, p a ⥤{q a} mkSortType w}
           (Q : DefPi (λ a => ((defFunToProp P) a ⥤ mkSortType w)) (λ a => qa a)) :
      HasPiType (λ a => Pi ((defPiToProp Q) a)) :=
    hasPiType (defSubstProp₁ Q)

  def substProp₂' {u v w : Level} (α : Q(Sort u)) (P : Q($α → Sort v)) (Q : Q(∀ a, $P a → Sort w))
                  (f : Q(∀ a, $P a)) :
      Q($α → Sort w) :=
    ⌜λ a => $Q a ($f a)⌝

  def defSubstProp₂ {α : _sort} {v w : Level} {p : α → mkSortType v} {P : α ⥤{p} mkSortType v}
                    {q : ∀ a, p a → mkSortType w} {qa : ∀ a, p a ⥤{q a} mkSortType w}
                    (Q : DefPi (λ a => ((defFunToProp P) a ⥤ mkSortType w)) (λ a => qa a))
                    (f : Pi (defFunToProp P)) :
      α ⥤{λ a => q a (f a)} mkSortType w :=
    ⟨substProp₂' (v := v) (w := w) α.α P.inst Q.inst f⟩

  instance {α : _sort} {v w : Level} {p : α → mkSortType v} {P : α ⥤{p} mkSortType v}
           {q : ∀ a, p a → mkSortType w} {qa : ∀ a, p a ⥤{q a} mkSortType w}
           (Q : DefPi (λ a => ((defFunToProp P) a ⥤ mkSortType w)) (λ a => qa a))
           (f : Pi (defFunToProp P)) :
      HasPiType (λ a => (defPiToProp Q) a (f a)) :=
    hasPiType (defSubstProp₂ Q f)

  instance hasSubstPi {α : _sort} {v w : Level} {p : α → mkSortType v} {P : α ⥤{p} mkSortType v}
                      {q : ∀ a, p a → mkSortType w} {qa : ∀ a, p a ⥤{q a} mkSortType w}
                      (Q : DefPi (λ a => ((defFunToProp P) a ⥤ mkSortType w)) (λ a => qa a)) :
      HasSubstPi (defPiToProp Q) :=
    ⟨λ f g => ⟨mkSubstPi (v := v) (w := w) α.α P.inst Q.inst f g⟩⟩

  def substProp₃' {u v w : Level} (α : Q(Sort u)) (P : Q($α → Sort v)) (Q : Q(∀ a, $P a → Sort w)) :
      Q((∀ a, $P a) → Sort (imax u w)) :=
    ⌜λ f => ∀ a, $Q a (f a)⌝

  def defSubstProp₃ {α : _sort} {v w : Level} {p : α → mkSortType v} {P : α ⥤{p} mkSortType v}
                    {q : ∀ a, p a → mkSortType w} {qa : ∀ a, p a ⥤{q a} mkSortType w}
                    (Q : DefPi (λ a => ((defFunToProp P) a ⥤ mkSortType w)) (λ a => qa a)) :
      Pi (defFunToProp P)
      ⥤{λ f => (Pi (λ a => (defPiToProp Q) a (f a))).α}
      mkSortType (mkLevelIMax α.u w) :=
    ⟨substProp₃' (v := v) (w := w) α.α P.inst Q.inst⟩

  instance {α : _sort} {v w : Level} {p : α → mkSortType v} {P : α ⥤{p} mkSortType v}
           {q : ∀ a, p a → mkSortType w} {qa : ∀ a, p a ⥤{q a} mkSortType w}
           (Q : DefPi (λ a => ((defFunToProp P) a ⥤ mkSortType w)) (λ a => qa a)) :
      HasPiType (λ f : Pi (defFunToProp P) => Pi (λ a => (defPiToProp Q) a (f a))) :=
    hasPiType (defSubstProp₃ Q)

  instance hasRevSubstPi₂ {α : _sort} {v w : Level} {p : α → mkSortType v} {P : α ⥤{p} mkSortType v}
                          {q : ∀ a, p a → mkSortType w} {qa : ∀ a, p a ⥤{q a} mkSortType w}
                          (Q : DefPi (λ a => ((defFunToProp P) a ⥤ mkSortType w)) (λ a => qa a)) :
      HasRevSubstPi₂ (defPiToProp Q) :=
    ⟨λ g => ⟨mkRevSubstPi₂ (v := v) (w := w) α.α P.inst Q.inst g⟩⟩

  instance hasRevSubstPiFun {α : _sort} {v w : Level} {p : α → mkSortType v}
                            {P : α ⥤{p} mkSortType v} {q : ∀ a, p a → mkSortType w}
                            {qa : ∀ a, p a ⥤{q a} mkSortType w}
                            (Q : DefPi (λ a => ((defFunToProp P) a ⥤ mkSortType w)) (λ a => qa a)) :
      HasRevSubstPiFun (defPiToProp Q) :=
    ⟨⟨mkRevSubstPiFun (v := v) (w := w) α.α P.inst Q.inst⟩⟩


  def defConstPropFun (α β : _sort) : α ⥤{Function.const α β} mkSortType β.u :=
    HasConstPi.defConstFun α β

  @[reducible] def constProp (α β : _sort) : α → _sort := defFunToProp (defConstPropFun α β)

  -- Need to change definition of `hasFunPi` for this, but that results in instance search problems.
  --theorem constProp.test (α β : _sort) : (α ⥤ β) = Pi (constProp α β) := rfl


-- TODO: There is some type class defeq issue that will probably also cause other problems.
--
--  instance hasLinearLogic : HasLinearLogic _sort :=
--    HasLinearLogic.construct _sort
--                             (hRevApp := λ α β => hasPiAppFunPi (defConstPropFun α β))
--                             (hRevComp := λ α β γ => hasRevCompFunPiFun α β (defConstPropFun β γ))
--
--  instance hasSubLinearLogic : HasSubLinearLogic _sort :=
--    HasSubLinearLogic.construct _sort
--
--  instance hasAffineLogic : HasAffineLogic _sort := ⟨⟩
--
--  instance hasNonLinearLogic : HasNonLinearLogic _sort :=
--    HasNonLinearLogic.construct _sort
--
--  instance hasFullLogic : HasFullLogic _sort := ⟨⟩

end _sort
