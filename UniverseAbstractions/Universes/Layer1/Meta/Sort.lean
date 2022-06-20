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



def _sort := exprUniverse id

namespace _sort

  def mk {u : Level} (α : ⌜Sort u⌝) : _sort := ⟨α⟩

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

  -- Functors

  instance hasFunctors (α β : _sort) : HasFunctors α β where
    defPiType := { A    := ⟨mkFun α.α β.α⟩,
                   elim := λ (f : mkFun α.α β.α) (a : α.α) => mkFun.mkApp f a }

  instance hasUnivFunctors : HasUnivFunctors _sort _sort := ⟨⟩

  def defFun {α β : _sort} {f' : α → β} (f : mkFun α.α β.α) : α ⥤{f'} β := defInst f

  def defFun₂ {α β γ : _sort} {f' : α → β → γ} (f : mkFun α.α (mkFun β.α γ.α)) : α ⥤ β ⥤{f'} γ :=
    ⟨λ a => defFun (mkFun.mkApp f a), defFun f⟩

  def defFun₃ {α β γ δ : _sort} {f' : α → β → γ → δ} (f : mkFun α.α (mkFun β.α (mkFun γ.α δ.α))) :
      α ⥤ β ⥤ γ ⥤{f'} δ :=
    ⟨λ a => defFun₂ (mkFun.mkApp f a), defFun f⟩

  def defInFunCtorFun (u : Level) (β : _sort) :
      mkSortType u ⥤{λ α => (α ⥤ β).α} mkSortType (mkLevelIMax u β.u) :=
    defFun ⌜λ α => α → $β.α⌝

  @[reducible] def inFunCtorFun (u : Level) (β : _sort) :
      mkSortType u ⥤ mkSortType (mkLevelIMax u β.u) :=
    defInFunCtorFun u β

  def defOutFunCtorFun (α : _sort) (v : Level) :
      mkSortType v ⥤{λ β => (α ⥤ mkSortType.toSort β).α} mkSortType (mkLevelIMax α.u v) :=
    defFun ⌜λ β => $α.α → β⌝

  @[reducible] def outFunCtorFun (α : _sort) (v : Level) :
      mkSortType v ⥤ mkSortType (mkLevelIMax α.u v) :=
    defOutFunCtorFun α v

  instance hasLinearLogic : HasLinearLogic _sort where
    defIdFun       α     := defFun  ⌜id⌝
    defRevAppFun₂  α β   := defFun₂ ⌜λ a f => f a⌝
    defRevCompFun₃ α β γ := defFun₃ ⌜Function.comp⌝

  instance hasSubLinearLogic : HasSubLinearLogic _sort where
    defConstFun₂ α β := defFun₂ ⌜Function.const _⌝

  instance hasAffineLogic : HasAffineLogic _sort := ⟨⟩

  instance hasNonLinearLogic : HasNonLinearLogic _sort where
    defDupFun₂ α β := defFun₂ ⌜λ f a => f a a⌝

  instance hasFullLogic : HasFullLogic _sort := ⟨⟩

  -- Π types

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
      HasPiType (defFunToProp P) where
    defPiType := { A    := ⟨mkForAll α.α (v := v) P.inst⟩,
                   elim := λ (f : mkForAll α.α (v := v) P.inst) (a : α.α) => mkForAll.mkApp f a }

  def defPi {α : _sort} {v : Level} {p : α → mkSortType v} {P : α ⥤{p} mkSortType v} {f' : ∀ a, p a}
            (f : mkForAll α.α (v := v) P.inst) :
      DefPi (defFunToProp P) f' :=
    defInst f

  -- Π constructor that takes a property.
  def defPiCtorFun (α : _sort) (v : Level) :
      (α ⥤ mkSortType v) ⥤{λ P => (Pi (funToProp P)).α} mkSortType (mkLevelIMax α.u v) :=
    defFun ⌜λ P => ∀ a, P a⌝

  @[reducible] def piCtorFun (α : _sort) (v : Level) :
      (α ⥤ mkSortType v) ⥤ mkSortType (mkLevelIMax α.u v) :=
    defPiCtorFun α v

  -- The type of `piCtorFun` after abstracting `α`.
  def defPiCtorFunCtor (u v : Level) :
      mkSortType u
      ⥤{λ α => ((α ⥤ mkSortType v) ⥤ mkSortType (mkLevelIMax u v)).α}
      mkSortType (mkLevelIMax (mkLevelIMax u (mkLevelSucc v)) (mkLevelSucc (mkLevelIMax u v))) :=
    -- This can be written the composition of two instances of `inFunCtorFun`, but that's not really
    -- an improvement.
    defFun ⌜λ α => (α → Sort v) → Sort (imax u v)⌝

  @[reducible] def piCtorFunCtor (u v : Level) :
      mkSortType u ⥤
      mkSortType (mkLevelIMax (mkLevelIMax u (mkLevelSucc v)) (mkLevelSucc (mkLevelIMax u v))) :=
    defPiCtorFunCtor u v

  -- Π constructor that takes both the domain and a property on that domain.
  def defPiCtorFunPi (u v : Level) :
      DefPi (defFunToProp (defPiCtorFunCtor u v)) (λ α => piCtorFun α v) :=
    defPi ⌜λ α P => ∀ a, P a⌝

  instance {α : _sort} {v : Level} {p : α → mkSortType v} (P : α ⥤{p} mkSortType v) :
      HasPiType (λ a => (defFunToProp P) a) :=
    hasPiType P

  instance {α β : _sort} {v : Level} {p : α → β → mkSortType v} (P : α ⥤ β ⥤{p} mkSortType v)
           (a : α) :
      HasPiType ((defFunToProp₂ P) a) :=
    hasPiType (P.app a)

  instance {α β : _sort} {v : Level} {p : α → β → mkSortType v} (P : α ⥤ β ⥤{p} mkSortType v) :
      HasPiType (λ a => Pi ((defFunToProp₂ P) a)) :=
    hasPiType (HasCompFunPi.defCompDefFun P.toDefFun (defPiCtorFun β v))

  instance {α β : _sort} {v : Level} {p : α → β → mkSortType v} (P : α ⥤ β ⥤{p} mkSortType v)
           (b : β) :
      HasPiType (λ a => (defFunToProp₂ P) a b) :=
    hasPiType (HasSwapPi.defSwapDefFun P b)

  instance {α β : _sort} {v : Level} {p : α → β → mkSortType v} (P : α ⥤ β ⥤{p} mkSortType v) :
      HasPiType (λ b => Pi (λ a => (defFunToProp₂ P) a b)) :=
    hasPiType (HasCompFunPi.defCompDefFun (HasSwapPi₂.defSwapDefFun₂ P).toDefFun (defPiCtorFun α v))

  instance {α : _sort} {v w : Level} {p : α → mkSortType v} (P : α ⥤{p} mkSortType v) :
      HasPiType (λ a => ((defFunToProp P) a ⥤ mkSortType w)) :=
    hasPiType (HasCompFunPi.defCompDefFun P (defInFunCtorFun v (mkSortType w)))

  def defPiToProp {α : _sort} {v w : Level} {p : α → mkSortType v} {P : α ⥤{p} mkSortType v}
                  {q : ∀ a, p a ⥤ mkSortType w}
                  (Q : DefPi (λ a => ((defFunToProp P) a ⥤ mkSortType w)) q) :
      ∀ a, (defFunToProp P) a → _sort :=
    λ a b => q a b

  @[reducible] def piToProp {α : _sort} {v w : Level} {P : α ⥤ mkSortType v}
                            (Q : Pi (λ a => ((funToProp P) a ⥤ mkSortType w))) :
      ∀ a, P a → _sort :=
    defPiToProp (DefPi.defAppPi Q)

  instance hasIdFun (α : _sort) : HasIdFun α := ⟨defFun ⌜id⌝⟩

  def piAppFun' {u v : Level} (α : Q(Sort u)) (P : Q($α → Sort v)) (a : Q($α)) :
      Q((∀ a, $P a) → $P $a) :=
    ⌜λ f => f $a⌝

  instance hasPiAppFun {α : _sort} {v : Level} {p : α → mkSortType v} (P : α ⥤{p} mkSortType v) :
      HasPiAppFun (defFunToProp P) :=
    ⟨λ a => defFun (piAppFun' (v := v) α.α P.inst a)⟩

  instance {α : _sort} {v : Level} {p : α → mkSortType v} (P : α ⥤{p} mkSortType v) :
      HasPiType (λ a => Pi (defFunToProp P) ⥤ (defFunToProp P) a) :=
    hasPiType (HasCompFunPi.defCompDefFun P (defOutFunCtorFun (Pi (defFunToProp P)) v))

  def piAppFunPi' {u v : Level} (α : Q(Sort u)) (P : Q($α → Sort v)) :
      Q(∀ a, (∀ a', $P a') → $P a) :=
    ⌜λ a f => f a⌝

  instance hasPiAppFunPi {α : _sort} {v : Level} {p : α → mkSortType v} (P : α ⥤{p} mkSortType v) :
      HasPiAppFunPi (defFunToProp P) :=
    ⟨defPi (piAppFunPi' (v := v) α.α P.inst)⟩

  def swapPi' {u u' v : Level} (α : Q(Sort u)) (β : Q(Sort u')) (P : Q($α → $β → Sort v))
              (f : Q(∀ a b, $P a b)) (b : Q($β)) :
      Q(∀ a, $P a $b) :=
    ⌜λ a => $f a $b⌝

  instance hasSwapPi {α β : _sort} {v : Level} {p : α → β → mkSortType v}
                     (P : α ⥤ β ⥤{p} mkSortType v) :
      HasSwapPi (defFunToProp₂ P) :=
    ⟨λ f b => defPi (swapPi' (v := v) α.α β.α P.inst f b)⟩

  def swapPi₂' {u u' v : Level} (α : Q(Sort u)) (β : Q(Sort u')) (P : Q($α → $β → Sort v))
               (f : Q(∀ a b, $P a b)) :
      Q(∀ b a, $P a b) :=
    ⌜λ b a => $f a b⌝

  instance hasSwapPi₂ {α β : _sort} {v : Level} {p : α → β → mkSortType v}
                      (P : α ⥤ β ⥤{p} mkSortType v) :
      HasSwapPi₂ (defFunToProp₂ P) :=
    ⟨λ f => defPi (swapPi₂' (v := v) α.α β.α P.inst f)⟩

  def swapPiFun' {u u' v : Level} (α : Q(Sort u)) (β : Q(Sort u')) (P : Q($α → $β → Sort v)) :
      Q((∀ a b, $P a b) → (∀ b a, $P a b)) :=
    ⌜λ f b a => f a b⌝

  instance hasSwapPiFun {α β : _sort} {v : Level} {p : α → β → mkSortType v}
                        (P : α ⥤ β ⥤{p} mkSortType v) :
      HasSwapPiFun (defFunToProp₂ P) :=
    ⟨defFun (swapPiFun' (v := v) α.α β.α P.inst)⟩

  instance (α β : _sort) {w : Level} {q : β → mkSortType w} (Q : β ⥤{q} mkSortType w) (f : α ⥤ β) :
      HasPiType (λ a => (defFunToProp Q) (f a)) :=
    hasPiType (HasCompFunPi.defCompFunDefFun f Q)

  def compFunPi' {u v w : Level} (α : Q(Sort u)) (β : Q(Sort v)) (Q : Q($β → Sort w))
                 (f : Q($α → $β)) (g : Q(∀ b, $Q b)) :
      Q(∀ a, $Q ($f a)) :=
    ⌜λ a => $g ($f a)⌝

  instance hasCompFunPi (α β : _sort) {w : Level} {q : β → mkSortType w} (Q : β ⥤{q} mkSortType w) :
      HasCompFunPi α (defFunToProp Q) :=
    ⟨λ f g => defPi (compFunPi' (w := w) α.α β.α Q.inst f g)⟩

  instance (α β : _sort) {w : Level} {q : β → mkSortType w} (Q : β ⥤{q} mkSortType w) :
      HasPiType (λ (f : α ⥤ β) => Pi (λ a => (defFunToProp Q) (f a))) :=
    hasPiType ⟨piCtorFun α w ⊙ (HasRevCompFunPi₂.defRevCompDefFun₂ α Q).inst⟩

  def revCompFunPi₂' {u v w : Level} (α : Q(Sort u)) (β : Q(Sort v)) (Q : Q($β → Sort w))
                     (g : Q(∀ b, $Q b)) :
      Q(∀ (f : $α → $β) a, $Q (f a)) :=
    ⌜λ f a => $g (f a)⌝

  instance hasRevCompFunPi₂ (α β : _sort) {w : Level} {q : β → mkSortType w}
                            (Q : β ⥤{q} mkSortType w) :
      HasRevCompFunPi₂ α (defFunToProp Q) :=
    ⟨λ g => defPi (revCompFunPi₂' (w := w) α.α β.α Q.inst g)⟩

  def revCompFunPiFun' {u v w : Level} (α : Q(Sort u)) (β : Q(Sort v)) (Q : Q($β → Sort w)) :
      Q((∀ b, $Q b) → (∀ (f : $α → $β) a, $Q (f a))) :=
    ⌜λ g f a => g (f a)⌝

  instance hasRevCompFunPiFun (α β : _sort) {w : Level} {q : β → mkSortType w}
                              (Q : β ⥤{q} mkSortType w) :
      HasRevCompFunPiFun α (defFunToProp Q) :=
    ⟨defFun (revCompFunPiFun' (w := w) α.α β.α Q.inst)⟩

  def constFun' {u v : Level} (α : Q(Sort u)) (β : Q(Sort v)) (b : Q($β)) : Q($α → $β) :=
    ⌜Function.const $α $b⌝

  instance hasConstPi (α β : _sort) : HasConstPi α β :=
    ⟨λ b => defFun (constFun' α.α β.α b)⟩

  def constFun₂' {u v : Level} (α : Q(Sort u)) (β : Q(Sort v)) : Q($β → ($α → $β)) :=
    ⌜Function.const $α⌝

  instance hasConstPiFun (α β : _sort) : HasConstPiFun α β :=
    ⟨defFun (constFun₂' α.α β.α)⟩

  instance {α : _sort} {v : Level} {p : α → α → mkSortType v} (P : α ⥤ α ⥤{p} mkSortType v) :
      HasPiType (λ a => (defFunToProp₂ P) a a) :=
    hasPiType (HasDupPi.defDupDefFun P)

  def dupPi' {u v : Level} (α : Q(Sort u)) (P : Q($α → $α → Sort v)) (f : Q(∀ a a', $P a a')) :
      Q(∀ a, $P a a) :=
    ⌜λ a => $f a a⌝

  instance hasDupPi {α : _sort} {v : Level} {p : α → α → mkSortType v}
                    (P : α ⥤ α ⥤{p} mkSortType v) :
      HasDupPi (defFunToProp₂ P) :=
    ⟨λ f => defPi (dupPi' (v := v) α.α P.inst f)⟩

  def dupPiFun' {u v : Level} (α : Q(Sort u)) (P : Q($α → $α → Sort v)) :
      Q((∀ a a', $P a a') → (∀ a, $P a a)) :=
    ⌜λ f a => f a a⌝

  instance hasDupPiFun {α : _sort} {v : Level} {p : α → α → mkSortType v}
                       (P : α ⥤ α ⥤{p} mkSortType v) :
      HasDupPiFun (defFunToProp₂ P) :=
    ⟨defFun (dupPiFun' (v := v) α.α P.inst)⟩

  def piSelfAppPi' {u v : Level} (α : Q(Sort u)) (Q : Q($α → Sort v)) (f : Q((∀ a, $Q a) → $α)) :
      Q(∀ g, $Q ($f g)) :=
    ⌜λ g => g ($f g)⌝

  instance hasPiSelfAppPi {α : _sort} {v : Level} {q : α → mkSortType v} (Q : α ⥤{q} mkSortType v) :
      HasPiSelfAppPi (defFunToProp Q) :=
    ⟨λ f => defPi (piSelfAppPi' (v := v) α.α Q.inst f)⟩

  def piSelfAppPi₂' {u v : Level} (α : Q(Sort u)) (Q : Q($α → Sort v)) :
      Q(∀ (f : (∀ a, $Q a) → $α) g, $Q (f g)) :=
    ⌜λ f g => g (f g)⌝

  instance hasPiSelfAppPi₂ {α : _sort} {v : Level} {q : α → mkSortType v} (Q : α ⥤{q} mkSortType v) :
      HasPiSelfAppPi₂ (defFunToProp Q) :=
    ⟨defPi (piSelfAppPi₂' (v := v) α.α Q.inst)⟩

  instance {α : _sort} {v w : Level} {p : α → mkSortType v} (P : α ⥤{p} mkSortType v)
           {q : ∀ a, p a ⥤ mkSortType w} (Q : DefPi (λ a => ((defFunToProp P) a ⥤ mkSortType w)) q)
           (a : α) :
      HasPiType ((defPiToProp Q) a) :=
    hasPiType ⟨q a⟩

  def substProp₁' {u v w : Level} (α : Q(Sort u)) (P : Q($α → Sort v)) (Q : Q(∀ a, $P a → Sort w)) :
      Q($α → Sort (imax v w)) :=
    ⌜λ a => ∀ b, $Q a b⌝

  def defSubstProp₁ {α : _sort} {v w : Level} {p : α → mkSortType v} {P : α ⥤{p} mkSortType v}
                    {q : ∀ a, p a ⥤ mkSortType w}
                    (Q : DefPi (λ a => ((defFunToProp P) a ⥤ mkSortType w)) q) :
      α ⥤{λ a => (Pi ((defPiToProp Q) a)).α} mkSortType (mkLevelIMax v w) :=
    ⟨substProp₁' (v := v) (w := w) α.α P.inst Q.inst⟩

  instance {α : _sort} {v w : Level} {p : α → mkSortType v} {P : α ⥤{p} mkSortType v}
           {q : ∀ a, p a ⥤ mkSortType w} (Q : DefPi (λ a => ((defFunToProp P) a ⥤ mkSortType w)) q) :
      HasPiType (λ a => Pi ((defPiToProp Q) a)) :=
    hasPiType (defSubstProp₁ Q)

  def substProp₂' {u v w : Level} (α : Q(Sort u)) (P : Q($α → Sort v)) (Q : Q(∀ a, $P a → Sort w))
                  (f : Q(∀ a, $P a)) :
      Q($α → Sort w) :=
    ⌜λ a => $Q a ($f a)⌝

  def defSubstProp₂ {α : _sort} {v w : Level} {p : α → mkSortType v} {P : α ⥤{p} mkSortType v}
                    {q : ∀ a, p a ⥤ mkSortType w}
                    (Q : DefPi (λ a => ((defFunToProp P) a ⥤ mkSortType w)) q)
                    (f : Pi (defFunToProp P)) :
      α ⥤{λ a => q a (f a)} mkSortType w :=
    ⟨substProp₂' (v := v) (w := w) α.α P.inst Q.inst f⟩

  instance {α : _sort} {v w : Level} {p : α → mkSortType v} {P : α ⥤{p} mkSortType v}
           {q : ∀ a, p a ⥤ mkSortType w} (Q : DefPi (λ a => ((defFunToProp P) a ⥤ mkSortType w)) q)
           (f : Pi (defFunToProp P)) :
      HasPiType (λ a => (defPiToProp Q) a (f a)) :=
    hasPiType (defSubstProp₂ Q f)

  def substPi' {u v w : Level} (α : Q(Sort u)) (P : Q($α → Sort v)) (Q : Q(∀ a, $P a → Sort w))
               (f : Q(∀ a, $P a)) (g : Q(∀ a b, $Q a b)) :
      Q(∀ a, $Q a ($f a)) :=
    ⌜λ a => $g a ($f a)⌝

  instance hasSubstPi {α : _sort} {v w : Level} {p : α → mkSortType v} {P : α ⥤{p} mkSortType v}
                      {q : ∀ a, p a ⥤ mkSortType w}
                      (Q : DefPi (λ a => ((defFunToProp P) a ⥤ mkSortType w)) q) :
      HasSubstPi (defPiToProp Q) :=
    ⟨λ f g => defPi (substPi' (v := v) (w := w) α.α P.inst Q.inst f g)⟩

  def substProp₃' {u v w : Level} (α : Q(Sort u)) (P : Q($α → Sort v)) (Q : Q(∀ a, $P a → Sort w)) :
      Q((∀ a, $P a) → Sort (imax u w)) :=
    ⌜λ f => ∀ a, $Q a (f a)⌝

  def defSubstProp₃ {α : _sort} {v w : Level} {p : α → mkSortType v} {P : α ⥤{p} mkSortType v}
                    {q : ∀ a, p a ⥤ mkSortType w}
                    (Q : DefPi (λ a => ((defFunToProp P) a ⥤ mkSortType w)) q) :
      Pi (defFunToProp P)
      ⥤{λ f => (Pi (λ a => (defPiToProp Q) a (f a))).α}
      mkSortType (mkLevelIMax α.u w) :=
    ⟨substProp₃' (v := v) (w := w) α.α P.inst Q.inst⟩

  instance {α : _sort} {v w : Level} {p : α → mkSortType v} {P : α ⥤{p} mkSortType v}
           {q : ∀ a, p a ⥤ mkSortType w} (Q : DefPi (λ a => ((defFunToProp P) a ⥤ mkSortType w)) q) :
      HasPiType (λ f : Pi (defFunToProp P) => Pi (λ a => (defPiToProp Q) a (f a))) :=
    hasPiType (defSubstProp₃ Q)

  def revSubstPi₂' {u v w : Level} (α : Q(Sort u)) (P : Q($α → Sort v)) (Q : Q(∀ a, $P a → Sort w))
                   (g : Q(∀ a b, $Q a b)) :
      Q(∀ (f : ∀ a, $P a) a, $Q a (f a)) :=
    ⌜λ f a => $g a (f a)⌝

  instance hasRevSubstPi₂ {α : _sort} {v w : Level} {p : α → mkSortType v} {P : α ⥤{p} mkSortType v}
                          {q : ∀ a, p a ⥤ mkSortType w}
                          (Q : DefPi (λ a => ((defFunToProp P) a ⥤ mkSortType w)) q) :
      HasRevSubstPi₂ (defPiToProp Q) :=
    ⟨λ g => defPi (revSubstPi₂' (v := v) (w := w) α.α P.inst Q.inst g)⟩

  def revSubstPiFun' {u v w : Level} (α : Q(Sort u)) (P : Q($α → Sort v))
                     (Q : Q(∀ a, $P a → Sort w)) :
      Q((∀ a b, $Q a b) → (∀ (f : ∀ a, $P a) a, $Q a (f a))) :=
    ⌜λ g f a => g a (f a)⌝

  instance hasRevSubstPiFun {α : _sort} {v w : Level} {p : α → mkSortType v}
                            {P : α ⥤{p} mkSortType v} {q : ∀ a, p a ⥤ mkSortType w}
                            (Q : DefPi (λ a => ((defFunToProp P) a ⥤ mkSortType w)) q) :
      HasRevSubstPiFun (defPiToProp Q) :=
    ⟨defFun (revSubstPiFun' (v := v) (w := w) α.α P.inst Q.inst)⟩

end _sort
