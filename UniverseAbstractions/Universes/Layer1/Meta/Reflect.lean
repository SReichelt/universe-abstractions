import UniverseAbstractions.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedFunctors
import UniverseAbstractions.Meta.TypedExpr
import UniverseAbstractions.Meta.Helpers



namespace UniverseAbstractions.Layer1.Meta

set_option autoBoundImplicitLocal false

open Lean Lean.Meta Qq



structure _Sort where
{u : Level}
(α : ⌜Sort u⌝)

def exprUniverse {β : Type} (inst : β → _Sort) : Universe :=
{ a    := β,
  inst := ⟨λ b => (inst b).α⟩ }



-- On the meta level, we can define several different universes of expressions. In particular:
-- * All object-level universes along with their structure are reflected on the meta level by
--   universes with the same structure.
-- * Of course, the above includes each universe `sort.{u}`. However, for these we can go a
--   little further and combine them into a single universe `_sort` by bundling a `Level` with
--   each `Expr` that denotes a type.
--
-- Using universe-based structures on the meta level has the advantage that we have all "proofs"
-- about universes (which are actually definitions) at our disposal, and we can be certain that
-- this code is error-free.
--
-- We start with the definition of `_sort`, which is far less verbose.

def _sort := exprUniverse id

namespace _sort

  def mkFun {u v : Level} (α : ⌜Sort u⌝) (β : ⌜Sort v⌝) : ⌜Sort (imax u v)⌝ := ⌜$α → $β⌝
  def mkApp {u v : Level} {α : ⌜Sort u⌝} {β : ⌜Sort v⌝} (f : mkFun α β) (a : α) : β := ⌜$f $a⌝

  instance hasFunctors : HasFunctors _sort :=
  { Fun   := λ A B => ⟨mkFun A.α B.α⟩,
    apply := λ {A B} (f : mkFun A.α B.α) (a : A.α) => mkApp f a }

  -- When using this, make sure that `f` is defeq to what `f'` specifies.
  def defFun {A B : _sort} {f' : A → B} (f : mkFun A.α B.α) : A ⟶{f'} B := ⟨f⟩

  def defFun₂ {A B C : _sort} {f' : A → B → C} (f : mkFun A.α (mkFun B.α C.α)) : A ⟶ B ⟶{f'} C :=
  ⟨λ a => defFun (mkApp f a), defFun f⟩

  def defFun₃ {A B C D : _sort} {f' : A → B → C → D} (f : mkFun A.α (mkFun B.α (mkFun C.α D.α))) :
    A ⟶ B ⟶ C ⟶{f'} D :=
  ⟨λ a => defFun₂ (mkApp f a), defFun f⟩

  instance hasFullLogic : HasFullLogic _sort :=
  { defIdFun      := λ _     => defFun  ⌜id⌝,
    defRevAppFun₂ := λ _ _   => defFun₂ ⌜λ a f => f a⌝,
    defCompFun₃   := λ _ _ _ => defFun₃ ⌜λ f g => g ∘ f⌝,
    defConstFun₂  := λ _ _   => defFun₂ ⌜Function.const _⌝,
    defDupFun₂    := λ _ _   => defFun₂ ⌜λ f a => f a a⌝ }

end _sort



def mkHasInstances' (u : Level) {v : Level} (I : ⌜Sort v⌝) : ClassExpr :=
⟨⌜HasInstances.{u, v} $I⌝⟩

class mkHasInstances (u : outParam Level) {v : Level} (I : ⌜Sort v⌝) extends
mkHasInstances' u I

namespace mkHasInstances

  def mkInst {u v : Level} {I : ⌜Sort v⌝} [h : mkHasInstances u I] (A : I) : ⌜Sort u⌝ :=
  let _ := h.h
  ⌜$A⌝

  instance reflect {u v : Level} (I : ⌜Sort v⌝) [h : mkHasInstances u I] : HasInstances I :=
  ⟨λ A => mkInst A⟩

end mkHasInstances



structure _Universe where
{u v : Level}
(U   : ⌜Universe.{u, v}⌝)

namespace _Universe

  instance : Coe _Universe Expr := ⟨_Universe.U⟩

  def mkFreshMVar : MetaM _Universe := do
    let u ← mkFreshLevelMVar
    let v ← mkFreshLevelMVar
    let U : ⌜Universe.{u, v}⌝ ← TypedExpr.mkFreshMVar
    pure ⟨U⟩

  def instantiate (U : _Universe) : MetaM _Universe := do
    let u ← instantiateLevelMVars U.u
    let v ← instantiateLevelMVars U.v
    let U : ⌜Universe.{u, v}⌝ ← TypedExpr.instantiate U.U
    pure ⟨U⟩

  def mkInst (U : _Universe) : ⌜Sort $U.v⌝ := ⌜$U.U⌝
  notation "_⌈" U:0 "⌉_" => _Universe.mkInst U

  instance (U : _Universe) : mkHasInstances U.u _⌈U⌉_ := { h := ⌜Universe.instInst _⌝ }

  instance instInst (U : _Universe) : HasInstances _⌈U⌉_ := mkHasInstances.reflect _⌈U⌉_

  @[reducible] def LeanUniv (U : _Universe) := ⌜Sort $U.u⌝

  def mkInstInst {U : _Universe} (A : _⌈U⌉_) : LeanUniv U := mkHasInstances.mkInst A
  notation "_⌈" A:0 "⌉" => _Universe.mkInstInst A

  def reflect (U : _Universe) := exprUniverse (λ A : _⌈U⌉_ => ⟨_⌈A⌉⟩)
  instance : Coe _Universe Universe := ⟨reflect⟩

  def mkFreshTypeMVar {U : _Universe} : MetaM _⌈U⌉_ := TypedExpr.mkFreshMVar
  def mkFreshInstMVar {U : _Universe} {A : _⌈U⌉_} : MetaM A := TypedExpr.mkFreshMVar (α := _⌈A⌉)

  def instantiateTypeMVars {U : _Universe} : _⌈U⌉_ → MetaM _⌈U⌉_ := TypedExpr.instantiate
  def instantiateInstMVars' {U : _Universe} {A A' : _⌈U⌉_} : A → MetaM A' := TypedExpr.instantiate (α := _⌈A⌉) (α' := _⌈A'⌉)
  def instantiateInstMVars {U : _Universe} {A : _⌈U⌉_} : A → MetaM A := U.instantiateInstMVars'

  @[reducible] def FVar {U : _Universe} (A : _⌈U⌉_) := Lean.FVar _⌈A⌉

end _Universe



def mkHasFunctors' {u v : Level} (U : ⌜Universe.{u, v}⌝) := ⌜HasFunctors $U⌝

namespace mkHasFunctors'

  variable {u v : Level} {U : ⌜Universe.{u, v}⌝}

  def mkArrow (A B : Q($U)) := ⌜$A → $B⌝
  def mkArrow.mkApp (A B : Q($U)) (f : Q($A → $B)) (a : Q($A)) : Q($B) := ⌜$f $a⌝

  variable (h : mkHasFunctors' U)

  def mkFun (A B : Q($U)) : Q($U) := ⌜$A ⟶ $B⌝

  def mkApplyFn (A B : Q($U)) (F : Q($A ⟶ $B)) : Q($A → $B) := ⌜HasFunctors.apply $F⌝
  def mkApply (A B : Q($U)) (F : Q($A ⟶ $B)) (a : Q($A)) : Q($B) := ⌜$F $a⌝

  def mkDefFun (A B : Q($U)) (f : Q($A → $B)) := ⌜$A ⟶{$f} $B⌝

  namespace mkDefFun

    variable (A B : Q($U)) (f : Q($A → $B))

    def mkMk (F : Q($A ⟶ $B)) : mkDefFun h A B f := ⌜HasFunctors.DefFun.mk (f := $f) $F⌝

    variable (F : mkDefFun h A B f)

    def mkF : Q($A ⟶ $B) := ⌜($F).F⌝

  end mkDefFun

  def mkAppFun (A B : Q($U)) (F : Q($A ⟶ $B)) : Q($A ⟶ $B) := ⌜HasFunctors.appFun $F⌝

  def mkIsFunApp (A B : Q($U)) (b : Q($B)) : ClassExpr := ⟨⌜HasFunctors.IsFunApp $A $b⌝⟩

  namespace mkIsFunApp

    variable (A B : Q($U)) (b : Q($B)) [hFunApp : mkIsFunApp h A B b]

    def mkF : Q($A ⟶ $B) := ⌜($hFunApp.h).F⌝
    def mka : Q($A)      := ⌜($hFunApp.h).a⌝

  end mkIsFunApp

  def mkIsFunApp₂ (A B C : Q($U)) (c : Q($C)) : ClassExpr :=
  ⟨⌜HasFunctors.IsFunApp₂ $A $B $c⌝⟩

  namespace mkIsFunApp₂

    variable (A B C : Q($U)) (c : Q($C)) [hFunApp : mkIsFunApp₂ h A B C c]

    def mkF : Q($A ⟶ $B ⟶ $C) := ⌜($hFunApp.h).F⌝
    def mka : Q($A)           := ⌜($hFunApp.h).a⌝
    def mkb : Q($B)           := ⌜($hFunApp.h).b⌝

  end mkIsFunApp₂

  def mkIsFunApp₃ (A B C D : Q($U)) (d : Q($D)) : ClassExpr :=
  ⟨⌜HasFunctors.IsFunApp₃ $A $B $C $d⌝⟩

  namespace mkIsFunApp₃

    variable (A B C D : Q($U)) (d : Q($D)) [hFunApp : mkIsFunApp₃ h A B C D d]

    def mkF : Q($A ⟶ $B ⟶ $C ⟶ $D) := ⌜($hFunApp.h).F⌝
    def mka : Q($A)                := ⌜($hFunApp.h).a⌝
    def mkb : Q($B)                := ⌜($hFunApp.h).b⌝
    def mkc : Q($C)                := ⌜($hFunApp.h).c⌝

  end mkIsFunApp₃

  def mkIsFunApp₄ (A B C D E : Q($U)) (e : Q($E)) : ClassExpr :=
  ⟨⌜HasFunctors.IsFunApp₄ $A $B $C $D $e⌝⟩

  namespace mkIsFunApp₄

    variable (A B C D E : Q($U)) (e : Q($E)) [hFunApp : mkIsFunApp₄ h A B C D E e]

    def mkF : Q($A ⟶ $B ⟶ $C ⟶ $D ⟶ $E) := ⌜($hFunApp.h).F⌝
    def mka : Q($A)                     := ⌜($hFunApp.h).a⌝
    def mkb : Q($B)                     := ⌜($hFunApp.h).b⌝
    def mkc : Q($C)                     := ⌜($hFunApp.h).c⌝
    def mkd : Q($D)                     := ⌜($hFunApp.h).d⌝

  end mkIsFunApp₄

  def mkIsFunApp₂' (A₁ A₂ B : Q($U)) (b : Q($B)) : ClassExpr :=
  ⟨⌜HasFunctors.IsFunApp₂' $A₁ $A₂ $b⌝⟩

  namespace mkIsFunApp₂'

    variable (A₁ A₂ B : Q($U)) (b : Q($B)) [hFunApp₂ : mkIsFunApp₂' h A₁ A₂ B b]
  
    instance : mkIsFunApp h A₁ B b := ⟨⌜($hFunApp₂.h).h₂⌝⟩
    instance : mkIsFunApp h A₂ B b := ⟨⌜($hFunApp₂.h).toIsFunApp⌝⟩

  end mkIsFunApp₂'

  def mkIsFunApp₃' (A₁ A₂ A₃ B : Q($U)) (b : Q($B)) : ClassExpr :=
  ⟨⌜HasFunctors.IsFunApp₃' $A₁ $A₂ $A₃ $b⌝⟩

  namespace mkIsFunApp₃'

    variable (A₁ A₂ A₃ B : Q($U)) (b : Q($B)) [hFunApp₃ : mkIsFunApp₃' h A₁ A₂ A₃ B b]

    instance : mkIsFunApp h A₁ B b := ⟨⌜($hFunApp₃.h).h₃⌝⟩
    instance : mkIsFunApp₂' h A₂ A₃ B b := ⟨⌜($hFunApp₃.h).toIsFunApp₂'⌝⟩

  end mkIsFunApp₃'

  def mkIsFunApp₄' (A₁ A₂ A₃ A₄ B : Q($U)) (b : Q($B)) : ClassExpr :=
  ⟨⌜HasFunctors.IsFunApp₄' $A₁ $A₂ $A₃ $A₄ $b⌝⟩

  namespace mkIsFunApp₄'

    variable (A₁ A₂ A₃ A₄ B : Q($U)) (b : Q($B)) [hFunApp₄ : mkIsFunApp₄' h A₁ A₂ A₃ A₄ B b]

    instance : mkIsFunApp h A₁ B b := ⟨⌜($hFunApp₄.h).h₄⌝⟩
    instance : mkIsFunApp₃' h A₂ A₃ A₄ B b := ⟨⌜($hFunApp₄.h).toIsFunApp₃'⌝⟩

  end mkIsFunApp₄'

end mkHasFunctors'

def mkHasFunctors (U : _Universe) : ClassExpr := ⟨mkHasFunctors' U.U⟩

namespace mkHasFunctors

  variable {U : _Universe} [h : mkHasFunctors U]

  instance reflect : HasFunctors U :=
  { Fun   := mkHasFunctors'.mkFun h.h,
    apply := λ {A B} => mkHasFunctors'.mkApply h.h A B }

  @[reducible] def _Fun (A B : _⌈U⌉_) : _⌈U⌉_ := HasFunctors.Fun (U := U) A B
  infixr:20 " _⟶ " => mkHasFunctors._Fun

  instance (A B : _⌈U⌉_) : CoeFun (A _⟶ B) (λ _ => A → B) :=
  HasFunctors.coeFun (U := U) A B

  def mkApplyFn {A B : _⌈U⌉_} (F : A _⟶ B) : ⌜$A → $B⌝ :=
  mkHasFunctors'.mkApplyFn h.h A B F

  @[reducible] def _DefFun (A B : _⌈U⌉_) (f : A → B) := HasFunctors.DefFun (U := U) A B f
  notation:20 A:21 " _⟶{" f:0 "} " B:21 => mkHasFunctors._DefFun A B f

  def mkAppFun {A B : _⌈U⌉_} (F : A _⟶ B) : A _⟶ B := mkHasFunctors'.mkAppFun h.h A B F

  def mkDefFun (A B : _⌈U⌉_) (f : A _⟶ B) := mkHasFunctors'.mkDefFun h.h A B f

  namespace mkDefFun

    variable (A B : _⌈U⌉_) (f : A _⟶ B)

    def mkMk (F : A _⟶ B) : mkDefFun A B f := mkHasFunctors'.mkDefFun.mkMk h.h A B f F

    variable (F : mkDefFun A B f)

    def mkF : A _⟶ B := mkHasFunctors'.mkDefFun.mkF h.h A B f F

  end mkDefFun

  class mkIsFunApp (A : _⌈U⌉_) {B : _⌈U⌉_} (b : B) extends
  mkHasFunctors'.mkIsFunApp h.h A B b

  namespace mkIsFunApp

    def reflect (A : _⌈U⌉_) {B : _⌈U⌉_} (b : B) [hFunApp : mkIsFunApp A b] :
        MetaM (HasFunctors.IsFunApp (U := U) A b) := do
      pure { F := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp.mkF h.h A B b),
             a := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp.mka h.h A B b) }

  end mkIsFunApp

  class mkIsFunApp₂ (A B : _⌈U⌉_) {C : _⌈U⌉_} (c : C) extends
  mkHasFunctors'.mkIsFunApp₂ h.h A B C c

  namespace mkIsFunApp₂

    def reflect (A B : _⌈U⌉_) {C : _⌈U⌉_} (c : C) [hFunApp : mkIsFunApp₂ A B c] :
        MetaM (HasFunctors.IsFunApp₂ (U := U) A B c) := do
      pure { F := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₂.mkF h.h A B C c),
             a := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₂.mka h.h A B C c),
             b := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₂.mkb h.h A B C c) }

  end mkIsFunApp₂

  class mkIsFunApp₃ (A B C : _⌈U⌉_) {D : _⌈U⌉_} (d : D) extends
  mkHasFunctors'.mkIsFunApp₃ h.h A B C D d

  namespace mkIsFunApp₃

    def reflect (A B C : _⌈U⌉_) {D : _⌈U⌉_} (d : D) [hFunApp : mkIsFunApp₃ A B C d] :
        MetaM (HasFunctors.IsFunApp₃ (U := U) A B C d) := do
      pure { F := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₃.mkF h.h A B C D d),
             a := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₃.mka h.h A B C D d),
             b := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₃.mkb h.h A B C D d),
             c := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₃.mkc h.h A B C D d) }

  end mkIsFunApp₃

  class mkIsFunApp₄ (A B C D : _⌈U⌉_) {E : _⌈U⌉_} (e : E) extends
  mkHasFunctors'.mkIsFunApp₄ h.h A B C D E e

  namespace mkIsFunApp₄

    def reflect (A B C D : _⌈U⌉_) {E : _⌈U⌉_} (e : E) [hFunApp : mkIsFunApp₄ A B C D e] :
        MetaM (HasFunctors.IsFunApp₄ (U := U) A B C D e) := do
      pure { F := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₄.mkF h.h A B C D E e),
             a := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₄.mka h.h A B C D E e),
             b := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₄.mkb h.h A B C D E e),
             c := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₄.mkc h.h A B C D E e),
             d := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₄.mkd h.h A B C D E e) }

  end mkIsFunApp₄

  class mkIsFunApp₂' (A₁ A₂ : _⌈U⌉_) {B : _⌈U⌉_} (b : B) extends
  mkHasFunctors'.mkIsFunApp₂' h.h A₁ A₂ B b

  namespace mkIsFunApp₂'

    variable (A₁ A₂ : _⌈U⌉_) {B : _⌈U⌉_} (b : B) [mkIsFunApp₂' A₁ A₂ b]
  
    instance : mkIsFunApp A₁ b := ⟨⟩
    instance : mkIsFunApp A₂ b := ⟨⟩

  end mkIsFunApp₂'

  class mkIsFunApp₃' (A₁ A₂ A₃ : _⌈U⌉_) {B : _⌈U⌉_} (b : B) extends
  mkHasFunctors'.mkIsFunApp₃' h.h A₁ A₂ A₃ B b

  namespace mkIsFunApp₃'

    variable (A₁ A₂ A₃ : _⌈U⌉_) {B : _⌈U⌉_} (b : B) [mkIsFunApp₃' A₁ A₂ A₃ b]

    instance : mkIsFunApp A₁ b := ⟨⟩
    instance : mkIsFunApp₂' A₂ A₃ b := ⟨⟩

  end mkIsFunApp₃'

  class mkIsFunApp₄' (A₁ A₂ A₃ A₄ : _⌈U⌉_) {B : _⌈U⌉_} (b : B) extends
  mkHasFunctors'.mkIsFunApp₄' h.h A₁ A₂ A₃ A₄ B b

  namespace mkIsFunApp₄'

    variable (A₁ A₂ A₃ A₄ : _⌈U⌉_) {B : _⌈U⌉_} (b : B) [mkIsFunApp₄' A₁ A₂ A₃ A₄ b]

    instance : mkIsFunApp A₁ b := ⟨⟩
    instance : mkIsFunApp₃' A₂ A₃ A₄ b := ⟨⟩

  end mkIsFunApp₄'

  structure FunApp {B : _⌈U⌉_} (b : B) where
  {A       : _⌈U⌉_}
  (hFunApp : HasFunctors.IsFunApp (U := U) A b)

  -- `b` and `b'` must be defeq.
  def synthesizeFunApps'' {B : _⌈U⌉_} (b : B) {b' : B} : MetaM (List (FunApp b')) := do
    let A₁ : _⌈U⌉_ ← U.mkFreshTypeMVar
    let A₂ : _⌈U⌉_ ← U.mkFreshTypeMVar
    let A₃ : _⌈U⌉_ ← U.mkFreshTypeMVar
    let A₄ : _⌈U⌉_ ← U.mkFreshTypeMVar
    let hFunApp₄'? : Option (mkHasFunctors'.mkIsFunApp₄' h.h A₁ A₂ A₃ A₄ B b) ← InstanceExpr.synthesize?
    match hFunApp₄'? with
    | some hFunApp₄' =>
      let A₁ : _⌈U⌉_ ← A₁.instantiate
      let A₂ : _⌈U⌉_ ← A₂.instantiate
      let A₃ : _⌈U⌉_ ← A₃.instantiate
      let A₄ : _⌈U⌉_ ← A₄.instantiate
      let _ : mkIsFunApp₄' A₁ A₂ A₃ A₄ b' := { toInstanceExpr := ← hFunApp₄'.instantiate }
      pure [⟨← mkIsFunApp.reflect A₄ b'⟩,
            ⟨← mkIsFunApp.reflect A₃ b'⟩,
            ⟨← mkIsFunApp.reflect A₂ b'⟩,
            ⟨← mkIsFunApp.reflect A₁ b'⟩]
    | none =>
      let hFunApp₃'? : Option (mkHasFunctors'.mkIsFunApp₃' h.h A₁ A₂ A₃ B b) ← InstanceExpr.synthesize?
      match hFunApp₃'? with
      | some hFunApp₃' =>
        let A₁ : _⌈U⌉_ ← A₁.instantiate
        let A₂ : _⌈U⌉_ ← A₂.instantiate
        let A₃ : _⌈U⌉_ ← A₃.instantiate
        let _ : mkIsFunApp₃' A₁ A₂ A₃ b' := { toInstanceExpr := ← hFunApp₃'.instantiate }
        pure [⟨← mkIsFunApp.reflect A₃ b'⟩,
              ⟨← mkIsFunApp.reflect A₂ b'⟩,
              ⟨← mkIsFunApp.reflect A₁ b'⟩]
      | none =>
        let hFunApp₂'? : Option (mkHasFunctors'.mkIsFunApp₂' h.h A₁ A₂ B b) ← InstanceExpr.synthesize?
        match hFunApp₂'? with
        | some hFunApp₂' =>
          let A₁ : _⌈U⌉_ ← A₁.instantiate
          let A₂ : _⌈U⌉_ ← A₂.instantiate
          let _ : mkIsFunApp₂' A₁ A₂ b' := { toInstanceExpr := ← hFunApp₂'.instantiate }
          pure [⟨← mkIsFunApp.reflect A₂ b'⟩,
                ⟨← mkIsFunApp.reflect A₁ b'⟩]
        | none =>
          let hFunApp? : Option (mkHasFunctors'.mkIsFunApp h.h A₁ B b) ← InstanceExpr.synthesize?
          match hFunApp? with
          | some hFunApp =>
            let A₁ : _⌈U⌉_ ← A₁.instantiate
            let _ : mkIsFunApp A₁ b' := { toInstanceExpr := ← hFunApp.instantiate }
            pure [⟨← mkIsFunApp.reflect A₁ b'⟩]
          | none =>
            let hFunApp₂? : Option (mkHasFunctors'.mkIsFunApp₂ h.h A₁ A₂ B b) ← InstanceExpr.synthesize?
            match hFunApp₂? with
            | some hFunApp₂ =>
              let A₁ : _⌈U⌉_ ← A₁.instantiate
              let A₂ : _⌈U⌉_ ← A₂.instantiate
              let _ : mkIsFunApp₂ A₁ A₂ b' := { toInstanceExpr := ← hFunApp₂.instantiate }
              let _ ← mkIsFunApp₂.reflect A₁ A₂ b'
              pure [⟨HasFunctors.IsFunApp₂.isFunApp⟩]
            | none =>
              let hFunApp₃? : Option (mkHasFunctors'.mkIsFunApp₃ h.h A₁ A₂ A₃ B b) ← InstanceExpr.synthesize?
              match hFunApp₃? with
              | some hFunApp₃ =>
                let A₁ : _⌈U⌉_ ← A₁.instantiate
                let A₂ : _⌈U⌉_ ← A₂.instantiate
                let A₃ : _⌈U⌉_ ← A₃.instantiate
                let _ : mkIsFunApp₃ A₁ A₂ A₃ b' := { toInstanceExpr := ← hFunApp₃.instantiate }
                let _ ← mkIsFunApp₃.reflect A₁ A₂ A₃ b'
                pure [⟨HasFunctors.IsFunApp₃.isFunApp⟩]
              | none =>
                let hFunApp₄? : Option (mkHasFunctors'.mkIsFunApp₄ h.h A₁ A₂ A₃ A₄ B b) ← InstanceExpr.synthesize?
                match hFunApp₄? with
                | some hFunApp₄ =>
                  let A₁ : _⌈U⌉_ ← A₁.instantiate
                  let A₂ : _⌈U⌉_ ← A₂.instantiate
                  let A₃ : _⌈U⌉_ ← A₃.instantiate
                  let A₄ : _⌈U⌉_ ← A₄.instantiate
                  let _ : mkIsFunApp₄ A₁ A₂ A₃ A₄ b' := { toInstanceExpr := ← hFunApp₄.instantiate }
                  let _ ← mkIsFunApp₄.reflect A₁ A₂ A₃ A₄ b'
                  pure [⟨HasFunctors.IsFunApp₄.isFunApp⟩]
                | none => pure []

  def synthesizeFunApps' {B : _⌈U⌉_} (b : B) : MetaM (List (FunApp b)) :=
  synthesizeFunApps'' b

  def synthesizeFunApps {B : _⌈U⌉_} (b : B) : MetaM (List (FunApp b)) := do
    -- First check whether `b` is literally a functor application.
    -- This sees through some definitions that are opaque to type class synthesis.
    let A : _⌈U⌉_ ← _Universe.mkFreshTypeMVar
    let F : (A _⟶ B) ← _Universe.mkFreshInstMVar
    let a : A ← _Universe.mkFreshInstMVar
    if ← isDefEq b (F a) then
      let A : _⌈U⌉_ ← A.instantiate
      return [⟨{ F := ← U.instantiateInstMVars F,
                 a := ← U.instantiateInstMVars a }⟩]
    -- Now try to find an `IsFunApp` instance.
    match ← synthesizeFunApps' b with
    | List.nil => do
      -- Next, check if `b` is an application of `DefFun.F`. If it is, pass that to `IsFunApp`
      -- instead of the original value of `b`, as `IsFunApp` is usually defined on such terms.
      let A' : _⌈U⌉_ ← _Universe.mkFreshTypeMVar
      let B' : _⌈U⌉_ ← _Universe.mkFreshTypeMVar
      let f_b :  ⌜$A' → $B'⌝ ← TypedExpr.mkFreshMVar
      let b' : mkHasFunctors'.mkDefFun h.h A' B' f_b ← TypedExpr.mkFreshMVar
      let b'' : (A' _⟶ B') := mkHasFunctors'.mkDefFun.mkF h.h A' B' f_b b'
      if ← isDefEq b b'' then
        let A' : _⌈U⌉_ ← _Universe.instantiateTypeMVars A'
        let B' : _⌈U⌉_ ← _Universe.instantiateTypeMVars B'
        let f_b :  ⌜$A' → $B'⌝ ← f_b.instantiate
        let b' : mkHasFunctors'.mkDefFun h.h A' B' f_b ← b'.instantiate
        let b'' : B := mkHasFunctors'.mkDefFun.mkF h.h A' B' f_b b'
        return ← synthesizeFunApps'' b''
      pure []
    | result => result

end mkHasFunctors



def mkHasLinearLogic' {u v : Level} (U : ⌜Universe.{u, v}⌝) (hFun : mkHasFunctors' U) :=
⌜HasLinearLogic $U⌝

def mkHasLinearLogic (U : _Universe) [hFun : mkHasFunctors U] : ClassExpr :=
⟨mkHasLinearLogic' U.U hFun.h⟩

namespace mkHasLinearLogic

  variable {U : _Universe} [hFun : mkHasFunctors U] [h : mkHasLinearLogic U]

  def mkIdFun (A : _⌈U⌉_) : A _⟶ A :=
  let _ := h.h
  ⌜HasLinearLogic.idFun $A⌝

  def mkRevAppFun {A : _⌈U⌉_} (a : A) (B : _⌈U⌉_) : (A _⟶ B) _⟶ B :=
  let _ := h.h
  let a' : Q($A) := a
  ⌜HasLinearLogic.revAppFun $a' $B⌝

  def mkRevAppFun₂ (A B : _⌈U⌉_) : A _⟶ (A _⟶ B) _⟶ B :=
  let _ := h.h
  ⌜HasLinearLogic.revAppFun₂ $A $B⌝

  def mkCompFun {A B C : _⌈U⌉_} (F : A _⟶ B) (G : B _⟶ C) : A _⟶ C :=
  let _ := h.h
  let F' : Q($A ⟶ $B) := F
  let G' : Q($B ⟶ $C) := G
  ⌜$G' ⊙ $F'⌝

  def mkCompFun₂ {A B : _⌈U⌉_} (F : A _⟶ B) (C : _⌈U⌉_) : (B _⟶ C) _⟶ (A _⟶ C) :=
  let _ := h.h
  let F' : Q($A ⟶ $B) := F
  ⌜HasLinearLogic.compFun₂ $F' $C⌝

  def mkCompFun₃ (A B C : _⌈U⌉_) : (A _⟶ B) _⟶ (B _⟶ C) _⟶ (A _⟶ C) :=
  let _ := h.h
  ⌜HasLinearLogic.compFun₃ $A $B $C⌝

  def mkSwapFun {A B C : _⌈U⌉_} (F : A _⟶ B _⟶ C) (b : B) : A _⟶ C :=
  let _ := h.h
  let F' : Q($A ⟶ $B ⟶ $C) := F
  let b' : Q($B) := b
  ⌜HasLinearLogic.swapFun $F' $b'⌝

  def mkSwapFun₂ {A B C : _⌈U⌉_} (F : A _⟶ B _⟶ C) : B _⟶ A _⟶ C :=
  let _ := h.h
  let F' : Q($A ⟶ $B ⟶ $C) := F
  ⌜HasLinearLogic.swapFun₂ $F'⌝

  def mkSwapFun₃ (A B C : _⌈U⌉_) : (A _⟶ B _⟶ C) _⟶ (B _⟶ A _⟶ C) :=
  let _ := h.h
  ⌜HasLinearLogic.swapFun₃ $A $B $C⌝

  def mkRevCompFun₂ (A : _⌈U⌉_) {B C : _⌈U⌉_} (G : B _⟶ C) : (A _⟶ B) _⟶ (A _⟶ C) :=
  let _ := h.h
  let G' : Q($B ⟶ $C) := G
  ⌜HasLinearLogic.revCompFun₂ $A $G'⌝

  def mkRevCompFun₃ (A B C : _⌈U⌉_) : (B _⟶ C) _⟶ (A _⟶ B) _⟶ (A _⟶ C) :=
  let _ := h.h
  ⌜HasLinearLogic.revCompFun₃ $A $B $C⌝

  instance reflect : HasLinearLogic U :=
  { defIdFun      := λ A     => ⟨mkIdFun A⟩,
    defRevAppFun₂ := λ A B   => ⟨λ a => ⟨mkRevAppFun a B⟩,
                                 ⟨mkRevAppFun₂ (h := h) A B⟩⟩,
    defCompFun₃   := λ A B C => ⟨λ F => ⟨λ G => ⟨mkCompFun F G⟩,
                                         ⟨mkCompFun₂ F C⟩⟩,
                                 ⟨mkCompFun₃ A B C⟩⟩ }

end mkHasLinearLogic


def mkHasSubLinearLogic' {u v : Level} (U : ⌜Universe.{u, v}⌝) (hFun : mkHasFunctors' U) :=
⌜HasSubLinearLogic $U⌝

def mkHasSubLinearLogic (U : _Universe) [hFun : mkHasFunctors U] : ClassExpr :=
⟨mkHasSubLinearLogic' U.U hFun.h⟩

namespace mkHasSubLinearLogic

  variable {U : _Universe} [hFun : mkHasFunctors U] [h : mkHasSubLinearLogic U]

  def mkConstFun (A : _⌈U⌉_) {B : _⌈U⌉_} (b : B) : A _⟶ B :=
  let _ := h.h
  let b' : Q($B) := b
  ⌜HasSubLinearLogic.constFun $A $b'⌝

  def mkConstFun₂ (A B : _⌈U⌉_) : B _⟶ (A _⟶ B) :=
  let _ := h.h
  ⌜HasSubLinearLogic.constFun₂ $A $B⌝

  instance reflect : HasSubLinearLogic U :=
  { defConstFun₂ := λ A B => ⟨λ b => ⟨mkConstFun A b⟩,
                              ⟨mkConstFun₂ A B⟩⟩ }

end mkHasSubLinearLogic


def mkHasNonLinearLogic' {u v : Level} (U : ⌜Universe.{u, v}⌝) (hFun : mkHasFunctors' U) :=
⌜HasNonLinearLogic $U⌝

def mkHasNonLinearLogic (U : _Universe) [hFun : mkHasFunctors U] : ClassExpr :=
⟨mkHasNonLinearLogic' U.U hFun.h⟩

namespace mkHasNonLinearLogic

  variable {U : _Universe} [hFun : mkHasFunctors U] [h : mkHasNonLinearLogic U]

  def mkDupFun {A B : _⌈U⌉_} (F : A _⟶ A _⟶ B) : A _⟶ B :=
  let _ := h.h
  let F' : Q($A ⟶ $A ⟶ $B) := F
  ⌜HasNonLinearLogic.dupFun $F'⌝

  def mkDupFun₂ (A B : _⌈U⌉_) : (A _⟶ A _⟶ B) _⟶ (A _⟶ B) :=
  let _ := h.h
  ⌜HasNonLinearLogic.dupFun₂ $A $B⌝

  variable [hLin : mkHasLinearLogic U]

  def mkRevSelfAppFun {A B : _⌈U⌉_} (F : (A _⟶ B) _⟶ A) : (A _⟶ B) _⟶ B :=
  let _ := hLin.h
  let _ := h.h
  let F' : Q(($A ⟶ $B) ⟶ $A) := F
  ⌜HasNonLinearLogic.revSelfAppFun $F'⌝

  def mkRevSelfAppFun₂ (A B : _⌈U⌉_) : ((A _⟶ B) _⟶ A) _⟶ (A _⟶ B) _⟶ B :=
  let _ := hLin.h
  let _ := h.h
  ⌜HasNonLinearLogic.revSelfAppFun₂ $A $B⌝

  def mkSubstFun {A B C : _⌈U⌉_} (F : A _⟶ B) (G : A _⟶ B _⟶ C) : A _⟶ C :=
  let _ := hLin.h
  let _ := h.h
  let F' : Q($A ⟶ $B) := F
  let G' : Q($A ⟶ $B ⟶ $C) := G
  ⌜HasNonLinearLogic.substFun $F' $G'⌝

  def mkSubstFun₂ {A B : _⌈U⌉_} (F : A _⟶ B) (C : _⌈U⌉_) : (A _⟶ B _⟶ C) _⟶ (A _⟶ C) :=
  let _ := hLin.h
  let _ := h.h
  let F' : Q($A ⟶ $B) := F
  ⌜HasNonLinearLogic.substFun₂ $F' $C⌝

  def mkSubstFun₃ (A B C : _⌈U⌉_) : (A _⟶ B) _⟶ (A _⟶ B _⟶ C) _⟶ (A _⟶ C) :=
  let _ := hLin.h
  let _ := h.h
  ⌜HasNonLinearLogic.substFun₃ $A $B $C⌝

  def mkRevSubstFun₂ {A B C : _⌈U⌉_} (G : A _⟶ B _⟶ C) : (A _⟶ B) _⟶ (A _⟶ C) :=
  let _ := hLin.h
  let _ := h.h
  let G' : Q($A ⟶ $B ⟶ $C) := G
  ⌜HasNonLinearLogic.revSubstFun₂ $G'⌝

  def mkRevSubstFun₃ (A B C : _⌈U⌉_) : (A _⟶ B _⟶ C) _⟶ (A _⟶ B) _⟶ (A _⟶ C) :=
  let _ := hLin.h
  let _ := h.h
  ⌜HasNonLinearLogic.revSubstFun₃ $A $B $C⌝

  instance reflect : HasNonLinearLogic U :=
  { defDupFun₂ := λ A B => ⟨λ b => ⟨mkDupFun A b⟩,
                            ⟨mkDupFun₂ A B⟩⟩ }

end mkHasNonLinearLogic



#exit



  -- We can optimize equivalence relations of expressions by using a distinct value (`none`) for
  -- `refl` that we can treat specially in all operations.
  -- In particular, we can use `none` for all terms that are defeq.

  def optionalRelation {α β : Type} {inst : β → _Sort} (R : MetaRelation α (exprUniverse inst)) :
    MetaRelation α type :=
  λ a b => Option (R a b)

  namespace optionalRelation

    variable {α β : Type} {inst : β → _Sort} (R : MetaRelation α (exprUniverse inst))

    instance hasRefl : HasRefl (optionalRelation R) := ⟨λ _ => none⟩

    instance hasSymm [HasSymm R] : HasSymm (optionalRelation R) :=
    ⟨λ f => match f with
            | some f' => some f'⁻¹
            | none    => none⟩

    instance hasTrans [HasTrans R] : HasTrans (optionalRelation R) :=
    ⟨λ f g => match f, g with
              | some f', some g' => some (g' • f')
              | some f', none    => some f'
              | none,    some g' => some g'
              | none,    none    => none⟩

    instance isPreorder [HasTrans R] : IsPreorder (optionalRelation R) := ⟨⟩
    instance isEquivalence [HasSymm R] [HasTrans R] : IsEquivalence (optionalRelation R) := ⟨⟩

    def materialize [HasRefl R] {a b : α} : (optionalRelation R) a b → R a b
    | some e => e
    | none   => HasRefl.refl (R := R) a

  end optionalRelation






  @[reducible] def _MetaRelation {u : Level} (α : ⌜Sort u⌝) (V : _Universe) := ⌜$α → $α → $V.U⌝

  namespace _MetaRelation

    def reflect {u : Level} {α : ⌜Sort u⌝} {V : _Universe} (R : _MetaRelation α V) :
      MetaRelation α V :=
    λ a b => ⌜$R $a $b⌝

    instance {u : Level} (α : ⌜Sort u⌝) (V : _Universe) :
      CoeFun (_MetaRelation α V) (λ _ => MetaRelation α V) :=
    ⟨reflect⟩

    variable {u : Level} {α : ⌜Sort u⌝} {V : _Universe} (R : _MetaRelation α V)

    def mkHasRefl  : ClassExpr := ⟨⌜HasRefl  $R⌝⟩
    def mkHasSymm  : ClassExpr := ⟨⌜HasSymm  $R⌝⟩
    def mkHasTrans : ClassExpr := ⟨⌜HasTrans $R⌝⟩

    instance mkHasRefl.reflect [h : mkHasRefl R] : HasRefl (reflect R) :=
    let _ := h.h
    ⟨λ a => ⌜HasRefl.refl (R := $R) $a⌝⟩

    instance mkHasSymm.reflect [h : mkHasSymm R] : HasSymm (reflect R) :=
    let _ := h.h
    ⟨λ {a b} (e : Q($R $a $b)) => ⌜$e⁻¹⌝⟩

    instance mkHasTrans.reflect [h : mkHasTrans R] : HasTrans (reflect R) :=
    let _ := h.h
    ⟨λ {a b c} (e : Q($R $a $b)) (f : Q($R $b $c)) => ⌜$f • $e⌝⟩

    def mkIsPreorder : ClassExpr := ⟨⌜IsPreorder $R⌝⟩

    namespace mkIsPreorder

      variable [h : mkIsPreorder R]

      instance : mkHasRefl  R := let _ := h.h; ⟨⌜IsPreorder.toHasRefl⌝⟩
      instance : mkHasTrans R := let _ := h.h; ⟨⌜IsPreorder.toHasTrans⌝⟩

      instance reflect : IsPreorder (reflect R) := ⟨⟩

    end mkIsPreorder

    def mkIsEquivalence : ClassExpr := ⟨⌜IsEquivalence $R⌝⟩

    namespace mkIsEquivalence

      variable [h : mkIsEquivalence R]

      instance : mkIsPreorder R := let _ := h.h; ⟨⌜IsEquivalence.toIsPreorder⌝⟩
      instance : mkHasSymm    R := let _ := h.h; ⟨⌜IsEquivalence.toHasSymm⌝⟩

      instance reflect : IsEquivalence (reflect R) := ⟨⟩

    end mkIsEquivalence

  end _MetaRelation
