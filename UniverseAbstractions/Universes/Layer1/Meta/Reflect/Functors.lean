import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedFunctors
import UniverseAbstractions.Universes.Layer1.Meta.Reflect.Universes



namespace UniverseAbstractions.Layer1.Meta

set_option autoBoundImplicitLocal false

open Lean Lean.Meta Qq HasFunctors HasLinearLogic HasSubLinearLogic HasNonLinearLogic



def mkHasFunctors' {u v : Level} (U : Q(Universe.{u, v})) := ⌜HasFunctors $U⌝

namespace mkHasFunctors'

  variable {u v : Level} {U : Q(Universe.{u, v})}

  def mkArrow (A B : Q($U)) := ⌜$A → $B⌝
  def mkArrow.mkApp (A B : Q($U)) (f : Q($A → $B)) (a : Q($A)) : Q($B) := ⌜$f $a⌝

  variable (h : mkHasFunctors' U)

  def mkFun (A B : Q($U)) : Q($U) := ⌜$A ⟶ $B⌝

  def mkApplyFn (A B : Q($U)) (F : Q($A ⟶ $B)) : Q($A → $B) := ⌜apply $F⌝
  def mkApply (A B : Q($U)) (F : Q($A ⟶ $B)) (a : Q($A)) : Q($B) := ⌜$F $a⌝

  def mkDefFun (A B : Q($U)) (f : Q($A → $B)) := ⌜$A ⟶{$f} $B⌝

  namespace mkDefFun

    variable (A B : Q($U)) (f : Q($A → $B))

    def mkMk (F : Q($A ⟶ $B)) : mkDefFun h A B f := ⌜DefFun.mk (f := $f) $F⌝

    variable (F : mkDefFun h A B f)

    def mkF : Q($A ⟶ $B) := ⌜($F).F⌝

  end mkDefFun

  def mkIsFunApp (A B : Q($U)) (b : Q($B)) : ClassExpr := ⟨⌜IsFunApp $A $b⌝⟩

  namespace mkIsFunApp

    variable (A B : Q($U)) (b : Q($B)) [hFunApp : mkIsFunApp h A B b]

    def mkF : Q($A ⟶ $B) := ⌜($hFunApp.h).F⌝
    def mka : Q($A)      := ⌜($hFunApp.h).a⌝

  end mkIsFunApp

  def mkIsFunApp₂ (A B C : Q($U)) (c : Q($C)) : ClassExpr :=
  ⟨⌜IsFunApp₂ $A $B $c⌝⟩

  namespace mkIsFunApp₂

    variable (A B C : Q($U)) (c : Q($C)) [hFunApp : mkIsFunApp₂ h A B C c]

    def mkF : Q($A ⟶ $B ⟶ $C) := ⌜($hFunApp.h).F⌝
    def mka : Q($A)           := ⌜($hFunApp.h).a⌝
    def mkb : Q($B)           := ⌜($hFunApp.h).b⌝

  end mkIsFunApp₂

  def mkIsFunApp₃ (A B C D : Q($U)) (d : Q($D)) : ClassExpr :=
  ⟨⌜IsFunApp₃ $A $B $C $d⌝⟩

  namespace mkIsFunApp₃

    variable (A B C D : Q($U)) (d : Q($D)) [hFunApp : mkIsFunApp₃ h A B C D d]

    def mkF : Q($A ⟶ $B ⟶ $C ⟶ $D) := ⌜($hFunApp.h).F⌝
    def mka : Q($A)                := ⌜($hFunApp.h).a⌝
    def mkb : Q($B)                := ⌜($hFunApp.h).b⌝
    def mkc : Q($C)                := ⌜($hFunApp.h).c⌝

  end mkIsFunApp₃

  def mkIsFunApp₄ (A B C D E : Q($U)) (e : Q($E)) : ClassExpr :=
  ⟨⌜IsFunApp₄ $A $B $C $D $e⌝⟩

  namespace mkIsFunApp₄

    variable (A B C D E : Q($U)) (e : Q($E)) [hFunApp : mkIsFunApp₄ h A B C D E e]

    def mkF : Q($A ⟶ $B ⟶ $C ⟶ $D ⟶ $E) := ⌜($hFunApp.h).F⌝
    def mka : Q($A)                     := ⌜($hFunApp.h).a⌝
    def mkb : Q($B)                     := ⌜($hFunApp.h).b⌝
    def mkc : Q($C)                     := ⌜($hFunApp.h).c⌝
    def mkd : Q($D)                     := ⌜($hFunApp.h).d⌝

  end mkIsFunApp₄

  def mkIsFunApp₂' (A₁ A₂ B : Q($U)) (b : Q($B)) : ClassExpr :=
  ⟨⌜IsFunApp₂' $A₁ $A₂ $b⌝⟩

  namespace mkIsFunApp₂'

    variable (A₁ A₂ B : Q($U)) (b : Q($B)) [hFunApp₂ : mkIsFunApp₂' h A₁ A₂ B b]
  
    instance : mkIsFunApp h A₁ B b := ⟨⌜($hFunApp₂.h).h₂⌝⟩
    instance : mkIsFunApp h A₂ B b := ⟨⌜($hFunApp₂.h).toIsFunApp⌝⟩

  end mkIsFunApp₂'

  def mkIsFunApp₃' (A₁ A₂ A₃ B : Q($U)) (b : Q($B)) : ClassExpr :=
  ⟨⌜IsFunApp₃' $A₁ $A₂ $A₃ $b⌝⟩

  namespace mkIsFunApp₃'

    variable (A₁ A₂ A₃ B : Q($U)) (b : Q($B)) [hFunApp₃ : mkIsFunApp₃' h A₁ A₂ A₃ B b]

    instance : mkIsFunApp h A₁ B b := ⟨⌜($hFunApp₃.h).h₃⌝⟩
    instance : mkIsFunApp₂' h A₂ A₃ B b := ⟨⌜($hFunApp₃.h).toIsFunApp₂'⌝⟩

  end mkIsFunApp₃'

  def mkIsFunApp₄' (A₁ A₂ A₃ A₄ B : Q($U)) (b : Q($B)) : ClassExpr :=
  ⟨⌜IsFunApp₄' $A₁ $A₂ $A₃ $A₄ $b⌝⟩

  namespace mkIsFunApp₄'

    variable (A₁ A₂ A₃ A₄ B : Q($U)) (b : Q($B)) [hFunApp₄ : mkIsFunApp₄' h A₁ A₂ A₃ A₄ B b]

    instance : mkIsFunApp h A₁ B b := ⟨⌜($hFunApp₄.h).h₄⌝⟩
    instance : mkIsFunApp₃' h A₂ A₃ A₄ B b := ⟨⌜($hFunApp₄.h).toIsFunApp₃'⌝⟩

  end mkIsFunApp₄'

end mkHasFunctors'


def mkHasFunctors (U : _Universe) : ClassExpr := ⟨mkHasFunctors' U.U⟩

namespace mkHasFunctors

  variable {U : _Universe} [h : mkHasFunctors U]

  instance reflect : HasFunctors _(U) :=
  { Fun   := mkHasFunctors'.mkFun h.h,
    apply := λ {A B} => mkHasFunctors'.mkApply h.h A B }

  def mkArrow (A B : _(U)) := mkHasFunctors'.mkArrow (U := U.U) A B

  def mkApplyFn {A B : _(U)} (F : A ⟶ B) : mkArrow A B :=
  mkHasFunctors'.mkApplyFn h.h A B F

  def mkDefFun (A B : _(U)) (f : A ⟶ B) := mkHasFunctors'.mkDefFun h.h A B f

  namespace mkDefFun

    variable (A B : _(U)) (f : mkArrow A B)

    def mkMk (F : A ⟶ B) : mkDefFun A B f := mkHasFunctors'.mkDefFun.mkMk h.h A B f F

    variable (F : mkDefFun A B f)

    def mkF : A ⟶ B := mkHasFunctors'.mkDefFun.mkF h.h A B f F

  end mkDefFun

  class mkIsFunApp (A : _(U)) {B : _(U)} (b : B) extends
  mkHasFunctors'.mkIsFunApp h.h A B b

  namespace mkIsFunApp

    def reflect (A : _(U)) {B : _(U)} (b : B) [hFunApp : mkIsFunApp A b] :
        MetaM (IsFunApp (U := _(U)) A b) := do
      pure { F := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp.mkF h.h A B b),
             a := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp.mka h.h A B b) }

  end mkIsFunApp

  class mkIsFunApp₂ (A B : _(U)) {C : _(U)} (c : C) extends
  mkHasFunctors'.mkIsFunApp₂ h.h A B C c

  namespace mkIsFunApp₂

    def reflect (A B : _(U)) {C : _(U)} (c : C) [hFunApp : mkIsFunApp₂ A B c] :
        MetaM (IsFunApp₂ (U := _(U)) A B c) := do
      pure { F := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₂.mkF h.h A B C c),
             a := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₂.mka h.h A B C c),
             b := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₂.mkb h.h A B C c) }

  end mkIsFunApp₂

  class mkIsFunApp₃ (A B C : _(U)) {D : _(U)} (d : D) extends
  mkHasFunctors'.mkIsFunApp₃ h.h A B C D d

  namespace mkIsFunApp₃

    def reflect (A B C : _(U)) {D : _(U)} (d : D) [hFunApp : mkIsFunApp₃ A B C d] :
        MetaM (IsFunApp₃ (U := _(U)) A B C d) := do
      pure { F := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₃.mkF h.h A B C D d),
             a := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₃.mka h.h A B C D d),
             b := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₃.mkb h.h A B C D d),
             c := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₃.mkc h.h A B C D d) }

  end mkIsFunApp₃

  class mkIsFunApp₄ (A B C D : _(U)) {E : _(U)} (e : E) extends
  mkHasFunctors'.mkIsFunApp₄ h.h A B C D E e

  namespace mkIsFunApp₄

    def reflect (A B C D : _(U)) {E : _(U)} (e : E) [hFunApp : mkIsFunApp₄ A B C D e] :
        MetaM (IsFunApp₄ (U := _(U)) A B C D e) := do
      pure { F := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₄.mkF h.h A B C D E e),
             a := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₄.mka h.h A B C D E e),
             b := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₄.mkb h.h A B C D E e),
             c := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₄.mkc h.h A B C D E e),
             d := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₄.mkd h.h A B C D E e) }

  end mkIsFunApp₄

  class mkIsFunApp₂' (A₁ A₂ : _(U)) {B : _(U)} (b : B) extends
  mkHasFunctors'.mkIsFunApp₂' h.h A₁ A₂ B b

  namespace mkIsFunApp₂'

    variable (A₁ A₂ : _(U)) {B : _(U)} (b : B) [mkIsFunApp₂' A₁ A₂ b]
  
    instance : mkIsFunApp A₁ b := ⟨⟩
    instance : mkIsFunApp A₂ b := ⟨⟩

  end mkIsFunApp₂'

  class mkIsFunApp₃' (A₁ A₂ A₃ : _(U)) {B : _(U)} (b : B) extends
  mkHasFunctors'.mkIsFunApp₃' h.h A₁ A₂ A₃ B b

  namespace mkIsFunApp₃'

    variable (A₁ A₂ A₃ : _(U)) {B : _(U)} (b : B) [mkIsFunApp₃' A₁ A₂ A₃ b]

    instance : mkIsFunApp A₁ b := ⟨⟩
    instance : mkIsFunApp₂' A₂ A₃ b := ⟨⟩

  end mkIsFunApp₃'

  class mkIsFunApp₄' (A₁ A₂ A₃ A₄ : _(U)) {B : _(U)} (b : B) extends
  mkHasFunctors'.mkIsFunApp₄' h.h A₁ A₂ A₃ A₄ B b

  namespace mkIsFunApp₄'

    variable (A₁ A₂ A₃ A₄ : _(U)) {B : _(U)} (b : B) [mkIsFunApp₄' A₁ A₂ A₃ A₄ b]

    instance : mkIsFunApp A₁ b := ⟨⟩
    instance : mkIsFunApp₃' A₂ A₃ A₄ b := ⟨⟩

  end mkIsFunApp₄'

  structure FunApp {B : _(U)} (b : B) where
  {A       : _(U)}
  (hFunApp : IsFunApp (U := _(U)) A b)

  -- `b` and `b'` must be defeq.
  def synthesizeFunApps'' {B : _(U)} (b : B) {b' : B} : MetaM (List (FunApp b')) := do
    let A₁ : _(U) ← U.mkFreshTypeMVar
    let A₂ : _(U) ← U.mkFreshTypeMVar
    let A₃ : _(U) ← U.mkFreshTypeMVar
    let A₄ : _(U) ← U.mkFreshTypeMVar
    let hFunApp₄'? : Option (mkHasFunctors'.mkIsFunApp₄' h.h A₁ A₂ A₃ A₄ B b) ← InstanceExpr.synthesize?
    match hFunApp₄'? with
    | some hFunApp₄' =>
      let A₁ : _(U) ← _Universe.instantiateTypeMVars A₁
      let A₂ : _(U) ← _Universe.instantiateTypeMVars A₂
      let A₃ : _(U) ← _Universe.instantiateTypeMVars A₃
      let A₄ : _(U) ← _Universe.instantiateTypeMVars A₄
      let _ : mkIsFunApp₄' A₁ A₂ A₃ A₄ b' := { toInstanceExpr := ← hFunApp₄'.instantiate }
      pure [⟨← mkIsFunApp.reflect A₄ b'⟩,
            ⟨← mkIsFunApp.reflect A₃ b'⟩,
            ⟨← mkIsFunApp.reflect A₂ b'⟩,
            ⟨← mkIsFunApp.reflect A₁ b'⟩]
    | none =>
      let hFunApp₃'? : Option (mkHasFunctors'.mkIsFunApp₃' h.h A₁ A₂ A₃ B b) ← InstanceExpr.synthesize?
      match hFunApp₃'? with
      | some hFunApp₃' =>
        let A₁ : _(U) ← _Universe.instantiateTypeMVars A₁
        let A₂ : _(U) ← _Universe.instantiateTypeMVars A₂
        let A₃ : _(U) ← _Universe.instantiateTypeMVars A₃
        let _ : mkIsFunApp₃' A₁ A₂ A₃ b' := { toInstanceExpr := ← hFunApp₃'.instantiate }
        pure [⟨← mkIsFunApp.reflect A₃ b'⟩,
              ⟨← mkIsFunApp.reflect A₂ b'⟩,
              ⟨← mkIsFunApp.reflect A₁ b'⟩]
      | none =>
        let hFunApp₂'? : Option (mkHasFunctors'.mkIsFunApp₂' h.h A₁ A₂ B b) ← InstanceExpr.synthesize?
        match hFunApp₂'? with
        | some hFunApp₂' =>
          let A₁ : _(U) ← _Universe.instantiateTypeMVars A₁
          let A₂ : _(U) ← _Universe.instantiateTypeMVars A₂
          let _ : mkIsFunApp₂' A₁ A₂ b' := { toInstanceExpr := ← hFunApp₂'.instantiate }
          pure [⟨← mkIsFunApp.reflect A₂ b'⟩,
                ⟨← mkIsFunApp.reflect A₁ b'⟩]
        | none =>
          let hFunApp? : Option (mkHasFunctors'.mkIsFunApp h.h A₁ B b) ← InstanceExpr.synthesize?
          match hFunApp? with
          | some hFunApp =>
            let A₁ : _(U) ← _Universe.instantiateTypeMVars A₁
            let _ : mkIsFunApp A₁ b' := { toInstanceExpr := ← hFunApp.instantiate }
            pure [⟨← mkIsFunApp.reflect A₁ b'⟩]
          | none =>
            let hFunApp₂? : Option (mkHasFunctors'.mkIsFunApp₂ h.h A₁ A₂ B b) ← InstanceExpr.synthesize?
            match hFunApp₂? with
            | some hFunApp₂ =>
              let A₁ : _(U) ← _Universe.instantiateTypeMVars A₁
              let A₂ : _(U) ← _Universe.instantiateTypeMVars A₂
              let _ : mkIsFunApp₂ A₁ A₂ b' := { toInstanceExpr := ← hFunApp₂.instantiate }
              let _ ← mkIsFunApp₂.reflect A₁ A₂ b'
              pure [⟨IsFunApp₂.isFunApp⟩]
            | none =>
              let hFunApp₃? : Option (mkHasFunctors'.mkIsFunApp₃ h.h A₁ A₂ A₃ B b) ← InstanceExpr.synthesize?
              match hFunApp₃? with
              | some hFunApp₃ =>
                let A₁ : _(U) ← _Universe.instantiateTypeMVars A₁
                let A₂ : _(U) ← _Universe.instantiateTypeMVars A₂
                let A₃ : _(U) ← _Universe.instantiateTypeMVars A₃
                let _ : mkIsFunApp₃ A₁ A₂ A₃ b' := { toInstanceExpr := ← hFunApp₃.instantiate }
                let _ ← mkIsFunApp₃.reflect A₁ A₂ A₃ b'
                pure [⟨IsFunApp₃.isFunApp⟩]
              | none =>
                let hFunApp₄? : Option (mkHasFunctors'.mkIsFunApp₄ h.h A₁ A₂ A₃ A₄ B b) ← InstanceExpr.synthesize?
                match hFunApp₄? with
                | some hFunApp₄ =>
                  let A₁ : _(U) ← _Universe.instantiateTypeMVars A₁
                  let A₂ : _(U) ← _Universe.instantiateTypeMVars A₂
                  let A₃ : _(U) ← _Universe.instantiateTypeMVars A₃
                  let A₄ : _(U) ← _Universe.instantiateTypeMVars A₄
                  let _ : mkIsFunApp₄ A₁ A₂ A₃ A₄ b' := { toInstanceExpr := ← hFunApp₄.instantiate }
                  let _ ← mkIsFunApp₄.reflect A₁ A₂ A₃ A₄ b'
                  pure [⟨IsFunApp₄.isFunApp⟩]
                | none => pure []

  def synthesizeFunApps' {B : _(U)} (b : B) : MetaM (List (FunApp b)) :=
  synthesizeFunApps'' b

  def synthesizeFunApps {B : _(U)} (b : B) : MetaM (List (FunApp b)) := do
    -- First check whether `b` is literally a functor application.
    -- This sees through some definitions that are opaque to type class synthesis.
    let A : _(U) ← _Universe.mkFreshTypeMVar
    let F : (A ⟶ B) ← _Universe.mkFreshInstMVar
    let a : A ← _Universe.mkFreshInstMVar
    if ← isDefEq b (F a) then
      let A : _(U) ← _Universe.instantiateTypeMVars A
      let F : (A ⟶ B) ← _Universe.instantiateInstMVars F
      let a : A ← _Universe.instantiateInstMVars a
      return [⟨⟨F, a⟩⟩]
    -- Now try to find an `IsFunApp` instance.
    match ← synthesizeFunApps' b with
    | List.nil => do
      -- Next, check if `b` is an application of `DefFun.F`. If it is, pass that to `IsFunApp`
      -- instead of the original value of `b`, as `IsFunApp` is usually defined on such terms.
      let A' : _(U) ← _Universe.mkFreshTypeMVar
      let B' : _(U) ← _Universe.mkFreshTypeMVar
      let f_b :  mkArrow A' B' ← TypedExpr.mkFreshMVar
      let b' : mkHasFunctors'.mkDefFun h.h A' B' f_b ← TypedExpr.mkFreshMVar
      let b'' : (A' ⟶ B') := mkHasFunctors'.mkDefFun.mkF h.h A' B' f_b b'
      if ← isDefEq b b'' then
        let A' : _(U) ← _Universe.instantiateTypeMVars A'
        let B' : _(U) ← _Universe.instantiateTypeMVars B'
        let f_b : mkArrow A' B' ← f_b.instantiate
        let b' : mkHasFunctors'.mkDefFun h.h A' B' f_b ← b'.instantiate
        let b'' : B := mkHasFunctors'.mkDefFun.mkF h.h A' B' f_b b'
        return ← synthesizeFunApps'' b''
      pure []
    | result => pure result

end mkHasFunctors



def mkHasLinearLogic' {u v : Level} (U : Q(Universe.{u, v})) (hFun : mkHasFunctors' U) :=
⌜HasLinearLogic $U⌝

namespace mkHasLinearLogic'

  variable {u v : Level} (U : Q(Universe.{u, v})) {hFun : mkHasFunctors' U}
           (h : mkHasLinearLogic' U hFun)

  def mkIdFun (A : Q($U)) : Q($A ⟶ $A) := ⌜idFun $A⌝

  def mkRevAppFun (A B : Q($U)) (a : Q($A)) : Q(($A ⟶ $B) ⟶ $B) := ⌜revAppFun $a $B⌝
  def mkRevAppFun₂ (A B : Q($U)) : Q($A ⟶ ($A ⟶ $B) ⟶ $B) := ⌜revAppFun₂ $A $B⌝

  def mkCompFun (A B C : Q($U)) (F : Q($A ⟶ $B)) (G : Q($B ⟶ $C)) : Q($A ⟶ $C) := ⌜$G ⊙ $F⌝
  def mkCompFun₂ (A B C : Q($U)) (F : Q($A ⟶ $B)) : Q(($B ⟶ $C) ⟶ ($A ⟶ $C)) := ⌜compFun₂ $F $C⌝
  def mkCompFun₃ (A B C : Q($U)) : Q(($A ⟶ $B) ⟶ ($B ⟶ $C) ⟶ ($A ⟶ $C)) := ⌜compFun₃ $A $B $C⌝

  def mkSwapFun (A B C : Q($U)) (F : Q($A ⟶ $B ⟶ $C)) (b : Q($B)) : Q($A ⟶ $C) := ⌜swapFun $F $b⌝

end mkHasLinearLogic'


def mkHasLinearLogic (U : _Universe) [hFun : mkHasFunctors U] : ClassExpr :=
⟨mkHasLinearLogic' U.U hFun.h⟩

namespace mkHasLinearLogic

  variable {U : _Universe} [hFun : mkHasFunctors U] [h : mkHasLinearLogic U]

  def mkIdFun (A : _(U)) : A ⟶ A := mkHasLinearLogic'.mkIdFun U.U h.h A

  def mkRevAppFun {A : _(U)} (a : A) (B : _(U)) : (A ⟶ B) ⟶ B :=
  mkHasLinearLogic'.mkRevAppFun U.U h.h A B a
  def mkRevAppFun₂ (A B : _(U)) : A ⟶ (A ⟶ B) ⟶ B := mkHasLinearLogic'.mkRevAppFun₂ U.U h.h A B

  def mkCompFun {A B C : _(U)} (F : A ⟶ B) (G : B ⟶ C) : A ⟶ C :=
  mkHasLinearLogic'.mkCompFun U.U h.h A B C F G
  def mkCompFun₂ {A B : _(U)} (F : A ⟶ B) (C : _(U)) : (B ⟶ C) ⟶ (A ⟶ C) :=
  mkHasLinearLogic'.mkCompFun₂ U.U h.h A B C F
  def mkCompFun₃ (A B C : _(U)) : (A ⟶ B) ⟶ (B ⟶ C) ⟶ (A ⟶ C) :=
  mkHasLinearLogic'.mkCompFun₃ U.U h.h A B C

  def mkSwapFun {A B C : _(U)} (F : A ⟶ B ⟶ C) (b : B) : A ⟶ C :=
  mkHasLinearLogic'.mkSwapFun U.U h.h A B C F b

  instance reflect : HasLinearLogic _(U) :=
  { defIdFun      := λ A     => ⟨mkIdFun A⟩,
    defRevAppFun₂ := λ A B   => ⟨λ a => ⟨mkRevAppFun a B⟩,
                                 ⟨mkRevAppFun₂ A B⟩⟩,
    defCompFun₃   := λ A B C => ⟨λ F => ⟨λ G => ⟨mkCompFun F G⟩,
                                         ⟨mkCompFun₂ F C⟩⟩,
                                 ⟨mkCompFun₃ A B C⟩⟩ }

end mkHasLinearLogic



def mkHasSubLinearLogic' {u v : Level} (U : Q(Universe.{u, v})) (hFun : mkHasFunctors' U) :=
⌜HasSubLinearLogic $U⌝

namespace mkHasSubLinearLogic'

  variable {u v : Level} (U : Q(Universe.{u, v})) {hFun : mkHasFunctors' U}
           (h : mkHasSubLinearLogic' U hFun)

  def mkConstFun (A B : Q($U)) (b : Q($B)) : Q($A ⟶ $B) := ⌜constFun $A $b⌝
  def mkConstFun₂ (A B : Q($U)) : Q($B ⟶ ($A ⟶ $B)) := ⌜constFun₂ $A $B⌝

end mkHasSubLinearLogic'


def mkHasSubLinearLogic (U : _Universe) [hFun : mkHasFunctors U] : ClassExpr :=
⟨mkHasSubLinearLogic' U.U hFun.h⟩

namespace mkHasSubLinearLogic

  variable {U : _Universe} [hFun : mkHasFunctors U] [h : mkHasSubLinearLogic U]

  def mkConstFun (A : _(U)) {B : _(U)} (b : B) : A ⟶ B :=
  mkHasSubLinearLogic'.mkConstFun U.U h.h A B b
  def mkConstFun₂ (A B : _(U)) : B ⟶ (A ⟶ B) := mkHasSubLinearLogic'.mkConstFun₂ U.U h.h A B

  instance reflect : HasSubLinearLogic _(U) :=
  { defConstFun₂ := λ A B => ⟨λ b => ⟨mkConstFun A b⟩,
                              ⟨mkConstFun₂ A B⟩⟩ }

end mkHasSubLinearLogic



def mkHasNonLinearLogic' {u v : Level} (U : Q(Universe.{u, v})) (hFun : mkHasFunctors' U) :=
⌜HasNonLinearLogic $U⌝

namespace mkHasNonLinearLogic'

  variable {u v : Level} (U : Q(Universe.{u, v})) {hFun : mkHasFunctors' U}
           (h : mkHasNonLinearLogic' U hFun)

  def mkDupFun (A B : Q($U)) (F : Q($A ⟶ $A ⟶ $B)) : Q($A ⟶ $B) := ⌜dupFun $F⌝
  def mkDupFun₂ (A B : Q($U)) : Q(($A ⟶ $A ⟶ $B) ⟶ ($A ⟶ $B)) := ⌜dupFun₂ $A $B⌝

  variable (hLin : mkHasLinearLogic' U hFun)

  def mkRevSelfAppFun (A B : Q($U)) (F : Q(($A ⟶ $B) ⟶ $A)) : Q(($A ⟶ $B) ⟶ $B) :=
  ⌜revSelfAppFun $F⌝

  def mkSubstFun (A B C : Q($U)) (F : Q($A ⟶ $B)) (G : Q($A ⟶ $B ⟶ $C)) : Q($A ⟶ $C) :=
  ⌜substFun $F $G⌝

end mkHasNonLinearLogic'


def mkHasNonLinearLogic (U : _Universe) [hFun : mkHasFunctors U] : ClassExpr :=
⟨mkHasNonLinearLogic' U.U hFun.h⟩

namespace mkHasNonLinearLogic

  variable {U : _Universe} [hFun : mkHasFunctors U] [h : mkHasNonLinearLogic U]

  def mkDupFun {A B : _(U)} (F : A ⟶ A ⟶ B) : A ⟶ B := mkHasNonLinearLogic'.mkDupFun U.U h.h A B F
  def mkDupFun₂ (A B : _(U)) : (A ⟶ A ⟶ B) ⟶ (A ⟶ B) := mkHasNonLinearLogic'.mkDupFun₂ U.U h.h A B

  variable [hLin : mkHasLinearLogic U]

  def mkRevSelfAppFun {A B : _(U)} (F : (A ⟶ B) ⟶ A) : (A ⟶ B) ⟶ B :=
  mkHasNonLinearLogic'.mkRevSelfAppFun U.U h.h hLin.h A B F

  def mkSubstFun {A B C : _(U)} (F : A ⟶ B) (G : A ⟶ B ⟶ C) : A ⟶ C :=
  mkHasNonLinearLogic'.mkSubstFun U.U h.h hLin.h A B C F G

  instance reflect : HasNonLinearLogic _(U) :=
  { defDupFun₂ := λ A B => ⟨λ b => ⟨mkDupFun A b⟩,
                            ⟨mkDupFun₂ A B⟩⟩ }

end mkHasNonLinearLogic
