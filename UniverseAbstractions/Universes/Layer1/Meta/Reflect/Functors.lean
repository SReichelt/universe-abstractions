import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Meta.Reflect.Universes



namespace UniverseAbstractions.Layer1.Meta

set_option autoBoundImplicitLocal false
set_option synthInstance.maxHeartbeats 10000

open Lean Lean.Meta Qq UniverseAbstractions.Meta
     HasFunctors



def mkHasFunctors' {u v vv : Level} (α : Q(Sort u)) (V : Q(Universe.{v, vv})) :=
  ⌜HasFunctors $α $V⌝

namespace mkHasFunctors'

  variable {v vv : Level}

  section

    variable {u : Level} (α : Q(Sort u)) (V : Q(Universe.{v, vv}))

    def mkArrow (Y : Q($V)) := ⌜$α → $Y⌝

    def mkArrow.mkApp (Y : Q($V))
                      (f : Q($α → $Y)) (a : Q($α)) : Q($Y) :=
      ⌜$f $a⌝
  
  end

  variable {V : Q(Universe.{v, vv})}

  section

    variable {u : Level} {α : Q(Sort u)} (hα : mkHasFunctors' α V) (Y : Q($V))

    def mkFun : Q($V) := ⌜$α ⥤ $Y⌝

    def mkApplyFn (F : Q($α ⥤ $Y)) : Q($α → $Y) := ⌜apply $F⌝
    def mkApply (F : Q($α ⥤ $Y)) (a : Q($α)) : Q($Y) := ⌜$F $a⌝

    def mkDefFun (f : Q($α → $Y)) := ⌜$α ⥤{$f} $Y⌝

    namespace mkDefFun

      variable (f : Q($α → $Y))

      def mkMk (F : Q($α ⥤ $Y)) : mkDefFun hα Y f := ⌜DefFun.mk (f := $f) $F⌝

      variable (F : mkDefFun hα Y f)

      def mkInst : Q($α ⥤ $Y) := ⌜($F).inst⌝

    end mkDefFun

  end

  section

    variable {u : Level} {α : Q(Sort u)} (hα : mkHasFunctors' α V) (Y : Q($V)) (y : Q($Y))

    def mkIsFunApp : ClassExpr := ⟨⌜IsFunApp $α $y⌝⟩

    namespace mkIsFunApp

      variable [hFunApp : mkIsFunApp hα Y y]

      def mkF : Q($α ⥤ $Y) := ⌜($hFunApp.h).F⌝
      def mka : Q($α)      := ⌜($hFunApp.h).a⌝

    end mkIsFunApp

  end

  section

    variable {u u' : Level} {α : Q(Sort u)} {β : Q(Sort u')} (hα : mkHasFunctors' α V)
             (hβ : mkHasFunctors' β V) (Y : Q($V)) (y : Q($Y))

    def mkIsFunApp₂ : ClassExpr := ⟨⌜IsFunApp₂ $α $β $y⌝⟩

    namespace mkIsFunApp₂

      variable [hFunApp : mkIsFunApp₂ hα hβ Y y]

      def mkF : Q($α ⥤ $β ⥤ $Y) := ⌜($hFunApp.h).F⌝
      def mka : Q($α)           := ⌜($hFunApp.h).a⌝
      def mkb : Q($β)           := ⌜($hFunApp.h).b⌝

    end mkIsFunApp₂

    def mkIsFunApp₂' : ClassExpr := ⟨⌜IsFunApp₂' $α $β $y⌝⟩

    namespace mkIsFunApp₂'

      variable [hFunApp₂ : mkIsFunApp₂' hα hβ Y y]
    
      instance : mkIsFunApp hα Y y := ⟨⌜($hFunApp₂.h).h₂⌝⟩
      instance : mkIsFunApp hβ Y y := ⟨⌜($hFunApp₂.h).toIsFunApp⌝⟩

    end mkIsFunApp₂'

  end

  section

    variable {u u' u'' : Level} {α : Q(Sort u)} {β : Q(Sort u')} {γ : Q(Sort u'')}
             (hα : mkHasFunctors' α V) (hβ : mkHasFunctors' β V) (hγ : mkHasFunctors' γ V)
             (Y : Q($V)) (y : Q($Y))

    def mkIsFunApp₃ : ClassExpr := ⟨⌜IsFunApp₃ $α $β $γ $y⌝⟩

    namespace mkIsFunApp₃

      variable [hFunApp : mkIsFunApp₃ hα hβ hγ Y y]

      def mkF : Q($α ⥤ $β ⥤ $γ ⥤ $Y) := ⌜($hFunApp.h).F⌝
      def mka : Q($α)                := ⌜($hFunApp.h).a⌝
      def mkb : Q($β)                := ⌜($hFunApp.h).b⌝
      def mkc : Q($γ)                := ⌜($hFunApp.h).c⌝

    end mkIsFunApp₃

    def mkIsFunApp₃' : ClassExpr := ⟨⌜IsFunApp₃' $α $β $γ $y⌝⟩

    namespace mkIsFunApp₃'

      variable [hFunApp₃ : mkIsFunApp₃' hα hβ hγ Y y]
    
      instance : mkIsFunApp hα Y y := ⟨⌜($hFunApp₃.h).h₃⌝⟩
      instance : mkIsFunApp₂' hβ hγ Y y := ⟨⌜($hFunApp₃.h).toIsFunApp₂'⌝⟩

    end mkIsFunApp₃'

  end

  section

    variable {u u' u'' u''' : Level} {α : Q(Sort u)} {β : Q(Sort u')} {γ : Q(Sort u'')}
             {δ : Q(Sort u''')} (hα : mkHasFunctors' α V) (hβ : mkHasFunctors' β V)
             (hγ : mkHasFunctors' γ V) (hδ : mkHasFunctors' δ V) (Y : Q($V)) (y : Q($Y))

    def mkIsFunApp₄ : ClassExpr := ⟨⌜IsFunApp₄ $α $β $γ $δ $y⌝⟩

    namespace mkIsFunApp₄

      variable [hFunApp : mkIsFunApp₄ hα hβ hγ hδ Y y]

      def mkF : Q($α ⥤ $β ⥤ $γ ⥤ $δ ⥤ $Y) := ⌜($hFunApp.h).F⌝
      def mka : Q($α)                     := ⌜($hFunApp.h).a⌝
      def mkb : Q($β)                     := ⌜($hFunApp.h).b⌝
      def mkc : Q($γ)                     := ⌜($hFunApp.h).c⌝
      def mkd : Q($δ)                     := ⌜($hFunApp.h).d⌝

    end mkIsFunApp₄

    def mkIsFunApp₄' : ClassExpr := ⟨⌜IsFunApp₄' $α $β $γ $δ $y⌝⟩

    namespace mkIsFunApp₄'

      variable [hFunApp₄ : mkIsFunApp₄' hα hβ hγ hδ Y y]
    
      instance : mkIsFunApp hα Y y := ⟨⌜($hFunApp₄.h).h₄⌝⟩
      instance : mkIsFunApp₃' hβ hγ hδ Y y := ⟨⌜($hFunApp₄.h).toIsFunApp₃'⌝⟩

    end mkIsFunApp₄'

  end

end mkHasFunctors'

def mkHasFunctors (α : _Sort) (V : _Universe) : ClassExpr := ⟨mkHasFunctors' α.α V.U⟩

namespace mkHasFunctors

  instance reflect (α : _Sort) (V : _Universe) [hα : mkHasFunctors α V] :
      HasFunctors α _(V) where
    defFunType Y := { A    := mkHasFunctors'.mkFun   hα.h Y,
                      elim := mkHasFunctors'.mkApply hα.h Y }

  instance reflect' {U V : _Universe} (A : _(U)) [hA : mkHasFunctors _⌈A⌉ V] : HasFunctors A _(V) :=
    reflect _⌈A⌉ V

  variable {u : Level} {V : _Universe}

  def mkArrow (α : _Sort) (Y : _(V)) := mkHasFunctors'.mkArrow α.α V.U Y

  def mkApplyFn {α : _Sort} [hα : mkHasFunctors α V] {Y : _(V)} (F : α ⥤ Y) : mkArrow α Y :=
    mkHasFunctors'.mkApplyFn hα.h Y F

  section

    variable (α : _Sort) [hα : mkHasFunctors α V] (Y : _(V))

    def mkDefFun (f : α ⥤ Y) := mkHasFunctors'.mkDefFun hα.h Y f

    namespace mkDefFun

      variable (f : mkArrow α Y)

      def mkMk (F : α ⥤ Y) : mkDefFun α Y f := mkHasFunctors'.mkDefFun.mkMk hα.h Y f F

      variable (F : mkDefFun α Y f)

      def mkInst : α ⥤ Y := mkHasFunctors'.mkDefFun.mkInst hα.h Y f F

    end mkDefFun

  end

  section

    variable (α : _Sort) [hα : mkHasFunctors α V] {Y : _(V)} (y : Y)

    class mkIsFunApp extends mkHasFunctors'.mkIsFunApp hα.h Y y

    namespace mkIsFunApp

      def reflect [hFunApp : mkIsFunApp α y] : MetaM (IsFunApp α y) := do
        pure { F := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp.mkF hα.h Y y),
               a := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp.mka hα.h Y y) }

    end mkIsFunApp

  end

  section

    variable (α β : _Sort) [hα : mkHasFunctors α V] [hβ : mkHasFunctors β V] {Y : _(V)} (y : Y)

    class mkIsFunApp₂ extends mkHasFunctors'.mkIsFunApp₂ hα.h hβ.h Y y

    namespace mkIsFunApp₂

      def reflect [hFunApp : mkIsFunApp₂ α β y] : MetaM (IsFunApp₂ α β y) := do
        pure { F := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₂.mkF hα.h hβ.h Y y),
               a := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₂.mka hα.h hβ.h Y y),
               b := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₂.mkb hα.h hβ.h Y y) }

    end mkIsFunApp₂

    class mkIsFunApp₂' extends mkHasFunctors'.mkIsFunApp₂' hα.h hβ.h Y y

    namespace mkIsFunApp₂'

      variable [mkIsFunApp₂' α β y]
    
      instance : mkIsFunApp α y := ⟨⟩
      instance : mkIsFunApp β y := ⟨⟩

    end mkIsFunApp₂'

  end

  section

    variable (α β γ : _Sort) [hα : mkHasFunctors α V] [hβ : mkHasFunctors β V]
             [hγ : mkHasFunctors γ V] {Y : _(V)} (y : Y)

    class mkIsFunApp₃ extends mkHasFunctors'.mkIsFunApp₃ hα.h hβ.h hγ.h Y y

    namespace mkIsFunApp₃

      def reflect [hFunApp : mkIsFunApp₃ α β γ y] : MetaM (IsFunApp₃ α β γ y) := do
        pure { F := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₃.mkF hα.h hβ.h hγ.h Y y),
               a := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₃.mka hα.h hβ.h hγ.h Y y),
               b := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₃.mkb hα.h hβ.h hγ.h Y y),
               c := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₃.mkc hα.h hβ.h hγ.h Y y) }

    end mkIsFunApp₃

    class mkIsFunApp₃' extends mkHasFunctors'.mkIsFunApp₃' hα.h hβ.h hγ.h Y y

    namespace mkIsFunApp₃'

      variable [mkIsFunApp₃' α β γ y]

      instance : mkIsFunApp α y := ⟨⟩
      instance : mkIsFunApp₂' β γ y := ⟨⟩

    end mkIsFunApp₃'

  end

  section

    variable (α β γ δ : _Sort) [hα : mkHasFunctors α V] [hβ : mkHasFunctors β V]
             [hγ : mkHasFunctors γ V] [hδ : mkHasFunctors δ V] {Y : _(V)} (y : Y)

    class mkIsFunApp₄ extends mkHasFunctors'.mkIsFunApp₄ hα.h hβ.h hγ.h hδ.h Y y

    namespace mkIsFunApp₄

      def reflect [hFunApp : mkIsFunApp₄ α β γ δ y] : MetaM (IsFunApp₄ α β γ δ y) := do
        pure { F := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₄.mkF hα.h hβ.h hγ.h hδ.h Y y),
               a := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₄.mka hα.h hβ.h hγ.h hδ.h Y y),
               b := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₄.mkb hα.h hβ.h hγ.h hδ.h Y y),
               c := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₄.mkc hα.h hβ.h hγ.h hδ.h Y y),
               d := ← TypedExpr.unfold_once (mkHasFunctors'.mkIsFunApp₄.mkd hα.h hβ.h hγ.h hδ.h Y y) }

    end mkIsFunApp₄

    class mkIsFunApp₄' extends mkHasFunctors'.mkIsFunApp₄' hα.h hβ.h hγ.h hδ.h Y y

    namespace mkIsFunApp₄'

      variable [mkIsFunApp₄' α β γ δ y]

      instance : mkIsFunApp α y := ⟨⟩
      instance : mkIsFunApp₃' β γ δ y := ⟨⟩

    end mkIsFunApp₄'

  end

end mkHasFunctors


def mkHasUnivFunctors' {u uu v vv : Level} (U : Q(Universe.{u, uu})) (V : Q(Universe.{v, vv})) :=
  ⌜HasUnivFunctors $U $V⌝

namespace mkHasUnivFunctors'

  variable {u uu v vv : Level} {U : Q(Universe.{u, uu})} {V : Q(Universe.{v, vv})}
           (h : mkHasUnivFunctors' U V)

  instance mkHasFunctors' (A : Q($U)) : mkHasFunctors' ⌜$A⌝ V := ⌜inferInstance⌝

end mkHasUnivFunctors'

def mkHasUnivFunctors (U V : _Universe) : ClassExpr := ⟨mkHasUnivFunctors' U.U V.U⟩

namespace mkHasUnivFunctors

  variable (U V : _Universe) [h : mkHasUnivFunctors U V]

  instance mkHasFunctors (A : _(U)) : mkHasFunctors _⌈A⌉ V :=
    ⟨mkHasUnivFunctors'.mkHasFunctors' h.h A⟩

  instance reflect : HasUnivFunctors _(U) _(V) := ⟨⟩

end mkHasUnivFunctors



structure FunApp {V : _Universe} {Y : _(V)} (y : Y) where
  {α      : _Sort}
  [h      : mkHasFunctors α V]
  hFunApp : IsFunApp α y

namespace FunApp

  open mkHasFunctors

  variable {V : _Universe} {Y : _(V)} (y : Y)

  -- `y` and `y'` must be defeq.
  def synthesizeFunApps' {y' : Y} : MetaM (List (FunApp y')) := do
    let u ← mkFreshLevelMVar
    let α ← _Sort.mkFreshMVar
    let β ← _Sort.mkFreshMVar
    let γ ← _Sort.mkFreshMVar
    let δ ← _Sort.mkFreshMVar
    let hα : mkHasFunctors α V ← InstanceExpr.mkFreshMVar
    let hβ : mkHasFunctors β V ← InstanceExpr.mkFreshMVar
    let hγ : mkHasFunctors γ V ← InstanceExpr.mkFreshMVar
    let hδ : mkHasFunctors δ V ← InstanceExpr.mkFreshMVar
    let hFunApp₄'? : Option (mkHasFunctors'.mkIsFunApp₄' hα.h hβ.h hγ.h hδ.h Y y)
        ← InstanceExpr.synthesize?
    match hFunApp₄'? with
    | some hFunApp₄' =>
      let α ← α.instantiate
      let β ← β.instantiate
      let γ ← γ.instantiate
      let δ ← δ.instantiate
      let hα : mkHasFunctors α V ← hα.instantiate
      let hβ : mkHasFunctors β V ← hβ.instantiate
      let hγ : mkHasFunctors γ V ← hγ.instantiate
      let hδ : mkHasFunctors δ V ← hδ.instantiate
      let _ : mkIsFunApp₄' α β γ δ y' := { toInstanceExpr := ← hFunApp₄'.instantiate }
      pure [⟨← mkIsFunApp.reflect δ y'⟩,
            ⟨← mkIsFunApp.reflect γ y'⟩,
            ⟨← mkIsFunApp.reflect β y'⟩,
            ⟨← mkIsFunApp.reflect α y'⟩]
    | none =>
      let hFunApp₃'? : Option (mkHasFunctors'.mkIsFunApp₃' hα.h hβ.h hγ.h Y y)
          ← InstanceExpr.synthesize?
      match hFunApp₃'? with
      | some hFunApp₃' =>
        let α ← α.instantiate
        let β ← β.instantiate
        let γ ← γ.instantiate
        let hα : mkHasFunctors α V ← hα.instantiate
        let hβ : mkHasFunctors β V ← hβ.instantiate
        let hγ : mkHasFunctors γ V ← hγ.instantiate
        let _ : mkIsFunApp₃' α β γ y' := { toInstanceExpr := ← hFunApp₃'.instantiate }
        pure [⟨← mkIsFunApp.reflect γ y'⟩,
              ⟨← mkIsFunApp.reflect β y'⟩,
              ⟨← mkIsFunApp.reflect α y'⟩]
      | none =>
        let hFunApp₂'? : Option (mkHasFunctors'.mkIsFunApp₂' hα.h hβ.h Y y)
            ← InstanceExpr.synthesize?
        match hFunApp₂'? with
        | some hFunApp₂' =>
          let α ← α.instantiate
          let β ← β.instantiate
          let hα : mkHasFunctors α V ← hα.instantiate
          let hβ : mkHasFunctors β V ← hβ.instantiate
          let _ : mkIsFunApp₂' α β y' := { toInstanceExpr := ← hFunApp₂'.instantiate }
          pure [⟨← mkIsFunApp.reflect β y'⟩,
                ⟨← mkIsFunApp.reflect α y'⟩]
        | none =>
          let hFunApp? : Option (mkHasFunctors'.mkIsFunApp hα.h Y y) ← InstanceExpr.synthesize?
          match hFunApp? with
          | some hFunApp =>
            let α ← α.instantiate
            let hα : mkHasFunctors α V ← hα.instantiate
            let _ : mkIsFunApp α y' := { toInstanceExpr := ← hFunApp.instantiate }
            pure [⟨← mkIsFunApp.reflect α y'⟩]
          | none =>
            -- TODO: Can we replace these with better unfolding (see `DerivedFunctors.lean`)?
            let hFunApp₂? : Option (mkHasFunctors'.mkIsFunApp₂ hα.h hβ.h Y y)
                ← InstanceExpr.synthesize?
            match hFunApp₂? with
            | some hFunApp₂ =>
              let α ← α.instantiate
              let β ← β.instantiate
              let hα : mkHasFunctors α V ← hα.instantiate
              let hβ : mkHasFunctors β V ← hβ.instantiate
              let _ : mkIsFunApp₂ α β y' := { toInstanceExpr := ← hFunApp₂.instantiate }
              let _ ← mkIsFunApp₂.reflect α β y'
              pure [⟨IsFunApp₂.isFunApp (V := _(V))⟩]
            | none =>
              let hFunApp₃? : Option (mkHasFunctors'.mkIsFunApp₃ hα.h hβ.h hγ.h Y y)
                  ← InstanceExpr.synthesize?
              match hFunApp₃? with
              | some hFunApp₃ =>
                let α ← α.instantiate
                let β ← β.instantiate
                let γ ← γ.instantiate
                let hα : mkHasFunctors α V ← hα.instantiate
                let hβ : mkHasFunctors β V ← hβ.instantiate
                let hγ : mkHasFunctors γ V ← hγ.instantiate
                let _ : mkIsFunApp₃ α β γ y' := { toInstanceExpr := ← hFunApp₃.instantiate }
                let _ ← mkIsFunApp₃.reflect α β γ y'
                pure [⟨IsFunApp₃.isFunApp (V := _(V))⟩]
              | none =>
                let hFunApp₄? : Option (mkHasFunctors'.mkIsFunApp₄ hα.h hβ.h hγ.h hδ.h Y y)
                    ← InstanceExpr.synthesize?
                match hFunApp₄? with
                | some hFunApp₄ =>
                  let α ← α.instantiate
                  let β ← β.instantiate
                  let γ ← γ.instantiate
                  let δ ← δ.instantiate
                  let hα : mkHasFunctors α V ← hα.instantiate
                  let hβ : mkHasFunctors β V ← hβ.instantiate
                  let hγ : mkHasFunctors γ V ← hγ.instantiate
                  let hδ : mkHasFunctors δ V ← hδ.instantiate
                  let _ : mkIsFunApp₄ α β γ δ y' := { toInstanceExpr := ← hFunApp₄.instantiate }
                  let _ ← mkIsFunApp₄.reflect α β γ δ y'
                  pure [⟨IsFunApp₄.isFunApp (V := _(V))⟩]
                | none => pure []

  def synthesizeFunApps : MetaM (List (FunApp y)) := do
    -- Now try to find an `IsFunApp` instance.
    match ← synthesizeFunApps' y with
    | List.nil => do
      -- If none was found, check if `y` is an application of `DefFun.inst`. If it is, pass that to
      -- `IsFunApp` instead of the original value of `y`, as `IsFunApp` is usually defined on such
      -- terms.
      let α ← _Sort.mkFreshMVar
      let hα : mkHasFunctors α V ← InstanceExpr.mkFreshMVar
      let B : _(V) ← _Universe.mkFreshTypeMVar
      let f_y :  mkArrow α B ← TypedExpr.mkFreshMVar
      let F_y : mkHasFunctors'.mkDefFun hα.h B f_y ← TypedExpr.mkFreshMVar
      let y' : (α ⥤ B) := mkHasFunctors'.mkDefFun.mkInst hα.h B f_y F_y
      if ← isDefEq y y' then
        let α ← α.instantiate
        let hα : mkHasFunctors α V ← hα.instantiate
        let B : _(V) ← _Universe.instantiateTypeMVars B
        let f_y : mkArrow α B ← f_y.instantiate
        let F_y : mkHasFunctors'.mkDefFun hα.h B f_y ← F_y.instantiate
        let y' : Y := mkHasFunctors'.mkDefFun.mkInst hα.h B f_y F_y
        -- However, if that is in turn reducibly an application of `DefFun.mk`, then use the
        -- argument of that.
        let y'' : Y ← _Universe.mkFreshInstMVar
        let F_y' := mkHasFunctors'.mkDefFun.mkMk hα.h B f_y y''
        if ← withReducible (isDefEq F_y F_y') then
          let y'' : Y ← _Universe.instantiateInstMVars y''
          return ← synthesizeFunApps' y''
        return ← synthesizeFunApps' y'
      -- Lastly, check whether `y` is literally a functor application.
      -- This sees through some definitions that are opaque to type class synthesis.
      -- Only do this if all else fails, as we want to return all alternatives if multiple exist.
      let F : (α ⥤ Y) ← _Universe.mkFreshInstMVar
      let a : α ← TypedExpr.mkFreshMVar
      if ← isDefEq y (F a) then
        let α ← α.instantiate
        let hα : mkHasFunctors α V ← hα.instantiate
        let F : (α ⥤ Y) ← _Universe.instantiateInstMVars F
        let a : α ← a.instantiate
        return [⟨⟨F, a⟩⟩]
      pure []
    | result => pure result

end FunApp



def mkHasIdFun' {u uu : Level} {U : Q(Universe.{u, uu})} (A : Q($U)) (hA : mkHasFunctors' ⌜$A⌝ U) :=
  ⌜HasIdFun $A⌝

namespace mkHasIdFun'

  variable {u uu : Level} {U : Q(Universe.{u, uu})} {A : Q($U)} {hA : mkHasFunctors' ⌜$A⌝ U}
           (h : mkHasIdFun' A hA)

  def mkIdFun : Q($A ⥤ $A) := ⌜HasIdFun.idFun $A⌝

end mkHasIdFun'

def mkHasIdFun {U : _Universe} (A : _(U)) [hA : mkHasFunctors _⌈A⌉ U] : ClassExpr :=
  ⟨mkHasIdFun' (U := U.U) A hA.h⟩

namespace mkHasIdFun

  variable {U : _Universe} (A : _(U)) [mkHasFunctors _⌈A⌉ U] [h : mkHasIdFun A]

  def mkIdFun : A ⥤ A := mkHasIdFun'.mkIdFun h.h

  instance reflect : HasIdFun A where
    defIdFun := ⟨mkIdFun A⟩

end mkHasIdFun


def mkHasRevAppFun' {u v vv : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})}
                    (hα : mkHasFunctors' α V) (hV : mkHasUnivFunctors' V V) :=
  ⌜HasRevAppFun $α $V⌝

namespace mkHasRevAppFun'

  variable {u v vv : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})} {hα : mkHasFunctors' α V}
           {hV : mkHasUnivFunctors' V V} (h : mkHasRevAppFun' hα hV)

  def mkRevAppFun (a : Q($α)) (B : Q($V)) : Q(($α ⥤ $B) ⥤ $B) :=
    ⌜HasRevAppFun.revAppFun $a $B⌝

  def mkRevAppFun₂ (B : Q($V)) : Q($α ⥤ ($α ⥤ $B) ⥤ $B) :=
    ⌜HasRevAppFun.revAppFun₂ $α $B⌝

end mkHasRevAppFun'

def mkHasRevAppFun (α : _Sort) (V : _Universe) [hα : mkHasFunctors α V]
                   [hV : mkHasUnivFunctors V V] :
    ClassExpr :=
  ⟨mkHasRevAppFun' hα.h hV.h⟩

namespace mkHasRevAppFun

  variable (α : _Sort) {V : _Universe} [mkHasFunctors α V] [mkHasUnivFunctors V V]
           [h : mkHasRevAppFun α V]

  def mkRevAppFun (a : α) (B : _(V)) : (α ⥤ B) ⥤ B := mkHasRevAppFun'.mkRevAppFun h.h a B
  def mkRevAppFun₂ (B : _(V)) : B ⥤ (α ⥤ B) ⥤ B := mkHasRevAppFun'.mkRevAppFun₂ h.h B

  instance reflect : HasRevAppFun α _(V) where
    defRevAppFun₂ B := ⟨λ a => ⟨mkRevAppFun α a B⟩, ⟨mkRevAppFun₂ α B⟩⟩

end mkHasRevAppFun


def mkHasSwapFun' {u u' v vv : Level} {α : Q(Sort u)} {β : Q(Sort u')} {V : Q(Universe.{v, vv})}
                  (hα : mkHasFunctors' α V) (hβ : mkHasFunctors' β V) :=
  ⌜HasSwapFun $α $β $V⌝

namespace mkHasSwapFun'

  variable {u u' v vv : Level} {α : Q(Sort u)} {β : Q(Sort u')} {V : Q(Universe.{v, vv})}
           {hα : mkHasFunctors' α V} {hβ : mkHasFunctors' β V} (h : mkHasSwapFun' hα hβ)

  def mkSwapFun (C : Q($V)) (F : Q($α ⥤ $β ⥤ $C)) (b : Q($β)) : Q($α ⥤ $C) :=
    ⌜HasSwapFun.swapFun $F $b⌝

  def mkSwapFun₂ (C : Q($V)) (F : Q($α ⥤ $β ⥤ $C)) : Q($β ⥤ $α ⥤ $C) :=
    ⌜HasSwapFun.swapFun₂ $F⌝

end mkHasSwapFun'

def mkHasSwapFun (α β : _Sort) (V : _Universe) [hα : mkHasFunctors α V] [hβ : mkHasFunctors β V] :
    ClassExpr :=
  ⟨mkHasSwapFun' hα.h hβ.h⟩

namespace mkHasSwapFun

  variable {α β : _Sort} {V : _Universe} [mkHasFunctors α V] [mkHasFunctors β V]
           [h : mkHasSwapFun α β V]

  def mkSwapFun {C : _(V)} (F : α ⥤ β ⥤ C) (b : β) : α ⥤ C := mkHasSwapFun'.mkSwapFun h.h C F b
  def mkSwapFun₂ {C : _(V)} (F : α ⥤ β ⥤ C) : β ⥤ α ⥤ C := mkHasSwapFun'.mkSwapFun₂ h.h C F

  instance reflect : HasSwapFun α β _(V) where
    defSwapFun₂ F := ⟨λ b => ⟨mkSwapFun F b⟩, ⟨mkSwapFun₂ F⟩⟩

end mkHasSwapFun


def mkHasCompFun' {u v vv w ww : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})}
                  {W : Q(Universe.{w, ww})} (hαV : mkHasFunctors' α V) (B : Q($V))
                  (hBW : mkHasFunctors' ⌜$B⌝ W) (hαW : mkHasFunctors' α W) :=
  ⌜HasCompFun $α $B $W⌝

namespace mkHasCompFun'

  variable {u v vv w ww : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})} {W : Q(Universe.{w, ww})}
           {hαV : mkHasFunctors' α V} (B : Q($V)) {hBW : mkHasFunctors' ⌜$B⌝ W}
           {hαW : mkHasFunctors' α W} (h : mkHasCompFun' hαV B hBW hαW)

  def mkRevCompFun (C : Q($W)) (G : Q($B ⥤ $C)) (F : Q($α ⥤ $B)) : Q($α ⥤ $C) := ⌜$G ⊙ $F⌝

end mkHasCompFun'

def mkHasCompFun (α : _Sort) {V : _Universe} (B : _(V)) (W : _Universe) [hαV : mkHasFunctors α V]
                 [hBW : mkHasFunctors _⌈B⌉ W] [hαW : mkHasFunctors α W] :
    ClassExpr :=
  ⟨mkHasCompFun' hαV.h B hBW.h hαW.h⟩

namespace mkHasCompFun

  variable (α : _Sort) {V W : _Universe} [mkHasFunctors α V] [mkHasFunctors α W] {B : _(V)}
           [mkHasFunctors _⌈B⌉ W] [h : mkHasCompFun α B W]

  def mkRevCompFun {C : _(W)} (G : B ⥤ C) (F : α ⥤ B) : α ⥤ C :=
    mkHasCompFun'.mkRevCompFun B h.h C G F

  instance reflect : HasCompFun α B _(W) where
    defCompFun F G := ⟨mkRevCompFun α G F⟩

end mkHasCompFun


def mkHasConstFun' {u v vv : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})}
                   (hα : mkHasFunctors' α V) :=
  ⌜HasConstFun $α $V⌝

namespace mkHasConstFun'

  variable {u v vv : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})} {hα : mkHasFunctors' α V}
           (h : mkHasConstFun' hα)

  def mkConstFun (B : Q($V)) (b : Q($B)) : Q($α ⥤ $B) := ⌜HasConstFun.constFun $α $b⌝

end mkHasConstFun'

def mkHasConstFun (α : _Sort) (V : _Universe) [hα : mkHasFunctors α V] :
    ClassExpr :=
  ⟨mkHasConstFun' hα.h⟩

namespace mkHasConstFun

  variable (α : _Sort) {V : _Universe} [mkHasFunctors α V] [h : mkHasConstFun α V]

  def mkConstFun {B : _(V)} (b : B) : α ⥤ B := mkHasConstFun'.mkConstFun h.h B b

  instance reflect : HasConstFun α _(V) where
    defConstFun b := ⟨mkConstFun α b⟩

end mkHasConstFun


def mkHasDupFun' {u v vv : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})}
                 (hα : mkHasFunctors' α V) :=
  ⌜HasDupFun $α $V⌝

namespace mkHasDupFun'

  variable {u v vv : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})} {hα : mkHasFunctors' α V}
           (h : mkHasDupFun' hα)

  def mkDupFun (B : Q($V)) (F : Q($α ⥤ $α ⥤ $B)) : Q($α ⥤ $B) := ⌜HasDupFun.dupFun $F⌝

end mkHasDupFun'

def mkHasDupFun (α : _Sort) (V : _Universe) [hα : mkHasFunctors α V] : ClassExpr :=
  ⟨mkHasDupFun' hα.h⟩

namespace mkHasDupFun

  variable {α : _Sort} {V : _Universe} [mkHasFunctors α V] [h : mkHasDupFun α V]

  def mkDupFun {B : _(V)} (F : α ⥤ α ⥤ B) : α ⥤ B := mkHasDupFun'.mkDupFun h.h B F

  instance reflect : HasDupFun α _(V) where
    defDupFun F := ⟨mkDupFun F⟩

end mkHasDupFun


def mkHasRevSelfAppFun' {u uu v vv : Level} {U : Q(Universe.{u, uu})} {V : Q(Universe.{v, vv})}
                        (hUV : mkHasUnivFunctors' U V) (hVU : mkHasUnivFunctors' V U)
                        (hVV : mkHasUnivFunctors' V V) :=
  ⌜HasRevSelfAppFun $U $V⌝

namespace mkHasRevSelfAppFun'

  variable {u uu v vv : Level} {U : Q(Universe.{u, uu})} {V : Q(Universe.{v, vv})}
           {hUV : mkHasUnivFunctors' U V} {hVU : mkHasUnivFunctors' V U}
           {hVV : mkHasUnivFunctors' V V} (h : mkHasRevSelfAppFun' hUV hVU hVV)

  def mkRevSelfAppFun (A : Q($U)) (B : Q($V)) (F : Q(($A ⥤ $B) ⥤ $A)) : Q(($A ⥤ $B) ⥤ $B) :=
    ⌜HasRevSelfAppFun.revSelfAppFun $F⌝

  def mkRevSelfAppFun₂ (A : Q($U)) (B : Q($V)) : Q((($A ⥤ $B) ⥤ $A) ⥤ (($A ⥤ $B) ⥤ $B)) :=
    ⌜HasRevSelfAppFun.revSelfAppFun₂ $A $B⌝

end mkHasRevSelfAppFun'

def mkHasRevSelfAppFun (U V : _Universe) [hUV : mkHasUnivFunctors U V]
                       [hVU : mkHasUnivFunctors V U] [hVV : mkHasUnivFunctors V V] :
    ClassExpr :=
  ⟨mkHasRevSelfAppFun' hUV.h hVU.h hVV.h⟩

namespace mkHasRevSelfAppFun

  variable {U V : _Universe} [mkHasUnivFunctors U V] [mkHasUnivFunctors V U]
           [mkHasUnivFunctors V V] [h : mkHasRevSelfAppFun U V]

  def mkRevSelfAppFun {A : _(U)} {B : _(V)} (F : (A ⥤ B) ⥤ A) : (A ⥤ B) ⥤ B :=
    mkHasRevSelfAppFun'.mkRevSelfAppFun h.h A B F

  def mkRevSelfAppFun₂ (A : _(U)) (B : _(V)) : ((A ⥤ B) ⥤ A) ⥤ ((A ⥤ B) ⥤ B) :=
    mkHasRevSelfAppFun'.mkRevSelfAppFun₂ h.h A B

  instance reflect : HasRevSelfAppFun _(U) _(V) where
    defRevSelfAppFun₂ A B := ⟨λ F => ⟨mkRevSelfAppFun F⟩,
                              ⟨mkRevSelfAppFun₂ A B⟩⟩

end mkHasRevSelfAppFun


def mkHasSubstFun' {u v vv w ww : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})}
                   {W : Q(Universe.{w, ww})} (hαV : mkHasFunctors' α V) (B : Q($V))
                   (hBW : mkHasFunctors' ⌜$B⌝ W) (hαW : mkHasFunctors' α W) :=
  ⌜HasSubstFun $α $B $W⌝

namespace mkHasSubstFun'

  variable {u v vv w ww : Level} {α : Q(Sort u)} {V : Q(Universe.{v, vv})} {W : Q(Universe.{w, ww})}
           {hαV : mkHasFunctors' α V} (B : Q($V)) {hBW : mkHasFunctors' ⌜$B⌝ W}
           {hαW : mkHasFunctors' α W} (h : mkHasSubstFun' hαV B hBW hαW)

  def mkRevSubstFun (C : Q($W)) (G : Q($α ⥤ $B ⥤ $C)) (F : Q($α ⥤ $B)) : Q($α ⥤ $C) :=
    ⌜HasSubstFun.revSubstFun $G $F⌝

end mkHasSubstFun'

def mkHasSubstFun (α : _Sort) {V : _Universe} (B : _(V)) (W : _Universe) [hαV : mkHasFunctors α V]
                  [hBW : mkHasFunctors _⌈B⌉ W] [hαW : mkHasFunctors α W] :
    ClassExpr :=
  ⟨mkHasSubstFun' hαV.h B hBW.h hαW.h⟩

namespace mkHasSubstFun

  variable (α : _Sort) {V W : _Universe} [mkHasFunctors α V] [mkHasFunctors α W] {B : _(V)}
           [mkHasFunctors _⌈B⌉ W] [h : mkHasSubstFun α B W]

  def mkRevSubstFun {C : _(W)} (G : α ⥤ B ⥤ C) (F : α ⥤ B) : α ⥤ C :=
    mkHasSubstFun'.mkRevSubstFun B h.h C G F

  instance reflect : HasSubstFun α B _(W) where
    defSubstFun F G := ⟨mkRevSubstFun α G F⟩

end mkHasSubstFun
