import UniverseAbstractions.Universes.Layer1.Meta.Reflect.Functors
import UniverseAbstractions.Universes.Layer1.Meta.FVar



namespace UniverseAbstractions.Layer1.Meta.Tactics.Functoriality

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedVariables false

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic Lean.TSyntax.Compat UniverseAbstractions.Meta
     HasPiType HasFunctors



-- By treating the primite and derived functors as combinators (see
-- https://en.wikipedia.org/wiki/Combinatory_logic), we obtain an algorithm to construct a functor
-- for a given lambda term, i.e. to prove functoriality automatically.
--
-- Below, `t` and `T` denote arbitrary terms of the correct type (which is a functor type in case
-- of `T`).
-- We write `Λ a => t` for the functor obtained for `λ a => t` using this algorithm recursively.
-- This notation is defined near the bottom of this file.
--
--  Input                 | Condition      | Output
-- -----------------------+----------------+-------------------------------------------------------
--  `Λ a => t`            | `a` not in `t` | `constFun _ t`
--  `Λ a => a`            |                | `idFun _`
--  `Λ a => T a`          | `a` not in `T` | `appFun T`, i.e. just `T`
--  `Λ a => T t`          | `a` not in `T` | `compFun (Λ a => t) T`
--  `Λ F => F t`          | `F` not in `t` | `revAppFun t _`
--  `Λ a => T t`          | `a` not in `t` | `swapFun (Λ a => T) t`
--  `Λ a => T a`          |                | `dupFun (Λ a => T)`
--  `Λ F => F t`          |                | `revSelfAppFun (Λ F => t)`
--  `Λ a => T t`          |                | `substFun (Λ a => t) (Λ a => T)`,
--  `Λ a => ?Fun t₁...tₙ` |                | `Λ a => (?Fun₂ t₁...tₙ₋₁) tₙ`
--                        |                | (optimization: use `rev` if it makes `?Fun₂` term
--                        |                | constant)
--
-- Although all cases of functor application inside the lambda body can be handled generically by
-- `substFun` (matching SKI combinator calculus), `substFun` requires `FullLogic`, whereas
-- `compFun`, `revAppFun`, and `swapFun` only require `LinearLogic` (corresponding to linear logic,
-- where each variable is used exactly once). So the special cases are not merely optimizations.
--
-- The algorithm is generalized in such a way that it can output `constPi` etc. if the result type
-- is a dependent functor type.



def PiLambdaAbstraction {v : Level} {V : _Universe v} (φ : PiData V) :=
  LambdaAbstraction (mkHasPiType.defSortPropFun φ.P)


-- TODO: Revisit this when reimplementing extensionality.
--def synthesizePiApps {φ : PiData} (f : PiLambdaAbstraction φ) (forcePrimitive : Bool) :
--    MetaM (List (PiApp f.y)) := do
--  -- `forcePrimitive` is used in the extensionality tactic.
--  -- It causes `IsPiApp` declarations of `swapFun`, `revSelfAppFun`, and `substFun` to be ignored.
--  if forcePrimitive then
--    let X ← _Universe.mkFreshMVar
--    let hα : mkHasFunctors φ.α X ← InstanceExpr.mkFreshMVar
--    let hX : mkHasUnivFunctors X φ.V ← InstanceExpr.mkFreshMVar
--    let compFun_B : _(X) ← _Universe.mkFreshTypeMVar
--    let compFun_C : _(φ.V) ← _Universe.mkFreshTypeMVar
--    let compFun_F : φ.α ⥤ compFun_B ← _Universe.mkFreshInstMVar
--    let compFun_G : compFun_B ⥤ compFun_C ← _Universe.mkFreshInstMVar
--    let hCompFun : mkHasCompFun φ.α compFun_B φ.V ← InstanceExpr.mkFreshMVar
--    let compFun := HasCompFun.revCompFun (C := compFun_C) compFun_G compFun_F
--    if ← isDefEq f.y compFun then
--      return ← PiApp.synthesizePiApps' (Y := φ.Y) compFun
--    let dupFun_B : _(φ.V) ← _Universe.mkFreshTypeMVar
--    let dupFun_F : φ.α ⥤ φ.α ⥤ dupFun_B ← _Universe.mkFreshInstMVar
--    let hDupFun : mkHasDupFun φ.α φ.V ← InstanceExpr.mkFreshMVar
--    let dupFun := HasDupFun.dupFun dupFun_F
--    if ← isDefEq f.y dupFun then
--      return ← PiApp.synthesizePiApps' (Y := φ.Y) dupFun
--  PiApp.synthesizePiApps f.y

def ConstructLambdaFunctor := {v : Level} → {V : _Universe v} → {φ : PiData V} →
                              (f : PiLambdaAbstraction φ) → MetaM φ.mkPi

-- The following functions would normally form a mutual induction, but we break it by passing the
-- main entry point `constructLambdaFunctor` to the other functions, so that only
-- `constructLambdaFunctor` itself is really recursive. The individual functions handle different
-- cases of functor application in the lambda body, depending on which parts are either constant
-- with respect to the lambda variable or equal to it.

-- Handles the most generic case where everything may depend on `f.a`.
-- This is also the fallback if everything else failed; it outputs `substPi/substFun` because that
-- subsumes everything else (if it is available).
def constructLambdaAppFunctor_dep {v : Level} {V : _Universe v} {φ : PiData V}
                                  (f : PiLambdaAbstraction φ) (Y? : Option V) (piApp : PiApp f.y)
                                  (requireConstF : Bool)
                                  (constructLambdaFunctor : ConstructLambdaFunctor) :
    MetaM (Option φ.mkPi) := do
  if requireConstF then
    return none
  if let some Y := Y? then
    let piApp_A : V ← _Universe.mkFreshTypeMVar
    if ← isDefEq piApp.α.α _⌈piApp_A⌉.α then
      let piApp_A ← _Universe.instantiateTypeMVars piApp_A
      let piApp_A' := f.mkDependentExpr piApp_A
      if let LambdaBodyCategory.const (piApp_A'' : V) ← piApp_A'.classify then
        let α? : _sort := { u := v, α := φ.α.α }
        let hV : mkHasLinearLogic V ← InstanceExpr.synthesize
        let hLin : mkHasExternalLinearLogic α? V ← InstanceExpr.synthesize
        let hNonLin : mkHasExternalNonLinearLogic α? V ← InstanceExpr.synthesize
        let a : FVar α? := ⟨f.a.a, f.a.n⟩
        let piApp_a := f.mkDependentExpr piApp.a
        let piApp_a' : DependentTypedExpr a ⟨_⌈piApp_A''⌉.α⟩ := ⟨piApp_a.y⟩
        let φ_a : PiData V := PiData.constructFun α? piApp_A''
        let f_a : PiLambdaAbstraction φ_a := ⟨piApp_a'⟩
        let F_a : α? ⥤ piApp_A'' ← constructLambdaFunctor f_a
        let piApp_F := f.mkDependentExpr piApp.F
        let piApp_F' : DependentTypedExpr a ⟨_⌈piApp_A'' ⥤ Y⌉.α⟩ := ⟨piApp_F.y⟩
        let φ_F : PiData V := PiData.constructFun α? (piApp_A'' ⥤ Y)
        let f_F : PiLambdaAbstraction φ_F := ⟨piApp_F'⟩
        let F_F : α? ⥤ piApp_A'' ⥤ Y ← constructLambdaFunctor f_F
        let F := mkHasExternalNonLinearLogic.mkRevSubstFun F_F F_a
        return some F
  let x ← mkFreshLevelMVar
  let X ← _Universe.mkFreshMVar x
  let piApp_A : X ← _Universe.mkFreshTypeMVar
  if ← isDefEq piApp.α.α _⌈piApp_A⌉.α then
    let x ← instantiateLevelMVars x
    let X ← X.instantiate x
    let piApp_A : X ← _Universe.instantiateTypeMVars piApp_A
    let piApp_A' := f.mkDependentExpr piApp_A
    let P : φ.α ⥤ _[X] := piApp_A'.toPi
    let P' := defAppFun P
    let hP : mkHasPiType P' ← InstanceExpr.synthesize
    let piApp_P := f.mkDependentExpr piApp.P
    let Q : Pi (mkHasUnivQuantPiType.metaProp P' V) := piApp_P.toPi
    let q : ∀ a, (mkHasPiType.reflectProp P') a → V := λ a b => HasPiType.apply (Q a) b
    let Q'' : ∀ a, [_⌈(mkHasPiType.reflectProp P') a⌉ ⥤ _[V]]_{q a} := λ a => defAppFun (Q a)
    let Q' : [∀ a, (mkHasUnivQuantPiType.metaProp P' V) a | _sort]_{Q''} := Q
    let hQa : mkHasUnivQuantPiType Q' ← InstanceExpr.synthesize
    let hPiQa : mkHasPiType (mkHasUnivQuantPiType.piProp Q') ← InstanceExpr.synthesize
    let hQaFa : mkHasIndepQuantPiType (mkHasSubstPi.prop Q') ← InstanceExpr.synthesize
    let hSubst : mkHasSubstPi Q' ← InstanceExpr.synthesize
    let piApp_a := f.mkDependentExpr piApp.a
    let piApp_a' : DependentTypedExpr f.a ⟨_⌈(mkHasPiType.reflectProp P') f.a.a⌉.α⟩ := ⟨piApp_a.y⟩
    let φ_a : PiData X := PiData.constructPi P'
    let f_a : PiLambdaAbstraction φ_a := ⟨piApp_a'⟩
    let F_a ← constructLambdaFunctor f_a
    let piApp_F := f.mkDependentExpr piApp.F
    let piApp_F' : DependentTypedExpr f.a ⟨_⌈Pi ((mkHasUnivQuantPiType.reflectProp Q') f.a.a)⌉.α⟩ :=
        ⟨piApp_F.y⟩
    let φ_F : PiData V := PiData.constructPi (mkHasUnivQuantPiType.piProp Q')
    let f_F : PiLambdaAbstraction φ_F := ⟨piApp_F'⟩
    let F_F ← constructLambdaFunctor f_F
    return some (mkHasSubstPi.mkRevSubstPi (Q := Q') F_F F_a)
  pure none

-- Handles the case where `piApp.α` is independent of `f.a`, but `piApp.P` (and thus `piApp.F`) may
-- not necessarily be. `piApp.α` must always be independent of `f.a` if `piApp.a` is constant with
-- respect to `f.a`, and also if `piApp.a` is exactly `f.a`.
-- Abstracting `piApp.P` then yields a bi-property.
-- If `piApp.a` is constant, we output `swapPi`. If `piApp.a` equals `f.a`, we output `dupPi`.
-- Otherwise, we fall back to `substPi`.
def constructLambdaAppFunctor_indep_dep {v : Level} {V : _Universe v} {φ : PiData V}
                                        (f : PiLambdaAbstraction φ) (Y? : Option V)
                                        (piApp : PiApp f.y) (requireConstF : Bool)
                                        (constructLambdaFunctor : ConstructLambdaFunctor) :
    MetaM (Option φ.mkPi) := do
  if requireConstF then
    return none
  let piApp_F := f.mkDependentExpr piApp.F
  let piApp_a := f.mkDependentExpr piApp.a
  match ← piApp_a.classifyExt with
  | LambdaBodyCategoryExt.const (piApp_a' : piApp.α) =>
    if let some Y := Y? then
      let hV : mkHasLinearLogic V ← InstanceExpr.synthesize
      let α? : _sort.mkSortType v := φ.α.α
      let hα : mkHasExternalLinearLogic α? V ← InstanceExpr.synthesize
      let piApp_α? : _sort.mkSortType v := piApp.α.α
      let hPiApp_α : mkHasExternalLinearLogic piApp_α? V ← InstanceExpr.synthesize
      let a : FVar α? := ⟨f.a.a, f.a.n⟩
      let piApp_F' : DependentTypedExpr a ⟨_⌈piApp_α? ⥤ Y⌉.α⟩ := ⟨piApp_F.y⟩
      let φ_F : PiData V := PiData.constructFun α? (piApp_α? ⥤ Y)
      let f_F : PiLambdaAbstraction φ_F := ⟨piApp_F'⟩
      let F_F : α? ⥤ piApp_α? ⥤ Y ← constructLambdaFunctor f_F
      let piApp_a'' : piApp_α? := piApp_a'
      let F := mkHasExternalLinearLogic.mkSwapFun F_F piApp_a''
      return some F
    let piApp_P := f.mkDependentExpr piApp.P
    let Q : φ.α ⥤ piApp.α ⥤ _[V] := piApp_P.toPi
    let Q' := defAppFun₂ Q
    let hQa : mkHasIndepQuantPiType Q' ← InstanceExpr.synthesize
    let hPiQa : mkHasPiType (mkHasIndepQuantPiType.piProp Q') ← InstanceExpr.synthesize
    let hQab : mkHasIndepQuantPiType (mkHasSwapPi.prop Q') ← InstanceExpr.synthesize
    let hSwapPi : mkHasSwapPi Q' ← InstanceExpr.synthesize
    let piApp_F' : DependentTypedExpr f.a ⟨_⌈Pi ((mkHasIndepQuantPiType.reflectProp Q') f.a.a)⌉.α⟩ :=
        ⟨piApp_F.y⟩
    let φ_F : PiData V := PiData.constructPi (mkHasIndepQuantPiType.piProp Q')
    let f_F : PiLambdaAbstraction φ_F := ⟨piApp_F'⟩
    let F_F ← constructLambdaFunctor f_F
    return some (mkHasSwapPi.mkSwapPi (P := Q') F_F piApp_a')
  | LambdaBodyCategoryExt.id =>
    if let some Y := Y? then
      let hV : mkHasLinearLogic V ← InstanceExpr.synthesize
      let α? : _sort := { u := v, α := φ.α.α }
      let hαV : mkHasFunctors α? V ← InstanceExpr.synthesize
      let hNonLin : mkHasExternalNonLinearLogic α? V ← InstanceExpr.synthesize
      let a : FVar α? := ⟨f.a.a, f.a.n⟩
      let piApp_F' : DependentTypedExpr a ⟨_⌈α? ⥤ Y⌉.α⟩ := ⟨piApp_F.y⟩
      let φ_F : PiData V := PiData.constructFun α? (α? ⥤ Y)
      let f_F : PiLambdaAbstraction φ_F := ⟨piApp_F'⟩
      let F_F : α? ⥤ α? ⥤ Y ← constructLambdaFunctor f_F
      let F := mkHasExternalNonLinearLogic.mkDupFun F_F
      return some F
    let piApp_P := f.mkDependentExpr piApp.P
    let Q : φ.α ⥤ φ.α ⥤ _[V] := piApp_P.toPi
    let Q' := defAppFun₂ Q
    let hQa : mkHasIndepQuantPiType Q' ← InstanceExpr.synthesize
    let hPiQa : mkHasPiType (mkHasIndepQuantPiType.piProp Q') ← InstanceExpr.synthesize
    let hQaa : mkHasPiType (mkHasDupPi.prop Q') ← InstanceExpr.synthesize
    let hDupFun : mkHasDupPi Q' ← InstanceExpr.synthesize
    let piApp_F' : DependentTypedExpr f.a ⟨_⌈Pi ((mkHasIndepQuantPiType.reflectProp Q') f.a.a)⌉.α⟩ :=
        ⟨piApp_F.y⟩
    let φ_F : PiData V := PiData.constructPi (mkHasIndepQuantPiType.piProp Q')
    let f_F : PiLambdaAbstraction φ_F := ⟨piApp_F'⟩
    let F_F ← constructLambdaFunctor f_F
    return some (mkHasDupPi.mkDupPi (P := Q') F_F)
  | LambdaBodyCategoryExt.dep => pure ()
  constructLambdaAppFunctor_dep f Y? piApp requireConstF constructLambdaFunctor

-- Handles the case where both `piApp.α` and `piApp.P` are independent of `f.a`. This must always be
-- the case if `piApp.F` is constant with respect to `f.a`, and also if `piApp.F` is exactly `f.a`.
-- If `piApp.F` is constant, we output `compFunPi`. If `piApp.F` equals `f.a` and `piApp.a` is
-- constant, we output `piAppFun`. If `piApp.F` equals `f.a` and `piApp.a` is not constant, we
-- output `piSelfAppPi`. Otherwise, we fall back to `swapPi`, `dupPi`, or `substPi`.
-- (We do not optimize the case where both parts are constant, since that means that the whole term
-- is constant, which should have been handled already.)
def constructLambdaAppFunctor_indep_indep {v : Level} {V : _Universe v} {φ : PiData V}
                                          (f : PiLambdaAbstraction φ) (Y? : Option V)
                                          (piApp : PiApp f.y) (requireConstF : Bool)
                                          (constructLambdaFunctor : ConstructLambdaFunctor) :
    MetaM (Option φ.mkPi) := do
  let piApp_F := f.mkDependentExpr piApp.F
  let piApp_a := f.mkDependentExpr piApp.a
  match ← piApp_F.classifyExt with
  | LambdaBodyCategoryExt.const (piApp_F' : Pi (mkHasPiType.reflectProp piApp.P)) =>
    if ← piApp_a.isId then
      return some piApp_F'
    if let some Y := Y? then
      let piApp_A : V ← _Universe.mkFreshTypeMVar
      if ← isDefEq piApp.α.α _⌈piApp_A⌉.α then
        let piApp_A ← _Universe.instantiateTypeMVars piApp_A
        let α? : _sort := { u := v, α := φ.α.α }
        let hVV : mkHasUnivFunctors V V ← InstanceExpr.synthesize
        let hLin : mkHasExternalLinearLogic α? V ← InstanceExpr.synthesize
        let piApp_F'' : piApp_A ⥤ Y := piApp_F'
        let a : FVar α? := ⟨f.a.a, f.a.n⟩
        let piApp_a := f.mkDependentExpr piApp.a
        let piApp_a' : DependentTypedExpr a ⟨_⌈piApp_A⌉.α⟩ := ⟨piApp_a.y⟩
        let φ_a : PiData V := PiData.constructFun α? piApp_A
        let f_a : PiLambdaAbstraction φ_a := ⟨piApp_a'⟩
        let F_a : α? ⥤ piApp_A ← constructLambdaFunctor f_a
        let F := mkHasExternalLinearLogic.mkRevCompFun (α := α?) piApp_F'' F_a
        return some F
    let X ← _Universe.mkFreshMVar φ.α.u
    let piApp_A : X ← _Universe.mkFreshTypeMVar
    if ← isDefEq piApp.α.α _⌈piApp_A⌉.α then
      let X ← X.instantiate φ.α.u
      let piApp_A : X ← _Universe.instantiateTypeMVars piApp_A
      let hαX : mkHasFunctors φ.α X ← InstanceExpr.synthesize
      let piApp_P : [_⌈piApp_A⌉ ⥤ _[V]]_{piApp.p} := piApp.P
      let piApp_hP : mkHasPiType piApp_P := ⟨piApp.h.h⟩
      let hPFa : mkHasIndepQuantPiType (mkHasCompFunPi.prop φ.α piApp_P) ← InstanceExpr.synthesize
      let hCompFunPi : mkHasCompFunPi φ.α piApp_P ← InstanceExpr.synthesize
      let piApp_F'' : Pi (mkHasPiType.reflectProp piApp_P) := piApp_F'
      let piApp_a' : DependentTypedExpr f.a ⟨_⌈piApp_A⌉.α⟩ := ⟨piApp_a.y⟩
      let φ_a : PiData X := PiData.constructFun φ.α piApp_A
      let f_a : PiLambdaAbstraction φ_a := ⟨piApp_a'⟩
      let F_a' ← constructLambdaFunctor f_a
      let F_a : φ.α ⥤ piApp_A := F_a'
      let revCompFunPi := mkHasCompFunPi.mkRevCompFunPi piApp_F'' F_a
      return some revCompFunPi
  | LambdaBodyCategoryExt.id =>
    if requireConstF then
      return none
    match ← piApp_a.classify with
    | LambdaBodyCategory.const (piApp_a' : piApp.α) =>
      let hVV : mkHasUnivFunctors V V ← InstanceExpr.synthesize
      if let some Y := Y? then
        let piApp_α? : _sort := { u := v, α := piApp.α.α }
        if let some (hLin : mkHasExternalLinearLogic piApp_α? V) ← InstanceExpr.synthesize? then
          if ← isDefEq φ.α.α _⌈piApp_α? ⥤ Y⌉.α then
            let piApp_a'' : piApp_α? := piApp_a'
            let F := mkHasExternalLinearLogic.mkRevAppFun piApp_a'' Y
            return some F
      let hPiAppFun : mkHasPiAppFun piApp.P ← InstanceExpr.synthesize
      let piAppFun := mkHasPiAppFun.mkPiAppFun piApp.P piApp_a'
      return some piAppFun
    | LambdaBodyCategory.dep =>
      if let some Y := Y? then
        let hV : mkHasLinearLogic V ← InstanceExpr.synthesize
        let A : V ← _Universe.mkFreshTypeMVar
        if ← isDefEq φ.α.α _⌈A ⥤ Y⌉.α then
          let A ← _Universe.instantiateTypeMVars A
          let hNonLin : mkHasNonLinearLogic V ← InstanceExpr.synthesize
          let a : FVar _⌈A ⥤ Y⌉ := ⟨f.a.a, f.a.n⟩
          let piApp_a' : DependentTypedExpr a ⟨_⌈A⌉.α⟩ := ⟨piApp_a.y⟩
          let φ_a : PiData V := PiData.constructFun _⌈A ⥤ Y⌉ A
          let f_a : PiLambdaAbstraction φ_a := ⟨piApp_a'⟩
          let F_a : (A ⥤ Y) ⥤ A ← constructLambdaFunctor f_a
          let F := mkHasNonLinearLogic.mkRevSelfAppFun F_a
          return some F
      let X ← _Universe.mkFreshMVar v
      let A : X ← _Universe.mkFreshTypeMVar
      let Q : _⌈A⌉ ⥤ _[V] ← _sort.mkFreshInstMVar
      let Q' := defAppFun Q
      let hQ : mkHasPiType Q' ← InstanceExpr.mkFreshMVar
      if ← isDefEq φ.α.α _⌈Pi (mkHasPiType.reflectProp' Q')⌉.α then
        let X ← X.instantiate v
        let A : X ← _Universe.instantiateTypeMVars A
        let Q : _⌈A⌉ ⥤ _[V] ← _sort.instantiateInstMVars Q
        let Q' := defAppFun Q
        let hQ : mkHasPiType Q' ← hQ.instantiate
        let hVX : mkHasUnivFunctors V X ← InstanceExpr.synthesize
        let hQF : mkHasIndepQuantPiType (mkHasPiSelfAppPi.prop Q') ← InstanceExpr.synthesize
        let hRevSelfApp : mkHasPiSelfAppPi Q' ← InstanceExpr.synthesize
        let hPiQX : mkHasFunctors _⌈Pi (mkHasPiType.reflectProp' Q')⌉ X := inferInstance
        let a : FVar _⌈Pi (mkHasPiType.reflectProp' Q')⌉ := ⟨f.a.a, f.a.n⟩
        let piApp_a' : DependentTypedExpr a ⟨_⌈A⌉.α⟩ := ⟨piApp_a.y⟩
        let φ_a : PiData X := PiData.constructFun _⌈Pi (mkHasPiType.reflectProp' Q')⌉ A
        let f_a : PiLambdaAbstraction φ_a := ⟨piApp_a'⟩
        let F_a' ← constructLambdaFunctor f_a
        let F_a : Pi (mkHasPiType.reflectProp' Q') ⥤ A := F_a'
        let piSelfAppPi := mkHasPiSelfAppPi.mkPiSelfAppPi (Q := Q') F_a
        return some piSelfAppPi
  | LambdaBodyCategoryExt.dep => pure ()
  constructLambdaAppFunctor_indep_dep f Y? piApp requireConstF constructLambdaFunctor

-- Differentiates between both cases where `piApp.α` is independent of `f.a`. (This is nearly always
-- the case. If `piApp.α` depends on `f.a`, then everything else also does, so `substPi` is then the
-- only possibility.)
def constructLambdaAppFunctor_indep {v : Level} {V : _Universe v} {φ : PiData V}
                                    (f : PiLambdaAbstraction φ) (Y? : Option V) (piApp : PiApp f.y)
                                    (requireConstF : Bool)
                                    (constructLambdaFunctor : ConstructLambdaFunctor) :
    MetaM (Option φ.mkPi) := do
  let piApp_P := f.mkDependentExpr piApp.P
  if let LambdaBodyCategory.const (piApp_P' : piApp.α ⥤ _[V]) ← piApp_P.classify then
    let piApp_P'' := defAppFun piApp_P'
    let piApp_h := f.mkDependentExpr piApp.h.h
    if let LambdaBodyCategory.const piApp_h' ← piApp_h.classify then
      let hPi : mkHasPiType piApp_P'' := ⟨piApp_h'⟩
      if let some hFun := piApp.hFun? then
        let piApp_hFun := f.mkDependentExpr hFun
        if let LambdaBodyCategory.const piApp_hFun' ← piApp_hFun.classify then
          let piApp' : PiApp f.y := ⟨⟨piApp_P'', some ⟨piApp_hFun'⟩⟩, piApp.F, piApp.a⟩
          return ← constructLambdaAppFunctor_indep_indep f Y? piApp' requireConstF constructLambdaFunctor
      let piApp' : PiApp f.y := ⟨⟨piApp_P'', none⟩, piApp.F, piApp.a⟩
      return ← constructLambdaAppFunctor_indep_indep f Y? piApp' requireConstF constructLambdaFunctor
  constructLambdaAppFunctor_indep_dep f Y? piApp requireConstF constructLambdaFunctor

-- Checks whether `piApp.α` depends on `f.a`, and calls the appropriate function.
def constructLambdaAppFunctor {v : Level} {V : _Universe v} {φ : PiData V}
                              (f : PiLambdaAbstraction φ) (Y? : Option V) (piApp : PiApp f.y)
                              (requireConstF : Bool)
                              (constructLambdaFunctor : ConstructLambdaFunctor) :
    MetaM (Option φ.mkPi) := do
  let piApp_α := f.mkDependentExpr piApp.α.α
  if let LambdaBodyCategory.const (piApp_α' : _sort.mkSortType piApp.α.u) ← piApp_α.classify then
    let piApp_P' : [piApp_α' ⥤ _[V]]_{piApp.p} := piApp.P
    let piApp_hP' : mkHasPiType piApp_P' := ⟨piApp.h.h⟩
    let piApp_hFun? : Option (mkHasFunctors (_sort.mk (u := v) piApp_α') V) :=
        match piApp.hFun? with
        | some hFun => some ⟨hFun.h⟩
        | none      => none
    let piApp' : PiApp f.y := ⟨⟨piApp_P', piApp_hFun?⟩, piApp.F, piApp.a⟩
    return ← constructLambdaAppFunctor_indep f Y? piApp' requireConstF constructLambdaFunctor
  constructLambdaAppFunctor_dep f Y? piApp requireConstF constructLambdaFunctor

-- Determines all ways in which the body is a Π application, and calls `constructLambdaAppFunctor`
-- on each to determine a good match.
def tryConstructLambdaAppFunctor {v : Level} {V : _Universe v} {φ : PiData V}
                                 (f : PiLambdaAbstraction φ) (Y? : Option V)
                                 (constructLambdaFunctor : ConstructLambdaFunctor) :
    MetaM φ.mkPi := do
  let piApps ← PiApp.synthesizePiApps f.y
  match piApps with
  | List.nil =>
    let y : Expr := f.y
    throwError "unsupported lambda body '{y}': failed to synthesize IsPiApp instance"
  | List.cons mainPiApp _ =>
    for piApp in piApps do
      match ← constructLambdaAppFunctor f Y? piApp true constructLambdaFunctor with
      | some F => return F
      | none   => pure ()
    match ← constructLambdaAppFunctor f Y? mainPiApp false constructLambdaFunctor with
    | some F => pure F
    | none   =>
      -- Since we set `requireConstF` to `false`, this shouldn't happen.
      let y : Expr := f.y
      let F : Expr := mainPiApp.F
      let a : Expr := mainPiApp.a
      throwError "internal error for lambda body '{y}': unable to handle application of '{F}' with argument '{a}'"

-- The main entry point, which handles `constFun` and `idFun` directly, and calls
-- `tryConstructLambdaAppFunctor` to deal with a Π application.
partial def constructLambdaFunctor {v : Level} {V : _Universe v} {φ : PiData V}
                                   (f : PiLambdaAbstraction φ) :
    MetaM φ.mkPi := do
  let Y : DependentExpr f.a := ⟨φ.p f.a.a⟩
  match ← Y.classify with
  | LambdaBodyCategory.const (Y' : V) =>
    match ← f.t.classifyExt with
    | LambdaBodyCategoryExt.const (y : Y') =>
      let α? : _sort := { u := v, α := φ.α.α }
      if let some (hαV : mkHasFunctors α? V) ← InstanceExpr.synthesize? then
        let hVV : mkHasUnivFunctors V V ← InstanceExpr.synthesize
        let hSubLin : mkHasExternalSubLinearLogic α? V ← InstanceExpr.synthesize
        return mkHasExternalSubLinearLogic.mkConstFun α? y
      let hαY : mkHasPiType (HasConstPi.defConstPi (α := φ.α) _(Y')) := ⟨φ.h.h⟩
      let hConstPi : mkHasConstPi φ.α Y' ← InstanceExpr.synthesize
      pure (mkHasConstPi.mkConstPi φ.α y)
    | LambdaBodyCategoryExt.id =>
      let hVV : mkHasUnivFunctors V V ← InstanceExpr.synthesize
      let hIdFun : mkHasIdFun Y' ← InstanceExpr.synthesize
      pure (mkHasIdFun.mkIdFun Y')
    | LambdaBodyCategoryExt.dep => tryConstructLambdaAppFunctor f (some Y') constructLambdaFunctor
  | LambdaBodyCategory.dep => tryConstructLambdaAppFunctor f none constructLambdaFunctor


def constructFunctor {v : Level} {V : _Universe v} {φ : PiData V} (f : φ.mkSortPi) : MetaM φ.mkPi :=
  LambdaAbstraction.fromPi f (fun f' =>
    match f'.t.mvarId? with
    | some mvarId =>
      -- TODO: Is there a way to show the standard placeholder message at the right place?
      throwError "unfilled placeholder in functor declaration\n{MessageData.ofGoal mvarId}"
    | none => constructLambdaFunctor f')


-- The `makeFunctor` elaborator, which calls `constructFunctor` based on the target type and
-- given term. Note that the target type determines how to elaborate the term, which enables us
-- to omit the variable type in `Λ` expressions.
elab "makeFunctor " hf:term:1023 : term <= type => do
  let v ← mkFreshLevelMVar
  let V ← _Universe.mkFreshMVar v
  let A : V ← V.mkFreshTypeMVar
  unless ← isDefEq type _⌈A⌉.α do
    throwError "could not determine universe of type '{type}'"
  let v ← instantiateLevelMVars v
  let V ← V.instantiate v
  let A : V ← V.instantiateTypeMVars A
  let φ ← PiData.mkFreshMVar V
  unless ← isDefEq A φ.mkPi do
    let A' : Expr := A
    let V' : Expr := V
    throwError "type '{A'} : {V'}' is not an application of 'HasPiType.Pi'"
  let φ ← φ.instantiate V
  let f : φ.mkSortPi ← _sort.elaborate' hf
  constructFunctor f

-- Implementation of the `Λ` notation.
-- We want `Λ a b ... => t` to be a shortcut for:
-- `makeFunctor (λ a => makeFunctor (λ b => ... t))`.
-- However, `expandExplicitBinders` only accepts a name and `makeFunctor` isn't one, so as a
-- hack, we currently pass it a dummy name `__makeFunctor` and then recursively replace the
-- corresponding syntax nodes in the result.
partial def replaceMakeFunctor : Syntax → MacroM Syntax
  | `(__makeFunctor $f) => do
    let f ← replaceMakeFunctor f
    `(makeFunctor $f)
  | f => match f with
         | Syntax.node info kind args => do
           let args ← args.sequenceMap replaceMakeFunctor
           pure (Syntax.node info kind args)
         | f => pure f

macro "Λ " xs:explicitBinders " => " b:term : term => do
  let f ← expandExplicitBinders `__makeFunctor xs b
  replaceMakeFunctor f


-- The `functoriality` tactic, which constructs instances of `DefInst`.

partial def functoriality? {v : Level} {V : _Universe v} (A : V) : MetaM (Option A) := do
  let φ ← PiData.mkFreshMVar V
  let f : φ.mkSortPi ← _sort.mkFreshInstMVar
  if ← withReducible (isDefEq A (mkHasPiType.mkDefPi φ.P f)) then
    let φ ← φ.instantiate V
    let f : φ.mkSortPi ← _sort.instantiateInstMVars f
    unless f.isMVar do
      let F ← constructFunctor f
      return (some F)
  let u' ← mkFreshLevelMVar
  let β : φ.α ⥤ _sort.mkSortType u' ← _sort.mkFreshInstMVar
  let h : mkHasPiType.mkHasDepElim' φ.P β ← InstanceExpr.mkFreshMVar
  let f : Pi (mkHasPiType.sortProp' β) ← _sort.mkFreshInstMVar
  if ← isDefEq A (mkHasPiType.mkDefPi' φ.P β f) then
    let φ ← φ.instantiate V
    let u' ← instantiateLevelMVars u'
    let β : φ.α ⥤ _sort.mkSortType u' ← _sort.instantiateInstMVars β
    let h : mkHasPiType.mkHasDepElim' φ.P β ← h.instantiate
    let f : Pi (mkHasPiType.sortProp' β) ← _sort.instantiateInstMVars f
    let f? : Option φ.mkSortPi ← LambdaAbstraction.fromPi f (fun f' => do
      let B : V := mkHasPiType.mkHasDepElim'.mkApp φ.P β f f'.a.a
      match ← functoriality? B with
      | some G => pure (some (f'.mkDependentExpr G).toPi)
      | none   => pure none)
    if let some f := f? then
      let F ← constructFunctor f
      return some F
  pure none

def functoriality (mvarId : MVarId) : TacticM Expr := do
  let type ← mvarId.getType
  let v ← mkFreshLevelMVar
  let V ← _Universe.mkFreshMVar v
  let A : V ← V.mkFreshTypeMVar
  unless ← isDefEq type _⌈A⌉.α do
    throwError "could not determine universe of type '{type}'"
  let v ← instantiateLevelMVars v
  let V ← V.instantiate v
  let A : V ← V.instantiateTypeMVars A
  match ← functoriality? A with
  | some F => pure F
  | none   =>
    let A' : Expr := A
    throwTacticEx `functoriality mvarId
                  m!"type '{A'}' is not an application of 'DefInst'"

elab "functoriality" : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let e ← functoriality mvarId
    mvarId.assign e
