import UniverseAbstractions.Universes.Layer1.Meta.Reflect.Functors
import UniverseAbstractions.Universes.Layer1.Meta.FVar



namespace UniverseAbstractions.Layer1.Meta.Tactics.Functoriality

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option linter.unusedVariables false

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic UniverseAbstractions.Meta
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



def PiLambdaAbstraction {v : Level} {V : _Universe v} (φ : PiData V) :=
  LambdaAbstraction (mkHasPiType.defSortPropFun φ.P)


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

-- This function handles the different cases of functor application in the lambda body,
-- depending on which parts are either equal to the lambda variable or constant with respect
-- to it. (We do not optimize the case where both parts are constant, since that should have
-- been handled already.)

-- Handles the most generic case where everything may depend on `f.a`.
def constructLambdaAppFunctor_dep {v : Level} {V : _Universe v} {φ : PiData V}
                                  (f : PiLambdaAbstraction φ) (piApp : PiApp f.y)
                                  (requireConstF : Bool)
                                  (constructLambdaFunctor : ConstructLambdaFunctor) :
    MetaM (Option φ.mkPi) := do
  if requireConstF then
    return none
  let x ← mkFreshLevelMVar
  let X ← _Universe.mkFreshMVar x
  let A : X ← _Universe.mkFreshTypeMVar
  if ← isDefEq piApp.α.α _⌈A⌉.α then
    let x ← instantiateLevelMVars x
    let X ← X.instantiate x
    let A : X ← _Universe.instantiateTypeMVars A
    let piApp_A := f.mkDependentExpr A
    let P : φ.α ⥤ _[X] := piApp_A.toPi
    let P' := DefFun.defAppFun P
    let ⟨p, P', hP⟩ ← mkHasPiType.synthesize P'
    let piApp_P := f.mkDependentExpr piApp.P.inst
    let Q : Pi (λ a => (_⌈(mkHasPiType.reflectProp P') a⌉ ⥤ _[V])) := piApp_P.toPi
    let Q' := DefPi.defAppPi Q
    let hQa : mkHasQuantDepPiType Q' ← InstanceExpr.synthesize
    let hPiQa : mkHasPiType (mkHasQuantDepPiType.piProp Q') := { h := ← TypedExpr.synthesize, hFun := none } -- TODO
    let hQaFa : mkHasQuantPiType (mkHasSubstPi.prop Q') ← InstanceExpr.synthesize
    let hSubst : mkHasSubstPi Q' ← InstanceExpr.synthesize
    let piApp_a := f.mkDependentExpr piApp.a
    let piApp_a' : DependentTypedExpr f.a ⟨_⌈p f.a.a⌉.α⟩ := ⟨piApp_a.y⟩
    let φ_a : PiData X := ⟨P'⟩
    let f_a : PiLambdaAbstraction φ_a := ⟨piApp_a'⟩
    let F_a ← constructLambdaFunctor f_a
    let piApp_F := f.mkDependentExpr piApp.F
    let piApp_F' : DependentTypedExpr f.a ⟨_⌈Pi (mkHasQuantDepPiType.reflectAppProp Q' f.a.a)⌉.α⟩ :=
        ⟨piApp_F.y⟩
    let φ_F : PiData V := ⟨mkHasQuantDepPiType.piProp Q'⟩
    let f_F : PiLambdaAbstraction φ_F := ⟨piApp_F'⟩
    let F_F ← constructLambdaFunctor f_F
    return some (mkHasSubstPi.mkRevSubstPi (Q := Q') F_F F_a)
  pure none

-- Handles the case where `piApp.α` is independent of `f.a`, but `piApp.P` may not necessarily be.
-- Abstracting `piApp.P` then yields a bi-property.
def constructLambdaAppFunctor_indep_dep {v : Level} {V : _Universe v} {φ : PiData V}
                                        (f : PiLambdaAbstraction φ) (piApp : PiApp f.y)
                                        (requireConstF : Bool)
                                        (constructLambdaFunctor : ConstructLambdaFunctor) :
    MetaM (Option φ.mkPi) := do
  if requireConstF then
    return none
  let piApp_F := f.mkDependentExpr piApp.F
  let piApp_a := f.mkDependentExpr piApp.a
  match ← piApp_a.classifyExt with
  | LambdaBodyCategoryExt.const (piApp_a' : piApp.α) => do
    let piApp_P := f.mkDependentExpr piApp.P.inst
    let Q : φ.α ⥤ piApp.α ⥤ _[V] := piApp_P.toPi
    let Q' := DefFun₂.defAppFun Q
    let hQa : mkHasQuantPiType Q' ← InstanceExpr.synthesize
    let hPiQa : mkHasPiType (mkHasQuantPiType.piProp Q') :=
        { h := ← TypedExpr.synthesize, hFun := none } -- TODO
    let hQab : mkHasQuantPiType (mkHasSwapPi.prop Q') ← InstanceExpr.synthesize
    let hSwapPi : mkHasSwapPi Q' ← InstanceExpr.synthesize
    let piApp_F' : DependentTypedExpr f.a ⟨_⌈Pi (mkHasQuantPiType.reflectAppProp Q' f.a.a)⌉.α⟩ :=
        ⟨piApp_F.y⟩
    let φ_F : PiData V := ⟨mkHasQuantPiType.piProp Q'⟩
    let f_F : PiLambdaAbstraction φ_F := ⟨piApp_F'⟩
    let F_F ← constructLambdaFunctor f_F
    pure (some (mkHasSwapPi.mkSwapPi (P := Q') F_F piApp_a'))
  | LambdaBodyCategoryExt.id => do
    let piApp_P := f.mkDependentExpr piApp.P.inst
    let Q : φ.α ⥤ φ.α ⥤ _[V] := piApp_P.toPi
    let Q' := DefFun₂.defAppFun Q
    let hQa : mkHasQuantPiType Q' ← InstanceExpr.synthesize
    let hPiQa : mkHasPiType (mkHasQuantPiType.piProp Q') :=
        { h := ← TypedExpr.synthesize, hFun := none } -- TODO
    let hQaa : mkHasPiType (mkHasDupPi.prop Q') :=
        { h := ← TypedExpr.synthesize, hFun := none } -- TODO
    let hDupFun : mkHasDupPi Q' ← InstanceExpr.synthesize
    let piApp_F' : DependentTypedExpr f.a ⟨_⌈Pi (mkHasQuantPiType.reflectAppProp Q' f.a.a)⌉.α⟩ :=
        ⟨piApp_F.y⟩
    let φ_F : PiData V := ⟨mkHasQuantPiType.piProp Q'⟩
    let f_F : PiLambdaAbstraction φ_F := ⟨piApp_F'⟩
    let F_F ← constructLambdaFunctor f_F
    pure (some (mkHasDupPi.mkDupPi (P := Q') F_F))
  | LambdaBodyCategoryExt.dep =>
    constructLambdaAppFunctor_dep f piApp requireConstF constructLambdaFunctor

-- Handles the case where both `piApp.α` and `piApp.P` are independent of `f.a`. This must always be
-- the case if `piApp.F` is independent of `f.a`, and also if `piApp.F` is exactly `f.a`.
def constructLambdaAppFunctor_indep_indep {v : Level} {V : _Universe v} {φ : PiData V}
                                          (f : PiLambdaAbstraction φ) (piApp : PiApp f.y)
                                          (requireConstF : Bool)
                                          (constructLambdaFunctor : ConstructLambdaFunctor) :
    MetaM (Option φ.mkPi) := do
  let piApp_F := f.mkDependentExpr piApp.F
  let piApp_a := f.mkDependentExpr piApp.a
  match ← piApp_F.classifyExt with
  | LambdaBodyCategoryExt.const (piApp_F' : Pi (mkHasPiType.reflectProp piApp.P)) => do
    if ← piApp_a.isId then
      return some piApp_F'
    let X ← _Universe.mkFreshMVar φ.α.u
    let piApp_A : X ← _Universe.mkFreshTypeMVar
    if ← isDefEq piApp.α.α _⌈piApp_A⌉.α then
      let X ← X.instantiate φ.α.u
      let piApp_A : X ← _Universe.instantiateTypeMVars piApp_A
      let hαA : mkHasFunctors φ.α piApp_A ← InstanceExpr.synthesize
      let piApp_P : _⌈piApp_A⌉ ⥤{piApp.p} _[V] := ⟨piApp.P.inst⟩
      let piApp_hP : mkHasPiType piApp_P := { h := piApp.h.h, hFun := piApp.h.hFun }
      let hPFa : mkHasQuantPiType (mkHasCompFunPi.prop φ.α piApp_P) ← InstanceExpr.synthesize
      let hCompFunPi : mkHasCompFunPi φ.α piApp_P ← InstanceExpr.synthesize
      let piApp_F'' : Pi (mkHasPiType.reflectProp piApp_P) := piApp_F'
      let piApp_a' : DependentTypedExpr f.a ⟨_⌈piApp_A⌉.α⟩ := ⟨piApp_a.y⟩
      let φ_a : PiData X := ⟨HasConstPi.defConstFun φ.α _(piApp_A)⟩
      let f_a : PiLambdaAbstraction φ_a := ⟨piApp_a'⟩
      let F_a' ← constructLambdaFunctor f_a
      let F_a : φ.α ⥤ piApp_A := F_a'
      let revCompFunPi := mkHasCompFunPi.mkRevCompFunPi piApp_F'' F_a
      return some revCompFunPi
    constructLambdaAppFunctor_indep_dep f piApp requireConstF constructLambdaFunctor
  | LambdaBodyCategoryExt.id => do
    if requireConstF then
      return none
    match ← piApp_a.classify with
    | LambdaBodyCategory.const (piApp_a' : piApp.α) => do
      let hVV : mkHasUnivFunctors V V ← InstanceExpr.synthesize
      let hPiAppFun : mkHasPiAppFun piApp.P ← InstanceExpr.synthesize
      let piAppFun := mkHasPiAppFun.mkPiAppFun piApp.P piApp_a'
      pure (some piAppFun)
    | LambdaBodyCategory.dep => do
      let X ← _Universe.mkFreshMVar v
      let A : X ← _Universe.mkFreshTypeMVar
      let Q : _⌈A⌉ ⥤ _[V] ← _sort.mkFreshInstMVar
      let Q' := DefFun.defAppFun Q
      let hQ : mkHasPiType Q' ← mkHasPiType.mkFreshMVar
      if ← isDefEq φ.α.α _⌈Pi (mkHasPiType.reflectProp Q')⌉.α then
        let X ← X.instantiate v
        let X' ← X.instantiate φ.α.u
        let A : X ← _Universe.instantiateTypeMVars A
        let A' : X' := A
        let Q : _⌈A⌉ ⥤ _[V] ← _sort.instantiateInstMVars Q
        let Q' := DefFun.defAppFun Q
        let hQ : mkHasPiType Q' := { h := ← hQ.h.instantiate, hFun := none } -- TODO
        let hVX : mkHasUnivFunctors V X ← InstanceExpr.synthesize
        let hQF : mkHasQuantPiType (mkHasPiSelfAppPi.prop Q') ← InstanceExpr.synthesize
        let hRevSelfApp : mkHasPiSelfAppPi Q' ← InstanceExpr.synthesize
        let hPiQA : mkHasFunctors _⌈Pi (mkHasPiType.reflectProp Q')⌉ A := inferInstance
        let hαA : mkHasFunctors φ.α A' := { h := hPiQA.h }
        let piApp_a' : DependentTypedExpr f.a ⟨_⌈A'⌉.α⟩ := ⟨piApp_a.y⟩
        let φ_a : PiData X' := ⟨HasConstPi.defConstFun φ.α _(A')⟩
        let f_a : PiLambdaAbstraction φ_a := ⟨piApp_a'⟩
        let F_a' ← constructLambdaFunctor f_a
        let F_a : Pi (mkHasPiType.reflectProp Q') := F_a'
        let piSelfAppPi := mkHasPiSelfAppPi.mkPiSelfAppPi (Q := Q') F_a
        return some piSelfAppPi
      constructLambdaAppFunctor_indep_dep f piApp requireConstF constructLambdaFunctor
  | LambdaBodyCategoryExt.dep =>
    constructLambdaAppFunctor_indep_dep f piApp requireConstF constructLambdaFunctor

-- Handles both cases where `piApp.α` is independent of `f.a`. (This is nearly always the case. If
-- `piApp.α` depends on `f.a`, then everything else also does, so `substPi` is then the only
-- possibility.)
def constructLambdaAppFunctor_indep {v : Level} {V : _Universe v} {φ : PiData V}
                                    (f : PiLambdaAbstraction φ) (piApp : PiApp f.y)
                                    (requireConstF : Bool)
                                    (constructLambdaFunctor : ConstructLambdaFunctor) :
    MetaM (Option φ.mkPi) := do
  match piApp.h.hFun with
  | some piApp_hFun => do
    let piApp_hFun := f.mkDependentExpr piApp_hFun
    match ← piApp_hFun.classify with
    | LambdaBodyCategory.const piApp_hFun'' => do
      let α : _sort.mkSortType v := piApp.α.α
      let Y : V := φ.p f.a.a
      let hFun : mkHasFunctors α Y := { h := piApp_hFun'' }
      let piApp' : PiApp f.y := ⟨⟨HasConstPi.defConstFun α _(Y)⟩, piApp.F, piApp.a⟩
      constructLambdaAppFunctor_indep_indep f piApp' requireConstF constructLambdaFunctor
    | LambdaBodyCategory.dep => do
      constructLambdaAppFunctor_indep_dep f piApp requireConstF constructLambdaFunctor
  | none => do
    let piApp_P := f.mkDependentExpr piApp.P.inst
    match ← piApp_P.classify with
    | LambdaBodyCategory.const (piApp_P' : piApp.α ⥤ _[V]) => do
      let piApp_P'' := DefFun.defAppFun piApp_P'
      let piApp_hP_h := f.mkDependentExpr piApp.h.h
      match ← piApp_hP_h.classify with
      | LambdaBodyCategory.const piApp_hP_h' => do
        let hPiApp_P'' : mkHasPiType piApp_P'' := { h := piApp_hP_h', hFun := none }
        let piApp' : PiApp f.y := ⟨⟨piApp_P''⟩, piApp.F, piApp.a⟩
        constructLambdaAppFunctor_indep_indep f piApp' requireConstF constructLambdaFunctor
      | LambdaBodyCategory.dep =>
        constructLambdaAppFunctor_indep_dep f piApp requireConstF constructLambdaFunctor
    | LambdaBodyCategory.dep =>
      constructLambdaAppFunctor_indep_dep f piApp requireConstF constructLambdaFunctor

-- Handles all cases.
def constructLambdaAppFunctor {v : Level} {V : _Universe v} {φ : PiData V}
                              (f : PiLambdaAbstraction φ) (piApp : PiApp f.y)
                              (requireConstF : Bool)
                              (constructLambdaFunctor : ConstructLambdaFunctor) :
    MetaM (Option φ.mkPi) := do
  let piApp_α := f.mkDependentExpr piApp.α.α
  match ← piApp_α.classify with
  | LambdaBodyCategory.const (piApp_α' : _sort.mkSortType piApp.α.u) => do
    let piApp_P' : piApp_α' ⥤{piApp.p} _[V] := ⟨piApp.P.inst⟩
    let piApp_hP' : mkHasPiType piApp_P' := { h := piApp.h.h, hFun := piApp.h.hFun }
    let piApp' : PiApp f.y := ⟨⟨piApp_P'⟩, piApp.F, piApp.a⟩
    constructLambdaAppFunctor_indep f piApp' requireConstF constructLambdaFunctor
  | LambdaBodyCategory.dep =>
    constructLambdaAppFunctor_dep f piApp requireConstF constructLambdaFunctor

-- Determines all ways in which the body is a Π application, and calls `constructLambdaAppFunctor`
-- on each to determine a good match.
def tryConstructLambdaAppFunctor {v : Level} {V : _Universe v} {φ : PiData V}
                                 (f : PiLambdaAbstraction φ)
                                 (constructLambdaFunctor : ConstructLambdaFunctor) :
    MetaM φ.mkPi := do
  let piApps ← PiApp.synthesizePiApps f.y
  match piApps with
  | List.nil =>
    let y : Expr := f.y
    throwError "unsupported lambda body '{y}': failed to synthesize IsPiApp instance"
  | List.cons mainPiApp _ =>
    for piApp in piApps do
      match ← constructLambdaAppFunctor f piApp true constructLambdaFunctor with
      | some F => return F
      | none   => pure ()
    match ← constructLambdaAppFunctor f mainPiApp false constructLambdaFunctor with
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
  | LambdaBodyCategory.const (Y' : V) => do
    match ← f.t.classifyExt with
    | LambdaBodyCategoryExt.const (y : Y') => do
      let hαY : mkHasPiType (HasConstPi.defConstFun φ.α _(Y')) := { h := φ.h.h, hFun := φ.h.hFun }
      let hConstPi : mkHasConstPi φ.α Y' ← InstanceExpr.synthesize
      pure (mkHasConstPi.mkConstPi φ.α y)
    | LambdaBodyCategoryExt.id => do
      let hYY : mkHasFunctors _⌈Y'⌉ Y' ← InstanceExpr.synthesize
      let hIdFun : mkHasIdFun Y' ← InstanceExpr.synthesize
      pure (mkHasIdFun.mkIdFun Y')
    | LambdaBodyCategoryExt.dep => tryConstructLambdaAppFunctor f constructLambdaFunctor
  | LambdaBodyCategory.dep => tryConstructLambdaAppFunctor f constructLambdaFunctor


def constructFunctor {v : Level} {V : _Universe v} {φ : PiData V} (f : φ.mkSortPi) : MetaM φ.mkPi :=
  LambdaAbstraction.fromPi f (fun f' =>
    match f'.t.mvarId? with
    | some mvarId =>
      -- TODO: Is there a way to show the standard placeholder message at the right place?
      throwError "unfilled placeholder in functor declaration\n{MessageData.ofGoal mvarId}"
    | none => constructLambdaFunctor f')


-- The `makeFunctor` elaborator, which calls `byFunctoriality` based on the target type and
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


-- The `functoriality` tactic, which constructs instances of `DefPi`, `DefPi₂`, etc.

mutual

  partial def functoriality? (type : Expr) : MetaM (Option Expr) := do
    let type ← whnf type
    let v ← mkFreshLevelMVar
    let V ← _Universe.mkFreshMVar v
    let φ ← PiData.mkFreshMVar V
    let f : φ.mkSortPi ← _sort.mkFreshInstMVar
    if ← isDefEq type (mkHasPiType.mkDefPi φ.P f) then
      let v ← instantiateLevelMVars v
      let V ← V.instantiate v
      let φ ← φ.instantiate V
      let f : φ.mkSortPi ← _sort.instantiateInstMVars f
      let F ← constructFunctor f
      return mkHasPiType.mkDefPi.mkMk φ.P f F
    structureFunctoriality? type

  partial def structureFunctoriality? (type : Expr) : MetaM (Option Expr) := do
    match type.getAppFn with
    | Expr.const declName .. => do
      let env ← getEnv
      if isStructure env declName then
        -- We should probably use code from `StructInst.lean` here, but unfortunately the relevant
        -- declarations are private. But this greatly simplified version is more than sufficient
        -- for us anyway.
        let ctorVal := getStructureCtor env declName
        if ctorVal.numParams == type.getAppNumArgs then
          let us ← mkFreshLevelMVars ctorVal.levelParams.length
          let ctorFn := mkConst ctorVal.name us
          let ctorHeader := mkAppN ctorFn type.getAppArgs
          return ← addStructureFunctorialityArgs ctorVal.numFields ctorHeader
      pure none
    | _ => pure none

  partial def addStructureFunctorialityArgs : Nat → Expr → MetaM (Option Expr)
    | 0,   e => pure (some e)
    | n+1, e => do
      match ← inferType e with
      | Expr.forallE _ argType _ _ =>
        match ← dependentFunctoriality? argType with
        | some F => addStructureFunctorialityArgs n (mkApp e F)
        | none   => pure none
      | _ => pure none

  partial def dependentFunctoriality? (type : Expr) : MetaM (Option Expr) := do
    match type with
    | Expr.forallE n d b c =>
      withLocalDecl n c.binderInfo d (fun a => do
        match ← dependentFunctoriality? (b.instantiate1 a) with
        | some F => pure (mkLambda n c.binderInfo d (F.abstract #[a]))
        | none   => pure none)
    | type => functoriality? type

end

def functoriality (mvarId : MVarId) : TacticM Expr := do
  let type ← getMVarType mvarId
  match ← functoriality? type with
  | some F => pure F
  | none   => throwTacticEx `functoriality mvarId
                            m!"type '{type}' is not an application of 'HasPiType.DefPi'"

elab "functoriality" : tactic => do
  let mvarId ← getMainGoal
  withMVarContext mvarId do
    let e ← functoriality mvarId
    assignExprMVar mvarId e
