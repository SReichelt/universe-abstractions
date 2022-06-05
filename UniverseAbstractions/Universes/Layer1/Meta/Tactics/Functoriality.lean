import UniverseAbstractions.Meta.TypedExpr
import UniverseAbstractions.Meta.Helpers

import UniverseAbstractions.Universes.Layer1.Meta.Reflect.Functors



namespace UniverseAbstractions.Layer1.Meta.Tactics.Functoriality

set_option autoBoundImplicitLocal false
set_option maxHeartbeats 250000

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic UniverseAbstractions.Meta



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



structure FunData where
  (α : _Sort)
  {V : _Universe}
  [h : mkHasFunctors α V]
  Y  : _(V)

namespace FunData

  def mkFreshMVar : MetaM FunData := do
    let u ← mkFreshLevelMVar
    let α ← _Sort.mkFreshMVar
    let V ← _Universe.mkFreshMVar
    let h : mkHasFunctors α V ← InstanceExpr.mkFreshMVar
    let Y : _(V) ← _Universe.mkFreshTypeMVar
    pure ⟨α, Y⟩

  def instantiate (φ : FunData) : MetaM FunData := do
    let α ← φ.α.instantiate
    let V ← φ.V.instantiate
    let h : mkHasFunctors α V ← φ.h.instantiate
    let Y : _(V) ← _Universe.instantiateTypeMVars φ.Y
    pure ⟨α, Y⟩

  variable (φ : FunData)

  instance : mkHasFunctors φ.α φ.V := φ.h

  def mkFun      := φ.α ⥤ φ.Y
  def mkFunArrow := ⌜$(φ.α.α) → $(_⌈φ.Y⌉.α)⌝

end FunData


structure FunctorLambdaAbstraction (φ : FunData) where
  n : Name
  a : φ.α
  y : φ.Y

namespace FunctorLambdaAbstraction

  variable {φ : FunData}

  def construct {a : φ.α} (t : DependentTerm a _⌈φ.Y⌉.α) : FunctorLambdaAbstraction φ :=
    ⟨t.n, a, t.b⟩

  variable (f : FunctorLambdaAbstraction φ)

  def a' : FVar φ.α.α := f.a
  def Term (γ : _Sort) := DependentTerm f.a' γ.α
  def term : f.Term _⌈φ.Y⌉ := ⟨f.n, f.y⟩
  def fn : φ.mkFunArrow := f.term.toFunction

end FunctorLambdaAbstraction


def synthesizeFunApps {φ : FunData} (f : FunctorLambdaAbstraction φ) (forcePrimitive : Bool) :
    MetaM (List (FunApp f.y)) := do
  -- `forcePrimitive` is used in the extensionality tactic.
  -- It causes `IsFunApp` declarations of `swapFun`, `revSelfAppFun`, and `substFun` to be ignored.
  if forcePrimitive then
    let X ← _Universe.mkFreshMVar
    let hα : mkHasFunctors φ.α X ← InstanceExpr.mkFreshMVar
    let hX : mkHasUnivFunctors X φ.V ← InstanceExpr.mkFreshMVar
    let compFun_B : _(X) ← _Universe.mkFreshTypeMVar
    let compFun_C : _(φ.V) ← _Universe.mkFreshTypeMVar
    let compFun_F : φ.α ⥤ compFun_B ← _Universe.mkFreshInstMVar
    let compFun_G : compFun_B ⥤ compFun_C ← _Universe.mkFreshInstMVar
    let hCompFun : mkHasCompFun φ.α compFun_B φ.V ← InstanceExpr.mkFreshMVar
    let compFun := HasCompFun.revCompFun (C := compFun_C) compFun_G compFun_F
    if ← isDefEq f.y compFun then
      return ← FunApp.synthesizeFunApps' (Y := φ.Y) compFun
    let dupFun_B : _(φ.V) ← _Universe.mkFreshTypeMVar
    let dupFun_F : φ.α ⥤ φ.α ⥤ dupFun_B ← _Universe.mkFreshInstMVar
    let hDupFun : mkHasDupFun φ.α φ.V ← InstanceExpr.mkFreshMVar
    let dupFun := HasDupFun.dupFun dupFun_F
    if ← isDefEq f.y dupFun then
      return ← FunApp.synthesizeFunApps' (Y := φ.Y) dupFun
  FunApp.synthesizeFunApps f.y

mutual

  -- The main entry point, which handles `constFun` and `idFun` directly, and calls
  -- `constructLambdaAppFunctor` to deal with a lambda application.

  partial def constructLambdaFunctor {φ : FunData} (f : FunctorLambdaAbstraction φ)
                                     (forcePrimitive : Bool) :
              MetaM φ.mkFun := do
    match ← f.term.asConstant? with
    | some (y : φ.Y) => do
      let hConstFun : mkHasConstFun φ.α φ.V ← InstanceExpr.synthesize
      pure (HasConstFun.constFun φ.α y)
    | none => do
      if ← f.term.isId then
        let hY : mkHasFunctors _⌈φ.Y⌉ φ.V := { h := φ.h.h }
        let hIdFun : mkHasIdFun φ.Y ← InstanceExpr.synthesize
        return mkHasIdFun.mkIdFun φ.Y
      let funApps ← synthesizeFunApps f forcePrimitive
      match funApps with
      | List.nil =>
        let y : Expr := f.y
        throwError "unsupported lambda body {y}: failed to synthesize IsFunApp instance"
      | List.cons mainFunApp _ =>
        for funApp in funApps do
          match ← constructLambdaAppFunctor f funApp forcePrimitive true with
          | some F => return F
          | none   => pure ()
        match ← constructLambdaAppFunctor f mainFunApp forcePrimitive false with
        | some F => pure F
        | none   => panic "unsupported lambda body {y}: failed to determine a universe"

  partial def constructLambdaFunctor' (φ : FunData) {a : φ.α} (t : DependentTerm a _⌈φ.Y⌉.α)
                                      (forcePrimitive : Bool) :=
    constructLambdaFunctor (FunctorLambdaAbstraction.construct t) forcePrimitive

  -- This function handles the different cases of functor application in the lambda body,
  -- depending on which parts are either equal to the lambda variable or constant with respect
  -- to it. (We do not optimize the case where both parts are constant, since that should have
  -- been handled already.)

  partial def constructLambdaAppFunctor {φ : FunData} (f : FunctorLambdaAbstraction φ)
                                        (funApp : FunApp f.y)
                                        (forcePrimitive : Bool) (requireConstG : Bool) :
              MetaM (Option φ.mkFun) := do
    let β := funApp.α
    let hβ : mkHasFunctors β φ.V := funApp.h
    let G : f.Term _⌈β ⥤ φ.Y⌉ := ⟨f.n, funApp.hFunApp.F⟩
    let b : f.Term β          := ⟨f.n, funApp.hFunApp.a⟩
    match ← G.asConstant? with
    | some (G' : β ⥤ φ.Y) => do
      if ← b.isId then
        return some G'
      let X ← _Universe.mkFreshMVar
      let B : _(X) ← _Universe.mkFreshTypeMVar
      if ← isDefEq β _⌈B⌉ then
        let X ← X.instantiate
        let B : _(X) ← _Universe.instantiateTypeMVars B
        let b' : f.Term _⌈B⌉ := ⟨b.n, b.b⟩ 
        let hαX : mkHasFunctors φ.α X ← InstanceExpr.synthesize
        let F_b ← constructLambdaFunctor' ⟨φ.α, B⟩ b' forcePrimitive
        let hBV : mkHasFunctors _⌈B⌉ φ.V ← InstanceExpr.synthesize
        let hCompFun : mkHasCompFun φ.α B φ.V ← InstanceExpr.synthesize
        return some (G' ⊙ F_b)
      pure none
    | none => do
      if requireConstG then
        return none
      match ← b.asConstant? with
      | some (b' : β) => do
        if ← G.isId then
          let hUU : mkHasUnivFunctors φ.V φ.V ← InstanceExpr.synthesize
          let hRevAppFun : mkHasRevAppFun β φ.V ← InstanceExpr.synthesize
          return some (HasRevAppFun.revAppFun b' φ.Y)
        let hSwapFun : mkHasSwapFun φ.α β φ.V ← InstanceExpr.synthesize
        let F_G ← constructLambdaFunctor' ⟨φ.α, β ⥤ φ.Y⟩ G forcePrimitive
        pure (some (HasSwapFun.swapFun F_G b'))
      | none => do
        if ← b.isId then
          let hDupFun : mkHasDupFun φ.α φ.V ← InstanceExpr.synthesize
          let G' : f.Term _⌈φ.α ⥤ φ.Y⌉ := ⟨G.n, G.b⟩
          let F_G ← constructLambdaFunctor' ⟨φ.α, φ.α ⥤ φ.Y⟩ G' forcePrimitive
          return some (HasDupFun.dupFun F_G)
        let X ← _Universe.mkFreshMVar
        let B : _(X) ← _Universe.mkFreshTypeMVar
        if ← isDefEq β _⌈B⌉ then
          let X ← X.instantiate
          let B : _(X) ← _Universe.instantiateTypeMVars B
          let b' : f.Term _⌈B⌉ := ⟨b.n, b.b⟩ 
          let hαX : mkHasFunctors φ.α X ← InstanceExpr.synthesize
          let F_b ← constructLambdaFunctor' ⟨φ.α, B⟩ b' forcePrimitive
          if ← G.isId then
            let hXV : mkHasUnivFunctors X φ.V ← InstanceExpr.synthesize
            let hVX : mkHasUnivFunctors φ.V X ← InstanceExpr.synthesize
            let hVV : mkHasUnivFunctors φ.V φ.V ← InstanceExpr.synthesize
            let hRevSelfApp : mkHasRevSelfAppFun X φ.V ← InstanceExpr.synthesize
            let F_b' : (B ⥤ φ.Y) ⥤ B := F_b
            return some (HasRevSelfAppFun.revSelfAppFun (A := B) (B := φ.Y) F_b')
          let hBV : mkHasFunctors _⌈B⌉ φ.V ← InstanceExpr.synthesize
          let hSubstFun : mkHasSubstFun φ.α B φ.V ← InstanceExpr.synthesize
          let F_G ← constructLambdaFunctor' ⟨φ.α, β ⥤ φ.Y⟩ G forcePrimitive
          return some (HasSubstFun.substFun F_b F_G)
        pure none

end

def constructFunctor {φ : FunData} (f : φ.mkFunArrow) : MetaM Expr :=
  DependentTerm.fromFunction f (fun t => do
    if t.isMVar then
      -- TODO: Is there a way to show the standard placeholder message at the right place?
      throwError "unfilled placeholder in functor declaration\n{MessageData.ofGoal t.mvarId!}"
    return ← constructLambdaFunctor' φ t false)


-- The `makeFunctor` elaborator, which calls `byFunctoriality` based on the target type and
-- given term. Note that the target type determines how to elaborate the term, which enables us
-- to omit the variable type in `Λ` expressions.

elab "makeFunctor " hf:term:1023 : term <= type => do
  let φ ← FunData.mkFreshMVar
  unless ← isDefEq type _⌈φ.mkFun⌉ do
    throwError "type '{type}' is not an application of 'HasFunctors.Fun'"
  let φ ← φ.instantiate
  let f : φ.mkFunArrow ← TypedExpr.elaborate' hf
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

macro "Λ" xs:explicitBinders " => " b:term : term => do
  let f ← expandExplicitBinders `__makeFunctor xs b
  replaceMakeFunctor f


-- The `functoriality` tactic, which constructs instances of `DefFun`, `DefFun₂`, etc.

mutual

  partial def functoriality? (type : Expr) : MetaM (Option Expr) := do
    let φ ← FunData.mkFreshMVar
    let f : φ.mkFunArrow ← TypedExpr.mkFreshMVar
    if ← isDefEq type (mkHasFunctors.mkDefFun φ.α φ.Y f) then
      let φ ← φ.instantiate
      let f : φ.mkFunArrow ← f.instantiate
      let F ← constructFunctor f
      return mkHasFunctors.mkDefFun.mkMk φ.α φ.Y f F
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
          return ← addFunctorialityArgs ctorVal.numFields ctorHeader
      pure none
    | _ => pure none

  partial def dependentFunctoriality? (type : Expr) : MetaM (Option Expr) := do
    match type with
    | Expr.forallE n d b c =>
      withLocalDecl n c.binderInfo d (fun a => do
        match ← dependentFunctoriality? (b.instantiate1 a) with
        | some F => pure (mkLambda n c.binderInfo d (F.abstract #[a]))
        | none   => pure none)
    | type => functoriality? type

  partial def addFunctorialityArgs : Nat → Expr → MetaM (Option Expr)
    | 0,   e => pure (some e)
    | n+1, e => do
      match ← inferType e with
      | Expr.forallE _ argType _ _ =>
        match ← dependentFunctoriality? argType with
        | some F => addFunctorialityArgs n (mkApp e F)
        | none   => pure none
      | _ => pure none

end

def functoriality (mvarId : MVarId) : TacticM Expr := do
  let type ← getMVarType mvarId
  match ← functoriality? type with
  | some F => pure F
  | none   => throwTacticEx `functoriality mvarId
                            m!"type '{type}' is not an application of 'HasFunctors.DefFun'"

elab "functoriality" : tactic => do
  let mvarId ← getMainGoal
  withMVarContext mvarId do
    let e ← functoriality mvarId
    assignExprMVar mvarId e
