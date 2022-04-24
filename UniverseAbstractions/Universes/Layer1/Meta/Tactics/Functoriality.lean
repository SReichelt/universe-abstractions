import UniverseAbstractions.Meta.TypedExpr
import UniverseAbstractions.Meta.Helpers
import UniverseAbstractions.Universes.Layer1.Meta.Reflect



namespace UniverseAbstractions.Layer1.Meta.Tactics.Functoriality

set_option autoBoundImplicitLocal false

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic



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
{U    : _Universe}
[hFun : mkHasFunctors U]
(A B  : _⌈U⌉_)

namespace FunData

  def mkFreshMVar : MetaM FunData := do
    let U ← _Universe.mkFreshMVar
    let hFun : mkHasFunctors U ← InstanceExpr.mkFreshMVar
    let A : _⌈U⌉_ ← _Universe.mkFreshTypeMVar
    let B : _⌈U⌉_ ← _Universe.mkFreshTypeMVar
    pure ⟨A, B⟩

  def instantiate (φ : FunData) : MetaM FunData := do
    let U ← φ.U.instantiate
    let hFun : mkHasFunctors U ← φ.hFun.instantiate
    let A : _⌈U⌉_ ← _Universe.instantiateTypeMVars φ.A
    let B : _⌈U⌉_ ← _Universe.instantiateTypeMVars φ.B
    pure ⟨A, B⟩

  variable (φ : FunData)

  instance : mkHasFunctors φ.U := φ.hFun

  def mkFun      := φ.A _⟶ φ.B
  def mkFunArrow := ⌜$(_⌈φ.A⌉) → $(_⌈φ.B⌉)⌝

end FunData


structure FunctorLambdaAbstraction (φ : FunData) where
(n : Name)
(a : φ.A)
(b : φ.B)

namespace FunctorLambdaAbstraction

  variable {φ : FunData}

  def construct {a : φ.A} (t : DependentTerm (α := _⌈φ.A⌉) a _⌈φ.B⌉) :
    FunctorLambdaAbstraction φ :=
  ⟨t.n, a, t.b⟩

  variable (f : FunctorLambdaAbstraction φ)

  def a' : FVar _⌈φ.A⌉ := f.a
  def Term {w : Level} (γ : ⌜Sort w⌝) := DependentTerm f.a' γ
  def term : f.Term _⌈φ.B⌉ := ⟨f.n, f.b⟩
  def fn : φ.mkFunArrow := f.term.toFunction

end FunctorLambdaAbstraction


def synthesizeFunApps {φ : FunData} (f : FunctorLambdaAbstraction φ) (forcePrimitive : Bool) :
    MetaM (List (mkHasFunctors.FunApp f.b)) := do
  -- `forcePrimitive` is used in the extensionality tactic.
  -- It causes `IsFunApp` declarations of `swapFun` and `substFun` to be ignored.
  if forcePrimitive then
    let compFun_A : _⌈φ.U⌉_ ← _Universe.mkFreshTypeMVar
    let compFun_B : _⌈φ.U⌉_ ← _Universe.mkFreshTypeMVar
    let compFun_C : _⌈φ.U⌉_ ← _Universe.mkFreshTypeMVar
    let compFun_F : compFun_A _⟶ compFun_B ← _Universe.mkFreshInstMVar
    let compFun_G : compFun_B _⟶ compFun_C ← _Universe.mkFreshInstMVar
    let hLin : mkHasLinearLogic φ.U ← InstanceExpr.mkFreshMVar
    let compFun := mkHasLinearLogic.mkCompFun compFun_F compFun_G
    if ← isDefEq f.b compFun then
      return ← mkHasFunctors.synthesizeFunApps'' (B := φ.B) compFun
    let dupFun_A : _⌈φ.U⌉_ ← _Universe.mkFreshTypeMVar
    let dupFun_B : _⌈φ.U⌉_ ← _Universe.mkFreshTypeMVar
    let dupFun_F : dupFun_A _⟶ dupFun_A _⟶ dupFun_B ← _Universe.mkFreshInstMVar
    let hNonLin : mkHasNonLinearLogic φ.U ← InstanceExpr.mkFreshMVar
    let dupFun := mkHasNonLinearLogic.mkDupFun dupFun_F
    if ← isDefEq f.b dupFun then
      return ← mkHasFunctors.synthesizeFunApps'' (B := φ.B) dupFun
  mkHasFunctors.synthesizeFunApps f.b

mutual

  -- The main entry point, which handles `constFun` and `idFun` directly, and calls
  -- `constructLambdaAppFunctor` to deal with a lambda application.

  partial def constructLambdaFunctor {φ : FunData} (f : FunctorLambdaAbstraction φ)
                                     (forcePrimitive : Bool) :
              MetaM φ.mkFun := do
    match ← f.term.asConstant? with
    | some (b : φ.B) => do
      let hSubLin : mkHasSubLinearLogic φ.U ← InstanceExpr.synthesize
      mkHasSubLinearLogic.mkConstFun φ.A b
    | none => do
      if ← f.term.isId then
        let hLin : mkHasLinearLogic φ.U ← InstanceExpr.synthesize
        return mkHasLinearLogic.mkIdFun φ.B
      let funApps ← synthesizeFunApps f forcePrimitive
      match funApps with
      | List.nil =>
        let b : Expr := f.b
        throwError "unsupported lambda body {b} (failed to synthesize IsFunApp instance)"
      | List.cons mainFunApp _ =>
        for funApp in funApps do
          match ← constructLambdaAppFunctor f funApp forcePrimitive true with
          | some F => return F
          | none   => ()
        match ← constructLambdaAppFunctor f mainFunApp forcePrimitive false with
        | some F => F
        | none   => panic "mandatory result missing"

  partial def constructLambdaFunctor' (φ : FunData) {a : φ.A}
                                      (t : DependentTerm (α := _⌈φ.A⌉) a _⌈φ.B⌉)
                                      (forcePrimitive : Bool) :=
  constructLambdaFunctor (FunctorLambdaAbstraction.construct t) forcePrimitive

  -- This function handles the different cases of functor application in the lambda body,
  -- depending on which parts are either equal to the lambda variable or constant with respect
  -- to it. (We do not optimize the case where both parts are constant, since that should have
  -- been handled already.)

  partial def constructLambdaAppFunctor {φ : FunData} (f : FunctorLambdaAbstraction φ)
                                        (funApp : mkHasFunctors.FunApp f.b)
                                        (forcePrimitive : Bool) (requireConstG : Bool) :
              MetaM (Option φ.mkFun) := do
    let C := funApp.A
    let G : f.Term _⌈C _⟶ φ.B⌉ := ⟨f.n, funApp.hFunApp.F⟩
    let c : f.Term _⌈C⌉        := ⟨f.n, funApp.hFunApp.a⟩
    match ← G.asConstant? with
    | some (G' : C _⟶ φ.B) => do
      if ← c.isId then
        return some G'
      let hLin : mkHasLinearLogic φ.U ← InstanceExpr.synthesize
      let F_c ← constructLambdaFunctor' ⟨φ.A, C⟩ c forcePrimitive
      some (mkHasLinearLogic.mkCompFun F_c G')
    | none => do
      if requireConstG then
        return none
      match ← c.asConstant? with
      | some (c' : C) => do
        let hLin : mkHasLinearLogic φ.U ← InstanceExpr.synthesize
        if ← G.isId then
          return some (mkHasLinearLogic.mkRevAppFun c' φ.B)
        let F_G ← constructLambdaFunctor' ⟨φ.A, C _⟶ φ.B⟩ G forcePrimitive
        some (mkHasLinearLogic.mkSwapFun F_G c')
      | none => do
        let hNonLin : mkHasNonLinearLogic φ.U ← InstanceExpr.synthesize
        if ← c.isId then
          let G' : f.Term _⌈φ.A _⟶ φ.B⌉ := ⟨G.n, G.b⟩
          let F_G ← constructLambdaFunctor' ⟨φ.A, φ.A _⟶ φ.B⟩ G' forcePrimitive
          return some (mkHasNonLinearLogic.mkDupFun F_G)
        let hLin : mkHasLinearLogic φ.U ← InstanceExpr.synthesize
        let F_c ← constructLambdaFunctor' ⟨φ.A, C⟩ c forcePrimitive
        if ← G.isId then
          let F_c' : (C _⟶ φ.B) _⟶ C := F_c
          return some (mkHasNonLinearLogic.mkRevSelfAppFun F_c')
        let F_G ← constructLambdaFunctor' ⟨φ.A, C _⟶ φ.B⟩ G forcePrimitive
        some (mkHasNonLinearLogic.mkSubstFun F_c F_G)

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
            Syntax.node info kind args
          | f => f

macro "Λ" xs:explicitBinders " => " b:term : term => do
  let f ← expandExplicitBinders `__makeFunctor xs b
  replaceMakeFunctor f


-- The `functoriality` tactic, which constructs instances of `DefFun`, `DefFun₂`, etc.

mutual

  partial def functoriality? (type : Expr) : MetaM (Option Expr) := do
    let φ ← FunData.mkFreshMVar
    let f : φ.mkFunArrow ← TypedExpr.mkFreshMVar
    if ← isDefEq type (mkHasFunctors.mkDefFun φ.A φ.B f) then
      let φ ← φ.instantiate
      let f : φ.mkFunArrow ← f.instantiate
      let F ← constructFunctor f
      return mkHasFunctors.mkDefFun.mkMk φ.A φ.B f F
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
      none
    | _ => none

  partial def dependentFunctoriality? (type : Expr) : MetaM (Option Expr) := do
    match type with
    | Expr.forallE n d b c =>
      withLocalDecl n c.binderInfo d (fun a => do
        match ← dependentFunctoriality? (b.instantiate1 a) with
        | some F => mkLambda n c.binderInfo d (F.abstract #[a])
        | none   => none)
    | type => functoriality? type

  partial def addFunctorialityArgs : Nat → Expr → MetaM (Option Expr)
    | 0,   e => some e
    | n+1, e => do
      match ← inferType e with
      | Expr.forallE _ argType _ _ =>
        match ← dependentFunctoriality? argType with
        | some F => addFunctorialityArgs n (mkApp e F)
        | none   => none
      | _ => none

end

def functoriality (mvarId : MVarId) : TacticM Expr := do
  let type ← getMVarType mvarId
  match ← functoriality? type with
  | some F => F
  | none   => throwTacticEx `functoriality mvarId
                            m!"type '{type}' is not an application of 'HasFunctors.DefFun'"

elab "functoriality" : tactic => do
  let mvarId ← getMainGoal
  withMVarContext mvarId do
    let e ← functoriality mvarId
    assignExprMVar mvarId e
