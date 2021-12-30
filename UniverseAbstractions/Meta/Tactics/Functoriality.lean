import UniverseAbstractions.Meta.TypedExpr
import UniverseAbstractions.Meta.Helpers
import UniverseAbstractions.Meta.Reflect
import UniverseAbstractions.Meta.FunData



set_option autoBoundImplicitLocal false



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
--  `Λ a => T t`          | `a` not in `t` | `swapFun (Λ a => T) t`, i.e. `Λ a => (Λ F => F t) T`
--  `Λ a => T a`          |                | `dupFun (Λ a => T)`
--  `Λ a => T t`          |                | `substFun (Λ a => t) (Λ a => T)`,
--                        |                | i.e. `Λ a => (Λ a' => T ((Λ a => t) a')) a`
--  `Λ a => ?Fun t₁...tₙ` |                | `Λ a => (?FunFun t₁...tₙ₋₁) tₙ`
--                        |                | (optimization: use `rev` if it makes `?FunFun` term
--                        |                | constant)
--
-- Although all cases of functor application inside the lambda body can be handled generically by
-- `substFun` (matching SKI combinator calculus), `substFun` requires `FullFunOp`, whereas
-- `compFun`, `revAppFun`, and `swapFun` only require `LinearFunOp` (corresponding to linear logic,
-- where each variable is used exactly once). So the special cases are not merely optimizations.



namespace Lean.Functoriality

  open Meta Elab Tactic

  def synthesizeFunApps {φ : DefFunData} (f : FunctorLambdaAbstraction φ)
                        (forcePrimitive : Bool) :
      MetaM (List (mkHasFunctors.FunApp f.b)) := do
    -- `forcePrimitive` is used in the extensionality tactic.
    -- It causes `IsFunApp` declarations of `swapFun` and `substFun` to be ignored.
    if forcePrimitive then
      let U ← _Universe.mkFreshMVar
      let V ← _Universe.mkFreshMVar
      let W ← _Universe.mkFreshMVar
      let UV ← _Universe.mkFreshMVar
      let VW ← _Universe.mkFreshMVar
      let hFun_UV : mkHasFunctors U V UV ← mkHasFunctors.mkFreshMVar
      let hFun_VW : mkHasFunctors V W VW ← mkHasFunctors.mkFreshMVar
      let hFun_UW : mkHasFunctors U W φ.V ← mkHasFunctors.mkFreshMVar
      let hId_W : mkHasIdentity W ← mkHasIdentity.mkFreshMVar
      let compFun_A : _⌈U⌉_ ← _Universe.mkFreshTypeMVar
      let compFun_B : _⌈V⌉_ ← _Universe.mkFreshTypeMVar
      let compFun_C : _⌈W⌉_ ← _Universe.mkFreshTypeMVar
      let compFun_F : compFun_A _⟶ compFun_B ← _Universe.mkFreshInstMVar
      let compFun_G : compFun_B _⟶ compFun_C ← _Universe.mkFreshInstMVar
      let hCompFun : mkHasCompFun U V W ← InstanceExpr.mkFreshMVar
      let compFun := mkHasCompFun.mkCompFun compFun_F compFun_G
      if ← isDefEq f.b compFun then
        return ← mkHasFunctors.synthesizeFunApps'' (B := φ.B) compFun
      let UUV ← _Universe.mkFreshMVar
      let hFun_UUV : mkHasFunctors U UV UUV ← mkHasFunctors.mkFreshMVar
      let hId_V : mkHasIdentity V ← mkHasIdentity.mkFreshMVar
      let dupFun_A : _⌈U⌉_ ← _Universe.mkFreshTypeMVar
      let dupFun_B : _⌈V⌉_ ← _Universe.mkFreshTypeMVar
      let dupFun_F : dupFun_A _⟶ dupFun_A _⟶ dupFun_B ← _Universe.mkFreshInstMVar
      let hDupFun : mkHasDupFun U V ← InstanceExpr.mkFreshMVar
      let dupFun := mkHasDupFun.mkDupFun dupFun_F
      if ← isDefEq f.b dupFun then
        return ← mkHasFunctors.synthesizeFunApps'' (B := φ.B) dupFun
    mkHasFunctors.synthesizeFunApps

  mutual

    -- The main entry point, which handles `constFun` and `idFun` directly, and calls
    -- `constructLambdaAppFunctor` to deal with a lambda application.

    partial def constructLambdaFunctor {φ : DefFunData} (f : FunctorLambdaAbstraction φ)
                                       (forcePrimitive : Bool) :
                MetaM f.FunDef := do
      match ← f.term.asConstant? with
      | some (b : φ.B) => do
        let hConstFun : mkHasConstFun φ.U φ.V := ⟨← TypedExpr.synthesize⟩
        let defConstFun := HasConstFun.defConstFun (U := φ.U) (V := φ.V) φ.A b
        FunctorLambdaAbstraction.FunDef.mk' f defConstFun
      | none => do
        if ← f.term.isId then
          let hFun_VV : mkHasFunctors φ.V φ.V φ.UV := { h := φ.hFun.h }
          let hIdFun : mkHasIdFun φ.V := ⟨← TypedExpr.synthesize⟩
          let defIdFun := HasIdFun.defIdFun (U := φ.V) φ.B
          let defIdFun' : φ.A _⟶__{id} φ.B := mkHasFunctors.castDefFun defIdFun
          return FunctorLambdaAbstraction.FunDef.mk' f defIdFun'
        let funApps ← synthesizeFunApps f forcePrimitive
        match funApps with
        | List.nil =>
          let b : Expr := f.b
          throwError "unsupported lambda body {b}"
        | List.cons mainFunApp _ =>
          for funApp in funApps do
            match ← constructLambdaAppFunctor f funApp forcePrimitive true with
            | some funDef => return funDef
            | none        => ()
          match ← constructLambdaAppFunctor f mainFunApp forcePrimitive false with
          | some funDef => funDef
          | none        => panic "mandatory result missing"

    partial def constructLambdaFunctor' (φ : DefFunData) {a : φ.A}
                                        (t : DependentTerm (α := _⌈φ.A⌉) a _⌈φ.B⌉)
                                        (forcePrimitive : Bool) :=
    constructLambdaFunctor (FunctorLambdaAbstraction.construct t) forcePrimitive

    -- This function handles the different cases of functor application in the lambda body,
    -- depending on which parts are either equal to the lambda variable or constant with respect
    -- to it. (We do not optimize the case where both parts are constant, since that should have
    -- been handled already.)

    partial def constructLambdaAppFunctor {φ : DefFunData} (f : FunctorLambdaAbstraction φ)
                                          (funApp : mkHasFunctors.FunApp f.b)
                                          (forcePrimitive : Bool) (requireConstG : Bool) :
                MetaM (Option f.FunDef) := do
      let W := funApp.U
      let WV := funApp.UV
      let _ := funApp.hFun
      let C := funApp.A
      let G : f.Term _⌈C _⟶ φ.B⌉ := ⟨f.n, funApp.hFunApp.F⟩
      let c : f.Term _⌈C⌉        := ⟨f.n, funApp.hFunApp.a⟩
      let e : Option (f.Term _⌈HasFunctors.apply funApp.hFunApp.F funApp.hFunApp.a __≃ f.b⌉) :=
              match funApp.hFunApp.e with
              | some e' => some ⟨f.n, e'⟩
              | none    => none
      match ← G.asConstant? with
      | some (G' : C _⟶ φ.B) => do
        if ← c.isId then
          let G'' : φ.A _⟶ φ.B := G'
          let defAppFun := HasFunctors.defAppFun G''
          return FunctorLambdaAbstraction.FunDef.mkWithEquiv' f defAppFun e
        let UW ← _Universe.mkFreshMVar
        let hFun_UW : mkHasFunctors φ.U W UW ← mkHasFunctors.synthesize
        let hCompFun : mkHasCompFun φ.U W φ.V ← InstanceExpr.synthesize
        let hId_W : mkHasIdentity W ← mkHasIdentity.synthesize
        let F_c ← constructLambdaFunctor' ⟨φ.A, C⟩ c forcePrimitive
        let hCongrArg : mkHasCongrArg W φ.V ← InstanceExpr.synthesize
        let defCompFun := HasCompFun.defCompDefFun (U := φ.U) (V := W) (W := φ.V) F_c.F G'
        FunctorLambdaAbstraction.FunDef.mkWithEquiv' f defCompFun e
      | none => do
        if requireConstG then
          return none
        match ← c.asConstant? with
        | some (c' : C) => do
          if ← G.isId then
            let hFun_VV : mkHasFunctors φ.V φ.V φ.V := { h := φ.hFun.h }
            let hRevAppFun : mkHasRevAppFun φ.V ← InstanceExpr.synthesize
            let defRevAppFun := HasRevAppFun.defRevAppFun (U := φ.V) c' φ.B
            let defRevAppFun' : φ.A _⟶__{λ (G : C _⟶ φ.B) => G c'} φ.B := mkHasFunctors.castDefFun defRevAppFun
            return FunctorLambdaAbstraction.FunDef.mkWithEquiv' f defRevAppFun' e
          let UWV ← _Universe.mkFreshMVar
          let hFun_UWV : mkHasFunctors φ.U WV UWV ← mkHasFunctors.synthesize
          let hSwapFun : mkHasSwapFun φ.U W φ.V ← InstanceExpr.synthesize
          let hId_WV : mkHasIdentity WV ← mkHasIdentity.synthesize
          let F_G ← constructLambdaFunctor' ⟨φ.A, C _⟶ φ.B⟩ G forcePrimitive
          let hCongrFun : mkHasCongrFun W φ.V ← InstanceExpr.synthesize
          let defSwapFun := HasSwapFun.defSwapDefFun (U := φ.U) (V := W) (W := φ.V) F_G.F c'
          FunctorLambdaAbstraction.FunDef.mkWithEquiv' f defSwapFun e
        | none => do
          if ← c.isId then
            let UUV ← _Universe.mkFreshMVar
            let hFun_UUV : mkHasFunctors φ.U φ.UV UUV ← mkHasFunctors.synthesize
            let hDupFun : mkHasDupFun φ.U φ.V ← InstanceExpr.synthesize
            let hId_UV : mkHasIdentity φ.UV ← mkHasIdentity.synthesize
            let G' : f.Term _⌈φ.A _⟶ φ.B⌉ := ⟨G.n, G.b⟩
            let F_G ← constructLambdaFunctor' ⟨φ.A, φ.A _⟶ φ.B⟩ G' forcePrimitive
            let hCongrFun : mkHasCongrFun φ.U φ.V ← InstanceExpr.synthesize
            let defDupFun := HasDupFun.defDupDefFun (U := φ.U) (V := φ.V) F_G.F
            return FunctorLambdaAbstraction.FunDef.mkWithEquiv' f defDupFun e
          let UW ← _Universe.mkFreshMVar
          let hFun_UW : mkHasFunctors φ.U W UW ← mkHasFunctors.synthesize
          let hId_W : mkHasIdentity W ← mkHasIdentity.synthesize
          let F_c ← constructLambdaFunctor' ⟨φ.A, C⟩ c forcePrimitive
          let UWV ← _Universe.mkFreshMVar
          let hFun_UWV : mkHasFunctors φ.U WV UWV ← mkHasFunctors.synthesize
          let hSubstFun : mkHasSubstFun φ.U W φ.V ← InstanceExpr.synthesize
          let hId_WV : mkHasIdentity WV ← mkHasIdentity.synthesize
          let F_G ← constructLambdaFunctor' ⟨φ.A, C _⟶ φ.B⟩ G forcePrimitive
          let hCongrArg : mkHasCongrArg W φ.V ← InstanceExpr.synthesize
          let hCongrFun : mkHasCongrFun W φ.V ← InstanceExpr.synthesize
          let defSubstFun := HasSubstFun.defSubstDefFun (U := φ.U) (V := W) (W := φ.V) F_c.F F_G.F
          FunctorLambdaAbstraction.FunDef.mkWithEquiv' f defSubstFun e

  end

  def byFunctoriality (φ : DefFunData) (f : φ.mkFunArrow) {γ : Type}
                      (k : {f : FunctorLambdaAbstraction φ} → f.FunDef → MetaM γ) : MetaM γ :=
    DependentTerm.fromFunction f (fun t => do
      if t.isMVar then
        -- TODO: Is there a way to show the standard placeholder message at the right place?
        throwError "unfilled placeholder in functor declaration\n{MessageData.ofGoal t.mvarId!}"
      let F ← constructLambdaFunctor' φ t false
      k F)

  -- The `makeFunctor` elaborator, which calls `byFunctoriality` based on the target type and
  -- given term. Note that the target type determines how to elaborate the term, which enables us
  -- to omit the variable type in `Λ` expressions.

  elab "makeFunctor " hf:term:1023 : term <= type => do
    let φ ← FunData.mkFreshMVar
    unless ← isDefEq type _⌈φ.mkFun⌉ do
      throwError "type '{type}' is not an application of 'HasFunctors.Fun'"
    let φ ← φ.instantiate
    let hId : mkHasIdentity φ.V ← mkHasIdentity.synthesize
    let f : φ.mkFunArrow ← TypedExpr.elaborate' hf
    byFunctoriality ⟨φ⟩ f FunctorLambdaAbstraction.FunDef.functor

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

  -- The `functoriality` tactic, which constructs instances of `DefFun`.
  -- Essentially, when asked to construct an instance of `A ⟶{f} B`, it outputs
  -- `(makeFunctor f) ◄ byDef`.

  def functoriality (mvarId : MVarId) : TacticM Expr := do
    let type ← getMVarType mvarId
    let φ ← DefFunData.mkFreshMVar
    let f : φ.mkFunArrow ← TypedExpr.mkFreshMVar
    unless ← isDefEq type (φ.A _⟶{f} φ.B) do
      throwTacticEx `functoriality mvarId m!"type '{type}' is not an application of 'HasFunctors.DefFun'"
    let φ ← φ.instantiate
    let f : φ.mkFunArrow ← f.instantiate
    byFunctoriality φ f FunctorLambdaAbstraction.FunDef.defFun

  elab "functoriality" : tactic => do
    let mvarId ← getMainGoal
    withMVarContext mvarId do
      let e ← functoriality mvarId
      assignExprMVar mvarId e

end Lean.Functoriality
