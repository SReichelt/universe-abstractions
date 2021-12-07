import UniverseAbstractions.Meta.TypedExpr
import UniverseAbstractions.Meta.Helpers
import UniverseAbstractions.Meta.Reflect



set_option autoBoundImplicitLocal false



-- By treating the primite and derived functors as combinators (see
-- https://en.wikipedia.org/wiki/Combinatory_logic), we obtain an algorithm to construct a functor
-- for a given lambda term, i.e. to prove functoriality automatically.
--
-- Below, `t` and `T` denote arbitrary terms of the correct type (which is a functor type in case
-- of `T`).
-- We write `Λ a => b` for the functor obtained for `λ a => b` using this algorithm recursively.
--
--  Functor               | Condition      | Definition
-- -----------------------+----------------+-------------------------------------------------------
--  `Λ a => t`            | `a` not in `t` | `constFun _ t`
--  `Λ a => a`            |                | `idFun _`
--  `Λ a => T a`          | `a` not in `T` | `appFun T`, i.e. just `T`
--  `Λ a => T t`          | `a` not in `T` | `compFun (Λ a => t) T`
--  `Λ F => F t`          | `F` not in `t` | `revAppFun t _`
--  `Λ a => T t`          | `a` not in `t` | `swapFun (Λ a => T) t`
--  `Λ a => T a`          |                | `dupFun (Λ a => T)`
--  `Λ a => T t`          |                | `substFun (Λ a => t) (Λ a => T)`
--  `Λ a => ?Fun t₁...tₙ` |                | `Λ a => (?FunFun t₁...tₙ₋₁) tₙ`
--                        |                | (optimization: use `rev` if it makes `?FunFun` term
--                        |                | constant)
--
-- Although all cases of functor application inside the lambda body can be handled generically by
-- `substFun` (matching SKI combinator calculus), `substFun` requires `FullFunOp`, whereas
-- `compFun`, `revAppFun`, and `swapFun` only require `LinearFunOp` (corresponding to linear logic,
-- where each variable is used exactly once). So the special cases are not merely optimizations.



namespace Lean

  open Meta Elab Tactic
       MetaRelation



  structure FunData where
  {U V UV : _Universe}
  [hFun   : mkHasFunctors U V UV]
  (A      : _⌈U⌉_)
  (B      : _⌈V⌉_)

  namespace FunData

    def mkFreshMVar : MetaM FunData := do
      let U ← _Universe.mkFreshMVar
      let V ← _Universe.mkFreshMVar
      let UV ← _Universe.mkFreshMVar
      let hFun : mkHasFunctors U V UV := { h := ← TypedExpr.mkFreshMVar }
      let A : _⌈U⌉_ ← _Universe.mkFreshTypeMVar
      let B : _⌈V⌉_ ← _Universe.mkFreshTypeMVar
      return ⟨A, B⟩

    def instantiate (φ : FunData) : MetaM FunData := do
      let U ← φ.U.instantiate
      let V ← φ.V.instantiate
      let UV ← φ.UV.instantiate
      let hFun : mkHasFunctors U V UV := { h := ← φ.hFun.h.instantiate }
      let A : _⌈U⌉_ ← _Universe.instantiateTypeMVars φ.A
      let B : _⌈V⌉_ ← _Universe.instantiateTypeMVars φ.B
      return ⟨A, B⟩

    variable (φ : FunData)

    instance : mkHasFunctors φ.U φ.V φ.UV := φ.hFun

    def mkFun      := φ.A _⟶ φ.B
    def mkFunArrow := ⌜$(_⌈φ.A⌉) → $(_⌈φ.B⌉)⌝

  end FunData

  structure DefFunData extends FunData where
  [hId : mkHasIdentity V]

  namespace DefFunData

    def mkFreshMVar : MetaM DefFunData := do
      let φ' ← FunData.mkFreshMVar
      let hId : mkHasIdentity φ'.V := { iu := ← mkFreshLevelMVar, iuv := ← mkFreshLevelMVar, h := { h := ← TypedExpr.mkFreshMVar } }
      return ⟨φ'⟩

    def instantiate (φ : DefFunData) : MetaM DefFunData := do
      let φ' ← φ.toFunData.instantiate
      let hId : mkHasIdentity φ'.V := { iu := ← instantiateLevelMVars φ.hId.iu, iuv := ← instantiateLevelMVars φ.hId.iuv, h := { h := ← φ.hId.h.h.instantiate } }
      return ⟨φ'⟩

    variable (φ : DefFunData)

    instance : mkHasIdentity φ.V := φ.hId

  end DefFunData

  structure FunctorLambdaAbstraction (φ : DefFunData) where
  (n : Name)
  (a : φ.A)
  (b : φ.B)

  namespace FunctorLambdaAbstraction

    def construct {φ : DefFunData} {a : φ.A} (t : DependentTerm (α := _⌈φ.A⌉) a _⌈φ.B⌉) :
      FunctorLambdaAbstraction φ :=
    ⟨t.n, a, t.b⟩

    variable {φ : DefFunData} (f : FunctorLambdaAbstraction φ)

    def Term {w : Level} (γ : ⌜Sort w⌝) := DependentTerm (α := _⌈φ.A⌉) f.a γ
    def term : f.Term _⌈φ.B⌉ := ⟨f.n, f.b⟩
    def fn : φ.mkFunArrow := f.term.toFunction

    structure FunDef where
    (F : φ.A _⟶_{f.fn} φ.B)

    namespace FunDef

      section

        variable {f' : φ.A → φ.B} (F : φ.A _⟶__{f'} φ.B)

        -- `f.b` must be defeq to `f' f.a`.
        def mk' : f.FunDef := ⟨mkHasFunctors.castDefFun F⟩

        -- `b` must be defeq to `f a`.
        def mkWithEquiv' {b : φ.B} (e : Option (f.Term _⌈mkHasInstanceEquivalences._Equiv (A := φ.B) b f.b⌉)) :
          f.FunDef :=
        mk' f (HasFunctors.castDefFun (f' := f.term.apply) F (λ a => match e with
                                                                     | some e' => some (e'.apply a)
                                                                     | none    => none))

        def mkWithEquiv (e : Option (f.Term _⌈mkHasInstanceEquivalences._Equiv (A := φ.B) (f' f.a) f.b⌉)) :
          f.FunDef :=
        mkWithEquiv' f F e
      
      end

      variable (F : f.FunDef)

      def equiv :=
      match F.F.eff f.a with
      | some e => e
      | none   => HasRefl.refl (R := mkHasEquivalenceRelation.reflectR _⌈φ.B⌉ (mkHasIdentity.univ φ.V)) f.b

      def functor : MetaM φ.mkFun := do
        let f' := f.fn
        if !(f.b.isAppOf ``HasFunctors.castFun) then
          match F.F.eff f.a with
          | some e => do
            -- Optimization: remove unnecessary `toDefFun' (fromDefFun ...) byDef`.
            -- In contrast to `defFun` below, here we need to make sure that the result is treated
            -- the same by the elaborator.
            let F' : φ.A _⟶{f'} φ.B ← TypedExpr.mkFreshMVar
            if ← isDefEq e (mkHasFunctors.mkByDef F' f.a) then
              let F'' := mkHasFunctors.mkFromDefFun (← F'.instantiate)
              -- Return the original term `F.F.F` if it is reducibly defeq, as it easier to read.
              if ← (withReducible (isDefEq F.F.F F'')) then
                return F.F.F
              return F''
          | none =>
            return mkHasFunctors.mkAppFun F.F.F
        let e' := FVar.abstractLambda' (α := _⌈φ.A⌉) f.a f.n F.equiv
        mkHasFunctors.mkCastFun' φ.hFun.h φ.hId.h.h φ.A φ.B F.F.F f' e'

      def defFun : MetaM (φ.A _⟶{f.fn} φ.B) :=
      match F.F.eff f.a with
      | some e => do
        let f' := f.fn
        -- Optimization: remove unnecessary `toDefFun' (fromDefFun ...) byDef`.
        let F' : φ.A _⟶{f'} φ.B ← TypedExpr.mkFreshMVar
        if ← isDefEq e (mkHasFunctors.mkByDef F' f.a) then
          return ← F'.instantiate
        let e' := FVar.abstractLambda' (α := _⌈φ.A⌉) f.a f.n e
        mkHasFunctors.mkToDefFun'' φ.hFun.h φ.hId.h.h φ.A φ.B F.F.F f' e'
      | none =>
        mkHasFunctors.mkDefAppFun F.F.F

    end FunDef

  end FunctorLambdaAbstraction



  mutual

    -- The main entry point, which handles `constFun` and `idFun` directly, and calls
    -- `constructLambdaAppFunctor` to deal with a lambda application.

    partial def constructLambdaFunctor (φ : DefFunData) (f : FunctorLambdaAbstraction φ) :
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
        let W ← _Universe.mkFreshMVar
        let WV ← _Universe.mkFreshMVar
        let hFun_WV : mkHasFunctors W φ.V WV := { h := ← TypedExpr.mkFreshMVar }
        let C : _⌈W⌉_ ← _Universe.mkFreshTypeMVar (U := W)
        let hFunApp : mkHasFunctors.mkIsFunApp C f.b ← mkHasFunctors.mkIsFunApp.synthesize
        let W ← W.instantiate
        let WV ← WV.instantiate
        let hFun_WV : mkHasFunctors W φ.V WV := { h := ← hFun_WV.h.instantiate }
        let C : _⌈W⌉_ ← C.instantiate
        let hFunApp : mkHasFunctors.mkIsFunApp C f.b := { h := ← hFunApp.h.instantiate }
        constructLambdaAppFunctor φ f C

    -- This function handles the different cases of functor application in the lambda body,
    -- depending on which parts are either equal to the lambda variable or constant with respect
    -- to it. (We do not optimize the case where both parts are constant, since that should have
    -- been handled already.)

    partial def constructLambdaAppFunctor (φ : DefFunData) (f : FunctorLambdaAbstraction φ)
                                          {W WV : _Universe} [hFun_WV : mkHasFunctors W φ.V WV]
                                          (C : _⌈W⌉_) [hFunApp : mkHasFunctors.mkIsFunApp C f.b] :
                MetaM f.FunDef := do
      let hApp : HasFunctors.IsFunApp (U := W) (V := φ.V) C f.b ← mkHasFunctors.mkIsFunApp.reflect C f.b
      let G : f.Term _⌈C _⟶ φ.B⌉ := ⟨f.n, hApp.F⟩
      let c : f.Term _⌈C⌉        := ⟨f.n, hApp.a⟩
      let e : Option (f.Term _⌈HasFunctors.apply hApp.F hApp.a _≃ f.b⌉) := match hApp.e with
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
        let hCompFun : mkHasCompFun φ.U W φ.V ← ClassExpr.synthesize
        let hId_W : mkHasIdentity W ← mkHasIdentity.synthesize
        let F_c ← constructLambdaFunctor ⟨φ.A, C⟩ (FunctorLambdaAbstraction.construct c)
        let hCongrArg : mkHasCongrArg W φ.V ← ClassExpr.synthesize
        let defCompFun := HasCompFun.defCompDefFun (U := φ.U) (V := W) (W := φ.V) F_c.F G'
        FunctorLambdaAbstraction.FunDef.mkWithEquiv' f defCompFun e
      | none => do
        match ← c.asConstant? with
        | some (c' : C) => do
          if ← G.isId then
            let hFun_VV : mkHasFunctors φ.V φ.V φ.V := { h := φ.hFun.h }
            let hRevAppFun : mkHasRevAppFun φ.V ← ClassExpr.synthesize
            let defRevAppFun := HasRevAppFun.defRevAppFun (U := φ.V) c' φ.B
            let defRevAppFun' : φ.A _⟶__{λ (G : C _⟶ φ.B) => G c'} φ.B := mkHasFunctors.castDefFun defRevAppFun
            return FunctorLambdaAbstraction.FunDef.mkWithEquiv' f defRevAppFun' e
          let UWV ← _Universe.mkFreshMVar
          let hFun_UWV : mkHasFunctors φ.U WV UWV ← mkHasFunctors.synthesize
          let hSwapFun : mkHasSwapFun φ.U W φ.V ← ClassExpr.synthesize
          let hId_WV : mkHasIdentity WV ← mkHasIdentity.synthesize
          let F_G ← constructLambdaFunctor ⟨φ.A, C _⟶ φ.B⟩ (FunctorLambdaAbstraction.construct G)
          let hCongrFun : mkHasCongrFun W φ.V ← ClassExpr.synthesize
          let defSwapFun := HasSwapFun.defSwapDefFun (U := φ.U) (V := W) (W := φ.V) F_G.F c'
          FunctorLambdaAbstraction.FunDef.mkWithEquiv' f defSwapFun e
        | none => do
          if ← c.isId then
            let UUV ← _Universe.mkFreshMVar
            let hFun_UUV : mkHasFunctors φ.U φ.UV UUV ← mkHasFunctors.synthesize
            let hDupFun : mkHasDupFun φ.U φ.V ← ClassExpr.synthesize
            let hId_UV : mkHasIdentity φ.UV ← mkHasIdentity.synthesize
            let G' : f.Term _⌈φ.A _⟶ φ.B⌉ := ⟨G.n, G.b⟩
            let F_G ← constructLambdaFunctor ⟨φ.A, φ.A _⟶ φ.B⟩ (FunctorLambdaAbstraction.construct G')
            let hCongrFun : mkHasCongrFun φ.U φ.V ← ClassExpr.synthesize
            let defDupFun := HasDupFun.defDupDefFun (U := φ.U) (V := φ.V) F_G.F
            return FunctorLambdaAbstraction.FunDef.mkWithEquiv' f defDupFun e
          let UW ← _Universe.mkFreshMVar
          let hFun_UW : mkHasFunctors φ.U W UW ← mkHasFunctors.synthesize
          let hId_W : mkHasIdentity W ← mkHasIdentity.synthesize
          let F_c ← constructLambdaFunctor ⟨φ.A, C⟩ (FunctorLambdaAbstraction.construct c)
          let UWV ← _Universe.mkFreshMVar
          let hFun_UWV : mkHasFunctors φ.U WV UWV ← mkHasFunctors.synthesize
          let hSubstFun : mkHasSubstFun φ.U W φ.V ← ClassExpr.synthesize
          let hId_WV : mkHasIdentity WV ← mkHasIdentity.synthesize
          let F_G ← constructLambdaFunctor ⟨φ.A, C _⟶ φ.B⟩ (FunctorLambdaAbstraction.construct G)
          let hCongrArg : mkHasCongrArg W φ.V ← ClassExpr.synthesize
          let hCongrFun : mkHasCongrFun W φ.V ← ClassExpr.synthesize
          let defSubstFun := HasSubstFun.defSubstDefFun (U := φ.U) (V := W) (W := φ.V) F_c.F F_G.F
          FunctorLambdaAbstraction.FunDef.mkWithEquiv' f defSubstFun e

  end

  def constructFunctor (φ : DefFunData) (f : φ.mkFunArrow) : MetaM φ.mkFun := do
    DependentTerm.fromFunction f (fun a b => do
      let F ← constructLambdaFunctor φ (FunctorLambdaAbstraction.construct b)
      F.functor)

  def constructDefFun (φ : DefFunData) (f : φ.mkFunArrow) : MetaM (φ.A _⟶{f} φ.B) :=
    DependentTerm.fromFunction f (fun a b => do
      let F ← constructLambdaFunctor φ (FunctorLambdaAbstraction.construct b)
      F.defFun)

  -- The `makeFunctor` tactic, which calls `constructFunctor` based on the target type and given
  -- term. Note that the target type determines how to elaborate the term, which enables us to omit
  -- the variable type in `Λ` expressions.

  def makeFunctor (mvarId : MVarId) (hf : Syntax) : TacticM Expr := do
    let type ← getMVarType mvarId
    let φ ← FunData.mkFreshMVar
    if ← isDefEq type _⌈φ.mkFun⌉ then
      let φ ← φ.instantiate
      let hId : mkHasIdentity φ.V ← mkHasIdentity.synthesize
      let f : φ.mkFunArrow ← TypedExpr.elaborate hf
      return ← constructFunctor ⟨φ⟩ f
    throwTacticEx `makeFunctor mvarId m!"type '{type}' is not an application of 'HasFunctors.Fun'"

  elab "makeFunctor " hf:term : tactic => do
    let mvarId ← getMainGoal
    withMVarContext mvarId do
      let e ← makeFunctor mvarId hf
      assignExprMVar mvarId e

  -- Implementation of the `Λ` notation.
  -- We want `Λ a b ... => t` to be a shortcut for:
  -- `by makeFunctor (λ a => by makeFunctor (λ b => ... t))`.
  -- However, `expandExplicitBinders` only accepts a name, so as a hack, we currently pass it a
  -- dummy name `__mkFun` and then recursively replace the corresponding syntax nodes in the
  -- result.

  partial def replaceMkFun : Syntax → MacroM Syntax
    | `(__mkFun $f) => do
      let f ← replaceMkFun f
      `(by makeFunctor $f)
    | f => match f with
           | Syntax.node info kind args => do
             let args ← args.sequenceMap replaceMkFun
             Syntax.node info kind args
           | f => f

  macro "Λ" xs:explicitBinders " => " b:term : term => do
    let f ← expandExplicitBinders `__mkFun xs b
    replaceMkFun f

  -- The `functoriality` tactic, which constructs instances of `DefFun`.
  -- Essentially, when asked to construct an instance of `A ⟶{f} B`, it outputs
  -- `(by makeFunctor f) ◄ byDef`.

  def functoriality (mvarId : MVarId) : TacticM Expr := do
    let type ← getMVarType mvarId
    let φ ← DefFunData.mkFreshMVar
    let f : φ.mkFunArrow ← TypedExpr.mkFreshMVar
    if ← isDefEq type (φ.A _⟶{f} φ.B) then
      let φ ← φ.instantiate
      let f : φ.mkFunArrow ← f.instantiate
      return ← constructDefFun φ f
    throwTacticEx `functoriality mvarId m!"type '{type}' is not an application of 'HasFunctors.DefFun'"

  elab "functoriality" : tactic => do
    let mvarId ← getMainGoal
    withMVarContext mvarId do
      let e ← functoriality mvarId
      assignExprMVar mvarId e

end Lean
