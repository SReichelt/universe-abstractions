import UniverseAbstractions.Meta.TypedExpr
import UniverseAbstractions.Meta.Helpers
import UniverseAbstractions.Meta.Reflect



set_option autoBoundImplicitLocal false



namespace Lean

  open Meta Elab Tactic



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
      let hFun : mkHasFunctors U V UV ← mkHasFunctors.mkFreshMVar
      let A : _⌈U⌉_ ← _Universe.mkFreshTypeMVar
      let B : _⌈V⌉_ ← _Universe.mkFreshTypeMVar
      pure ⟨A, B⟩

    def instantiate (φ : FunData) : MetaM FunData := do
      let U ← φ.U.instantiate
      let V ← φ.V.instantiate
      -- Hack: Unfortunately, we cannot just instantiate `hFun` but need to synthesize it now that
      -- we know `U` and `V`. Otherwise, the definitions in `CombinatorExtensionality.lean` fail.
      -- FIXME: There is probably a better way to do this.
      let hFun : mkHasFunctors U V φ.UV ← mkHasFunctors.synthesize
      let UV ← φ.UV.instantiate
      let A : _⌈U⌉_ ← _Universe.instantiateTypeMVars φ.A
      let B : _⌈V⌉_ ← _Universe.instantiateTypeMVars φ.B
      pure ⟨A, B⟩

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
      let hId : mkHasIdentity φ'.V ← mkHasIdentity.mkFreshMVar
      pure ⟨φ'⟩

    def instantiate (φ : DefFunData) : MetaM DefFunData := do
      let φ' ← φ.toFunData.instantiate
      let hId : mkHasIdentity φ'.V ← φ.hId.instantiate
      pure ⟨φ'⟩

    variable (φ : DefFunData)

    instance : mkHasIdentity φ.V := φ.hId

  end DefFunData


  structure FunEquivData where
  {U    : _Universe}
  [hId  : mkHasIdentity U]
  [hFun : mkHasInternalFunctors U]
  (A B  : _⌈U⌉_)
  
  namespace FunEquivData

    def mkFreshMVar : MetaM FunEquivData := do
      let U ← _Universe.mkFreshMVar
      let hId : mkHasIdentity U ← mkHasIdentity.mkFreshMVar
      let hFun : mkHasInternalFunctors U ← InstanceExpr.mkFreshMVar
      let A : _⌈U⌉_ ← _Universe.mkFreshTypeMVar
      let B : _⌈U⌉_ ← _Universe.mkFreshTypeMVar
      pure ⟨A, B⟩

    def instantiate (φ : FunEquivData) : MetaM FunEquivData := do
      let U ← φ.U.instantiate
      let hId : mkHasIdentity U ← φ.hId.instantiate
      let hFun : mkHasInternalFunctors U ← φ.hFun.instantiate
      let A : _⌈U⌉_ ← _Universe.instantiateTypeMVars φ.A
      let B : _⌈U⌉_ ← _Universe.instantiateTypeMVars φ.B
      pure ⟨A, B⟩

    variable (φ : FunEquivData)

    instance : mkHasIdentity φ.U := φ.hId
    instance : mkHasInternalFunctors φ.U := φ.hFun

    def toDefFunData : DefFunData := ⟨⟨φ.A, φ.B⟩⟩

    def mkFun      := φ.A _⟶ φ.B
    def mkFunArrow := ⌜$(_⌈φ.A⌉) → $(_⌈φ.B⌉)⌝

  end FunEquivData



  structure FunctorLambdaAbstraction (φ : DefFunData) where
  (n : Name)
  (a : φ.A)
  (b : φ.B)

  namespace FunctorLambdaAbstraction

    variable {φ : DefFunData}

    def construct {a : φ.A} (t : DependentTerm (α := _⌈φ.A⌉) a _⌈φ.B⌉) :
      FunctorLambdaAbstraction φ :=
    ⟨t.n, a, t.b⟩

    section

      variable (f : FunctorLambdaAbstraction φ)

      def a' : FVar _⌈φ.A⌉ := f.a
      def Term {w : Level} (γ : ⌜Sort w⌝) := DependentTerm f.a' γ
      def term : f.Term _⌈φ.B⌉ := ⟨f.n, f.b⟩
      def fn : φ.mkFunArrow := f.term.toFunction

    end

    structure FunDef (f : FunctorLambdaAbstraction φ) where
    (F : φ.A _⟶_{f.fn} φ.B)

    namespace FunDef

      section

        variable (f : FunctorLambdaAbstraction φ) {f' : φ.A → φ.B} (F : φ.A _⟶__{f'} φ.B)

        -- `f.b` must be defeq to `f' f.a`.
        def mk' : f.FunDef := ⟨mkHasFunctors.castDefFun F⟩

        -- `b` must be defeq to `f a`.
        def mkWithEquiv' {b : φ.B} (e : Option (f.Term _⌈mkHasInstanceEquivalences._Equiv' (A := φ.B) b f.b⌉)) :
          f.FunDef :=
        mk' f (HasFunctors.castDefFun (f' := f.term.apply) F (λ a => match e with
                                                                     | some e' => some (e'.apply a)
                                                                     | none    => none))

        def mkWithEquiv (e : Option (f.Term _⌈mkHasInstanceEquivalences._Equiv' (A := φ.B) (f' f.a) f.b⌉)) :
          f.FunDef :=
        mkWithEquiv' f F e
      
      end

      variable {f : FunctorLambdaAbstraction φ} (F : f.FunDef)

      def rawFunctor : φ.mkFun := F.F.F

      def functor : MetaM φ.mkFun := do
        let f' := f.fn
        let e := F.F.eff f.a
        if !(f.b.isAppOf ``HasFunctors.castFun) then
          match e with
          | some e' => do
            -- Optimization: remove unnecessary `toDefFun' (fromDefFun ...) byDef`.
            -- In contrast to `defFun` below, here we need to make sure that the result is treated
            -- the same by the elaborator.
            let F' : φ.A _⟶{f'} φ.B ← TypedExpr.mkFreshMVar
            if ← isDefEq e' (mkHasFunctors.mkByDef F' f.a) then
              let F' : φ.A _⟶{f'} φ.B ← F'.instantiate
              let F'' := mkHasFunctors.mkFromDefFun F'
              -- Return the original term `F.F.F` if it is reducibly defeq, as it is easier to read.
              if ← (withReducible (isDefEq F.F.F F'')) then
                return F.F.F
              return F''
          | none =>
            return mkHasFunctors.mkAppFun F.F.F
        let e' := mkHasInstanceEquivalences.materialize e
        let h := f.a'.abstractLambda' f.n e'
        mkHasFunctors.mkCastFun' φ.hFun.h φ.hId.h.h φ.A φ.B F.F.F f' h

      def defFun : MetaM (φ.A _⟶{f.fn} φ.B) :=
      let e := F.F.eff f.a
      match e with
      | some e' => do
        let f' := f.fn
        -- Optimization: remove unnecessary `toDefFun' (fromDefFun ...) byDef`.
        let F' : φ.A _⟶{f'} φ.B ← TypedExpr.mkFreshMVar
        if ← isDefEq e' (mkHasFunctors.mkByDef F' f.a) then
          return ← F'.instantiate
        let h := f.a'.abstractLambda' f.n e'
        mkHasFunctors.mkToDefFun'' φ.hFun.h φ.hId.h.h φ.A φ.B F.F.F f' h
      | none =>
        mkHasFunctors.mkDefAppFun F.F.F

    end FunDef

  end FunctorLambdaAbstraction


  structure FunEquivLambdaAbstraction (φ : FunEquivData) where
  (n     : Name)
  (a     : φ.A)
  (b₁ b₂ : φ.B)
  (e     : b₁ _≃ b₂)

  namespace FunEquivLambdaAbstraction

    variable {φ : FunEquivData}

    def EquivTypeTerm {a : φ.A} (t₁ t₂ : DependentTerm (α := _⌈φ.A⌉) a _⌈φ.B⌉) :
      DependentTerm (α := _⌈φ.A⌉) a (mkHasIdentity.univ φ.U).LeanUniv :=
    ⟨t₁.n, _⌈mkHasInstanceEquivalences._Equiv (A := φ.B) t₁.b t₂.b⌉⟩

    def construct {a : φ.A} (t₁ t₂ : DependentTerm (α := _⌈φ.A⌉) a _⌈φ.B⌉)
                  (t : DependentlyTypedTerm (EquivTypeTerm t₁ t₂)) :
      FunEquivLambdaAbstraction φ :=
    ⟨t.b.n, a, t₁.b, t₂.b, t.b.b⟩

    section

      variable (h : FunEquivLambdaAbstraction φ)

      def a' : FVar _⌈φ.A⌉ := h.a

      def f₁ : FunctorLambdaAbstraction φ.toDefFunData := ⟨h.n, h.a, h.b₁⟩
      def f₂ : FunctorLambdaAbstraction φ.toDefFunData := ⟨h.n, h.a, h.b₂⟩

      def term : DependentlyTypedTerm (EquivTypeTerm h.f₁.term h.f₂.term) := ⟨⟨h.n, h.e⟩⟩
      def fn := h.term.toFunction

    end

  end FunEquivLambdaAbstraction

end Lean
