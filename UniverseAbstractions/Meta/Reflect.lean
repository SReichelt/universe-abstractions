import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.MetaRelations
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.FunctorExtensionality
import UniverseAbstractions.Meta.TypedExpr
import UniverseAbstractions.Meta.Helpers



set_option autoBoundImplicitLocal false
set_option synthInstance.maxHeartbeats 2000



namespace Lean

  open Meta Elab Tactic Qq
       Universe MetaRelation



  structure _Sort where
  {u : Level}
  (α : ⌜Sort u⌝)

  def exprUniverse {β : Type} (inst : β → _Sort) : Universe :=
  { a    := β,
    inst := ⟨λ b => (inst b).α⟩ }



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

    def mkEq {u : Level} {α : ⌜Sort u⌝} (a b : α) : ⌜Prop⌝ := ⌜$a = $b⌝

    def _Eq {A : _sort} (a b : A) : _sort := ⟨mkEq (α := A.α) a b⟩

    instance _Eq.isEquivalence (A : _sort) : IsEquivalence (@_Eq A) :=
    { refl  := λ (a     : A.α)                               => ⌜Eq.refl  $a⌝,
      symm  := λ {a b   : A.α} (h : mkEq a b)                => ⌜Eq.symm  $h⌝,
      trans := λ {a b c : A.α} (h : mkEq a b) (i : mkEq b c) => ⌜Eq.trans $h $i⌝ }

    -- `none` signals that `a` and `b` are defeq. This easily lets us propagate definitional
    -- equivalence to avoid unnecessarily complicated proof terms.
    def _Eq' (A : _sort) := optionalRelation (@_Eq A)

    instance _Eq'.isEquivalence (A : _sort) : IsEquivalence (_Eq' A) :=
    optionalRelation.isEquivalence (@_Eq A)

    instance hasEquality (A : _sort) : HasEquivalenceRelation A type := ⟨_Eq' A⟩

    instance hasInstanceEquivalences : HasInstanceEquivalences _sort type := ⟨hasEquality⟩

    -- Returns an instance of `a ≃ b` if `a` and `b` are defeq, `none` otherwise.
    def checkDefEq {A : _sort} (a b : A) : MetaM (Option (a ≃ b)) := do
      if ← isDefEq a b then
        return some none
      none

    def mkFun {u v : Level} (α : ⌜Sort u⌝) (β : ⌜Sort v⌝) : ⌜Sort (imax u v)⌝ := ⌜$α → $β⌝
    def mkApp {u v : Level} {α : ⌜Sort u⌝} {β : ⌜Sort v⌝} (f : mkFun α β) (a : α) : β := ⌜$f $a⌝

    instance hasFunctors : HasFunctors _sort _sort _sort :=
    { Fun   := λ A B => ⟨mkFun A.α B.α⟩,
      apply := λ {A B} (f : mkFun A.α B.α) (a : A.α) => mkApp f a }

    -- When using this, make sure that `f` is defeq to what `f'` specifies.
    def defFun {A B : _sort} {f' : A → B} (f : mkFun A.α B.α) : A ⟶{f'} B :=
    { F   := f,
      eff := λ _ => none }

    def defFun₂ {A B C : _sort} {f' : A → B → C} (f : mkFun A.α (mkFun B.α C.α)) : A ⟶ B ⟶{f'} C :=
    ⟨λ a => defFun (mkApp f a), defFun f⟩

    def defFun₃ {A B C D : _sort} {f' : A → B → C → D} (f : mkFun A.α (mkFun B.α (mkFun C.α D.α))) :
      A ⟶ B ⟶ C ⟶{f'} D :=
    ⟨λ a => defFun₂ (mkApp f a), defFun f⟩

    instance hasCongrArg : HasCongrArg _sort _sort :=
    ⟨λ A B (f : mkFun A.α B.α) {a₁ a₂ : A.α} h => match h with
     | some (h' : mkEq a₁ a₂) => some ⌜congrArg $f $h'⌝
     | none                   => none⟩

    instance hasCongrFun : HasCongrFun _sort _sort :=
    ⟨λ A B {f₁ f₂ : mkFun A.α B.α} h (a : A.α) => match h with
     | some (h' : mkEq f₁ f₂) => some ⌜congrFun $h' $a⌝
     | none                   => none⟩

    instance hasInternalFunctors : HasInternalFunctors _sort := ⟨⟩

    instance hasLinearFunOp : HasLinearFunOp _sort :=
    { defIdFun     := λ _     => defFun  ⌜id⌝,
      defRevAppFun := λ _ _   => defFun₂ ⌜λ a f => f a⌝,
      defCompFun   := λ _ _ _ => defFun₃ ⌜λ f g => g ∘ f⌝ }

    instance hasAffineFunOp : HasAffineFunOp _sort :=
    { defConstFun := λ _ _ => defFun₂ ⌜Function.const _⌝ }

    instance hasFullFunOp : HasFullFunOp _sort :=
    { defDupFun := λ _ _ => defFun₂ ⌜λ f a => f a a⌝ }

  end _sort



  -- The remaining code reflects all object-level classes and structures as instances of
  -- themselves. E.g. `mkHasInstances` is the quoted version of `HasInstances`, and its
  -- `instance reflect` constructs a meta-level instance of `HasInstances` itself.



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
    def instantiateInstMVars {U : _Universe} {A A' : _⌈U⌉_} : A → MetaM A' := TypedExpr.instantiate (α := _⌈A⌉) (α' := _⌈A'⌉)

    @[reducible] def FVar {U : _Universe} (A : _⌈U⌉_) := Lean.FVar _⌈A⌉

  end _Universe



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



  def mkHasEquivalenceRelation {u : Level} (α : ⌜Sort u⌝) (V : _Universe) : ClassExpr :=
  ⟨⌜HasEquivalenceRelation $α $V.U⌝⟩

  namespace mkHasEquivalenceRelation

    variable {u : Level} (α : ⌜Sort u⌝) (V : _Universe) [h : mkHasEquivalenceRelation α V]

    def mkR : _MetaRelation α V :=
    let _ := h.h
    ⌜HasEquivalenceRelation.R⌝

    instance : _MetaRelation.mkIsEquivalence (mkR α V) :=
    let _ := h.h
    ⟨⌜HasEquivalenceRelation.h⌝⟩

    def reflectR : MetaRelation α V := _MetaRelation.reflect (mkR α V)

    instance isEquivalence : IsEquivalence (reflectR α V) :=
    _MetaRelation.mkIsEquivalence.reflect (mkR α V)

    instance reflect : HasEquivalenceRelation α type := ⟨optionalRelation (reflectR α V)⟩

  end mkHasEquivalenceRelation



  def mkHasInstanceEquivalences' (U IU : _Universe) : ClassExpr :=
  ⟨⌜HasInstanceEquivalences $U.U $IU.U⌝⟩

  class mkHasInstanceEquivalences (U : _Universe) (IU : outParam _Universe) extends
  mkHasInstanceEquivalences' U IU

  namespace mkHasInstanceEquivalences

    variable {U IU : _Universe} [h : mkHasInstanceEquivalences U IU]

    def mkHasEq (A : _⌈U⌉_) :=
    let h' := h.h
    ⌜($h').hasEq $A⌝

    instance (A : _⌈U⌉_) : mkHasEquivalenceRelation _⌈A⌉ IU := ⟨mkHasEq A⟩

    def _Rel (A : _⌈U⌉_) : MetaRelation ⌈A⌉ IU := mkHasEquivalenceRelation.reflectR _⌈A⌉ IU

    def _Equiv' {A : _⌈U⌉_} (a b : A) : _⌈IU⌉_ := (_Rel A) a b
    infix:25 " __≃ " => mkHasInstanceEquivalences._Equiv'

    @[reducible] def _Equiv {A : _⌈U⌉_} (a b : A) := (_Rel A) a b
    infix:25 " _≃ " => mkHasInstanceEquivalences._Equiv

    instance (A : _⌈U⌉_) : IsEquivalence (_Rel A) := mkHasEquivalenceRelation.isEquivalence _⌈A⌉ IU

    instance hasEquivalenceRelation (A : _⌈U⌉_) : HasEquivalenceRelation A type :=
    mkHasEquivalenceRelation.reflect _⌈A⌉ IU

    instance reflect : HasInstanceEquivalences U type := ⟨hasEquivalenceRelation⟩

    @[reducible] def __Equiv {A : _⌈U⌉_} (a b : A) : type := a ≃ b
    infix:25 " _≃_ " => mkHasInstanceEquivalences.__Equiv

    def materialize {A : _⌈U⌉_} {a b : A} : a _≃_ b → a _≃ b :=
    optionalRelation.materialize (_Rel A)

  end mkHasInstanceEquivalences



  def mkHasIdentity'' {u v : Level} (U : ⌜Universe.{u, v}⌝) (iu iuv : Level) :=
  ⌜HasIdentity.{u, iu, v, iuv} $U⌝

  def mkHasIdentity' (U : _Universe) (iu iuv : Level) : ClassExpr :=
  ⟨mkHasIdentity'' U.U iu iuv⟩

  class mkHasIdentity (U : _Universe) where
  (iu iuv : Level)
  [h      : mkHasIdentity' U iu iuv]

  namespace mkHasIdentity

    def mkFreshMVar {U : _Universe} : MetaM (mkHasIdentity U) := do
      pure { iu  := ← mkFreshLevelMVar,
             iuv := ← mkFreshLevelMVar,
             h   := ← InstanceExpr.mkFreshMVar }

    def instantiate {U U' : _Universe} (h : mkHasIdentity U) : MetaM (mkHasIdentity U') := do
      pure { iu  := ← instantiateLevelMVars h.iu,
             iuv := ← instantiateLevelMVars h.iuv,
             h   := ← h.h.instantiate }

    def synthesize {U : _Universe} : MetaM (mkHasIdentity U) := do
      pure { iu  := ← mkFreshLevelMVar,
             iuv := ← mkFreshLevelMVar,
             h   := ← InstanceExpr.synthesize }

    variable (U : _Universe) [h : mkHasIdentity U]

    def mkIU :=
    let h' := h.h.h
    ⌜($h').IU⌝
  
    def univ : _Universe := ⟨mkIU U⟩

    def mkHasInstEquiv :=
    let h' := h.h.h
    ⌜($h').hasInstanceEquivalences⌝

    instance : mkHasInstanceEquivalences U (univ U) := { h := mkHasInstEquiv U }

    instance reflect : HasIdentity U := ⟨⟩

  end mkHasIdentity



  def mkHasFunctors'' {u_U v_U u_V v_V u_UV v_UV : Level} (U : ⌜Universe.{u_U, v_U}⌝)
                      (V : ⌜Universe.{u_V, v_V}⌝) (UV : ⌜Universe.{u_UV, v_UV}⌝) :=
  ⌜HasFunctors $U $V $UV⌝

  def mkHasFunctors' (U V UV : _Universe) : ClassExpr :=
  ⟨mkHasFunctors'' U.U V.U UV.U⟩

  class mkHasFunctors (U V : _Universe) (UV : outParam _Universe) extends
  mkHasFunctors' U V UV

  namespace mkHasFunctors

    def mkFreshMVar {U V UV : _Universe} : MetaM (mkHasFunctors U V UV) := do
      pure { toInstanceExpr := ← InstanceExpr.mkFreshMVar }

    def instantiate {U U' V V' UV UV' : _Universe} (h : mkHasFunctors U V UV) :
        MetaM (mkHasFunctors U' V' UV') := do
      pure { toInstanceExpr := ← h.toInstanceExpr.instantiate }

    def synthesize {U V UV : _Universe} : MetaM (mkHasFunctors U V UV) := do
      pure { toInstanceExpr := ← InstanceExpr.synthesize }

    @[reducible] def mkArrowInst {u_U v_U u_V v_V u_UV v_UV : Level} {U : ⌜Universe.{u_U, v_U}⌝}
                                 {V : ⌜Universe.{u_V, v_V}⌝} {UV : ⌜Universe.{u_UV, v_UV}⌝}
                                 (h : mkHasFunctors'' U V UV) (A : Q($U)) (B : Q($V)) :=
    Q($A → $B)

    def mkArrowApp' {u_U v_U u_V v_V u_UV v_UV : Level} {U : ⌜Universe.{u_U, v_U}⌝}
                    {V : ⌜Universe.{u_V, v_V}⌝} {UV : ⌜Universe.{u_UV, v_UV}⌝}
                    (h : mkHasFunctors'' U V UV) (A : Q($U)) (B : Q($V)) (f : Q($A → $B))
                    (a : Q($A)) : Q($B) :=
    ⌜$f $a⌝

    def mkFun {u_U v_U u_V v_V u_UV v_UV : Level} {U : ⌜Universe.{u_U, v_U}⌝}
              {V : ⌜Universe.{u_V, v_V}⌝} {UV : ⌜Universe.{u_UV, v_UV}⌝}
              (h : mkHasFunctors'' U V UV) (A : Q($U)) (B : Q($V)) : Q($UV) :=
    ⌜$A ⟶ $B⌝

    @[reducible] def mkFunInst {u_U v_U u_V v_V u_UV v_UV : Level} {U : ⌜Universe.{u_U, v_U}⌝}
                               {V : ⌜Universe.{u_V, v_V}⌝} {UV : ⌜Universe.{u_UV, v_UV}⌝}
                               (h : mkHasFunctors'' U V UV) (A : Q($U)) (B : Q($V)) :=
    Q($A ⟶ $B)

    def mkApplyFn' {u_U v_U u_V v_V u_UV v_UV : Level} {U : ⌜Universe.{u_U, v_U}⌝}
                   {V : ⌜Universe.{u_V, v_V}⌝} {UV : ⌜Universe.{u_UV, v_UV}⌝}
                   (h : mkHasFunctors'' U V UV) (A : Q($U)) (B : Q($V))
                   (F : Q($A ⟶ $B)) : Q($A → $B) :=
    ⌜HasFunctors.apply $F⌝

    def mkApply {u_U v_U u_V v_V u_UV v_UV : Level} {U : ⌜Universe.{u_U, v_U}⌝}
                {V : ⌜Universe.{u_V, v_V}⌝} {UV : ⌜Universe.{u_UV, v_UV}⌝}
                (h : mkHasFunctors'' U V UV) (A : Q($U)) (B : Q($V))
                (F : Q($A ⟶ $B)) (a : Q($A)) : Q($B) :=
    ⌜$F $a⌝

    def mkToDefFun'' {u_U v_U u_V v_V u_UV v_UV iv ivv : Level} {U : ⌜Universe.{u_U, v_U}⌝}
                     {V : ⌜Universe.{u_V, v_V}⌝} {UV : ⌜Universe.{u_UV, v_UV}⌝}
                     (hFun : mkHasFunctors'' U V UV) (hId_V : mkHasIdentity'' V iv ivv)
                     (A : Q($U)) (B : Q($V)) (F : Q($A ⟶ $B)) (f : Q($A → $B))
                     (h : Q(∀ a, $F a ≃ $f a)) : Q($A ⟶{$f} $B) :=
    ⌜HasFunctors.toDefFun' $F $h⌝

    def mkCastFun' {u_U v_U u_V v_V u_UV v_UV iv ivv : Level} {U : ⌜Universe.{u_U, v_U}⌝}
                   {V : ⌜Universe.{u_V, v_V}⌝} {UV : ⌜Universe.{u_UV, v_UV}⌝}
                   (hFun : mkHasFunctors'' U V UV) (hId_V : mkHasIdentity'' V iv ivv)
                   (A : Q($U)) (B : Q($V)) (F : Q($A ⟶ $B)) (f : Q($A → $B))
                   (h : Q(∀ a, $F a ≃ $f a)) : Q($A ⟶ $B) :=
    ⌜HasFunctors.castFun $F $f $h⌝

    section

      variable {U V UV : _Universe} [h : mkHasFunctors U V UV]

      def mkArrowApp (A : _⌈U⌉_) (B : _⌈V⌉_) (f : ⌜$A → $B⌝) (a : A) : B :=
      mkArrowApp' h.h A B f a

      instance reflect : HasFunctors U V UV :=
      { Fun   := mkFun h.h,
        apply := λ {A B} => mkApply h.h A B }

      @[reducible] def _Fun (A : _⌈U⌉_) (B : _⌈V⌉_) : _⌈UV⌉_ := HasFunctors.Fun (U := U) (V := V) A B
      infixr:20 " _⟶ " => mkHasFunctors._Fun

      instance (A : _⌈U⌉_) (B : _⌈V⌉_) : CoeFun (A _⟶ B) (λ _ => A → B) :=
      HasFunctors.coeFun (U := U) (V := V) A B

      def mkApplyFn {A : _⌈U⌉_} {B : _⌈V⌉_} (F : A _⟶ B) := mkApplyFn' h.h A B F

      variable [hId : mkHasIdentity V]

      @[reducible] def __DefFun (A : _⌈U⌉_) (B : _⌈V⌉_) (f : A → B) :=
      HasFunctors.DefFun (U := U) (V := V) A B f
      notation:20 A:21 " _⟶__{" f:0 "} " B:21 => mkHasFunctors.__DefFun A B f

      def _DefFun (A : _⌈U⌉_) (B : _⌈V⌉_) (f : ⌜$A → $B⌝) := A _⟶__{λ a : Q($A) => ⌜$f $a⌝} B
      notation:20 A:21 " _⟶_{" f:0 "} " B:21 => mkHasFunctors._DefFun A B f

      -- Requires that all cast terms are defeq.
      def castDefFun {A : _⌈U⌉_} {B : _⌈V⌉_} {f : A → B} (F : A _⟶__{f} B)
                     {U' V' UV' : _Universe} [mkHasFunctors U' V' UV'] [mkHasIdentity V']
                     {A' : _⌈U'⌉_} {B' : _⌈V'⌉_} {f' : A' → B'} :
        A' _⟶__{f'} B' :=
      ⟨F.F, F.eff⟩

      def mkDefFun (A : _⌈U⌉_) (B : _⌈V⌉_) (f : ⌜$A → $B⌝) :=
      let _ := h.h
      let _ := hId.h.h
      ⌜$A ⟶{$f} $B⌝
      notation:20 A:21 " _⟶{" f:0 "} " B:21 => mkHasFunctors.mkDefFun A B f

      def mkFromDefFun {A : _⌈U⌉_} {B : _⌈V⌉_} {f : ⌜$A → $B⌝} (F : A _⟶{f} B) : A _⟶ B :=
      ⌜HasFunctors.fromDefFun $F⌝

      def mkByDef' {A : _⌈U⌉_} {B : _⌈V⌉_} {f : ⌜$A → $B⌝} (F : A _⟶{f} B) (a : Q($A)) :=
      ⌜($F).eff $a⌝

      def mkByDef {A : _⌈U⌉_} {B : _⌈V⌉_} {f : ⌜$A → $B⌝} (F : A _⟶{f} B) (a : Q($A)) :=
      ⌜HasFunctors.byDef (F := $F) (a := $a)⌝

      namespace mkDefFun

        variable {A : _⌈U⌉_} {B : _⌈V⌉_} {f : ⌜$A → $B⌝} (F : A _⟶{f} B)

        -- When using this, make sure that `F'` is defeq to `mkFromDefFun F`.
        def reflect' (F' : A _⟶ B) {g : A → B} : A _⟶__{g} B :=
        { F   := F',
          eff := λ a => some (mkByDef F a) }

        def reflect : A _⟶_{f} B := reflect' F (mkFromDefFun F)

      end mkDefFun

      def mkDefAppFun {A : _⌈U⌉_} {B : _⌈V⌉_} (F : A _⟶ B) :=
      let _ := h.h
      let _ := hId.h.h
      let F' : Q($A ⟶ $B) := F
      let F'' := ⌜HasFunctors.defAppFun $F'⌝
      let F''' : A _⟶{mkApplyFn F} B := F''
      F'''

      def mkAppFun {A : _⌈U⌉_} {B : _⌈V⌉_} (F : A _⟶ B) : A _⟶ B :=
      let _ := h.h
      let _ := hId.h.h
      let F' : Q($A ⟶ $B) := F
      ⌜HasFunctors.appFun $F'⌝

      def mkIsFunApp' (A : _⌈U⌉_) (B : _⌈V⌉_) (b : Q($B)) : ClassExpr :=
      let _ := h.h
      let _ := hId.h.h
      ⟨⌜HasFunctors.IsFunApp $A $b⌝⟩

      class mkIsFunApp (A : outParam _⌈U⌉_) {B : _⌈V⌉_} (b : B) extends
      mkIsFunApp' A B b

      namespace mkIsFunApp

        section

          variable (A : _⌈U⌉_) {B : _⌈V⌉_} (b : Q($B)) [hFunApp : mkIsFunApp' A B b]

          def mkF := ⌜($hFunApp.h).F⌝
          def mka := ⌜($hFunApp.h).a⌝
          def mke := ⌜($hFunApp.h).e⌝

        end

        def reflect (A : _⌈U⌉_) {B : _⌈V⌉_} (b : B) [h : mkIsFunApp A b] :
            MetaM (HasFunctors.IsFunApp (U := U) (V := V) A b) := do
          let b' : Q($B) := b
          pure { F := ← TypedExpr.unfold_once (mkF A b'),
                 a := ← TypedExpr.unfold_once (mka A b'),
                 e := some (← TypedExpr.unfold_once (mke A b')) }

      end mkIsFunApp

    end

    section

      variable {V : _Universe} [hId : mkHasIdentity V]

      def mkIsFunApp₂' {U₁ U₂ U₁V U₂V : _Universe} [hFun_U₁V : mkHasFunctors U₁ V U₁V]
                       [hFun_U₂V : mkHasFunctors U₂ V U₂V]
                       (A₁ : _⌈U₁⌉_) (A₂ : _⌈U₂⌉_) (B : _⌈V⌉_) (b : Q($B)) : ClassExpr :=
      let _ := hFun_U₁V.h
      let _ := hFun_U₂V.h
      let _ := hId.h.h
      ⟨⌜HasFunctors.IsFunApp₂ $A₁ $A₂ $b⌝⟩

      namespace mkIsFunApp₂'

        variable {U₁ U₂ U₁V U₂V : _Universe} [hFun_U₁V : mkHasFunctors U₁ V U₁V]
                 [hFun_U₂V : mkHasFunctors U₂ V U₂V]
                 (A₁ : _⌈U₁⌉_) (A₂ : _⌈U₂⌉_) (B : _⌈V⌉_) (b : Q($B))
                 [h : mkIsFunApp₂' A₁ A₂ B b]
      
        instance : mkIsFunApp A₁ (B := B) b := { h := ⌜($h.h).h₂⌝ }
        instance : mkIsFunApp A₂ (B := B) b := { h := ⌜($h.h).toIsFunApp⌝ }

      end mkIsFunApp₂'

      def mkIsFunApp₃' {U₁ U₂ U₃ U₁V U₂V U₃V : _Universe} [hFun_U₁V : mkHasFunctors U₁ V U₁V]
                       [hFun_U₂V : mkHasFunctors U₂ V U₂V] [hFun_U₃V : mkHasFunctors U₃ V U₃V]
                       (A₁ : _⌈U₁⌉_) (A₂ : _⌈U₂⌉_) (A₃ : _⌈U₃⌉_) (B : _⌈V⌉_) (b : Q($B)) : ClassExpr :=
      let _ := hFun_U₁V.h
      let _ := hFun_U₂V.h
      let _ := hFun_U₃V.h
      let _ := hId.h.h
      ⟨⌜HasFunctors.IsFunApp₃ $A₁ $A₂ $A₃ $b⌝⟩

      namespace mkIsFunApp₃'

        variable {U₁ U₂ U₃ U₁V U₂V U₃V : _Universe} [hFun_U₁V : mkHasFunctors U₁ V U₁V]
                 [hFun_U₂V : mkHasFunctors U₂ V U₂V] [hFun_U₃V : mkHasFunctors U₃ V U₃V]
                 (A₁ : _⌈U₁⌉_) (A₂ : _⌈U₂⌉_) (A₃ : _⌈U₃⌉_) (B : _⌈V⌉_) (b : Q($B))
                 [h : mkIsFunApp₃' A₁ A₂ A₃ B b]

        instance : mkIsFunApp A₁ (B := B) b := { h := ⌜($h.h).h₃⌝ }
        instance : mkIsFunApp₂' A₂ A₃ B b := ⟨⌜($h.h).toIsFunApp₂⌝⟩

      end mkIsFunApp₃'

      structure FunApp {B : _⌈V⌉_} (b : B) where
      {U UV    : _Universe}
      [hFun    : mkHasFunctors U V UV]
      (A       : _⌈U⌉_)
      (hFunApp : HasFunctors.IsFunApp (U := U) (V := V) A b)

      -- `b` and `b'` must be defeq.
      def synthesizeFunApps'' {B : _⌈V⌉_} (b : B) {b' : B} : MetaM (List (FunApp b')) := do
        let U₁ ← _Universe.mkFreshMVar
        let U₂ ← _Universe.mkFreshMVar
        let U₃ ← _Universe.mkFreshMVar
        let U₁V ← _Universe.mkFreshMVar
        let U₂V ← _Universe.mkFreshMVar
        let U₃V ← _Universe.mkFreshMVar
        let hFun_U₁V : mkHasFunctors U₁ V U₁V ← mkHasFunctors.mkFreshMVar
        let hFun_U₂V : mkHasFunctors U₂ V U₂V ← mkHasFunctors.mkFreshMVar
        let hFun_U₃V : mkHasFunctors U₃ V U₃V ← mkHasFunctors.mkFreshMVar
        let A₁ : _⌈U₁⌉_ ← U₁.mkFreshTypeMVar
        let A₂ : _⌈U₂⌉_ ← U₂.mkFreshTypeMVar
        let A₃ : _⌈U₃⌉_ ← U₃.mkFreshTypeMVar
        let hFunApp₃'? : Option (mkIsFunApp₃' A₁ A₂ A₃ B b) ← InstanceExpr.synthesize?
        match hFunApp₃'? with
        | some hFunApp₃' =>
          let U₁ ← U₁.instantiate
          let U₂ ← U₂.instantiate
          let U₃ ← U₃.instantiate
          let U₁V ← U₁V.instantiate
          let U₂V ← U₂V.instantiate
          let U₃V ← U₃V.instantiate
          let hFun_U₁V : mkHasFunctors U₁ V U₁V ← hFun_U₁V.instantiate
          let hFun_U₂V : mkHasFunctors U₂ V U₂V ← hFun_U₂V.instantiate
          let hFun_U₃V : mkHasFunctors U₃ V U₃V ← hFun_U₃V.instantiate
          let A₁ : _⌈U₁⌉_ ← A₁.instantiate
          let A₂ : _⌈U₂⌉_ ← A₂.instantiate
          let A₃ : _⌈U₃⌉_ ← A₃.instantiate
          let hFunApp₃' : mkIsFunApp₃' A₁ A₂ A₃ B b' ← hFunApp₃'.instantiate
          pure [⟨A₃, ← mkIsFunApp.reflect A₃ b'⟩,
                ⟨A₂, ← mkIsFunApp.reflect A₂ b'⟩,
                ⟨A₁, ← mkIsFunApp.reflect A₁ b'⟩]
        | none =>
          let hFunApp₂'? : Option (mkIsFunApp₂' A₁ A₂ B b) ← InstanceExpr.synthesize?
          match hFunApp₂'? with
          | some hFunApp₂' =>
            let U₁ ← U₁.instantiate
            let U₂ ← U₂.instantiate
            let U₁V ← U₁V.instantiate
            let U₂V ← U₂V.instantiate
            let hFun_U₁V : mkHasFunctors U₁ V U₁V ← hFun_U₁V.instantiate
            let hFun_U₂V : mkHasFunctors U₂ V U₂V ← hFun_U₂V.instantiate
            let A₁ : _⌈U₁⌉_ ← A₁.instantiate
            let A₂ : _⌈U₂⌉_ ← A₂.instantiate
            let hFunApp₂' : mkIsFunApp₂' A₁ A₂ B b' ← hFunApp₂'.instantiate
            pure [⟨A₂, ← mkIsFunApp.reflect A₂ b'⟩,
                  ⟨A₁, ← mkIsFunApp.reflect A₁ b'⟩]
          | none =>
            let hFunApp' : mkIsFunApp' A₁ B b ← InstanceExpr.synthesize
            let U₁ ← U₁.instantiate
            let U₁V ← U₁V.instantiate
            let hFun_U₁V : mkHasFunctors U₁ V U₁V ← hFun_U₁V.instantiate
            let A₁ : _⌈U₁⌉_ ← A₁.instantiate
            let hFunApp : mkIsFunApp A₁ b' := { toInstanceExpr := ← hFunApp'.instantiate }
            pure [⟨A₁, ← mkIsFunApp.reflect A₁ b'⟩]

      def synthesizeFunApps' {B : _⌈V⌉_} {b : B} : MetaM (List (FunApp b)) :=
      synthesizeFunApps'' b

      def synthesizeFunApps {B : _⌈V⌉_} {b : B} : MetaM (List (FunApp b)) := do
        -- First check whether `b` is literally a function application.
        -- This sees through some definitions that are opaque to type class synthesis.
        let U ← _Universe.mkFreshMVar
        let UV ← _Universe.mkFreshMVar
        let hFun_UV : mkHasFunctors U V UV ← mkHasFunctors.mkFreshMVar
        let A : _⌈U⌉_ ← _Universe.mkFreshTypeMVar
        let F : (A _⟶ B) ← _Universe.mkFreshInstMVar
        let a : A ← _Universe.mkFreshInstMVar
        if ← isDefEq b (F a) then
          let U ← U.instantiate
          let UV ← UV.instantiate
          let hFun_UV : mkHasFunctors U V UV ← hFun_UV.instantiate
          let A : _⌈U⌉_ ← A.instantiate
          return [⟨A, { F := ← UV.instantiateInstMVars F,
                        a := ← U.instantiateInstMVars a,
                        e := none }⟩]
        -- Next, check if `b` is an application of `fromDefFun`. If it is, pass that to
        -- `IsFunApp` instead of the original value of `b`, as `IsFunApp` is usually
        -- defined on such terms.
        let U' ← _Universe.mkFreshMVar
        let V' ← _Universe.mkFreshMVar
        let hFun_UV' : mkHasFunctors U' V' V ← mkHasFunctors.mkFreshMVar
        let hId_V' : mkHasIdentity V' ← mkHasIdentity.mkFreshMVar
        let A' : _⌈U'⌉_ ← _Universe.mkFreshTypeMVar
        let B' : _⌈V'⌉_ ← _Universe.mkFreshTypeMVar
        let f_b :  ⌜$A' → $B'⌝ ← TypedExpr.mkFreshMVar
        let b' : (A' _⟶{f_b} B') ← TypedExpr.mkFreshMVar
        let b'' : (A' _⟶ B') := mkFromDefFun b'
        if ← isDefEq b b'' then
          let U' ← U'.instantiate
          let V' ← V'.instantiate
          let hFun_UV' : mkHasFunctors U' V' V ← hFun_UV'.instantiate
          let hId_V' : mkHasIdentity V' ← hId_V'.instantiate
          let A' : _⌈U'⌉_ ← _Universe.instantiateTypeMVars A'
          let B' : _⌈V'⌉_ ← _Universe.instantiateTypeMVars B'
          let f_b :  ⌜$A' → $B'⌝ ← f_b.instantiate
          let b' : (A' _⟶{f_b} B') ← b'.instantiate
          -- If it's reducibly defeq to `toDefFun'`, it may have been constructed by
          -- the functoriality algorithm and does not have an `IsFunApp` instance then.
          -- So use the argument of `toDefFun'`.
          let F_B : mkFunInst hFun_UV'.h A' B' ← TypedExpr.mkFreshMVar
          let h_b ← mkFreshExprMVar none
          if ← withReducible (isDefEq b' (mkToDefFun'' hFun_UV'.h hId_V'.h.h A' B' F_B f_b h_b)) then
            let b'' : B ← V.instantiateTypeMVars F_B
            return ← synthesizeFunApps'' b''
          let b'' : B := mkFromDefFun b'
          return ← synthesizeFunApps'' b''
        -- Finally, try to synthesize an instance of `IsFunApp` normally.
        synthesizeFunApps'

    end

  end mkHasFunctors



  def mkHasCongrArg' {u_U v_U u_V v_V u_UV v_UV iu_U iuv_U iu_V iuv_V : Level}
                     (U : ⌜Universe.{u_U, v_U}⌝) (V : ⌜Universe.{u_V, v_V}⌝)
                     (UV : ⌜Universe.{u_UV, v_UV}⌝) (hFun : mkHasFunctors'' U V UV)
                     (hId_U : mkHasIdentity'' U iu_U iuv_U) (hId_V : mkHasIdentity'' V iu_V iuv_V) :=
  ⌜HasCongrArg $U $V⌝

  def mkHasCongrArg (U V : _Universe) {UV : _Universe} [hFun : mkHasFunctors U V UV]
                    [hId_U : mkHasIdentity U] [hId_V : mkHasIdentity V] :
    ClassExpr :=
  ⟨mkHasCongrArg' U.U V.U UV.U hFun.h hId_U.h.h hId_V.h.h⟩

  namespace mkHasCongrArg

    def mkCongrArg'' {U V UV : _Universe} {iu_U iuv_U iu_V iuv_V : Level}
                     (hFun : mkHasFunctors'' U.U V.U UV.U) (hId_U : mkHasIdentity'' U.U iu_U iuv_U)
                     (hId_V : mkHasIdentity'' V.U iu_V iuv_V)
                     (hCongrArg : mkHasCongrArg' U.U V.U UV.U hFun hId_U hId_V)
                     (A : _⌈U⌉_) (B : _⌈V⌉_) (F : Q($A ⟶ $B)) (a₁ a₂ : Q($A)) (h : Q($a₁ ≃ $a₂)) :
      Q($F $a₁ ≃ $F $a₂) :=
    ⌜HasCongrArg.congrArg $F $h⌝

    def mkDefCongrArg'' {U V UV : _Universe} {iu_U iuv_U iu_V iuv_V : Level}
                        (hFun : mkHasFunctors'' U.U V.U UV.U) (hId_U : mkHasIdentity'' U.U iu_U iuv_U)
                        (hId_V : mkHasIdentity'' V.U iu_V iuv_V)
                        (hCongrArg : mkHasCongrArg' U.U V.U UV.U hFun hId_U hId_V)
                        (A : _⌈U⌉_) (B : _⌈V⌉_) (f : Q($A → $B)) (F : Q($A ⟶{$f} $B))
                        (a₁ a₂ : Q($A)) (h : Q($a₁ ≃ $a₂)) :
      Q($f $a₁ ≃ $f $a₂) :=
    ⌜HasCongrArg.defCongrArg $F $h⌝

    variable {U V UV : _Universe} [hFun : mkHasFunctors U V UV] [hId_U : mkHasIdentity U]
             [hId_V : mkHasIdentity V] [hCongrArg : mkHasCongrArg U V]

    def mkCongrArg' {A : _⌈U⌉_} {B : _⌈V⌉_} (F : A _⟶ B) {a₁ a₂ : A} (h : a₁ _≃ a₂) : F a₁ _≃ F a₂ :=
    mkCongrArg'' hFun.h hId_U.h.h hId_V.h.h hCongrArg.h A B F a₁ a₂ h

    def mkCongrArg {A : _⌈U⌉_} {B : _⌈V⌉_} (F : A _⟶ B) {a₁ a₂ : A} (h : a₁ _≃_ a₂) : F a₁ _≃_ F a₂ :=
    match h with
    | some h' =>
      some (mkCongrArg' F h')
    | none =>
      none

    def mkDefCongrArg' {A : _⌈U⌉_} {B : _⌈V⌉_} {f : ⌜$A → $B⌝} (F : A _⟶{f} B) {a₁ a₂ : A} (h : a₁ _≃ a₂) :
      mkHasFunctors.mkArrowApp A B f a₁ _≃ mkHasFunctors.mkArrowApp A B f a₂ :=
    mkDefCongrArg'' hFun.h hId_U.h.h hId_V.h.h hCongrArg.h A B f F a₁ a₂ h

    def mkDefCongrArg {A : _⌈U⌉_} {B : _⌈V⌉_} {f : ⌜$A → $B⌝} (F : A _⟶{f} B) {a₁ a₂ : A} (h : a₁ _≃_ a₂) :
      mkHasFunctors.mkArrowApp A B f a₁ _≃_ mkHasFunctors.mkArrowApp A B f a₂ :=
    match h with
    | some h' =>
      some (mkDefCongrArg' F h')
    | none =>
      none

    instance reflect : HasCongrArg U V := ⟨mkCongrArg⟩

  end mkHasCongrArg


  def mkHasCongrFun' {u_U v_U u_V v_V u_UV v_UV iu_V iuv_V iu_UV iuv_UV : Level}
                     (U : ⌜Universe.{u_U, v_U}⌝) (V : ⌜Universe.{u_V, v_V}⌝)
                     (UV : ⌜Universe.{u_UV, v_UV}⌝) (hFun : mkHasFunctors'' U V UV)
                     (hId_V : mkHasIdentity'' V iu_V iuv_V)
                     (hId_UV : mkHasIdentity'' UV iu_UV iuv_UV) :=
  ⌜HasCongrFun $U $V⌝

  def mkHasCongrFun (U V : _Universe) {UV : _Universe} [hFun : mkHasFunctors U V UV]
                    [hId_V : mkHasIdentity V] [hId_UV : mkHasIdentity UV] :
    ClassExpr :=
  ⟨mkHasCongrFun' U.U V.U UV.U hFun.h hId_V.h.h hId_UV.h.h⟩

  namespace mkHasCongrFun

    open mkHasFunctors

    def mkCongrFun'' {U V UV : _Universe} {iu_V iuv_V iu_UV iuv_UV : Level}
                     (hFun : mkHasFunctors'' U.U V.U UV.U) (hId_V : mkHasIdentity'' V.U iu_V iuv_V)
                     (hId_UV : mkHasIdentity'' UV.U iu_UV iuv_UV)
                     (hCongrFun : mkHasCongrFun' U.U V.U UV.U hFun hId_V hId_UV)
                     (A : _⌈U⌉_) (B : _⌈V⌉_) (F₁ F₂ : Q($A ⟶ $B)) (h : Q($F₁ ≃ $F₂)) (a : Q($A)) :
      Q($F₁ $a ≃ $F₂ $a) :=
    ⌜HasCongrFun.congrFun $h $a⌝

    def mkFunEquiv' {U V UV : _Universe} {iu_V iuv_V : Level}
                    (hFun : mkHasFunctors'' U.U V.U UV.U) (hId_V : mkHasIdentity'' V.U iu_V iuv_V)
                    (A : _⌈U⌉_) (B : _⌈V⌉_) (F₁ F₂ : Q($A ⟶ $B)) :=
    ⌜∀ a, $F₁ a ≃ $F₂ a⌝

    def mkFunEquivTypeFun' {U V UV : _Universe} {iu_V iuv_V : Level}
                           (hFun : mkHasFunctors'' U.U V.U UV.U) (hId_V : mkHasIdentity'' V.U iu_V iuv_V)
                           (A : _⌈U⌉_) (B : _⌈V⌉_) (F₁ F₂ : Q($A ⟶ $B)) :
      Q($A → Sort iu_V) :=
    ⌜λ a => ⌈$F₁ a ≃ $F₂ a⌉⌝

    def mkIsExtensional' {U V UV : _Universe} {iu_V iuv_V iu_UV iuv_UV : Level}
                         (hFun : mkHasFunctors'' U.U V.U UV.U)
                         (hId_V : mkHasIdentity'' V.U iu_V iuv_V)
                         (hId_UV : mkHasIdentity'' UV.U iu_UV iuv_UV)
                         (A : _⌈U⌉_) (B : _⌈V⌉_) (F₁ F₂ : Q($A ⟶ $B))
                         (h : mkFunEquiv' hFun hId_V A B F₁ F₂) :
      Q(($hId_UV).IU) :=
    ⌜HasCongrFun.IsExtensional $F₁ $F₂ $h⌝

    variable {U V UV : _Universe} [hFun : mkHasFunctors U V UV] [hId_V : mkHasIdentity V]
             [hId_UV : mkHasIdentity UV]

    def mkCongrFun' [hCongrFun : mkHasCongrFun U V] {A : _⌈U⌉_} {B : _⌈V⌉_} {F₁ F₂ : A _⟶ B}
                    (h : F₁ _≃ F₂) (a : A) : F₁ a _≃ F₂ a :=
    mkCongrFun'' hFun.h hId_V.h.h hId_UV.h.h hCongrFun.h A B F₁ F₂ h a

    def mkCongrFun [hCongrFun : mkHasCongrFun U V] {A : _⌈U⌉_} {B : _⌈V⌉_} {F₁ F₂ : A _⟶ B}
                   (h : F₁ _≃_ F₂) (a : A) : F₁ a _≃_ F₂ a :=
    match h with
    | some h' =>
      some (mkCongrFun' h' a)
    | none =>
      none

    instance reflect [hCongrFun : mkHasCongrFun U V] : HasCongrFun U V := ⟨mkCongrFun⟩

    def mkFunEquiv {A : _⌈U⌉_} {B : _⌈V⌉_} (F₁ F₂ : A _⟶ B) :=
    mkFunEquiv' hFun.h hId_V.h.h A B F₁ F₂

    def mkFunEquivTypeFun {A : _⌈U⌉_} {B : _⌈V⌉_} (F₁ F₂ : A _⟶ B) :=
    mkFunEquivTypeFun' hFun.h hId_V.h.h A B F₁ F₂

    def mkIsExtensional {A : _⌈U⌉_} {B : _⌈V⌉_} (F₁ F₂ : A _⟶ B) (h : mkFunEquiv F₁ F₂) :
      _⌈mkHasIdentity.univ UV⌉_ :=
    mkIsExtensional' hFun.h hId_V.h.h hId_UV.h.h A B F₁ F₂ h

  end mkHasCongrFun



  def mkHasIdFun' {u_U v_U u_UU v_UU iu_U iuv_U : Level} (U : ⌜Universe.{u_U, v_U}⌝)
                  (UU : ⌜Universe.{u_UU, v_UU}⌝) (hFun : mkHasFunctors'' U U UU)
                  (hId_U : mkHasIdentity'' U iu_U iuv_U) :=
  ⌜HasIdFun $U⌝

  def mkHasIdFun (U : _Universe) {UU : _Universe} [hFun : mkHasFunctors U U UU]
                 [hId_U : mkHasIdentity U] :
    ClassExpr :=
  ⟨mkHasIdFun' U.U UU.U hFun.h hId_U.h.h⟩

  namespace mkHasIdFun

    variable {U UU : _Universe} [mkHasFunctors U U UU] [mkHasIdentity U] [h : mkHasIdFun U]

    def mkDefIdFun (A : _⌈U⌉_) : A _⟶{⌜id⌝} A :=
    let _ := h.h
    ⌜HasIdFun.defIdFun $A⌝
  
    def mkIdFun (A : _⌈U⌉_) : A _⟶ A :=
    let _ := h.h
    ⌜HasIdFun.idFun $A⌝

    instance reflect : HasIdFun U :=
    ⟨λ A => mkHasFunctors.mkDefFun.reflect' (mkDefIdFun A) (mkIdFun A)⟩

  end mkHasIdFun


  def mkHasConstFun' {u_U v_U u_V v_V u_UV v_UV iu_V iuv_V : Level} (U : ⌜Universe.{u_U, v_U}⌝)
                     (V : ⌜Universe.{u_V, v_V}⌝) (UV : ⌜Universe.{u_UV, v_UV}⌝)
                     (hFun : mkHasFunctors'' U V UV) (hId_V : mkHasIdentity'' V iu_V iuv_V) :=
  ⌜HasConstFun $U $V⌝

  def mkHasConstFun (U V : _Universe) {UV : _Universe} [hFun : mkHasFunctors U V UV]
                    [hId_V : mkHasIdentity V] :
    ClassExpr :=
  ⟨mkHasConstFun' U.U V.U UV.U hFun.h hId_V.h.h⟩

  namespace mkHasConstFun

    variable {U V UV : _Universe} [mkHasFunctors U V UV] [mkHasIdentity V] [h : mkHasConstFun U V]

    def mkDefConstFun (A : _⌈U⌉_) {B : _⌈V⌉_} (b : Q($B)) : A _⟶{⌜Function.const $A $b⌝} B :=
    let _ := h.h
    ⌜HasConstFun.defConstFun $A $b⌝
  
    def mkConstFun (A : _⌈U⌉_) {B : _⌈V⌉_} (b : B) : A _⟶ B :=
    let _ := h.h
    let b' : Q($B) := b
    ⌜HasConstFun.constFun $A $b'⌝

    instance reflect : HasConstFun U V :=
    ⟨λ A {_} b => mkHasFunctors.mkDefFun.reflect' (mkDefConstFun A b) (mkConstFun A b)⟩

  end mkHasConstFun


  def mkHasRevAppFun' {u_U v_U iu_U iuv_U : Level} (U : ⌜Universe.{u_U, v_U}⌝)
                      (hFun : mkHasFunctors'' U U U) (hId_U : mkHasIdentity'' U iu_U iuv_U) :=
  ⌜HasRevAppFun $U⌝

  def mkHasRevAppFun (U : _Universe) [hFun : mkHasFunctors U U U] [hId_U : mkHasIdentity U] :
    ClassExpr :=
  ⟨mkHasRevAppFun' U.U hFun.h hId_U.h.h⟩

  namespace mkHasRevAppFun

    variable {U : _Universe} [mkHasFunctors U U U] [mkHasIdentity U] [h : mkHasRevAppFun U]

    def mkDefRevAppFun' (A : _⌈U⌉_) (a : Q($A)) (B : _⌈U⌉_) : (A _⟶ B) _⟶{⌜λ F => F $a⌝} B :=
    let _ := h.h
    ⌜HasRevAppFun.defRevAppFun $a $B⌝

    def mkDefRevAppFun {A : _⌈U⌉_} (a : A) (B : _⌈U⌉_) := mkDefRevAppFun' A a B

    def mkRevAppFun {A : _⌈U⌉_} (a : A) (B : _⌈U⌉_) : (A _⟶ B) _⟶ B :=
    let _ := h.h
    let a' : Q($A) := a
    ⌜HasRevAppFun.revAppFun $a' $B⌝

    instance reflect : HasRevAppFun U :=
    ⟨λ a B => mkHasFunctors.mkDefFun.reflect' (mkDefRevAppFun a B) (mkRevAppFun a B)⟩

  end mkHasRevAppFun


  def mkHasCompFun' {u_U v_U u_V v_V u_W v_W u_UV v_UV u_VW v_VW u_UW v_UW iu_W iuv_W : Level}
                    (U : ⌜Universe.{u_U, v_U}⌝) (V : ⌜Universe.{u_V, v_V}⌝)
                    (W : ⌜Universe.{u_W, v_W}⌝) (UV : ⌜Universe.{u_UV, v_UV}⌝)
                    (VW : ⌜Universe.{u_VW, v_VW}⌝) (UW : ⌜Universe.{u_UW, v_UW}⌝)
                    (hFun_UV : mkHasFunctors'' U V UV) (hFun_VW : mkHasFunctors'' V W VW)
                    (hFun_UW : mkHasFunctors'' U W UW) (hId_W : mkHasIdentity'' W iu_W iuv_W) :=
  ⌜HasCompFun $U $V $W⌝

  def mkHasCompFun (U V W : _Universe) {UV VW UW : _Universe} [hFun_UV : mkHasFunctors U V UV]
                   [hFun_VW : mkHasFunctors V W VW] [hFun_UW : mkHasFunctors U W UW]
                   [hId_W : mkHasIdentity W] :
    ClassExpr :=
  ⟨mkHasCompFun' U.U V.U W.U UV.U VW.U UW.U hFun_UV.h hFun_VW.h hFun_UW.h hId_W.h.h⟩

  namespace mkHasCompFun

    variable {U V W UV VW UW : _Universe} [hFun_UV : mkHasFunctors U V UV]
             [hFun_VW : mkHasFunctors V W VW] [hFun_UW : mkHasFunctors U W UW] [mkHasIdentity W]
             [h : mkHasCompFun U V W]

    def mkDefCompFun' (A : _⌈U⌉_) (B : _⌈V⌉_) (C : _⌈W⌉_)
                      (F : mkHasFunctors.mkFunInst hFun_UV.h A B)
                      (G : mkHasFunctors.mkFunInst hFun_VW.h B C) :
      A _⟶{⌜λ a => $G ($F a)⌝} C :=
    let _ := h.h
    ⌜HasCompFun.defCompFun $F $G⌝

    def mkDefCompFun {A : _⌈U⌉_} {B : _⌈V⌉_} {C : _⌈W⌉_} (F : A _⟶ B) (G : B _⟶ C) :=
    mkDefCompFun' A B C F G

    def mkCompFun {A : _⌈U⌉_} {B : _⌈V⌉_} {C : _⌈W⌉_} (F : A _⟶ B) (G : B _⟶ C) : A _⟶ C :=
    let _ := h.h
    let F' : Q($A ⟶ $B) := F
    let G' : Q($B ⟶ $C) := G
    ⌜HasCompFun.compFun $F' $G'⌝

    instance reflect : HasCompFun U V W :=
    ⟨λ F G => mkHasFunctors.mkDefFun.reflect' (mkDefCompFun F G) (mkCompFun F G)⟩

  end mkHasCompFun


  def mkHasSwapFun' {u_U v_U u_V v_V u_W v_W u_VW v_VW u_UVW v_UVW u_UW v_UW iu_W iuv_W : Level}
                    (U : ⌜Universe.{u_U, v_U}⌝) (V : ⌜Universe.{u_V, v_V}⌝)
                    (W : ⌜Universe.{u_W, v_W}⌝) (VW : ⌜Universe.{u_VW, v_VW}⌝)
                    (UVW : ⌜Universe.{u_UVW, v_UVW}⌝) (UW : ⌜Universe.{u_UW, v_UW}⌝)
                    (hFun_VW : mkHasFunctors'' V W VW) (hFun_UVW : mkHasFunctors'' U VW UVW)
                    (hFun_UW : mkHasFunctors'' U W UW) (hId_W : mkHasIdentity'' W iu_W iuv_W) :=
  ⌜HasSwapFun $U $V $W⌝

  def mkHasSwapFun (U V W : _Universe) {VW UVW UW : _Universe} [hFun_VW : mkHasFunctors V W VW]
                   [hFun_UVW : mkHasFunctors U VW UVW] [hFun_UW : mkHasFunctors U W UW]
                   [hId_W : mkHasIdentity W] :
    ClassExpr :=
  ⟨mkHasSwapFun' U.U V.U W.U VW.U UVW.U UW.U hFun_VW.h hFun_UVW.h hFun_UW.h hId_W.h.h⟩

  namespace mkHasSwapFun

    variable {U V W VW UVW UW : _Universe} [hFun_VW : mkHasFunctors V W VW]
             [hFun_UVW : mkHasFunctors U VW UVW] [hFun_UW : mkHasFunctors U W UW] [mkHasIdentity W]
             [h : mkHasSwapFun U V W]

    def mkDefSwapFun' (A : _⌈U⌉_) (B : _⌈V⌉_) (C : _⌈W⌉_)
                      (F : mkHasFunctors.mkFunInst hFun_UVW.h A (B _⟶ C))
                      (b : Q($B)) :
      A _⟶{⌜λ a => $F a $b⌝} C :=
    let _ := h.h
    ⌜HasSwapFun.defSwapFun $F $b⌝

    def mkDefSwapFun {A : _⌈U⌉_} {B : _⌈V⌉_} {C : _⌈W⌉_} (F : A _⟶ B _⟶ C) (b : B) :=
    mkDefSwapFun' A B C F b

    def mkSwapFun {A : _⌈U⌉_} {B : _⌈V⌉_} {C : _⌈W⌉_} (F : A _⟶ B _⟶ C) (b : B) : A _⟶ C :=
    let _ := h.h
    let F' : Q($A ⟶ $B ⟶ $C) := F
    let b' : Q($B) := b
    ⌜HasSwapFun.swapFun $F' $b'⌝

    instance reflect : HasSwapFun U V W :=
    ⟨λ F b => mkHasFunctors.mkDefFun.reflect' (mkDefSwapFun F b) (mkSwapFun F b)⟩

  end mkHasSwapFun


  def mkHasDupFun' {u_U v_U u_V v_V u_UV v_UV u_UUV v_UUV iu_V iuv_V : Level}
                   (U : ⌜Universe.{u_U, v_U}⌝) (V : ⌜Universe.{u_V, v_V}⌝)
                   (UV : ⌜Universe.{u_UV, v_UV}⌝) (UUV : ⌜Universe.{u_UUV, v_UUV}⌝)
                   (hFun_UV : mkHasFunctors'' U V UV) (hFun_UUV : mkHasFunctors'' U UV UUV)
                   (hId_V : mkHasIdentity'' V iu_V iuv_V) :=
  ⌜HasDupFun $U $V⌝

  def mkHasDupFun (U V : _Universe) {UV UUV : _Universe} [hFun_UV : mkHasFunctors U V UV]
                  [hFun_UUV : mkHasFunctors U UV UUV] [hId_V : mkHasIdentity V] :
    ClassExpr :=
  ⟨mkHasDupFun' U.U V.U UV.U UUV.U hFun_UV.h hFun_UUV.h hId_V.h.h⟩

  namespace mkHasDupFun

    variable {U V UV UUV : _Universe} [hFun_UV : mkHasFunctors U V UV]
             [hFun_UUV : mkHasFunctors U UV UUV] [mkHasIdentity V] [h : mkHasDupFun U V]

    def mkDefDupFun' (A : _⌈U⌉_) (B : _⌈V⌉_) (F : mkHasFunctors.mkFunInst hFun_UUV.h A (A _⟶ B)) :
      A _⟶{⌜λ a => $F a a⌝} B :=
    let _ := h.h
    ⌜HasDupFun.defDupFun $F⌝
  
    def mkDefDupFun {A : _⌈U⌉_} {B : _⌈V⌉_} (F : A _⟶ A _⟶ B) := mkDefDupFun' A B F

    def mkDupFun {A : _⌈U⌉_} {B : _⌈V⌉_} (F : A _⟶ A _⟶ B) : A _⟶ B :=
    let _ := h.h
    let F' : Q($A ⟶ $A ⟶ $B) := F
    ⌜HasDupFun.dupFun $F'⌝

    instance reflect : HasDupFun U V :=
    ⟨λ F => mkHasFunctors.mkDefFun.reflect' (mkDefDupFun F) (mkDupFun F)⟩

  end mkHasDupFun


  def mkHasSubstFun' {u_U v_U u_V v_V u_W v_W u_UV v_UV u_VW v_VW u_UVW v_UVW u_UW v_UW iu_W iuv_W : Level}
                     (U : ⌜Universe.{u_U, v_U}⌝) (V : ⌜Universe.{u_V, v_V}⌝)
                     (W : ⌜Universe.{u_W, v_W}⌝) (UV : ⌜Universe.{u_UV, v_UV}⌝)
                     (VW : ⌜Universe.{u_VW, v_VW}⌝) (UVW : ⌜Universe.{u_UVW, v_UVW}⌝)
                     (UW : ⌜Universe.{u_UW, v_UW}⌝) (hFun_UV : mkHasFunctors'' U V UV)
                     (hFun_VW : mkHasFunctors'' V W VW) (hFun_UVW : mkHasFunctors'' U VW UVW)
                     (hFun_UW : mkHasFunctors'' U W UW) (hId_W : mkHasIdentity'' W iu_W iuv_W) :=
  ⌜HasSubstFun $U $V $W⌝

  def mkHasSubstFun (U V W : _Universe) {UV VW UVW UW : _Universe} [hFun_UV : mkHasFunctors U V UV]
                    [hFun_VW : mkHasFunctors V W VW] [hFun_UVW : mkHasFunctors U VW UVW]
                    [hFun_UW : mkHasFunctors U W UW] [hId_W : mkHasIdentity W] :
    ClassExpr :=
  ⟨mkHasSubstFun' U.U V.U W.U UV.U VW.U UVW.U UW.U hFun_UV.h hFun_VW.h hFun_UVW.h hFun_UW.h hId_W.h.h⟩

  namespace mkHasSubstFun

    variable {U V W UV VW UVW UW : _Universe} [hFun_UV : mkHasFunctors U V UV]
             [hFun_VW : mkHasFunctors V W VW] [hFun_UVW : mkHasFunctors U VW UVW]
             [hFun_UW : mkHasFunctors U W UW] [mkHasIdentity W] [h : mkHasSubstFun U V W]

    def mkDefSubstFun' (A : _⌈U⌉_) (B : _⌈V⌉_) (C : _⌈W⌉_)
                       (F : mkHasFunctors.mkFunInst hFun_UV.h A B)
                       (G : mkHasFunctors.mkFunInst hFun_UVW.h A (B _⟶ C)) :
      A _⟶{⌜λ a => $G a ($F a)⌝} C :=
    let _ := h.h
    ⌜HasSubstFun.defSubstFun $F $G⌝

    def mkDefSubstFun {A : _⌈U⌉_} {B : _⌈V⌉_} {C : _⌈W⌉_} (F : A _⟶ B) (G : A _⟶ B _⟶ C) :=
    mkDefSubstFun' A B C F G

    def mkSubstFun {A : _⌈U⌉_} {B : _⌈V⌉_} {C : _⌈W⌉_} (F : A _⟶ B) (G : A _⟶ B _⟶ C) : A _⟶ C :=
    let _ := h.h
    let F' : Q($A ⟶ $B) := F
    let G' : Q($A ⟶ $B ⟶ $C) := G
    ⌜HasSubstFun.substFun $F' $G'⌝

    instance reflect : HasSubstFun U V W :=
    ⟨λ F G => mkHasFunctors.mkDefFun.reflect' (mkDefSubstFun F G) (mkSubstFun F G)⟩

  end mkHasSubstFun



  def mkHasInternalFunctors' {u_U v_U iu iuv : Level} (U : ⌜Universe.{u_U, v_U}⌝)
                             (hId : mkHasIdentity'' U iu iuv) :=
  ⌜HasInternalFunctors $U⌝

  def mkHasInternalFunctors (U : _Universe) [hId : mkHasIdentity U] : ClassExpr :=
  ⟨mkHasInternalFunctors' U.U hId.h.h⟩

  namespace mkHasInternalFunctors

    variable (U : _Universe) [hId : mkHasIdentity U] [hFun : mkHasInternalFunctors U]

    instance : mkHasFunctors U U U := { h := ⌜($hFun.h).toHasFunctors⌝ }

    def hasCongrArg' : Expr := ⌜($hFun.h).toHasCongrArg⌝
    instance : mkHasCongrArg U U := ⟨hasCongrArg' U⟩

    instance reflect : HasInternalFunctors U := ⟨⟩

  end mkHasInternalFunctors



  def mkHasLinearFunOp' {u_U v_U iu iuv : Level} (U : ⌜Universe.{u_U, v_U}⌝)
                        (hId : mkHasIdentity'' U iu iuv) (hFun : mkHasInternalFunctors' U hId) :=
  ⌜HasLinearFunOp $U⌝

  def mkHasLinearFunOp (U : _Universe) [hId : mkHasIdentity U] [hFun : mkHasInternalFunctors U] :
    ClassExpr :=
  ⟨mkHasLinearFunOp' U.U hId.h.h hFun.h⟩

  namespace mkHasLinearFunOp

    variable {U : _Universe} [hId : mkHasIdentity U] [hFun : mkHasInternalFunctors U]
             [h : mkHasLinearFunOp U]

    def mkDefIdFun (A : _⌈U⌉_) : A _⟶{⌜id⌝} A :=
    let _ := h.h
    ⌜HasIdFun.defIdFun $A⌝
  
    def mkIdFun (A : _⌈U⌉_) : A _⟶ A :=
    let _ := h.h
    ⌜HasLinearFunOp.idFun $A⌝

    def mkDefRevAppFun' (A : _⌈U⌉_) (a : Q($A)) (B : _⌈U⌉_) : (A _⟶ B) _⟶{⌜λ F => F $a⌝} B :=
    let _ := h.h
    ⌜HasRevAppFun.defRevAppFun $a $B⌝

    def mkDefRevAppFun {A : _⌈U⌉_} (a : A) (B : _⌈U⌉_) := mkDefRevAppFun' A a B

    def mkRevAppFun {A : _⌈U⌉_} (a : A) (B : _⌈U⌉_) : (A _⟶ B) _⟶ B :=
    let _ := h.h
    let a' : Q($A) := a
    ⌜HasLinearFunOp.revAppFun $a' $B⌝

    def mkDefRevAppFunFunType (A B : _⌈U⌉_) :=
    let _ := h.h
    A _⟶{⌜λ a => HasLinearFunOp.revAppFun a $B⌝} ((A _⟶ B) _⟶ B)

    def mkDefRevAppFunFun (A B : _⌈U⌉_) : mkDefRevAppFunFunType A B :=
    let _ := h.h
    ⌜(HasLinearFunOp.defRevAppFun $A $B).defFunFun⌝

    def mkRevAppFunFun (A B : _⌈U⌉_) : (A _⟶ B) _⟶ B :=
    let _ := h.h
    ⌜HasLinearFunOp.revAppFunFun $A $B⌝

    def mkDefCompFun' (A B C : _⌈U⌉_)
                      (F : mkHasFunctors.mkFunInst mkHasFunctors.toInstanceExpr.h A B)
                      (G : mkHasFunctors.mkFunInst mkHasFunctors.toInstanceExpr.h B C) :
      A _⟶{⌜λ a => $G ($F a)⌝} C :=
    let _ := h.h
    ⌜HasCompFun.defCompFun $F $G⌝

    def mkDefCompFun {A B C : _⌈U⌉_} (F : A _⟶ B) (G : B _⟶ C) := mkDefCompFun' A B C F G

    def mkCompFun {A B C : _⌈U⌉_} (F : A _⟶ B) (G : B _⟶ C) : A _⟶ C :=
    let _ := h.h
    let F' : Q($A ⟶ $B) := F
    let G' : Q($B ⟶ $C) := G
    ⌜$G' • $F'⌝

    def mkDefCompFunFunType (A B : _⌈U⌉_) (F : A _⟶ B) (C : _⌈U⌉_) :=
    let _ := h.h
    let F' : Q($A ⟶ $B) := F
    (B _⟶ C) _⟶{⌜λ G => G • $F'⌝} (A _⟶ C)

    def mkDefCompFunFun' (A B : _⌈U⌉_)
                         (F : mkHasFunctors.mkFunInst mkHasFunctors.toInstanceExpr.h A B)
                         (C : _⌈U⌉_) :
      mkDefCompFunFunType A B F C :=
    let _ := h.h
    ⌜HasCompFunFun.defCompFunFun $F $C⌝

    def mkDefCompFunFun {A B : _⌈U⌉_} (F : A _⟶ B) (C : _⌈U⌉_) := mkDefCompFunFun' A B F C

    def mkCompFunFun {A B : _⌈U⌉_} (F : A _⟶ B) (C : _⌈U⌉_) : (B _⟶ C) _⟶ (A _⟶ C) :=
    let _ := h.h
    let F' : Q($A ⟶ $B) := F
    ⌜HasLinearFunOp.compFunFun $F' $C⌝

    def mkDefCompFunFunFunType (A B C : _⌈U⌉_) :=
    let _ := h.h
    (A _⟶ B) _⟶{⌜λ F => HasLinearFunOp.compFunFun F $C⌝} ((B _⟶ C) _⟶ (A _⟶ C))

    def mkDefCompFunFunFun (A B C : _⌈U⌉_) : mkDefCompFunFunFunType A B C :=
    let _ := h.h
    ⌜(HasLinearFunOp.defCompFun $A $B $C).defFunFunFun⌝

    def mkCompFunFunFun (A B C : _⌈U⌉_) : (A _⟶ B) _⟶ (B _⟶ C) _⟶ (A _⟶ C) :=
    let _ := h.h
    ⌜HasLinearFunOp.compFunFunFun $A $B $C⌝

    def mkDefSwapFun' (A B C : _⌈U⌉_)
                      (F : mkHasFunctors.mkFunInst mkHasFunctors.toInstanceExpr.h A (B _⟶ C))
                      (b : Q($B)) :
      A _⟶{⌜λ a => $F a $b⌝} C :=
    let _ := h.h
    ⌜HasSwapFun.defSwapFun $F $b⌝

    def mkDefSwapFun {A B C : _⌈U⌉_} (F : A _⟶ B _⟶ C) (b : B) :=
    mkDefSwapFun' A B C F b

    def mkSwapFun {A B C : _⌈U⌉_} (F : A _⟶ B _⟶ C) (b : B) : A _⟶ C :=
    let _ := h.h
    let F' : Q($A ⟶ $B ⟶ $C) := F
    let b' : Q($B) := b
    ⌜HasLinearFunOp.swapFun $F' $b'⌝

    def mkDefSwapFunFunType (A B C : _⌈U⌉_) (F : A _⟶ B _⟶ C) :=
    let _ := h.h
    let F' : Q($A ⟶ $B ⟶ $C) := F
    B _⟶{⌜λ b => HasLinearFunOp.swapFun $F' b⌝} (A _⟶ C)

    def mkDefSwapFunFun' (A B C : _⌈U⌉_)
                         (F : mkHasFunctors.mkFunInst mkHasFunctors.toInstanceExpr.h A (B _⟶ C)) :
      mkDefSwapFunFunType A B C F :=
    let _ := h.h
    ⌜HasSwapFunFun.defSwapFunFun $F⌝

    def mkDefSwapFunFun {A B C : _⌈U⌉_} (F : A _⟶ B _⟶ C) :=
    mkDefSwapFunFun' A B C F

    def mkSwapFunFun {A B C : _⌈U⌉_} (F : A _⟶ B _⟶ C) : B _⟶ A _⟶ C :=
    let _ := h.h
    let F' : Q($A ⟶ $B ⟶ $C) := F
    ⌜HasLinearFunOp.swapFunFun $F'⌝

    def mkDefSwapFunFunFunType (A B C : _⌈U⌉_) :=
    let _ := h.h
    (A _⟶ B _⟶ C) _⟶{⌜λ F => HasLinearFunOp.swapFunFun F⌝} (B _⟶ A _⟶ C)

    def mkDefSwapFunFunFun (A B C : _⌈U⌉_) : mkDefSwapFunFunFunType A B C :=
    let _ := h.h
    ⌜(HasLinearFunOp.defSwapFun $A $B $C).defFunFunFun⌝

    def mkSwapFunFunFun (A B C : _⌈U⌉_) : (A _⟶ B _⟶ C) _⟶ (B _⟶ A _⟶ C) :=
    let _ := h.h
    ⌜HasLinearFunOp.swapFunFunFun $A $B $C⌝

    def mkDefRevCompFunFunType (A B C : _⌈U⌉_) (G : B _⟶ C) :=
    let _ := h.h
    let G' : Q($B ⟶ $C) := G
    (A _⟶ B) _⟶{⌜λ F => HasLinearFunOp.compFun F $G'⌝} (A _⟶ C)

    def mkDefRevCompFunFun' (A B C : _⌈U⌉_)
                            (G : mkHasFunctors.mkFunInst mkHasFunctors.toInstanceExpr.h B C) :
      mkDefRevCompFunFunType A B C G :=
    let _ := h.h
    ⌜HasRevCompFunFun.defRevCompFunFun $A $G⌝

    def mkDefRevCompFunFun (A : _⌈U⌉_) {B C : _⌈U⌉_} (G : B _⟶ C) := mkDefRevCompFunFun' A B C G

    def mkRevCompFunFun (A : _⌈U⌉_) {B C : _⌈U⌉_} (G : B _⟶ C) : (A _⟶ B) _⟶ (A _⟶ C) :=
    let _ := h.h
    let G' : Q($B ⟶ $C) := G
    ⌜HasLinearFunOp.revCompFunFun $A $G'⌝

    def mkDefRevCompFunFunFunType (A B C : _⌈U⌉_) :=
    let _ := h.h
    (B _⟶ C) _⟶{⌜λ G => HasLinearFunOp.revCompFunFun $A G⌝} ((A _⟶ B) _⟶ (A _⟶ C))

    def mkDefRevCompFunFunFun (A B C : _⌈U⌉_) : mkDefRevCompFunFunFunType A B C :=
    let _ := h.h
    ⌜(HasLinearFunOp.defRevCompFun $A $B $C).defFunFunFun⌝

    def mkRevCompFunFunFun (A B C : _⌈U⌉_) : (B _⟶ C) _⟶ (A _⟶ B) _⟶ (A _⟶ C) :=
    let _ := h.h
    ⌜HasLinearFunOp.revCompFunFunFun $A $B $C⌝

    instance reflect : HasLinearFunOp U :=
    { defIdFun     := λ A => mkHasFunctors.mkDefFun.reflect' (mkDefIdFun A) (mkIdFun A),
      defRevAppFun := λ A B => ⟨λ a => mkHasFunctors.mkDefFun.reflect' (mkDefRevAppFun a B) (mkRevAppFun a B),
                                mkHasFunctors.mkDefFun.reflect' (mkDefRevAppFunFun A B) (mkRevAppFunFun (h := h) A B)⟩,
      defCompFun   := λ A B C => ⟨λ F => ⟨λ G => mkHasFunctors.mkDefFun.reflect' (mkDefCompFun F G) (mkCompFun F G),
                                          mkHasFunctors.mkDefFun.reflect' (mkDefCompFunFun F C) (mkCompFunFun F C)⟩,
                                  mkHasFunctors.mkDefFun.reflect' (mkDefCompFunFunFun A B C) (mkCompFunFunFun A B C)⟩ }

  end mkHasLinearFunOp



  namespace mkHasLinearFunOp

    def mkHasLinearFunExt' {u_U v_U iu iuv : Level} (U : ⌜Universe.{u_U, v_U}⌝)
                           (hId : mkHasIdentity'' U iu iuv) (hFun : mkHasInternalFunctors' U hId)
                           (hFunOp : mkHasLinearFunOp' U hId hFun) :=
    ⌜HasLinearFunOp.HasLinearFunExt $U⌝

    def mkHasLinearFunExt (U : _Universe) [hId : mkHasIdentity U] [hFun : mkHasInternalFunctors U]
                          [hFunOp : mkHasLinearFunOp U] :
      ClassExpr :=
    ⟨mkHasLinearFunExt' U.U hId.h.h hFun.h hFunOp.h⟩

    namespace mkHasLinearFunExt

      variable {U : _Universe} [hId : mkHasIdentity U] [hFun : mkHasInternalFunctors U]
               [hFunOp : mkHasLinearFunOp U] [h : mkHasLinearFunExt U]

      def mkRightId {A B : _⌈U⌉_} (F : A _⟶ B) :=
      let _ := h.h
      let F' : Q($A ⟶ $B) := F
      ⌜HasLinearFunOp.HasLinearFunExt.rightId $F'⌝

    end mkHasLinearFunExt

  end mkHasLinearFunOp

end Lean
