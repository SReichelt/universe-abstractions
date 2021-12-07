import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.MetaRelations
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.FunctorExtensionality
import UniverseAbstractions.Meta.TypedExpr
import UniverseAbstractions.Meta.Helpers



set_option autoBoundImplicitLocal false



namespace Lean

  open Meta Elab Tactic Qq
       Universe MetaRelation



  structure _Sort where
  {u : Level}
  (α : ⌜Sort u⌝)

  def exprUniverse {β : Type} (inst : β → _Sort) : Universe :=
  { A    := β,
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

    instance hasFunctors : HasFunctors _sort _sort _sort :=
    { Fun   := λ A B => ⟨mkFun A.α B.α⟩,
      apply := λ {A B} (f : mkFun A.α B.α) (a : A.α) => ⌜$f $a⌝ }

    -- When using this, make sure that `f` is defeq to what `f'` specifies.
    def defFun {A B : _sort} {f' : A → B} (f : mkFun A.α B.α) : A ⟶{f'} B :=
    { F   := f,
      eff := λ _ => none }

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
    { defIdFun         := λ A                                               => defFun ⌜id⌝,
      defRevAppFun     := λ {A} (a : A.α) B                                 => defFun ⌜λ f => f $a⌝,
      defRevAppFunFun  := λ A B                                             => defFun ⌜λ a f => f a⌝,
      defCompFun       := λ {A B C} (f : mkFun A.α B.α) (g : mkFun B.α C.α) => defFun ⌜$g ∘ $f⌝,
      defCompFunFun    := λ {A B} (f : mkFun A.α B.α) C                     => defFun ⌜λ g => g ∘ $f⌝,
      defCompFunFunFun := λ A B C                                           => defFun ⌜λ f g => g ∘ f⌝ }

    instance hasAffineFunOp : HasAffineFunOp _sort :=
    { defConstFun    := λ A {B} (b : B.α) => defFun ⌜Function.const _ $b⌝
      defConstFunFun := λ A B             => defFun ⌜Function.const _⌝ }

    instance hasFullFunOp : HasFullFunOp _sort :=
    { defDupFun    := λ {A B} (f : mkFun A.α (mkFun A.α B.α)) => defFun ⌜λ a => $f a a⌝,
      defDupFunFun := λ A B                                   => defFun ⌜λ f a => f a a⌝ }

    instance hasLinearFunExt : HasLinearFunOp.HasLinearFunExt _sort :=
    { rightId              := λ _         => none,
      rightIdExt           := λ _ _       => none,
      leftId               := λ _         => none,
      leftIdExt            := λ _ _       => none,
      swapRevApp           := λ _         => none,
      swapRevAppExt        := λ _ _       => none,
      swapCompFun          := λ _ _ _     => none,
      swapCompFunExt       := λ _ _       => none,
      swapCompFunExtExt    := λ _ _ _     => none,
      swapRevCompFun       := λ _ _       => none,
      swapRevCompFunExt    := λ _ {_ _} _ => none,
      swapRevCompFunExtExt := λ _ _ _     => none,
      compAssoc            := λ _ _ _     => none,
      compAssocExt         := λ _ _ _     => none,
      compAssocExtExt      := λ _ _ _     => none,
      compAssocExtExtExt   := λ _ _ _ _   => none }

    instance hasAffineFunExt : HasAffineFunOp.HasAffineFunExt _sort :=
    { rightConst       := λ _ {_ _} _ _ => none,
      rightConstExt    := λ _ {_} _ _   => none,
      rightConstExtExt := λ _ _ _       => none,
      leftConst        := λ _ _         => none,
      leftConstExt     := λ _ _         => none,
      leftConstExtExt  := λ _ _ _       => none }

    instance hasFullFunExt : HasFullFunOp.HasFullFunExt _sort :=
    { dupSwap        := λ _     => none,
      dupSwapExt     := λ _ _   => none,
      dupConst       := λ _     => none,
      dupConstExt    := λ _ _   => none,
      dupDup         := λ _     => none,
      dupDupExt      := λ _ _   => none,
      rightDup       := λ _ _   => none,
      rightDupExt    := λ _ _   => none,
      rightDupExtExt := λ _ _ _ => none,
      substDup       := λ _ _   => none,
      substDupExt    := λ _ _   => none,
      substDupExtExt := λ _ _ _ => none }

    instance hasStandardFunctors : HasStandardFunctors _sort := ⟨⟩

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
      return ⟨U⟩

    def instantiate (U : _Universe) : MetaM _Universe := do
      let u ← instantiateLevelMVars U.u
      let v ← instantiateLevelMVars U.v
      let U : ⌜Universe.{u, v}⌝ ← TypedExpr.instantiate U.U
      return ⟨U⟩

    def mkInst (U : _Universe) : ⌜Sort $U.v⌝ := ⌜$U.U⌝
    notation "_⌈" U:0 "⌉_" => _Universe.mkInst U

    instance (U : _Universe) : mkHasInstances U.u _⌈U⌉_ := { h := ⌜Universe.instInst _⌝ }

    instance instInst (U : _Universe) : HasInstances _⌈U⌉_ := mkHasInstances.reflect _⌈U⌉_

    def mkInstInst {U : _Universe} (A : _⌈U⌉_) : ⌜Sort $U.u⌝ := mkHasInstances.mkInst A
    notation "_⌈" A:0 "⌉" => _Universe.mkInstInst A

    def reflect (U : _Universe) := exprUniverse (λ A : _⌈U⌉_ => ⟨_⌈A⌉⟩)
    instance : Coe _Universe Universe := ⟨reflect⟩

    def mkFreshTypeMVar {U : _Universe} : MetaM _⌈U⌉_ := TypedExpr.mkFreshMVar
    def mkFreshInstMVar {U : _Universe} {A : _⌈U⌉_} : MetaM A := TypedExpr.mkFreshMVar (α := _⌈A⌉)

    def instantiateTypeMVars {U : _Universe} : _⌈U⌉_ → MetaM _⌈U⌉_ := TypedExpr.instantiate
    def instantiateInstMVars {U : _Universe} {A : _⌈U⌉_} : A → MetaM A := TypedExpr.instantiate (α := _⌈A⌉)

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

    instance : IsEquivalence (reflectR α V) := _MetaRelation.mkIsEquivalence.reflect (mkR α V)

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

    @[reducible] def _Equiv {A : _⌈U⌉_} (a b : _⌈A⌉) : _⌈IU⌉_ :=
    let _ := h.h
    ⌜$a ≃ $b⌝
    infix:25 " _≃ " => mkHasInstanceEquivalences._Equiv

    instance hasEquivalenceRelation (A : _⌈U⌉_) : HasEquivalenceRelation A type :=
    mkHasEquivalenceRelation.reflect _⌈A⌉ IU

    instance reflect : HasInstanceEquivalences U type := ⟨hasEquivalenceRelation⟩

    @[reducible] def __Equiv {A : _⌈U⌉_} (a b : A) : type := a ≃ b
    infix:25 " _≃_ " => mkHasInstanceEquivalences.__Equiv

  end mkHasInstanceEquivalences



  def mkHasIdentity'' {u v : Level} (U : ⌜Universe.{u, v}⌝) (iu iuv : Level) :=
  ⌜HasIdentity.{u, iu, v, iuv} $U⌝

  def mkHasIdentity' (U : _Universe) (iu iuv : Level) : ClassExpr :=
  ⟨mkHasIdentity'' U.U iu iuv⟩

  class mkHasIdentity (U : _Universe) where
  (iu iuv : Level)
  [h      : mkHasIdentity' U iu iuv]

  namespace mkHasIdentity

    def synthesize {U : _Universe} : MetaM (mkHasIdentity U) := do
      return { iu  := ← mkFreshLevelMVar,
               iuv := ← mkFreshLevelMVar,
               h   := ← ClassExpr.synthesize }

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

    def synthesize {U V UV : _Universe} : MetaM (mkHasFunctors U V UV) := do
      return { toInstanceExpr := ← ClassExpr.synthesize }

    def mkFun {u_U v_U u_V v_V u_UV v_UV : Level} {U : ⌜Universe.{u_U, v_U}⌝}
              {V : ⌜Universe.{u_V, v_V}⌝} {UV : ⌜Universe.{u_UV, v_UV}⌝}
              (h : mkHasFunctors'' U V UV) (A : Q($U)) (B : Q($V)) : Q($UV) :=
    ⌜$A ⟶ $B⌝

    @[reducible] def mkFunInst {u_U v_U u_V v_V u_UV v_UV : Level} {U : ⌜Universe.{u_U, v_U}⌝}
                               {V : ⌜Universe.{u_V, v_V}⌝} {UV : ⌜Universe.{u_UV, v_UV}⌝}
                               (h : mkHasFunctors'' U V UV) (A : Q($U)) (B : Q($V)) :=
    Q($A ⟶ $B)

    def mkApplyFn {u_U v_U u_V v_V u_UV v_UV : Level} {U : ⌜Universe.{u_U, v_U}⌝}
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

    variable {U V UV : _Universe} [h : mkHasFunctors U V UV]

    instance reflect : HasFunctors U V UV :=
    { Fun   := mkFun h.h,
      apply := λ {A B} => mkApply h.h A B }

    @[reducible] def _Fun (A : _⌈U⌉_) (B : _⌈V⌉_) : _⌈UV⌉_ := HasFunctors.Fun (U := U) (V := V) A B
    infixr:20 " _⟶ " => mkHasFunctors._Fun

    instance (A : _⌈U⌉_) (B : _⌈V⌉_) : CoeFun (A _⟶ B) (λ _ => A → B) :=
    HasFunctors.coeFun (U := U) (V := V) A B

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
    let F''' : A _⟶{mkApplyFn h.h A B F} B := F''
    F'''

    def mkAppFun {A : _⌈U⌉_} {B : _⌈V⌉_} (F : A _⟶ B) : A _⟶ B :=
    let _ := h.h
    let _ := hId.h.h
    let F' : Q($A ⟶ $B) := F
    ⌜HasFunctors.appFun $F'⌝

    def mkIsFunApp' (A : _⌈U⌉_) {B : _⌈V⌉_} (b : Q($B)) : ClassExpr :=
    let _ := h.h
    let _ := hId.h.h
    ⟨⌜HasFunctors.IsFunApp $A $b⌝⟩

    class mkIsFunApp (A : outParam _⌈U⌉_) {B : _⌈V⌉_} (b : B) extends
    mkIsFunApp' A (B := B) b

    namespace mkIsFunApp

      def mkRefl'' {A : _⌈U⌉_} {B : _⌈V⌉_} (F : A _⟶ B) (a : Q($A)) :=
      let _ := h.h
      let _ := hId.h.h
      let F' : Q($A ⟶ $B) := F
      ⌜HasFunctors.IsFunApp.refl $F' $a⌝

      def mkRefl' {A : _⌈U⌉_} {B : _⌈V⌉_} (F : A _⟶ B) (a : A) {b : B} : mkIsFunApp A b :=
      { h := mkRefl'' F a }

      def mkRefl {A : _⌈U⌉_} {B : _⌈V⌉_} (F : A _⟶ B) (a : A) : mkIsFunApp A (B := B) (F a) :=
      mkRefl' F a

      def synthesize' {A : _⌈U⌉_} {B : _⌈V⌉_} {b : B} : MetaM (mkIsFunApp A b) := do
        -- TODO: Multiple alternatives.
        return { toInstanceExpr := ← ClassExpr.synthesize }

      def synthesize {A : _⌈U⌉_} {B : _⌈V⌉_} {b : B} : MetaM (mkIsFunApp A b) := do
        -- First check whether `b` is literally a function application.
        -- This sees through some definitions that are opaque to type class synthesis.
        let F : (A _⟶ B) ← _Universe.mkFreshInstMVar
        let a : A ← _Universe.mkFreshInstMVar
        if ← isDefEq b (F a) then
          return mkRefl' F a
        -- Next, check if `b` is an application of `fromDefFun`. If it is, pass that to
        -- `IsFunApp` instead of the original value of `b`, as `IsFunApp` is usually
        -- defined on such terms.
        let U' ← _Universe.mkFreshMVar
        let V' ← _Universe.mkFreshMVar
        let hFun_UV' : mkHasFunctors U' V' V := { h := ← TypedExpr.mkFreshMVar }
        let hId_V' : mkHasIdentity V' := { iu := ← mkFreshLevelMVar, iuv := ← mkFreshLevelMVar, h := { h := ← TypedExpr.mkFreshMVar } }
        let A' : _⌈U'⌉_ ← _Universe.mkFreshTypeMVar
        let B' : _⌈V'⌉_ ← _Universe.mkFreshTypeMVar
        let f_b :  ⌜$A' → $B'⌝ ← TypedExpr.mkFreshMVar
        let b' : (A' _⟶{f_b} B') ← TypedExpr.mkFreshMVar
        let b'' : (A' _⟶ B') := mkFromDefFun b'
        if ← isDefEq b b'' then
          let U' ← U'.instantiate
          let V' ← V'.instantiate
          let hFun_UV' : mkHasFunctors U' V' V := { h := ← hFun_UV'.h.instantiate }
          let hId_V' : mkHasIdentity V' := { iu := ← instantiateLevelMVars hId_V'.iu, iuv := ← instantiateLevelMVars hId_V'.iuv, h := { h := ← hId_V'.h.h.instantiate } }
          let A' : _⌈U'⌉_ ← U'.instantiateTypeMVars A'
          let B' : _⌈V'⌉_ ← V'.instantiateTypeMVars B'
          let f_b :  ⌜$A' → $B'⌝ ← f_b.instantiate
          let b' : (A' _⟶{f_b} B') ← b'.instantiate
          -- If it's reducibly defeq to `toDefFun'`, it may have been constructed by
          -- the functoriality algorithm and does not have an `IsFunApp` instance then.
          -- So use the argument of `toDefFun'`.
          let F_B : mkFunInst hFun_UV'.h A' B' ← TypedExpr.mkFreshMVar
          let h_b ← mkFreshExprMVar none
          if ← withReducible (isDefEq b' (mkToDefFun'' hFun_UV'.h hId_V'.h.h A' B' F_B f_b h_b)) then
            let b'' : (A' _⟶ B') ← TypedExpr.instantiate F_B
            let h : mkIsFunApp A (B := B) b'' ← synthesize'
            return { h := h.h }
          let b'' : (A' _⟶ B') := mkFromDefFun b'
          let h : mkIsFunApp A (B := B) b'' ← synthesize'
          return { h := h.h }
        -- Finally, try to synthesize an instance of `IsFunApp` normally.
        synthesize'

      section

        variable (A : _⌈U⌉_) {B : _⌈V⌉_} (b : Q($B)) [hFunApp : mkIsFunApp' A b]

        def mkF := ⌜($hFunApp.h).F⌝
        def mka := ⌜($hFunApp.h).a⌝
        def mke := ⌜($hFunApp.h).e⌝

      end

      def reflect (A : _⌈U⌉_) {B : _⌈V⌉_} (b : B) [h : mkIsFunApp A b] :
          MetaM (HasFunctors.IsFunApp (U := U) (V := V) A b) := do
        let b' : Q($B) := b
        let _ : mkIsFunApp' A b' := h.toInstanceExpr
        let F : A _⟶ B ← TypedExpr.unfold_once (mkF A b')
        let a : A ← TypedExpr.unfold_once (mka A b')
        let e := if ← isDefEq h.h (mkRefl'' F a) then
                   none
                 else
                   some (← TypedExpr.unfold_once (mke A b'))
        return { F := F,
                 a := a,
                 e := e }

    end mkIsFunApp

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

    def mkCongrArg' {U V UV : _Universe} {iu_U iuv_U iu_V iuv_V : Level}
                    (hFun : mkHasFunctors'' U.U V.U UV.U) (hId_U : mkHasIdentity'' U.U iu_U iuv_U)
                    (hId_V : mkHasIdentity'' V.U iu_V iuv_V)
                    (hCongrArg : mkHasCongrArg' U.U V.U UV.U hFun hId_U hId_V)
                    {A : _⌈U⌉_} {B : _⌈V⌉_} (F : Q($A ⟶ $B)) {a₁ a₂ : Q($A)} (h : Q($a₁ ≃ $a₂)) :
      Q($F $a₁ ≃ $F $a₂) :=
    ⌜HasCongrArg.congrArg $F $h⌝

    variable {U V UV : _Universe} [hFun : mkHasFunctors U V UV] [hId_U : mkHasIdentity U]
             [hId_V : mkHasIdentity V] [hCongrArg : mkHasCongrArg U V]

    def mkCongrArg {A : _⌈U⌉_} {B : _⌈V⌉_} (F : A _⟶ B) {a₁ a₂ : A} (h : a₁ _≃_ a₂) : F a₁ _≃_ F a₂ :=
    match h with
    | some h' =>
      some (mkCongrArg' hFun.h hId_U.h.h hId_V.h.h hCongrArg.h (A := A) (B := B) F (a₁ := a₁) (a₂ := a₂) h')
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

    def mkCongrFun' {U V UV : _Universe} {iu_V iuv_V iu_UV iuv_UV : Level}
                    (hFun : mkHasFunctors'' U.U V.U UV.U) (hId_V : mkHasIdentity'' V.U iu_V iuv_V)
                    (hId_UV : mkHasIdentity'' UV.U iu_UV iuv_UV)
                    (hCongrFun : mkHasCongrFun' U.U V.U UV.U hFun hId_V hId_UV)
                    {A : _⌈U⌉_} {B : _⌈V⌉_} {F₁ F₂ : Q($A ⟶ $B)} (h : Q($F₁ ≃ $F₂)) (a : Q($A)) :
      Q($F₁ $a ≃ $F₂ $a) :=
    ⌜HasCongrFun.congrFun $h $a⌝

    variable {U V UV : _Universe} [hFun : mkHasFunctors U V UV] [hId_V : mkHasIdentity V]
             [hId_UV : mkHasIdentity UV] [hCongrFun : mkHasCongrFun U V]

    def mkCongrFun {A : _⌈U⌉_} {B : _⌈V⌉_} {F₁ F₂ : A _⟶ B} (h : F₁ _≃_ F₂) (a : A) : F₁ a _≃_ F₂ a :=
    match h with
    | some h' => 
      some (mkCongrFun' hFun.h hId_V.h.h hId_UV.h.h hCongrFun.h (A := A) (B := B) (F₁ := F₁) (F₂ := F₂) h' a)
    | none =>
      none

    instance reflect : HasCongrFun U V := ⟨mkCongrFun⟩

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
  
    def mkConstFun (A : _⌈U⌉_) {B : _⌈V⌉_} (b : Q($B)) : A _⟶ B :=
    let _ := h.h
    ⌜HasConstFun.constFun $A $b⌝

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

    def mkDefRevAppFun {A : _⌈U⌉_} (a : Q($A)) (B : _⌈U⌉_) : (A _⟶ B) _⟶{⌜λ F => F $a⌝} B :=
    let _ := h.h
    ⌜HasRevAppFun.defRevAppFun $a $B⌝
  
    def mkRevAppFun {A : _⌈U⌉_} (a : Q($A)) (B : _⌈U⌉_) : (A _⟶ B)_⟶ B :=
    let _ := h.h
    ⌜HasRevAppFun.revAppFun $a $B⌝

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

    def mkDefCompFun {A : _⌈U⌉_} {B : _⌈V⌉_} {C : _⌈W⌉_}
                     (F : mkHasFunctors.mkFunInst hFun_UV.h A B)
                     (G : mkHasFunctors.mkFunInst hFun_VW.h B C) :
      A _⟶{⌜λ a => $G ($F a)⌝} C :=
    let _ := h.h
    ⌜HasCompFun.defCompFun $F $G⌝
  
    def mkCompFun {A : _⌈U⌉_} {B : _⌈V⌉_} {C : _⌈W⌉_}
                  (F : mkHasFunctors.mkFunInst hFun_UV.h A B)
                  (G : mkHasFunctors.mkFunInst hFun_VW.h B C) :
      A _⟶ C :=
    let _ := h.h
    ⌜HasCompFun.compFun $F $G⌝

    instance reflect : HasCompFun U V W :=
    ⟨λ {A B C} F G => mkHasFunctors.mkDefFun.reflect'
                        (mkDefCompFun (U := U) (V := V) (W := W) (A := A) (B := B) (C := C) F G)
                        (mkCompFun    (U := U) (V := V) (W := W) (A := A) (B := B) (C := C) F G)⟩

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

    def mkDefSwapFun {A : _⌈U⌉_} {B : _⌈V⌉_} {C : _⌈W⌉_}
                     (F : mkHasFunctors.mkFunInst hFun_UVW.h A (B _⟶ C))
                     (b : Q($B)) :
      A _⟶{⌜λ a => $F a $b⌝} C :=
    let _ := h.h
    ⌜HasSwapFun.defSwapFun $F $b⌝
  
    def mkSwapFun {A : _⌈U⌉_} {B : _⌈V⌉_} {C : _⌈W⌉_}
                  (F : mkHasFunctors.mkFunInst hFun_UVW.h A (B _⟶ C))
                  (b : Q($B)) :
      A _⟶ C :=
    let _ := h.h
    ⌜HasSwapFun.swapFun $F $b⌝

    instance reflect : HasSwapFun U V W :=
    ⟨λ {A B C} F G => mkHasFunctors.mkDefFun.reflect'
                        (mkDefSwapFun (U := U) (V := V) (W := W) (A := A) (B := B) (C := C) F G)
                        (mkSwapFun    (U := U) (V := V) (W := W) (A := A) (B := B) (C := C) F G)⟩

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

    def mkDefDupFun {A : _⌈U⌉_} {B : _⌈V⌉_} (F : mkHasFunctors.mkFunInst hFun_UUV.h A (A _⟶ B)) :
      A _⟶{⌜λ a => $F a a⌝} B :=
    let _ := h.h
    ⌜HasDupFun.defDupFun $F⌝
  
    def mkDupFun {A : _⌈U⌉_} {B : _⌈V⌉_} (F : mkHasFunctors.mkFunInst hFun_UUV.h A (A _⟶ B)) :
      A _⟶ B :=
    let _ := h.h
    ⌜HasDupFun.dupFun $F⌝

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

    def mkDefSubstFun {A : _⌈U⌉_} {B : _⌈V⌉_} {C : _⌈W⌉_}
                      (F : mkHasFunctors.mkFunInst hFun_UV.h A B)
                      (G : mkHasFunctors.mkFunInst hFun_UVW.h A (B _⟶ C)) :
      A _⟶{⌜λ a => $G a ($F a)⌝} C :=
    let _ := h.h
    ⌜HasSubstFun.defSubstFun $F $G⌝
  
    def mkSubstFun {A : _⌈U⌉_} {B : _⌈V⌉_} {C : _⌈W⌉_}
                   (F : mkHasFunctors.mkFunInst hFun_UV.h A B)
                   (G : mkHasFunctors.mkFunInst hFun_UVW.h A (B _⟶ C)) :
      A _⟶ C :=
    let _ := h.h
    ⌜HasSubstFun.substFun $F $G⌝

    instance reflect : HasSubstFun U V W :=
    ⟨λ {A B C} F G => mkHasFunctors.mkDefFun.reflect'
                        (mkDefSubstFun (U := U) (V := V) (W := W) (A := A) (B := B) (C := C) F G)
                        (mkSubstFun    (U := U) (V := V) (W := W) (A := A) (B := B) (C := C) F G)⟩

  end mkHasSubstFun

end Lean
