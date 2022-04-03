import UniverseAbstractions.Instances.Setoid
import UniverseAbstractions.CategoryTheory.Meta
import UniverseAbstractions.CategoryTheory.Basic
import UniverseAbstractions.CategoryTheory.Functors
import UniverseAbstractions.CategoryTheory.NaturalTransformations
import UniverseAbstractions.CategoryTheory.Functors.Basic
import UniverseAbstractions.CategoryTheory.Functors.Nested
import UniverseAbstractions.CategoryTheory.FunctorExtensionality
import UniverseAbstractions.CategoryTheory.Utils.Trivial



set_option autoBoundImplicitLocal false
set_option synthInstance.maxHeartbeats 1000
--set_option pp.universes true

universe u v w



namespace Setoid.IsHomUniverse

  open MetaRelation CategoryTheory

  abbrev homUniv := tuniv.{max u w}

  instance isHomUniverse : IsHomUniverse homUniv.{u, w} := ⟨⟩

  -- This is defeq to `tuniv.{u}` but solves some universe unification issues.
  abbrev tuniv' := homUniv.{u, 0}

  -- We need to copy `IsPreorderEq` and similar classes because we need them as `Prop`.
  structure CatDescEquiv {U : Universe.{u}} {R : BundledRelation U homUniv.{u, w}}
                         (C D : CatDesc R) :
    Prop where
  (reflEq (a : R.A) : C.homIsPreorder.refl a ≈ D.homIsPreorder.refl a)
  (transEq {a b c : R.A} (f : R.Hom a b) (g : R.Hom b c) :
     C.homIsPreorder.trans f g ≈ D.homIsPreorder.trans f g)

  instance catDescSetoid {U : Universe.{u}} (R : BundledRelation U homUniv.{u, w}) :
    Setoid.{max 1 u w} (CatDesc R) :=
  { r     := CatDescEquiv,
    iseqv := { refl  := λ C   => ⟨λ a   => Setoid.refl  (C.homIsPreorder.refl  a),
                                  λ f g => Setoid.refl  (C.homIsPreorder.trans f g)⟩,
               symm  := λ h   => ⟨λ a   => Setoid.symm  (h.reflEq  a),
                                  λ f g => Setoid.symm  (h.transEq f g)⟩,
               trans := λ h i => ⟨λ a   => Setoid.trans (h.reflEq  a)   (i.reflEq  a),
                                  λ f g => Setoid.trans (h.transEq f g) (i.transEq f g)⟩ } }

  def CatProp (U : Universe.{u}) :
    MetaProperty (BundledRelation U homUniv.{u, w}) homUniv.{u, w} :=
  λ R => { a    := CatDesc       R,
           inst := catDescSetoid R }

  instance hasCat (U : Universe.{u}) : HasCatProp U homUniv.{u, w} :=
  { Cat  := CatProp U,
    desc := id }

  @[reducible] def Cat (U : Universe.{u}) := HasCatProp.Category U homUniv.{u, w}
  @[reducible] def Cat' (U : Universe.{u}) := HasCatProp.Category U tuniv'.{u}

  def defCat {U : Universe.{u}} {R : BundledRelation U homUniv.{u, w}} (C : CatDesc R) :
    HasCatProp.DefCat C :=
  { C   := C,
    hEq := IsPreorderEq.refl R.Hom (hR := C.homIsPreorder) }

  instance hasTrivialCatProp (U : Universe.{u}) : HasCatProp.HasTrivialCatProp U homUniv.{u, w} :=
  ⟨defCat⟩

  section

    variable {U : Universe.{u}}

    instance isoDescSetoid {A : Cat.{u, w} U} (a b : A) : Setoid.{max 1 u w} (IsoDesc a b) :=
    lift (inst (a ⇾ b)) IsoDesc.toHom

    def IsoRel (A : Cat.{u, w} U) : MetaRelation A homUniv.{u, w} :=
    λ a b => { a    := IsoDesc       a b,
               inst := isoDescSetoid a b }

    instance hasIsoRel (A : Cat.{u, w} U) : HasIsoRel A :=
    { Iso         := IsoRel A,
      desc        := id,
      defToHomFun := λ _ _ => Setoid.defFun id,
      toHomInj    := id }

    def defIso {A : Cat.{u, w} U} {a b : A} (e : IsoDesc a b) : HasIsoRel.DefIso e :=
    { e    := e,
      toEq := Setoid.refl e }

    instance hasTrivialIsomorphismCondition (A : Cat.{u, w} U) :
      HasIsoRel.HasTrivialIsomorphismCondition A :=
    ⟨defIso⟩

    instance isoIsEquivalence (A : Cat.{u, w} U) : IsEquivalence (IsoRel A) :=
    HasIsoOp.isoIsEquivalence A

    -- Lean bug :-(
    noncomputable instance hasIsomorphisms (A : Cat.{u, w} U) : HasIsomorphisms A :=
    { isoHasSymmFun  := ⟨λ _ _   => Setoid.defFun (λ h => IsoDesc.toInvEquiv h)⟩,
      isoHasTransFun := ⟨λ _ _ _ => ⟨λ e => Setoid.defFun (λ h => HasTransFun.congrArgTransLeft e.toHom h),
                                     Setoid.defFun (λ h f => HasTransFun.congrArgTransRight (R := A.Hom) h f.toHom)⟩⟩,
      defIsoCat      := HasCatProp.HasTrivialCatProp.defCat }

  end

  noncomputable instance isCatUniverse (U : Universe.{u}) : IsCatUniverse U homUniv.{u, w} := ⟨⟩
  noncomputable instance isSortCatUniverse : IsSortCatUniverse.{u} homUniv.{u, w} := ⟨⟩

  -- Functors

  section

    variable {U V : Universe.{u}}

    instance funDescSetoid {A : Cat.{u, w} U} {B : Cat.{u, w} V} (φ : A → B) :
      Setoid.{max 1 u w} (FunDesc φ) :=
    lift (biFunctionSetoid (λ a b => (a ⇾ b) ⟶ (φ a ⇾ φ b))) (λ F => F.F.baseFun)

    def FunProp (A : Cat.{u, w} U) (B : Cat.{u, w} V) : MetaProperty (A → B) homUniv.{u, w} :=
    λ φ => { a    := FunDesc       φ,
             inst := funDescSetoid φ }

    instance hasFunProp (A : Cat.{u, w} U) (B : Cat.{u, w} V) : HasFunProp A B :=
    { Fun  := FunProp A B,
      desc := id }

    def defFun {A : Cat.{u, w} U} {B : Cat.{u, w} V} {φ : A → B} (F : FunDesc φ) :
      HasFunProp.DefFun F :=
    { F  := F,
      eq := λ a b => Setoid.refl (F.F.baseFun a b) }

    instance hasTrivialFunctorialityCondition (A : Cat.{u, w} U) (B : Cat.{u, w} V) :
      HasFunProp.HasTrivialFunctorialityCondition A B :=
    ⟨defFun⟩

    noncomputable instance hasIsoFun {A : Cat.{u, w} U} {B : Cat.{u, w} V} (F : A ⮕ B) :
      HasIsoFun F :=
    { defMapIso    := λ _   => HasIsoRel.HasTrivialIsomorphismCondition.defIso,
      defMapIsoFun := λ _ _ => Setoid.defFun (HasFunProp.Functor.mapHom.congrArg F),
      defIsoFun    := HasFunProp.HasTrivialFunctorialityCondition.defFun }

  end

  instance hasIdFun {U : Universe.{u}} (A : Cat.{u, w} U) : HasFunProp.HasIdFun A :=
  HasFunProp.HasIdFun.trivial A

  instance hasConstFun {U V : Universe.{u}} (A : Cat.{u, w} U) (B : Cat.{u, w} V) :
    HasFunProp.HasConstFun A B :=
  HasFunProp.HasConstFun.trivial A B

  instance hasCompFun {U U' U'' : Universe.{u}}
                      (A : Cat.{u, w} U) (B : Cat.{u, w} U') (C : Cat.{u, w} U'') :
    HasFunProp.HasCompFun A B C :=
  HasFunProp.HasCompFun.trivial A B C

  noncomputable instance isFunUniverse (U V : Universe.{u}) : IsFunUniverse U V homUniv.{u, w} := ⟨⟩

  noncomputable instance isSortFunUniverse : IsSortFunUniverse.{u} homUniv.{u, w} := ⟨⟩

  instance isFunUniverse.hasCatIdFun (U : Universe.{u}) :
    IsFunUniverse.HasCatIdFun U homUniv.{u, w} :=
  ⟨⟩

  instance isFunUniverse.hasCatConstFun (U V : Universe.{u}) :
    IsFunUniverse.HasCatConstFun U V homUniv.{u, w} :=
  ⟨⟩

  instance isFunUniverse.hasCatCompFun (U U' U'' : Universe.{u}) :
    IsFunUniverse.HasCatCompFun U U' U'' homUniv.{u, w} :=
  ⟨⟩

  -- Natural transformations

  section

    variable {U V : Universe.{u}}

    instance natDescSetoid {A : Cat.{u, w} U} {B : Cat.{u, w} V} (F G : A ⮕ B) :
      Setoid.{max 1 u w} (NatDesc F G) :=
    lift (functionSetoid (λ a => F a ⇾ G a)) NatDesc.η

    def NatRel (A : Cat.{u, w} U) (B : Cat.{u, w} V) : MetaRelation (A ⮕ B) homUniv.{u, w} :=
    λ F G => { a    := NatDesc       F G,
               inst := natDescSetoid F G }

    instance hasNaturalityRelation (A : Cat.{u, w} U) (B : Cat.{u, w} V) : HasNatRel A B :=
    { Nat       := NatRel A B,
      desc      := id,
      defNatFun := λ _ _ a => Setoid.defFun (λ h => h a) }

    def defNat {A : Cat.{u, w} U} {B : Cat.{u, w} V} {F G : A ⮕ B} (η : NatDesc F G) :
      HasNatRel.DefNat η :=
    { η     := η,
      natEq := λ a => Setoid.refl (η.η a) }

    instance hasTrivialNaturalityCondition (A : Cat.{u, w} U) (B : Cat.{u, w} V) :
      HasNatRel.HasTrivialNaturalityCondition A B :=
    ⟨defNat⟩

    instance hasTrivialNatEquiv (A : Cat.{u, w} U) (B : Cat.{u, w} V) :
      HasNatRel.HasTrivialNatEquiv A B :=
    ⟨λ _ _ => id⟩

    instance natIsPreorder (A : Cat.{u, w} U) (B : Cat.{u, w} V) : IsPreorder (NatRel A B) :=
    HasNatOp.natIsPreorder A B

  end

  section

    -- TODO: Shouldn't `max 1 u` also work?
    variable {U V : Universe.{u + 1}}

    noncomputable instance hasNaturality (A : Cat' U) (B : Cat' V) : HasNaturality A B :=
    { natHasTransFun := ⟨λ _ _ _ => ⟨λ η => Setoid.defFun (λ {ε₁ ε₂} h a => have h₁ : ⌈ε₁.η a ≃ ε₂.η a⌉ := h a;
                                                                            HasTransFun.congrArgTransLeft (η.η a) h₁),
                                     Setoid.defFun (λ {η₁ η₂} h ε a => have h₂ : ⌈η₁.η a ≃ η₂.η a⌉ := h a;
                                                                       HasTransFun.congrArgTransRight h₂ (ε.η a))⟩⟩,
      defFunCat      := HasCatProp.HasTrivialCatProp.defCat }

    noncomputable instance hasIsoNat {A : Cat' U} {B : Cat' V} (F G : A ⮕' B) : HasIsoNat F G :=
    { defNatIso    := λ _ _ => HasIsoRel.HasTrivialIsomorphismCondition.defIso,
      defNatIsoFun := λ a   => Setoid.defFun (λ h => HasNatRel.nat.congrArg h a) }

    noncomputable instance hasIsoNaturality (A : Cat' U) (B : Cat' V) : HasIsoNaturality A B := ⟨⟩

    noncomputable def natIsoDescBuilder {A : Cat' U} {B : Cat' V}  {F G : A ⮕ B} (η : NatIsoDesc F G) :
      NatIsoDesc.IsoDescBuilder η :=
    { defToNat  := HasNatRel.HasTrivialNaturalityCondition.defNat,
      defInvNat := HasNatRel.HasTrivialNaturalityCondition.defNat,
      leftInv   := HasNatRel.HasTrivialNatEquiv.natEquiv,
      rightInv  := HasNatRel.HasTrivialNatEquiv.natEquiv }

    noncomputable def defNatIso {A : Cat' U} {B : Cat' V}  {F G : A ⮕' B} (η : NatIsoDesc F G) :
      HasIsoNat.DefNatIso η :=
    { η     := NatIsoDesc.IsoDescBuilder.isoDesc η (natIsoDescBuilder η),
      natEq := λ a => Setoid.refl (η.η a) }

    noncomputable instance hasTrivialIsoNaturalityCondition (A : Cat' U) (B : Cat' V) :
      HasIsoNaturality.HasTrivialIsoNaturalityCondition A B :=
    ⟨defNatIso⟩

  end

  noncomputable instance isNatUniverse (U V : Universe.{u + 1}) : IsNatUniverse U V tuniv'.{u + 1} :=
  ⟨⟩

  noncomputable instance isSortNatUniverse : IsSortNatUniverse.{u + 1} tuniv'.{u + 1} := ⟨⟩

  noncomputable instance isSortNatUniverse.hasTrivialNaturalIsomorphisms :
    IsSortNatUniverse.HasTrivialNaturalIsomorphisms.{u + 1} tuniv'.{u + 1} :=
  ⟨⟩

  -- Multifunctors

  section

    variable {U U' U'' : Universe.{u + 1}} {A : Cat' U} {B : Cat' U'} {C : Cat' U''}
             {F : A → (B ⮕ C)} {desc : HasNaturality.FunFunDesc F}

    noncomputable def defFunFunBase : HasNaturality.DefFunFunBase desc :=
    { defNat     := λ _     => HasNatRel.HasTrivialNaturalityCondition.defNat,
      defNatFun  := λ a₁ a₂ => Setoid.defFun (λ h b => HasCongrArg.defCongrArg (desc.defNatDescFun a₁ a₂ b) h),
      natReflEq  := λ _     => HasNatRel.HasTrivialNatEquiv.natEquiv,
      natTransEq := λ _ _   => HasNatRel.HasTrivialNatEquiv.natEquiv }

    noncomputable def defFunFun : HasNaturality.DefFunFun desc :=
    HasNaturality.DefFunFun.trivial defFunFunBase

  end

  section

    variable {U U' U'' U''' : Universe.{u + 1}} 
             {A : Cat' U} {B : Cat' U'} {C : Cat' U''} {D : Cat' U'''}
             {F : A → (B ⮕ C ⮕' D)} {desc : HasNaturality.FunFunFunDesc F}

    noncomputable def defFunFunFunBase : HasNaturality.DefFunFunFunBase desc :=
    { defRevFunFun := λ _ => defFunFunBase,
      defNatNat    := λ _ => HasNaturality.DefNatNatBase.trivial }

    noncomputable def defFunFunFun : HasNaturality.DefFunFunFun desc :=
    HasNaturality.DefFunFunFun.trivial defFunFunFunBase defFunFunBase

  end

  noncomputable instance hasRevAppFunFun {U V : Universe.{u + 1}} (A : Cat' U) (B : Cat' V) :
    HasNaturality.HasRevAppFunFun A B :=
  { defRevAppFun    := λ _ => HasFunProp.HasTrivialFunctorialityCondition.defFun,
    defRevAppFunFun := defFunFun }

  noncomputable instance hasCompFunFunFun {U U' U'' : Universe.{u + 1}}
                                          (A : Cat' U) (B : Cat' U') (C : Cat' U'') :
    HasNaturality.HasCompFunFunFun A B C :=
  { defCompFunFun    := λ _ => defFunFun,
    defCompFunFunFun := defFunFunFun }

  noncomputable instance hasConstFunFun {U V : Universe.{u + 1}} (A : Cat' U) (B : Cat' V) :
    HasNaturality.HasConstFunFun A B :=
  { defConstFunFun := defFunFun }

  noncomputable instance hasDupFunFun {U V : Universe.{u + 1}} (A : Cat' U) (B : Cat' V) :
    HasNaturality.HasDupFunFun A B :=
  { defDupFun    := λ _ => HasFunProp.HasTrivialFunctorialityCondition.defFun,
    defDupFunFun := defFunFun }

  noncomputable instance isSortNatUniverse.hasFullCatFun :
    IsSortNatUniverse.HasFullCatFun.{u + 1} tuniv'.{u + 1} :=
  { hasRevAppFunFun  := hasRevAppFunFun,
    hasCompFunFunFun := hasCompFunFunFun,
    hasConstFunFun   := hasConstFunFun,
    hasDupFunFun     := hasDupFunFun }

  noncomputable instance isSortNatUniverse.hasFullNatIso :
    IsSortNatUniverse.HasFullNatIso.{u + 1} tuniv'.{u + 1} :=
  inferInstance

end Setoid.IsHomUniverse
