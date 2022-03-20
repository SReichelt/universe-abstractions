import UniverseAbstractions.Instances.Sort
import UniverseAbstractions.CategoryTheory.Meta
import UniverseAbstractions.CategoryTheory.Basic
import UniverseAbstractions.CategoryTheory.Functors
import UniverseAbstractions.CategoryTheory.NaturalTransformations
import UniverseAbstractions.CategoryTheory.Functors.Basic
import UniverseAbstractions.CategoryTheory.Functors.Nested
import UniverseAbstractions.CategoryTheory.FunctorExtensionality
import UniverseAbstractions.CategoryTheory.Utils.Trivial



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w



-- This establishes the universe `type.{u}` as a morphism universe, which enables the construction
-- of categories with morphisms in `type`, i.e. regular 1-categories.
--
-- Due to the way functors are defined mathematically, the morphism universe always needs to be at
-- least as large as the universe of the domain, as it needs to hold natural transformation between
-- functors. We need to use some trickery to make Lean behave well with this restriction.

namespace type.IsHomUniverse

  open MetaRelation MetaFunctor CategoryTheory

  instance isHomUniverse : IsHomUniverse type.{u} := ⟨⟩

  abbrev homUniv := type.{max u w}

  -- This is defeq to `type.{u}` but solves some universe unification issues.
  abbrev type' := homUniv.{u, 0}

  instance hasCat (U : Universe.{u + 1}) : HasCatProp U homUniv.{u, w} :=
  { Cat  := CatDesc,
    desc := id }

  @[reducible] def Cat (U : Universe.{u + 1}) := HasCatProp.Category U homUniv.{u, w}
  @[reducible] def Cat' (U : Universe.{u + 1}) := HasCatProp.Category U type'.{u}

  def defCat {U : Universe.{u + 1}} {R : BundledRelation U homUniv.{u, w}} (C : CatDesc R) :
    HasCatProp.DefCat C :=
  { C   := C,
    hEq := IsPreorderEq.refl R.Hom (hR := C.homIsPreorder) }

  instance hasTrivialCatProp (U : Universe.{u + 1}) : HasCatProp.HasTrivialCatProp U homUniv.{u, w} :=
  ⟨defCat⟩

  theorem IsInv.ext {α : Sort u} {R : MetaRelation α type.{w}} [IsPreorder R]
                    {a b : α} {f : R a b} {g : R b a} (h₁ h₂ : IsInv (R := R) f g) :
    h₁ = h₂ :=
  match h₁, h₂ with
  | ⟨_, _⟩, ⟨_, _⟩ => rfl

  section

    variable {U : Universe.{u + 1}}

    theorem IsoDesc.ext {A : Cat.{u, w} U} {a b : A} {e₁ e₂ : IsoDesc a b} :
      e₁.toHom = e₂.toHom → e₁.invHom = e₂.invHom → e₁ = e₂ :=
    match e₁, e₂ with
    | { toHom := to₁, invHom := inv₁, isInv := isInv₁ },
      { toHom := to₂, invHom := inv₂, isInv := isInv₂ } =>
      λ (hTo : to₁ = to₂) (hInv : inv₁ = inv₂) => by subst hTo; subst hInv;
                                                     have invExt := IsInv.ext isInv₁ isInv₂;
                                                     subst invExt;
                                                     rfl

    theorem IsoDesc.ext' {A : Cat.{u, w} U} {a b : A} {e₁ e₂ : IsoDesc a b}
                         (h : e₁.toHom = e₂.toHom) :
      e₁ = e₂ :=
    IsoDesc.ext h (IsoDesc.toInvEquiv (e₁ := e₁) (e₂ := e₂) h)

    def IsoRel (A : Cat.{u, w} U) : MetaRelation A homUniv.{u, w} := IsoDesc

    instance hasIsoRel (A : Cat.{u, w} U) : HasIsoRel A :=
    { Iso         := IsoRel A,
      desc        := id,
      defToHomFun := λ _ _ => HasTrivialFunctoriality.defFun,
      toHomInj    := IsoDesc.ext' }

    def defIso {A : Cat.{u, w} U} {a b : A} (e : IsoDesc a b) : HasIsoRel.DefIso e :=
    { e    := e,
      toEq := rfl }

    instance hasTrivialIsomorphismCondition (A : Cat.{u, w} U) :
      HasIsoRel.HasTrivialIsomorphismCondition A :=
    ⟨defIso⟩

    instance isoIsEquivalence (A : Cat.{u, w} U) : IsEquivalence (IsoRel A) :=
    HasIsoOp.isoIsEquivalence A

    instance hasIsomorphisms (A : Cat.{u, w} U) : HasIsomorphisms A :=
    { isoHasSymmFun  := HasTrivialFunctoriality.hasSymmFun  (IsoRel A),
      isoHasTransFun := HasTrivialFunctoriality.hasTransFun (IsoRel A),
      defIsoCat      := HasCatProp.HasTrivialCatProp.defCat }

  end

  instance isCatUniverse (U : Universe.{u + 1}) : IsCatUniverse U homUniv.{u, w} := ⟨⟩
  instance isSortCatUniverse : IsSortCatUniverse.{u + 1} homUniv.{u, w} := ⟨⟩

  -- Functors

  section

    -- It should be possible for `U` and `V` to have different Lean universes. Unfortunately, that
    -- breaks all of the universe inference that we get from `homUniv`.
    variable {U V : Universe.{u + 1}}

    def FunProp (A : Cat.{u, w} U) (B : Cat.{u, w} V) : MetaProperty (A → B) homUniv.{u, w} :=
    FunDesc

    instance hasFunProp (A : Cat.{u, w} U) (B : Cat.{u, w} V) : HasFunProp A B :=
    { Fun  := FunProp A B,
      desc := id }

    def defFun {A : Cat.{u, w} U} {B : Cat.{u, w} V} {φ : A → B} (F : FunDesc φ) :
      HasFunProp.DefFun F :=
    { F  := F,
      eq := λ _ _ => rfl }

    instance hasTrivialFunctorialityCondition (A : Cat.{u, w} U) (B : Cat.{u, w} V) :
      HasFunProp.HasTrivialFunctorialityCondition A B :=
    ⟨defFun⟩

    -- Lean bug :-(
    noncomputable instance hasIsoFun {A : Cat.{u, w} U} {B : Cat.{u, w} V} (F : A ⮕ B) :
      HasIsoFun F :=
    { defMapIso    := λ _   => HasIsoRel.HasTrivialIsomorphismCondition.defIso,
      defMapIsoFun := λ _ _ => HasTrivialFunctoriality.defFun,
      defIsoFun    := HasFunProp.HasTrivialFunctorialityCondition.defFun }

  end

  instance hasIdFun {U : Universe.{u + 1}} (A : Cat.{u, w} U) : HasFunProp.HasIdFun A :=
  HasFunProp.HasIdFun.trivial A

  instance hasConstFun {U V : Universe.{u + 1}} (A : Cat.{u, w} U) (B : Cat.{u, w} V) :
    HasFunProp.HasConstFun A B :=
  HasFunProp.HasConstFun.trivial A B

  instance hasCompFun {U U' U'' : Universe.{u + 1}}
                      (A : Cat.{u, w} U) (B : Cat.{u, w} U') (C : Cat.{u, w} U'') :
    HasFunProp.HasCompFun A B C :=
  HasFunProp.HasCompFun.trivial A B C

  noncomputable instance isFunUniverse (U V : Universe.{u + 1}) :
    IsFunUniverse U V homUniv.{u, w} :=
  ⟨⟩

  noncomputable instance isSortFunUniverse : IsSortFunUniverse.{u + 1} homUniv.{u, w} := ⟨⟩

  instance isFunUniverse.hasCatIdFun (U : Universe.{u + 1}) :
    IsFunUniverse.HasCatIdFun U homUniv.{u, w} :=
  ⟨⟩

  instance isFunUniverse.hasCatConstFun (U V : Universe.{u + 1}) :
    IsFunUniverse.HasCatConstFun U V homUniv.{u, w} :=
  ⟨⟩

  instance isFunUniverse.hasCatCompFun (U U' U'' : Universe.{u + 1}) :
    IsFunUniverse.HasCatCompFun U U' U'' homUniv.{u, w} :=
  ⟨⟩

  -- Natural transformations

  theorem IsNatural.ext {α : Sort u} {β : Sort v}
                        {R : MetaRelation α type.{w}} {S : MetaRelation β type.{w}}
                        [HasTrans S] {φ ψ : α → β} {F : PreFunctor R S φ} {G : PreFunctor R S ψ}
                        (η : MetaQuantification S φ ψ) (h₁ h₂ : MetaQuantification.IsNatural F G η) :
    h₁ = h₂ :=
  match h₁, h₂ with
  | ⟨_⟩, ⟨_⟩ => rfl

  section

    variable {U V : Universe.{u + 1}}

    theorem NatDesc.ext {A : Cat.{u, w} U} {B : Cat.{u, w} V} {F G : A ⮕ B} (η₁ η₂ : NatDesc F G) :
      (∀ a, η₁.η a = η₂.η a) → η₁ = η₂ :=
    match η₁, η₂ with
    | { η := nat₁, isNat := isNat₁ }, { η := nat₂, isNat := isNat₂ } =>
      λ h => by have hNat : nat₁ = nat₂ := funext h;
                subst hNat;
                have hIsNat : isNat₁ = isNat₂ := IsNatural.ext nat₁ isNat₁ isNat₂;
                subst hIsNat;
                rfl

    def NatRel (A : Cat.{u, w} U) (B : Cat.{u, w} V) : MetaRelation (A ⮕ B) homUniv.{u, w} :=
    NatDesc

    instance hasNaturalityRelation (A : Cat.{u, w} U) (B : Cat.{u, w} V) : HasNatRel A B :=
    { Nat       := NatRel A B,
      desc      := id,
      defNatFun := λ _ _ _ => HasTrivialFunctoriality.defFun }

    def defNat {A : Cat.{u, w} U} {B : Cat.{u, w} V} {F G : A ⮕ B} (η : NatDesc F G) :
      HasNatRel.DefNat η :=
    { η     := η,
      natEq := λ _ => rfl }

    instance hasTrivialNaturalityCondition (A : Cat.{u, w} U) (B : Cat.{u, w} V) :
      HasNatRel.HasTrivialNaturalityCondition A B :=
    ⟨defNat⟩

    instance hasTrivialNatEquiv (A : Cat.{u, w} U) (B : Cat.{u, w} V) :
      HasNatRel.HasTrivialNatEquiv A B :=
    ⟨NatDesc.ext⟩

    instance natIsPreorder (A : Cat.{u, w} U) (B : Cat.{u, w} V) : IsPreorder (NatRel A B) :=
    HasNatOp.natIsPreorder A B

    instance hasNaturality (A : Cat' U) (B : Cat' V) : HasNaturality A B :=
    { natHasTransFun := HasTrivialFunctoriality.hasTransFun (NatRel A B),
      defFunCat      := HasCatProp.HasTrivialCatProp.defCat }

    instance hasIsoNat {A : Cat' U} {B : Cat' V} (F G : A ⮕' B) : HasIsoNat F G :=
    { defNatIso    := λ _ _ => HasIsoRel.HasTrivialIsomorphismCondition.defIso,
      defNatIsoFun := λ _   => HasTrivialFunctoriality.defFun }

    noncomputable instance hasIsoNaturality (A : Cat' U) (B : Cat' V) : HasIsoNaturality A B := ⟨⟩

    def natIsoDescBuilder {A : Cat' U} {B : Cat' V} {F G : A ⮕' B} (η : NatIsoDesc F G) :
      NatIsoDesc.IsoDescBuilder η :=
    { defToNat  := HasNatRel.HasTrivialNaturalityCondition.defNat,
      defInvNat := HasNatRel.HasTrivialNaturalityCondition.defNat,
      leftInv   := HasNatRel.HasTrivialNatEquiv.natEquiv,
      rightInv  := HasNatRel.HasTrivialNatEquiv.natEquiv }

    noncomputable def defNatIso {A : Cat' U} {B : Cat' V} {F G : A ⮕' B} (η : NatIsoDesc F G) :
      HasIsoNat.DefNatIso η :=
    { η     := NatIsoDesc.IsoDescBuilder.isoDesc η (natIsoDescBuilder η),
      natEq := λ _ => rfl }

    noncomputable instance hasTrivialIsoNaturalityCondition (A : Cat' U) (B : Cat' V) :
      HasIsoNaturality.HasTrivialIsoNaturalityCondition A B :=
    ⟨defNatIso⟩

  end

  noncomputable instance isNatUniverse (U V : Universe.{u + 1}) : IsNatUniverse U V type'.{u} :=
  ⟨⟩

  noncomputable instance isSortNatUniverse : IsSortNatUniverse.{u + 1} type'.{u} := ⟨⟩

  noncomputable instance isSortNatUniverse.hasTrivialNaturalIsomorphisms :
    IsSortNatUniverse.HasTrivialNaturalIsomorphisms.{u + 1} type'.{u} :=
  ⟨⟩

  -- Multifunctors

  section

    variable {U U' U'' : Universe.{u + 1}} {A : Cat' U} {B : Cat' U'} {C : Cat' U''}
             {F : A → (B ⮕ C)} {desc : HasNaturality.FunFunDesc F}

    def defFunFunBase : HasNaturality.DefFunFunBase desc :=
    { defNat     := λ _   => HasNatRel.HasTrivialNaturalityCondition.defNat,
      defNatFun  := λ _ _ => HasTrivialFunctoriality.defFun,
      natReflEq  := λ _   => HasNatRel.HasTrivialNatEquiv.natEquiv,
      natTransEq := λ _ _ => HasNatRel.HasTrivialNatEquiv.natEquiv }

    def defFunFun : HasNaturality.DefFunFun desc := HasNaturality.DefFunFun.trivial defFunFunBase

  end

  section

    variable {U U' U'' U''' : Universe.{u + 1}} 
             {A : Cat' U} {B : Cat' U'} {C : Cat' U''} {D : Cat' U'''}
             {F : A → (B ⮕ C ⮕' D)} {desc : HasNaturality.FunFunFunDesc F}

    def defFunFunFunBase : HasNaturality.DefFunFunFunBase desc :=
    { defRevFunFun := λ _ => defFunFunBase,
      defNatNat    := λ _ => HasNaturality.DefNatNatBase.trivial }

    def defFunFunFun : HasNaturality.DefFunFunFun desc :=
    HasNaturality.DefFunFunFun.trivial defFunFunFunBase defFunFunBase

  end

  instance hasRevAppFunFun {U V : Universe.{u + 1}} (A : Cat' U) (B : Cat' V) :
    HasNaturality.HasRevAppFunFun A B :=
  { defRevAppFun    := λ _ => HasFunProp.HasTrivialFunctorialityCondition.defFun,
    defRevAppFunFun := defFunFun }

  instance hasCompFunFunFun {U U' U'' : Universe.{u + 1}} (A : Cat' U) (B : Cat' U') (C : Cat' U'') :
    HasNaturality.HasCompFunFunFun A B C :=
  { defCompFunFun    := λ _ => defFunFun,
    defCompFunFunFun := defFunFunFun }

  instance hasConstFunFun {U V : Universe.{u + 1}} (A : Cat' U) (B : Cat' V) :
    HasNaturality.HasConstFunFun A B :=
  { defConstFunFun := defFunFun }

  instance hasDupFunFun {U V : Universe.{u + 1}} (A : Cat' U) (B : Cat' V) :
    HasNaturality.HasDupFunFun A B :=
  { defDupFun    := λ _ => HasFunProp.HasTrivialFunctorialityCondition.defFun,
    defDupFunFun := defFunFun }

  noncomputable instance isSortNatUniverse.hasFullCatFun :
    IsSortNatUniverse.HasFullCatFun.{u + 1} type'.{u} :=
  { hasRevAppFunFun  := hasRevAppFunFun,
    hasCompFunFunFun := hasCompFunFunFun,
    hasConstFunFun   := hasConstFunFun,
    hasDupFunFun     := hasDupFunFun }

  noncomputable instance isSortNatUniverse.hasFullNatIso :
    IsSortNatUniverse.HasFullNatIso.{u + 1} type'.{u} :=
  inferInstance

end type.IsHomUniverse
