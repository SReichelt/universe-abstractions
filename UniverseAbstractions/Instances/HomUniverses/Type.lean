import UniverseAbstractions.Instances.Basic
import UniverseAbstractions.Instances.Utils.TrivialCategoryTheory
import UniverseAbstractions.Axioms.CategoryTheory.Meta
import UniverseAbstractions.Axioms.CategoryTheory.Basic
import UniverseAbstractions.Axioms.CategoryTheory.Functors
import UniverseAbstractions.Axioms.CategoryTheory.NaturalTransformations
import UniverseAbstractions.Axioms.CategoryTheory.Isomorphisms



set_option autoBoundImplicitLocal false
set_option synthInstance.maxHeartbeats 5000
set_option pp.universes true

universe u v w



-- This establishes the universe `type.{w}` as a morphism universe, which enables the construction
-- of categories with morphisms in `type`, i.e. regular 1-categories.
--
-- Due to the way functors are defined mathematically, the morphism universe always needs to be at
-- least as large as the universe of the domain, as it needs to hold natural transformation between
-- functors. We need to use some trickery to make Lean behave well with this restriction.

namespace type

  open MetaRelation MetaFunctor CategoryTheory HasCatProp HasIsoRel

  instance isHomUniverse : IsHomUniverse type.{w} := ⟨⟩

  @[reducible] def homUniv := type.{max u w}

  -- This is defeq to `type.{u}` but solves some universe unification issues.
  abbrev type' := homUniv.{u, 0}

  instance hasCat : HasCatProp.{u + 1} homUniv.{u, w} :=
  { Cat  := CatDesc,
    desc := id }

  def defCat {R : BundledRelation.{u + 1} homUniv.{u, w}} (C : CatDesc R) : DefCat C :=
  { C   := C,
    hEq := IsPreorderEq.refl R.Hom (hR := C.homIsPreorder) }

  instance hasTrivialCatProp : HasCatProp.HasTrivialCatProp.{u + 1} homUniv.{u, w} := ⟨defCat⟩

  instance isCatUniverse : IsCatUniverse.{u + 1} type'.{u} :=
  { hasCat := hasCat }

  @[reducible] def Cat := Category.{u + 1} homUniv.{u, w}
  @[reducible] def Cat' := Cat.{u, 0}

  -- Functors

  -- TODO: It should be possible to make `A` and `B` live in different universes, here and in
  -- general. Unfortunately, it seems that Lean's universe unification algorithm currently cannot
  -- handle it.
  def FunProp (A B : Cat.{u, w}) : MetaProperty (A → B) homUniv.{u, w} := FunDesc

  instance hasFunProp (A B : Cat.{u, w}) : HasFunProp A B :=
  { Fun  := FunProp A B,
    desc := id }

  def defFun {A B : Cat.{u, w}} {φ : A → B} (F : FunDesc φ) : HasFunProp.DefFun F :=
  { F  := F,
    eq := λ _ _ => rfl }

  instance hasTrivialFunctorialityCondition (A B : Cat.{u, w}) :
    HasFunProp.HasTrivialFunctorialityCondition A B :=
  ⟨defFun⟩

  instance hasIdFun (A : Cat.{u, w}) : HasFunProp.HasIdFun A :=
  HasFunProp.HasIdFun.trivial A

  instance hasConstFun (A B : Cat.{u, w}) : HasFunProp.HasConstFun A B :=
  HasFunProp.HasConstFun.trivial A B

  instance hasCompFun (A B C : Cat.{u, w}) : HasFunProp.HasCompFun A B C :=
  HasFunProp.HasCompFun.trivial A B C

  instance isFunUniverse : IsFunUniverse.{u + 1} type'.{u} :=
  { hasFun := hasFunProp }

  instance isFunUniverse.hasAffineFunctors : IsFunUniverse.HasAffineFunctors.{u + 1} type'.{u} :=
  { hasIdFun    := hasIdFun,
    hasConstFun := hasConstFun,
    hasCompFun  := hasCompFun }

  -- Natural transformations

  theorem IsNatural.ext {α : Sort u} {β : Sort v} {R : MetaRelation α type.{w}} {S : MetaRelation β type.{w}}
                        [HasTrans S] {φ ψ : α → β} {F : PreFunctor R S φ} {G : PreFunctor R S ψ}
                        (η : MetaQuantification S φ ψ) (h₁ h₂ : MetaQuantification.IsNatural F G η) :
    h₁ = h₂ :=
  match h₁, h₂ with
  | ⟨_⟩, ⟨_⟩ => rfl

  theorem NatDesc.ext {A B : Cat.{u, w}} {F G : A ⮕ B} (η₁ η₂ : NatDesc F G) :
    (∀ a, η₁.η a = η₂.η a) → η₁ = η₂ :=
  match η₁, η₂ with
  | { η := nat₁, isNat := isNat₁ }, { η := nat₂, isNat := isNat₂ } =>
    λ h => by have hNat : nat₁ = nat₂ := funext h;
              subst hNat;
              have hIsNat : isNat₁ = isNat₂ := IsNatural.ext nat₁ isNat₁ isNat₂;
              subst hIsNat;
              rfl

  def NatRel (A B : Cat.{u, w}) : MetaRelation (A ⮕ B) homUniv.{u, w} := NatDesc

  instance hasNaturalityRelation (A B : Cat.{u, w}) : HasNatRel A B :=
  { Nat       := NatRel A B,
    desc      := id,
    defNatFun := λ _ _ _ => HasTrivialFunctoriality.defFun }

  def defNat {A B : Cat.{u, w}} {F G : A ⮕ B} (η : NatDesc F G) : HasNatRel.DefNat η :=
  { η     := η,
    natEq := λ _ => rfl }

  instance hasTrivialNaturalityCondition (A B : Cat.{u, w}) :
    HasNatRel.HasTrivialNaturalityCondition A B :=
  ⟨defNat⟩

  instance hasTrivialNatEquiv (A B : Cat.{u, w}) : HasNatRel.HasTrivialNatEquiv A B := ⟨NatDesc.ext⟩

  instance natIsPreorder (A B : Cat.{u, w}) : IsPreorder (NatRel A B) :=
  HasNatOp.natIsPreorder A B

  instance hasNaturality (A B : Cat'.{u}) : HasNaturality A B :=
  { natHasTransFun := HasTrivialFunctoriality.hasTransFun (NatRel A B),
    defFunCat      := HasTrivialCatProp.defCat }

  def defFunFunBaseBase {A B C : Cat'.{u}} {F : A → (B ⮕ C)}
                        {desc : HasNaturality.FunFunDesc F} :
    HasNaturality.DefFunFunBaseBase desc :=
  { defNat     := λ _   => HasNatRel.HasTrivialNaturalityCondition.defNat,
    natReflEq  := λ _   => HasNatRel.HasTrivialNatEquiv.natEquiv,
    natTransEq := λ _ _ => HasNatRel.HasTrivialNatEquiv.natEquiv }

  def defFunFunBase {A B C : Cat'.{u}} {F : A → (B ⮕ C)} {desc : HasNaturality.FunFunDesc F} :
    HasNaturality.DefFunFunBase desc :=
  { toDefFunFunBaseBase := defFunFunBaseBase,
    defNatFun  := λ _ _ => HasTrivialFunctoriality.defFun }

  def defFunFun {A B C : Cat'.{u}} {F : A → (B ⮕ C)} {desc : HasNaturality.FunFunDesc F} :
    HasNaturality.DefFunFun desc :=
  HasNaturality.DefFunFun.trivial defFunFunBase

  def defFunFunFunBase {A B C D : Cat'.{u}} {F : A → (B ⮕ C ⮕' D)}
                       {desc : HasNaturality.FunFunFunDesc F} :
    HasNaturality.DefFunFunFunBase desc :=
  { defRevFunFun := λ _ => defFunFunBaseBase,
    defNatNat    := λ _ => HasNaturality.DefNatNatBase.trivial }

  def defFunFunFun {A B C D : Cat'.{u}} {F : A → (B ⮕ C ⮕' D)}
                   {desc : HasNaturality.FunFunFunDesc F} :
    HasNaturality.DefFunFunFun desc :=
  HasNaturality.DefFunFunFun.trivial defFunFunFunBase defFunFunBase

  instance hasRevAppFunFun (A B : Cat'.{u}) : HasNaturality.HasRevAppFunFun A B :=
  { defRevAppFun    := λ _ => HasFunProp.HasTrivialFunctorialityCondition.defFun,
    defRevAppFunFun := defFunFun }

  instance hasCompFunFunFun (A B C : Cat'.{u}) : HasNaturality.HasCompFunFunFun A B C :=
  { defCompFunFun    := λ _ => defFunFun,
    defCompFunFunFun := defFunFunFun }

  instance hasConstFunFun (A B : Cat'.{u}) : HasNaturality.HasConstFunFun A B :=
  { defConstFunFun := defFunFun }

  instance hasDupFunFun (A B : Cat'.{u}) : HasNaturality.HasDupFunFun A B :=
  { defDupFun    := λ _ => HasFunProp.HasTrivialFunctorialityCondition.defFun,
    defDupFunFun := defFunFun }

  instance isNatUniverse : IsNatUniverse.{u + 1} type'.{u} :=
  { hasNat := hasNaturality }

  instance isNatUniverse.hasFullFunctors : IsNatUniverse.HasFullFunctors.{u + 1} type'.{u} :=
  { hasRevAppFunFun  := hasRevAppFunFun,
    hasCompFunFunFun := hasCompFunFunFun,
    hasConstFunFun   := hasConstFunFun,
    hasDupFunFun     := hasDupFunFun }

  -- Isomorphisms

  theorem IsInv.ext {α : Sort u} {R : MetaRelation α type.{w}} [IsPreorder R]
                    {a b : α} {f : R a b} {g : R b a} (h₁ h₂ : IsInv (R := R) f g) :
    h₁ = h₂ :=
  match h₁, h₂ with
  | ⟨_, _⟩, ⟨_, _⟩ => rfl

  theorem IsoDesc.ext {A : Cat.{u, w}} {a b : A} {e₁ e₂ : IsoDesc a b} :
    e₁.toHom = e₂.toHom → e₁.invHom = e₂.invHom → e₁ = e₂ :=
  match e₁, e₂ with
  | { toHom := to₁, invHom := inv₁, isInv := isInv₁ }, { toHom := to₂, invHom := inv₂, isInv := isInv₂ } =>
    λ (hTo : to₁ = to₂) (hInv : inv₁ = inv₂) => by subst hTo; subst hInv;
                                                   have invExt := IsInv.ext isInv₁ isInv₂;
                                                   subst invExt;
                                                   rfl

  theorem IsoDesc.ext' {A : Cat.{u, w}} {a b : A} {e₁ e₂ : IsoDesc a b}
                       (h : e₁.toHom = e₂.toHom) :
    e₁ = e₂ :=
  IsoDesc.ext h (IsoDesc.toInvEquiv (e₁ := e₁) (e₂ := e₂) h)

  def IsoRel (A : Cat.{u, w}) : MetaRelation A homUniv.{u, w} := IsoDesc

  instance hasIsoRel (A : Cat.{u, w}) : HasIsoRel A :=
  { Iso         := IsoRel A,
    desc        := id,
    defToHomFun := λ _ _ => HasTrivialFunctoriality.defFun,
    toHomInj    := IsoDesc.ext' }

  def defIso {A : Cat.{u, w}} {a b : A} (e : IsoDesc a b) : DefIso e :=
  { e    := e,
    toEq := rfl }

  instance hasTrivialIsomorphismCondition (A : Cat.{u, w}) : HasTrivialIsomorphismCondition A :=
  ⟨defIso⟩

  instance isoIsEquivalence (A : Cat.{u, w}) : IsEquivalence (IsoRel A) :=
  HasIsoOp.isoIsEquivalence A

  instance hasIsomorphisms (A : Cat.{u, w}) : HasIsomorphisms A :=
  { isoHasSymmFun  := HasTrivialFunctoriality.hasSymmFun  (IsoRel A),
    isoHasTransFun := HasTrivialFunctoriality.hasTransFun (IsoRel A),
    defIsoCat      := HasTrivialCatProp.defCat }

  -- Lean bug :-(
  noncomputable instance hasIsoFun {A B : Cat.{u, w}} (F : A ⮕ B) : HasIsoFun F :=
  { defMapIso    := λ _   => HasTrivialIsomorphismCondition.defIso,
    defMapIsoFun := λ _ _ => HasTrivialFunctoriality.defFun,
    defIsoFun    := HasFunProp.HasTrivialFunctorialityCondition.defFun }

  instance hasIsoNat {A B : Cat'.{u}} (F G : A ⮕' B) : HasIsoNat F G :=
  { defNatIso    := λ _ _ => HasTrivialIsomorphismCondition.defIso,
    defNatIsoFun := λ _   => HasTrivialFunctoriality.defFun }

  noncomputable instance isIsoUniverse : IsIsoUniverse.{u + 1} type'.{u} :=
  { hasIso    := hasIsomorphisms,
    hasIsoFun := hasIsoFun,
    hasIsoNat := hasIsoNat }

  noncomputable instance hasIsoFunctoriality (A B : Cat'.{u}) : HasIsoFunctoriality A B :=
  IsIsoUniverse.hasIsoFunctoriality A B

  noncomputable instance hasIsoNaturality (A B : Cat'.{u}) : HasIsoNaturality A B :=
  IsIsoUniverse.hasIsoNaturality A B

  def natIsoDescBuilder {A B : Cat'.{u}} {F G : A ⮕ B} (η : NatIsoDesc F G) :
    NatIsoDesc.IsoDescBuilder η :=
  { defToNat  := HasNatRel.HasTrivialNaturalityCondition.defNat,
    defInvNat := HasNatRel.HasTrivialNaturalityCondition.defNat,
    leftInv   := HasNatRel.HasTrivialNatEquiv.natEquiv,
    rightInv  := HasNatRel.HasTrivialNatEquiv.natEquiv }

  noncomputable def defNatIso {A B : Cat'.{u}} {F G : A ⮕' B} (η : NatIsoDesc F G) :
    HasIsoNat.DefNatIso η :=
  { η     := NatIsoDesc.IsoDescBuilder.isoDesc η (natIsoDescBuilder η),
    natEq := λ _ => rfl }

  noncomputable instance hasTrivialNatIsoCondition (A B : Cat'.{u}) :
    HasIsoNaturality.HasTrivialNaturalityCondition A B :=
  ⟨defNatIso⟩

  noncomputable instance isIsoUniverse.hasTrivialNaturalIsomorphisms :
    IsIsoUniverse.HasTrivialNaturalIsomorphisms.{u + 1} type'.{u} :=
  ⟨⟩

  noncomputable instance isIsoUniverse.hasFullNaturalIsomorphisms :
    IsIsoUniverse.HasFullNaturalIsomorphisms.{u + 1} type'.{u} :=
  inferInstance

end type
