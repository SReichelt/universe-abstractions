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

universe u u' u'' u''' v w



-- This establishes the universe `prop` as a morphism universe, which enables the construction of
-- categories with morphisms in `prop`, which are the same as preorders.

namespace prop.IsHomUniverse

  open MetaRelation CategoryTheory

  instance isHomUniverse : IsHomUniverse prop := ⟨⟩

  def catDesc {U : Universe.{u}} {R : BundledRelation U prop} (p : Preorder R.Hom) :
    CatDesc R :=
  { homIsPreorder            := nativePreorder p,
    homHasTransFun           := inferInstance,
    homIsCategoricalPreorder := inferInstance }

  instance hasCat (U : Universe.{u}) : HasCatProp U prop :=
  { Cat  := λ R => Preorder R.Hom,
    desc := catDesc }

  @[reducible] def Cat (U : Universe.{u}) := HasCatProp.Category U prop

  def defCat {U : Universe.{u}} {R : BundledRelation U prop} (C : CatDesc R) : HasCatProp.DefCat C :=
  ⟨{ refl  := C.homIsPreorder.refl,
     trans := C.homIsPreorder.trans }⟩

  instance hasTrivialCatProp (U : Universe.{u}) : HasCatProp.HasTrivialCatProp U prop := ⟨defCat⟩

  section

    variable {U : Universe.{u}}

    def IsoRel (A : Cat U) : MetaRelation A prop := λ a b => (a ⇾ b) ∧ (b ⇾ a)

    def isoDesc {A : Cat U} {a b : A} (p : IsoRel A a b) : IsoDesc a b := ⟨p.left, p.right⟩

    instance hasIsoRel (A : Cat U) : HasIsoRel A :=
    { Iso         := IsoRel A,
      desc        := isoDesc,
      defToHomFun := λ _ _ => HasTrivialFunctoriality.defFun,
      toHomInj    := λ _ => HasTrivialIdentity.eq }

    def defIso {A : Cat U} {a b : A} (e : IsoDesc a b) : HasIsoRel.DefIso e :=
    { e    := ⟨e.toHom, e.invHom⟩,
      toEq := HasTrivialIdentity.eq }

    instance hasTrivialIsomorphismCondition (A : Cat U) :
      HasIsoRel.HasTrivialIsomorphismCondition A :=
    ⟨defIso⟩

    instance isoIsEquivalence (A : Cat U) : IsEquivalence (IsoRel A) :=
    HasIsoOp.isoIsEquivalence A

    instance hasIsomorphisms (A : Cat U) : HasIsomorphisms A :=
    { isoHasSymmFun  := HasTrivialFunctoriality.hasSymmFun  (IsoRel A),
      isoHasTransFun := HasTrivialFunctoriality.hasTransFun (IsoRel A),
      defIsoCat      := HasCatProp.HasTrivialCatProp.defCat }

  end

  instance isCatUniverse (U : Universe.{u}) : IsCatUniverse U prop := ⟨⟩
  instance isSortCatUniverse : IsSortCatUniverse.{u} prop := ⟨⟩

  -- Functors

  section

    variable {U : Universe.{u}} {V : Universe.{v}}

    def FunProp (A : Cat U) (B : Cat V) : MetaProperty (A → B) prop :=
    λ φ => ∀ a b, (a ⇾ b) → (φ a ⇾ φ b)

    def funDesc {A : Cat U} {B : Cat V} {φ : A → B} (p : FunProp A B φ) : FunDesc φ := ⟨⟨p⟩⟩

    instance hasFunProp (A : Cat U) (B : Cat V) : HasFunProp A B :=
    { Fun  := FunProp A B,
      desc := funDesc }

    def defFun {A : Cat U} {B : Cat V} {φ : A → B} (F : FunDesc φ) : HasFunProp.DefFun F :=
    { F  := F.F.baseFun,
      eq := λ _ _ => HasTrivialIdentity.eq }

    instance hasTrivialFunctorialityCondition (A : Cat U) (B : Cat V) :
      HasFunProp.HasTrivialFunctorialityCondition A B :=
    ⟨defFun⟩

    -- Lean bug :-(
    noncomputable instance hasIsoFun {A : Cat U} {B : Cat V} (F : A ⮕ B) : HasIsoFun F :=
    { defMapIso    := λ _   => HasIsoRel.HasTrivialIsomorphismCondition.defIso,
      defMapIsoFun := λ _ _ => HasTrivialFunctoriality.defFun,
      defIsoFun    := HasFunProp.HasTrivialFunctorialityCondition.defFun }

  end

  instance hasIdFun {U : Universe.{u}} (A : Cat U) : HasFunProp.HasIdFun A :=
  HasFunProp.HasIdFun.trivial A

  instance hasConstFun {U : Universe.{u}} {V : Universe.{v}} (A : Cat U) (B : Cat V) :
    HasFunProp.HasConstFun A B :=
  HasFunProp.HasConstFun.trivial A B

  instance hasCompFun {U : Universe.{u}} {U' : Universe.{u'}} {U'' : Universe.{u''}}
                      (A : Cat U) (B : Cat U') (C : Cat U'') :
    HasFunProp.HasCompFun A B C :=
  HasFunProp.HasCompFun.trivial A B C

  noncomputable instance isFunUniverse (U : Universe.{u}) (V : Universe.{v}) :
    IsFunUniverse U V prop :=
  ⟨⟩

  noncomputable instance isSortFunUniverse : IsSortFunUniverse.{u, v} prop := ⟨⟩

  instance isFunUniverse.hasCatIdFun (U : Universe.{u}) : IsFunUniverse.HasCatIdFun U prop := ⟨⟩

  instance isFunUniverse.hasCatConstFun (U : Universe.{u}) (V : Universe.{v}) :
    IsFunUniverse.HasCatConstFun U V prop :=
  ⟨⟩

  instance isFunUniverse.hasCatCompFun (U : Universe.{u}) (U' : Universe.{u'}) (U'' : Universe.{u''}) :
    IsFunUniverse.HasCatCompFun U U' U'' prop :=
  ⟨⟩

  -- Natural transformations

  section

    variable {U : Universe.{u}} {V : Universe.{v}}

    def NatRel (A : Cat U) (B : Cat V) : MetaRelation (A ⮕ B) prop := λ F G => ∀ a, F a ⇾ G a

    -- Lean bug (?): IR check failed
    noncomputable def natDesc {A : Cat U} {B : Cat V} {F G : A ⮕ B} (p : NatRel A B F G) :
      NatDesc F G :=
    ⟨p⟩

    noncomputable instance hasNaturalityRelation (A : Cat U) (B : Cat V) : HasNatRel A B :=
    { Nat       := NatRel A B,
      desc      := natDesc,
      defNatFun := λ _ _ _ => HasTrivialFunctoriality.defFun }

    noncomputable def defNat {A : Cat U} {B : Cat V} {F G : A ⮕ B} (η : NatDesc F G) :
      HasNatRel.DefNat η :=
    { η     := η.η,
      natEq := λ _ => HasTrivialIdentity.eq }

    noncomputable instance hasTrivialNaturalityCondition (A : Cat U) (B : Cat V) :
      HasNatRel.HasTrivialNaturalityCondition A B :=
    ⟨defNat⟩

    instance hasTrivialNatEquiv (A : Cat U) (B : Cat V) : HasNatRel.HasTrivialNatEquiv A B :=
    ⟨λ _ _ _ => HasTrivialIdentity.eq⟩

    noncomputable instance natIsPreorder (A : Cat U) (B : Cat V) : IsPreorder (NatRel A B) :=
    HasNatOp.natIsPreorder A B

    noncomputable instance hasNaturality (A : Cat U) (B : Cat V) : HasNaturality A B :=
    { natHasTransFun := HasTrivialFunctoriality.hasTransFun (NatRel A B),
      defFunCat      := HasCatProp.HasTrivialCatProp.defCat }

    noncomputable instance hasIsoNat {A : Cat U} {B : Cat V} (F G : A ⮕' B) : HasIsoNat F G :=
    { defNatIso    := λ _ _ => HasIsoRel.HasTrivialIsomorphismCondition.defIso,
      defNatIsoFun := λ _   => HasTrivialFunctoriality.defFun }

    noncomputable def defNatIso {A : Cat U} {B : Cat V} {F G : A ⮕' B} (η : NatIsoDesc F G) :
      HasIsoNat.DefNatIso η :=
    { η     := ⟨λ a => (η.η a).left, λ a => (η.η a).right⟩,
      natEq := λ _ => HasTrivialIdentity.eq }

    noncomputable instance hasIsoNaturality (A : Cat U) (B : Cat V) : HasIsoNaturality A B := ⟨⟩

    noncomputable instance hasTrivialIsoNaturalityCondition (A : Cat U) (B : Cat V) :
      HasIsoNaturality.HasTrivialIsoNaturalityCondition A B :=
    ⟨defNatIso⟩

  end

  noncomputable instance isNatUniverse (U : Universe.{u}) (V : Universe.{v}) :
    IsNatUniverse U V prop :=
  ⟨⟩

  noncomputable instance isSortNatUniverse : IsSortNatUniverse.{u} prop := ⟨⟩

  noncomputable instance isSortNatUniverse.hasTrivialNaturalIsomorphisms :
    IsSortNatUniverse.HasTrivialNaturalIsomorphisms.{u} prop :=
  ⟨⟩

  -- Multifunctors

  section

    variable {U : Universe.{u}} {U' : Universe.{u'}} {U'' : Universe.{u''}}
             {A : Cat U} {B : Cat U'} {C : Cat U''} {F : A → (B ⮕ C)}
             {desc : HasNaturality.FunFunDesc F}

    noncomputable def defFunFunBase : HasNaturality.DefFunFunBase desc :=
    { defNat     := λ _   => HasNatRel.HasTrivialNaturalityCondition.defNat,
      defNatFun  := λ _ _ => HasTrivialFunctoriality.defFun,
      natReflEq  := λ _   => HasNatRel.HasTrivialNatEquiv.natEquiv,
      natTransEq := λ _ _ => HasNatRel.HasTrivialNatEquiv.natEquiv }

    noncomputable def defFunFun : HasNaturality.DefFunFun desc :=
    HasNaturality.DefFunFun.trivial defFunFunBase

  end

  section

    variable {U : Universe.{u}} {U' : Universe.{u'}} {U'' : Universe.{u''}} {U''' : Universe.{u'''}}
             {A : Cat U} {B : Cat U'} {C : Cat U''} {D : Cat U'''} {F : A → (B ⮕ C ⮕' D)}
             {desc : HasNaturality.FunFunFunDesc F}

    noncomputable def defFunFunFunBase : HasNaturality.DefFunFunFunBase desc :=
    { defRevFunFun := λ _ => defFunFunBase,
      defNatNat    := λ _ => HasNaturality.DefNatNatBase.trivial }

    noncomputable def defFunFunFun : HasNaturality.DefFunFunFun desc :=
    HasNaturality.DefFunFunFun.trivial defFunFunFunBase defFunFunBase

  end

  noncomputable instance hasRevAppFunFun {U : Universe.{u}} {V : Universe.{v}}
                                         (A : Cat U) (B : Cat V) :
    HasNaturality.HasRevAppFunFun A B :=
  { defRevAppFun    := λ _ => HasFunProp.HasTrivialFunctorialityCondition.defFun,
    defRevAppFunFun := defFunFun }

  noncomputable instance hasCompFunFunFun {U : Universe.{u}} {U' : Universe.{u'}}
                                          {U'' : Universe.{u''}}
                                          (A : Cat U) (B : Cat U') (C : Cat U'') :
    HasNaturality.HasCompFunFunFun A B C :=
  { defCompFunFun    := λ _ => defFunFun,
    defCompFunFunFun := defFunFunFun }

  noncomputable instance hasConstFunFun {U : Universe.{u}} {V : Universe.{v}}
                                        (A : Cat U) (B : Cat V) :
    HasNaturality.HasConstFunFun A B :=
  { defConstFunFun := defFunFun }

  noncomputable instance hasDupFunFun {U : Universe.{u}} {V : Universe.{v}}
                                      (A : Cat U) (B : Cat V) :
    HasNaturality.HasDupFunFun A B :=
  { defDupFun    := λ _ => HasFunProp.HasTrivialFunctorialityCondition.defFun,
    defDupFunFun := defFunFun }

  noncomputable instance isSortNatUniverse.hasFullCatFun :
    IsSortNatUniverse.HasFullCatFun.{u} prop :=
  { hasRevAppFunFun  := hasRevAppFunFun,
    hasCompFunFunFun := hasCompFunFunFun,
    hasConstFunFun   := hasConstFunFun,
    hasDupFunFun     := hasDupFunFun }

  noncomputable instance isSortNatUniverse.hasFullNatIso :
    IsSortNatUniverse.HasFullNatIso.{u} prop :=
  inferInstance

end prop.IsHomUniverse
