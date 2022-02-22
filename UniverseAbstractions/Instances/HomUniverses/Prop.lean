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



-- This establishes the universe `prop` as a morphism universe, which enables the construction of
-- categories with morphisms in `prop`, which are the same as preorders.

namespace prop

  open MetaRelation MetaFunctor CategoryTheory HasCatProp HasIsoRel

  instance isHomUniverse : IsHomUniverse prop := ⟨⟩

  def catDesc {R : BundledRelation.{u + 1} prop} (p : Preorder R.Hom) : CatDesc R :=
  { homIsPreorder            := nativePreorder p,
    homHasTransFun           := inferInstance,
    homIsCategoricalPreorder := inferInstance }

  instance hasCat : HasCatProp.{u + 1} prop :=
  { Cat  := λ R => Preorder R.Hom,
    desc := catDesc }

  def defCat {R : BundledRelation.{u + 1} prop} (C : CatDesc R) : DefCat C :=
  ⟨{ refl  := C.homIsPreorder.refl,
     trans := C.homIsPreorder.trans }⟩

  instance hasTrivialCatProp : HasCatProp.HasTrivialCatProp.{u + 1} prop := ⟨defCat⟩

  instance isCatUniverse : IsCatUniverse.{u + 1} prop :=
  { hasCat := hasCat }

  @[reducible] def Cat := Category.{u + 1} prop

  -- Functors

  def FunProp (A : Cat.{u}) (B : Cat.{v}) : MetaProperty (A → B) prop :=
  λ φ => ∀ a b, (a ⇾ b) → (φ a ⇾ φ b)

  def funDesc {A B : Cat} {φ : A → B} (p : FunProp A B φ) : FunDesc φ := ⟨⟨p⟩⟩

  instance hasFunProp (A : Cat.{u}) (B : Cat.{v}) : HasFunProp A B :=
  { Fun  := FunProp A B,
    desc := funDesc }

  def defFun {A B : Cat} {φ : A → B} (F : FunDesc φ) : HasFunProp.DefFun F :=
  { F  := F.F.baseFun,
    eq := λ _ _ => HasTrivialIdentity.eq }

  instance hasTrivialFunctorialityCondition (A B : Cat) :
    HasFunProp.HasTrivialFunctorialityCondition A B :=
  ⟨defFun⟩

  instance hasIdFun (A : Cat) : HasFunProp.HasIdFun A :=
  HasFunProp.HasIdFun.trivial A

  instance hasConstFun (A B : Cat) : HasFunProp.HasConstFun A B :=
  HasFunProp.HasConstFun.trivial A B

  instance hasCompFun (A B C : Cat) : HasFunProp.HasCompFun A B C :=
  HasFunProp.HasCompFun.trivial A B C

  instance isFunUniverse : IsFunUniverse.{u + 1} prop :=
  { hasFun := hasFunProp.{u, u} }

  instance isFunUniverse.hasAffineFunctors : IsFunUniverse.HasAffineFunctors.{u + 1} prop :=
  { hasIdFun    := hasIdFun,
    hasConstFun := hasConstFun,
    hasCompFun  := hasCompFun }

  -- Natural transformations

  def NatRel (A : Cat.{u}) (B : Cat.{v}) : MetaRelation (A ⮕ B) prop :=
  λ F G => ∀ a, F a ⇾ G a

  -- Lean bug (?): IR check failed
  noncomputable def natDesc {A B : Cat} {F G : A ⮕ B} (p : NatRel A B F G) : NatDesc F G := ⟨p⟩

  noncomputable instance hasNaturalityRelation (A : Cat.{u}) (B : Cat.{v}) : HasNatRel A B :=
  { Nat       := NatRel A B,
    desc      := natDesc,
    defNatFun := λ _ _ _ => HasTrivialFunctoriality.defFun }

  noncomputable def defNat {A B : Cat} {F G : A ⮕ B} (η : NatDesc F G) : HasNatRel.DefNat η :=
  { η     := η.η,
    natEq := λ _ => HasTrivialIdentity.eq }

  noncomputable instance hasTrivialNaturalityCondition (A B : Cat) :
    HasNatRel.HasTrivialNaturalityCondition A B :=
  ⟨defNat⟩

  instance hasTrivialNatEquiv (A B : Cat) : HasNatRel.HasTrivialNatEquiv A B :=
  ⟨λ _ _ _ => HasTrivialIdentity.eq⟩

  noncomputable instance natIsPreorder (A B : Cat) : IsPreorder (NatRel A B) :=
  HasNatOp.natIsPreorder A B

  noncomputable instance hasNaturality (A B : Cat) : HasNaturality A B :=
  { natHasTransFun := HasTrivialFunctoriality.hasTransFun (NatRel A B),
    defFunCat      := HasTrivialCatProp.defCat }

  noncomputable def defFunFunBaseBase {A B C : Cat} {F : A → (B ⮕ C)}
                                      {desc : HasNaturality.FunFunDesc F} :
    HasNaturality.DefFunFunBaseBase desc :=
  { defNat     := λ _   => HasNatRel.HasTrivialNaturalityCondition.defNat,
    natReflEq  := λ _   => HasNatRel.HasTrivialNatEquiv.natEquiv,
    natTransEq := λ _ _ => HasNatRel.HasTrivialNatEquiv.natEquiv }

  noncomputable def defFunFunBase {A B C : Cat} {F : A → (B ⮕ C)}
                                  {desc : HasNaturality.FunFunDesc F} :
    HasNaturality.DefFunFunBase desc :=
  { toDefFunFunBaseBase := defFunFunBaseBase,
    defNatFun  := λ _ _ => HasTrivialFunctoriality.defFun }

  noncomputable def defFunFun {A B C : Cat} {F : A → (B ⮕ C)} {desc : HasNaturality.FunFunDesc F} :
    HasNaturality.DefFunFun desc :=
  HasNaturality.DefFunFun.trivial defFunFunBase

  noncomputable def defFunFunFunBase {A B C D : Cat} {F : A → (B ⮕ C ⮕' D)}
                                     {desc : HasNaturality.FunFunFunDesc F} :
    HasNaturality.DefFunFunFunBase desc :=
  { defRevFunFun := λ _ => defFunFunBaseBase,
    defNatNat    := λ _ => HasNaturality.DefNatNatBase.trivial }

  noncomputable def defFunFunFun {A B C D : Cat} {F : A → (B ⮕ C ⮕' D)}
                                 {desc : HasNaturality.FunFunFunDesc F} :
    HasNaturality.DefFunFunFun desc :=
  HasNaturality.DefFunFunFun.trivial defFunFunFunBase defFunFunBase

  noncomputable instance hasRevAppFunFun (A B : Cat) : HasNaturality.HasRevAppFunFun A B :=
  { defRevAppFun    := λ _ => HasFunProp.HasTrivialFunctorialityCondition.defFun,
    defRevAppFunFun := defFunFun }

  noncomputable instance hasCompFunFunFun (A B C : Cat) : HasNaturality.HasCompFunFunFun A B C :=
  { defCompFunFun    := λ _ => defFunFun,
    defCompFunFunFun := defFunFunFun }

  noncomputable instance hasConstFunFun (A B : Cat) : HasNaturality.HasConstFunFun A B :=
  { defConstFunFun := defFunFun }

  noncomputable instance hasDupFunFun (A B : Cat) : HasNaturality.HasDupFunFun A B :=
  { defDupFun    := λ _ => HasFunProp.HasTrivialFunctorialityCondition.defFun,
    defDupFunFun := defFunFun }

  noncomputable instance isNatUniverse : IsNatUniverse.{u + 1} prop :=
  { hasNat := hasNaturality }

  noncomputable instance isNatUniverse.hasFullFunctors : IsNatUniverse.HasFullFunctors.{u + 1} prop :=
  { hasRevAppFunFun  := hasRevAppFunFun,
    hasCompFunFunFun := hasCompFunFunFun,
    hasConstFunFun   := hasConstFunFun,
    hasDupFunFun     := hasDupFunFun }

  -- Isomorphisms

  def IsoRel (A : Cat.{u}) : MetaRelation A prop := λ a b => (a ⇾ b) ∧ (b ⇾ a)

  def isoDesc {A : Cat} {a b : A} (p : IsoRel A a b) : IsoDesc a b := ⟨p.left, p.right⟩

  instance hasIsoRel (A : Cat.{u}) : HasIsoRel A :=
  { Iso         := IsoRel A,
    desc        := isoDesc,
    defToHomFun := λ _ _ => HasTrivialFunctoriality.defFun,
    toHomInj    := λ _ => HasTrivialIdentity.eq }

  def defIso {A : Cat} {a b : A} (e : IsoDesc a b) : DefIso e :=
  { e    := ⟨e.toHom, e.invHom⟩,
    toEq := HasTrivialIdentity.eq }

  instance hasTrivialIsomorphismCondition (A : Cat) : HasTrivialIsomorphismCondition A := ⟨defIso⟩

  instance isoIsEquivalence (A : Cat) : IsEquivalence (IsoRel A) :=
  HasIsoOp.isoIsEquivalence A

  instance hasIsomorphisms (A : Cat) : HasIsomorphisms A :=
  { isoHasSymmFun  := HasTrivialFunctoriality.hasSymmFun  (IsoRel A),
    isoHasTransFun := HasTrivialFunctoriality.hasTransFun (IsoRel A),
    defIsoCat      := HasTrivialCatProp.defCat }

  -- Lean bug :-(
  noncomputable instance hasIsoFun {A B : Cat} (F : A ⮕ B) : HasIsoFun F :=
  { defMapIso    := λ _   => HasTrivialIsomorphismCondition.defIso,
    defMapIsoFun := λ _ _ => HasTrivialFunctoriality.defFun,
    defIsoFun    := HasFunProp.HasTrivialFunctorialityCondition.defFun }

  noncomputable instance hasIsoNat {A B : Cat} (F G : A ⮕' B) : HasIsoNat F G :=
  { defNatIso    := λ _ _ => HasTrivialIsomorphismCondition.defIso,
    defNatIsoFun := λ _   => HasTrivialFunctoriality.defFun }

  noncomputable instance isIsoUniverse : IsIsoUniverse.{u + 1} prop :=
  { hasIso    := hasIsomorphisms,
    hasIsoFun := hasIsoFun,
    hasIsoNat := hasIsoNat }

  noncomputable instance hasIsoFunctoriality (A B : Cat.{u}) : HasIsoFunctoriality A B :=
  IsIsoUniverse.hasIsoFunctoriality A B

  noncomputable instance hasIsoNaturality (A B : Cat.{u}) : HasIsoNaturality A B :=
  IsIsoUniverse.hasIsoNaturality A B

  noncomputable def natIsoDescBuilder {A B : Cat.{u}} {F G : A ⮕ B} (η : NatIsoDesc F G) :
    NatIsoDesc.IsoDescBuilder η :=
  { defToNat  := HasNatRel.HasTrivialNaturalityCondition.defNat,
    defInvNat := HasNatRel.HasTrivialNaturalityCondition.defNat,
    leftInv   := HasNatRel.HasTrivialNatEquiv.natEquiv,
    rightInv  := HasNatRel.HasTrivialNatEquiv.natEquiv }

  noncomputable def defNatIso {A B : Cat.{u}} {F G : A ⮕' B} (η : NatIsoDesc F G) :
    HasIsoNat.DefNatIso η :=
  { η     := ⟨λ a => (η.η a).left, λ a => (η.η a).right⟩,
    natEq := λ _ => HasTrivialIdentity.eq }

  noncomputable instance hasTrivialNatIsoCondition (A B : Cat.{u}) :
    HasIsoNaturality.HasTrivialNaturalityCondition A B :=
  ⟨defNatIso⟩

  noncomputable instance isIsoUniverse.hasTrivialNaturalIsomorphisms :
    IsIsoUniverse.HasTrivialNaturalIsomorphisms.{u + 1} prop :=
  ⟨⟩

  noncomputable instance isIsoUniverse.hasFullNaturalIsomorphisms :
    IsIsoUniverse.HasFullNaturalIsomorphisms.{u + 1} prop :=
  inferInstance

end prop
