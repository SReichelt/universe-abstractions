import UniverseAbstractions.Instances.Setoid
import UniverseAbstractions.CategoryTheory.Meta
import UniverseAbstractions.CategoryTheory.Basic
import UniverseAbstractions.CategoryTheory.Functors
import UniverseAbstractions.CategoryTheory.NaturalTransformations
import UniverseAbstractions.CategoryTheory.Isomorphisms
import UniverseAbstractions.CategoryTheory.FunctorExtensionality
import UniverseAbstractions.CategoryTheory.Utils.Trivial



set_option autoBoundImplicitLocal false
set_option synthInstance.maxHeartbeats 10000
--set_option pp.universes true

universe u v w



namespace Setoid.IsHomUniverse

  open MetaRelation HasCongrArg MetaFunctor CategoryTheory HasCatProp HasIsoRel

  abbrev setoid : Universe.{u + 1} := tuniv.{u + 1}

  instance isHomUniverse : IsHomUniverse setoid.{u} := ⟨⟩

  @[reducible] def homUniv := setoid.{max u w}

  -- This is defeq to `setoid.{u}` but solves some universe unification issues.
  abbrev setoid' := homUniv.{u, 0}

  -- We need to copy `IsPreorderEq` and similar classes because we need them as `Prop`.
  structure CatDescEquiv {R : BundledRelation type.{u} homUniv.{u, w}} (C D : CatDesc R) : Prop where
  (reflEq (a : R.A) : C.homIsPreorder.refl a ≈ D.homIsPreorder.refl a)
  (transEq {a b c : R.A} (f : R.Hom a b) (g : R.Hom b c) :
     C.homIsPreorder.trans f g ≈ D.homIsPreorder.trans f g)

  instance catDescSetoid (R : BundledRelation type.{u} homUniv.{u, w}) :
    Setoid.{(max u w) + 1} (CatDesc R) :=
  { r     := CatDescEquiv,
    iseqv := { refl  := λ C   => ⟨λ a   => Setoid.refl  (C.homIsPreorder.refl a),
                                  λ f g => Setoid.refl  (C.homIsPreorder.trans f g)⟩,
               symm  := λ h   => ⟨λ a   => Setoid.symm  (h.reflEq  a),
                                  λ f g => Setoid.symm  (h.transEq f g)⟩,
               trans := λ h i => ⟨λ a   => Setoid.trans (h.reflEq  a)   (i.reflEq  a),
                                  λ f g => Setoid.trans (h.transEq f g) (i.transEq f g)⟩ } }

  def CatProp : MetaProperty (BundledRelation type.{u} homUniv.{u, w}) homUniv.{u, w} :=
  λ R => { a    := CatDesc       R,
           inst := catDescSetoid R }

  instance hasCat : HasCatProp type.{u} homUniv.{u, w} :=
  { Cat  := CatProp,
    desc := id }

  def defCat {R : BundledRelation type.{u} homUniv.{u, w}} (C : CatDesc R) : DefCat C :=
  { C   := C,
    hEq := IsPreorderEq.refl R.Hom (hR := C.homIsPreorder) }

  instance hasTrivialCatProp : HasCatProp.HasTrivialCatProp type.{u} homUniv.{u, w} := ⟨defCat⟩

  instance isCatUniverse : IsCatUniverse.{u + 1} setoid'.{u} :=
  { hasCat := hasCat }

  @[reducible] def Cat := Category type.{u} homUniv.{u, w}
  @[reducible] def Cat' := Cat.{u, 0}

  -- Functors

  structure FunDescEquiv {A B : Cat.{u, w}} (φ : A → B) (F G : FunDesc φ) : Prop where
  (eq (a b : A) : F.F.baseFun a b ≈ G.F.baseFun a b)

  instance funDescSetoid {A B : Cat.{u, w}} (φ : A → B) : Setoid.{(max u w) + 1} (FunDesc φ) :=
  { r     := FunDescEquiv φ,
    iseqv := { refl  := λ F   => ⟨λ a b => Setoid.refl  (F.F.baseFun a b)⟩,
               symm  := λ h   => ⟨λ a b => Setoid.symm  (h.eq a b)⟩,
               trans := λ h i => ⟨λ a b => Setoid.trans (h.eq a b) (i.eq a b)⟩ } }

  def FunProp (A B : Cat.{u, w}) : MetaProperty (A → B) homUniv.{u, w} :=
  λ φ => { a    := FunDesc       φ,
           inst := funDescSetoid φ }

  instance hasFunProp (A B : Cat.{u, w}) : HasFunProp A B :=
  { Fun  := FunProp A B,
    desc := id }

  def defFun {A B : Cat.{u, w}} {φ : A → B} (F : FunDesc φ) : HasFunProp.DefFun F :=
  { F  := F,
    eq := λ a b => Setoid.refl (F.F.baseFun a b) }

  instance hasTrivialFunctorialityCondition (A B : Cat.{u, w}) :
    HasFunProp.HasTrivialFunctorialityCondition A B :=
  ⟨defFun⟩

  instance hasIdFun (A : Cat.{u, w}) : HasFunProp.HasIdFun A :=
  HasFunProp.HasIdFun.trivial A

  instance hasConstFun (A B : Cat.{u, w}) : HasFunProp.HasConstFun A B :=
  HasFunProp.HasConstFun.trivial A B

  instance hasCompFun (A B C : Cat.{u, w}) : HasFunProp.HasCompFun A B C :=
  HasFunProp.HasCompFun.trivial A B C

  instance isFunUniverse : IsFunUniverse.{u + 1} setoid'.{u} :=
  { hasFun := hasFunProp }

  instance isFunUniverse.hasAffineFunctors : IsFunUniverse.HasAffineFunctors.{u + 1} setoid'.{u} :=
  { hasIdFun    := hasIdFun,
    hasConstFun := hasConstFun,
    hasCompFun  := hasCompFun }

  -- Natural transformations

  structure NatDescEquiv {A B : Cat.{u, w}} (F G : A ⮕ B) (η ε : NatDesc F G) : Prop where
  (eq (a : A) : η.η a ≈ ε.η a)

  instance natDescSetoid {A B : Cat.{u, w}} (F G : A ⮕ B) : Setoid.{(max u w) + 1} (NatDesc F G) :=
  { r     := NatDescEquiv F G,
    iseqv := { refl  := λ η   => ⟨λ a => Setoid.refl  (η.η a)⟩,
               symm  := λ h   => ⟨λ a => Setoid.symm  (h.eq a)⟩,
               trans := λ h i => ⟨λ a => Setoid.trans (h.eq a) (i.eq a)⟩ } }

  def NatRel (A B : Cat.{u, w}) : MetaRelation (A ⮕ B) homUniv.{u, w} :=
  λ F G => { a    := NatDesc       F G,
             inst := natDescSetoid F G }

  instance hasNaturalityRelation (A B : Cat.{u, w}) : HasNatRel A B :=
  { Nat       := NatRel A B,
    desc      := id,
    defNatFun := λ _ _ a => Setoid.defFun (λ h => h.eq a) }

  def defNat {A B : Cat.{u, w}} {F G : A ⮕ B} (η : NatDesc F G) : HasNatRel.DefNat η :=
  { η     := η,
    natEq := λ a => Setoid.refl (η.η a) }

  instance hasTrivialNaturalityCondition (A B : Cat.{u, w}) :
    HasNatRel.HasTrivialNaturalityCondition A B :=
  ⟨defNat⟩

  instance hasTrivialNatEquiv (A B : Cat.{u, w}) : HasNatRel.HasTrivialNatEquiv A B :=
  ⟨λ _ _ h => ⟨h⟩⟩

  instance natIsPreorder (A B : Cat.{u, w}) : IsPreorder (NatRel A B) :=
  HasNatOp.natIsPreorder A B

  -- Lean bug :-(
  noncomputable instance hasNaturality (A B : Cat'.{u}) : HasNaturality A B :=
  { natHasTransFun := { defTransFun    := λ η _ => Setoid.defFun (λ {ε₁ ε₂} h => ⟨λ a => have h₁ : ⌈ε₁.η a ≃ ε₂.η a⌉ := h.eq a;
                                                                                         HasTransFun.congrArgTransLeft (η.η a) h₁⟩),
                        defTransFunFun := λ _ _ _ => Setoid.defFun (λ {η₁ η₂} h ε => ⟨λ a => have h₂ : ⌈η₁.η a ≃ η₂.η a⌉ := h.eq a;
                                                                                             HasTransFun.congrArgTransRight h₂ (ε.η a)⟩) },
    defFunCat      := HasTrivialCatProp.defCat }

  noncomputable def defFunFunBase {A B C : Cat'.{u}} {F : A → (B ⮕ C)}
                                  {desc : HasNaturality.FunFunDesc F} :
    HasNaturality.DefFunFunBase desc :=
  { defNat     := λ _     => HasNatRel.HasTrivialNaturalityCondition.defNat,
    defNatFun  := λ a₁ a₂ => Setoid.defFun (λ h => ⟨λ b => defCongrArg (desc.defNatDescFun a₁ a₂ b) h⟩),
    natReflEq  := λ _     => HasNatRel.HasTrivialNatEquiv.natEquiv,
    natTransEq := λ _ _   => HasNatRel.HasTrivialNatEquiv.natEquiv }

  noncomputable def defFunFun {A B C : Cat'.{u}} {F : A → (B ⮕ C)} {desc : HasNaturality.FunFunDesc F} :
    HasNaturality.DefFunFun desc :=
  HasNaturality.DefFunFun.trivial defFunFunBase

  noncomputable def defFunFunFunBase {A B C D : Cat'.{u}} {F : A → (B ⮕ C ⮕' D)}
                                     {desc : HasNaturality.FunFunFunDesc F} :
    HasNaturality.DefFunFunFunBase desc :=
  { defRevFunFun := λ _ => defFunFunBase,
    defNatNat    := λ _ => HasNaturality.DefNatNatBase.trivial }

  noncomputable def defFunFunFun {A B C D : Cat'.{u}} {F : A → (B ⮕ C ⮕' D)}
                   {desc : HasNaturality.FunFunFunDesc F} :
    HasNaturality.DefFunFunFun desc :=
  HasNaturality.DefFunFunFun.trivial defFunFunFunBase defFunFunBase

  noncomputable instance hasRevAppFunFun (A B : Cat'.{u}) : HasNaturality.HasRevAppFunFun A B :=
  { defRevAppFun    := λ _ => HasFunProp.HasTrivialFunctorialityCondition.defFun,
    defRevAppFunFun := defFunFun }

  noncomputable instance hasCompFunFunFun (A B C : Cat'.{u}) : HasNaturality.HasCompFunFunFun A B C :=
  { defCompFunFun    := λ _ => defFunFun,
    defCompFunFunFun := defFunFunFun }

  noncomputable instance hasConstFunFun (A B : Cat'.{u}) : HasNaturality.HasConstFunFun A B :=
  { defConstFunFun := defFunFun }

  noncomputable instance hasDupFunFun (A B : Cat'.{u}) : HasNaturality.HasDupFunFun A B :=
  { defDupFun    := λ _ => HasFunProp.HasTrivialFunctorialityCondition.defFun,
    defDupFunFun := defFunFun }

  noncomputable instance isNatUniverse : IsNatUniverse.{u + 1} setoid'.{u} :=
  { hasNat := hasNaturality }

  noncomputable instance isNatUniverse.hasFullFunctors :
    IsNatUniverse.HasFullFunctors.{u + 1} setoid'.{u} :=
  { hasRevAppFunFun  := hasRevAppFunFun,
    hasCompFunFunFun := hasCompFunFunFun,
    hasConstFunFun   := hasConstFunFun,
    hasDupFunFun     := hasDupFunFun }

  -- Isomorphisms

  instance isoDescSetoid {A : Cat.{u, w}} (a b : A) : Setoid.{(max u w) + 1} (IsoDesc a b) :=
  { r     := λ e₁ e₂ => e₁.toHom ≈ e₂.toHom,
    iseqv := { refl  := λ e   => Setoid.refl  e.toHom,
               symm  := λ h   => Setoid.symm  h,
               trans := λ h i => Setoid.trans h i } }

  def IsoRel (A : Cat.{u, w}) : MetaRelation A homUniv.{u, w} :=
  λ a b => { a    := IsoDesc       a b,
             inst := isoDescSetoid a b }

  instance hasIsoRel (A : Cat.{u, w}) : HasIsoRel A :=
  { Iso         := IsoRel A,
    desc        := id,
    defToHomFun := λ _ _ => Setoid.defFun id,
    toHomInj    := id }

  def defIso {A : Cat.{u, w}} {a b : A} (e : IsoDesc a b) : DefIso e :=
  { e    := e,
    toEq := Setoid.refl e }

  instance hasTrivialIsomorphismCondition (A : Cat.{u, w}) : HasTrivialIsomorphismCondition A :=
  ⟨defIso⟩

  instance isoIsEquivalence (A : Cat.{u, w}) : IsEquivalence (IsoRel A) :=
  HasIsoOp.isoIsEquivalence A

  noncomputable instance hasIsomorphisms (A : Cat.{u, w}) : HasIsomorphisms A :=
  { isoHasSymmFun  := { defSymmFun     := λ _ _ => Setoid.defFun (λ h => IsoDesc.toInvEquiv h) },
    isoHasTransFun := { defTransFun    := λ e _ => Setoid.defFun (λ h => HasTransFun.congrArgTransLeft e.toHom h),
                        defTransFunFun := λ _ _ _ => Setoid.defFun (λ h f => HasTransFun.congrArgTransRight (R := A.Hom) h f.toHom) },
    defIsoCat      := HasTrivialCatProp.defCat }

  noncomputable instance hasIsoFun {A B : Cat.{u, w}} (F : A ⮕ B) : HasIsoFun F :=
  { defMapIso    := λ _   => HasTrivialIsomorphismCondition.defIso,
    defMapIsoFun := λ _ _ => Setoid.defFun (HasFunProp.Functor.mapHomCongrArg F),
    defIsoFun    := HasFunProp.HasTrivialFunctorialityCondition.defFun }

  noncomputable instance hasIsoNat {A B : Cat'.{u}} (F G : A ⮕' B) : HasIsoNat F G :=
  { defNatIso    := λ _ _ => HasTrivialIsomorphismCondition.defIso,
    defNatIsoFun := λ a   => Setoid.defFun (λ h => HasNatRel.natCongrArg h a) }

  noncomputable instance isIsoUniverse : IsIsoUniverse.{u + 1} setoid'.{u} :=
  { hasIso    := hasIsomorphisms,
    hasIsoFun := hasIsoFun,
    hasIsoNat := hasIsoNat }

  noncomputable instance hasIsoFunctoriality (A B : Cat'.{u}) : HasIsoFunctoriality A B :=
  IsIsoUniverse.hasIsoFunctoriality A B

  noncomputable instance hasIsoNaturality (A B : Cat'.{u}) : HasIsoNaturality A B :=
  IsIsoUniverse.hasIsoNaturality A B

  noncomputable def natIsoDescBuilder {A B : Cat'.{u}} {F G : A ⮕ B} (η : NatIsoDesc F G) :
    NatIsoDesc.IsoDescBuilder η :=
  { defToNat  := HasNatRel.HasTrivialNaturalityCondition.defNat,
    defInvNat := HasNatRel.HasTrivialNaturalityCondition.defNat,
    leftInv   := HasNatRel.HasTrivialNatEquiv.natEquiv,
    rightInv  := HasNatRel.HasTrivialNatEquiv.natEquiv }

  noncomputable def defNatIso {A B : Cat'.{u}} {F G : A ⮕' B} (η : NatIsoDesc F G) :
    HasIsoNat.DefNatIso η :=
  { η     := NatIsoDesc.IsoDescBuilder.isoDesc η (natIsoDescBuilder η),
    natEq := λ a => Setoid.refl (η.η a) }

  noncomputable instance hasTrivialNatIsoCondition (A B : Cat'.{u}) :
    HasIsoNaturality.HasTrivialNaturalityCondition A B :=
  ⟨defNatIso⟩

  noncomputable instance isIsoUniverse.hasTrivialNaturalIsomorphisms :
    IsIsoUniverse.HasTrivialNaturalIsomorphisms.{u + 1} setoid'.{u} :=
  ⟨⟩

  noncomputable instance isIsoUniverse.hasFullNaturalIsomorphisms :
    IsIsoUniverse.HasFullNaturalIsomorphisms.{u + 1} setoid'.{u} :=
  inferInstance

end Setoid.IsHomUniverse
