import UniverseAbstractions.Instances.Basic
import UniverseAbstractions.Instances.Utils.TrivialCategoryTheory
import UniverseAbstractions.Axioms.CategoryTheory.Meta
import UniverseAbstractions.Axioms.CategoryTheory.Basic
import UniverseAbstractions.Axioms.CategoryTheory.Extended



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u



-- This establishes the universe `type` as a morphism universe, i.e. makes it possible to construct
-- categories with morphisms in `type`, i.e. regular 1-categories.
--
-- The type of objects in a category is currently forced to be in the same Lean universe as the
-- type of morphisms. In general, it would be possible to weaken this restriction, but we run into
-- problems when defining functor categories: Since their morphisms, which are natural
-- transformations, need to live in the Lean universe where all morphisms live (at least if we want
-- to have internal functors), the morphism universe needs to be at least as large as the object
-- universe. And having a morphism universe that is even larger doesn't seem useful, so we use the
-- same universe for both.
--
-- Moreover, we cannot include `prop` here because structures like `IsoDesc` cannot be sufficiently
-- polymorphic in Lean. If necessary, a corresponding formalization for `prop` is easy to do. Note,
-- however, that categories with morphisms in `prop` are essentially the same as partially ordered
-- types, and groupoids with morphisms in `prop` are essentially the same as setoids, for which we
-- have a custom universe definition.
--
-- If necessary, changing `type.{u}` to `sort.{max 1 u}` should be unproblematic.

namespace type

  open MetaRelation MetaFunctor CategoryTheory IsCategory HasIsoRel

  theorem IsInv.ext {α : Type u} [hα : IsCategory type.{u} α] {a b : α} {f : a ⇾ b} {g : b ⇾ a}
                    (h₁ h₂ : IsInv hα.Hom f g) :
    h₁ = h₂ :=
  match h₁, h₂ with
  | ⟨_, _⟩, ⟨_, _⟩ => rfl

  theorem IsoDesc.ext {α : Type u} [hα : IsCategory type.{u} α] {a b : α} {e₁ e₂ : IsoDesc a b} :
    e₁.toHom = e₂.toHom → e₁.invHom = e₂.invHom → e₁ = e₂ :=
  match e₁, e₂ with
  | { toHom := to₁, invHom := inv₁, isInv := isInv₁ }, { toHom := to₂, invHom := inv₂, isInv := isInv₂ } =>
    λ (hTo : to₁ = to₂) (hInv : inv₁ = inv₂) => by subst hTo; subst hInv;
                                                   have invExt := IsInv.ext isInv₁ isInv₂;
                                                   subst invExt; rfl

  theorem IsoDesc.ext' {α : Type u} [hα : IsCategory type.{u} α] {a b : α} {e₁ e₂ : IsoDesc a b}
                       (h : e₁.toHom = e₂.toHom) :
    e₁ = e₂ :=
  IsoDesc.ext h (IsoDesc.toInvEquiv (e₁ := e₁) (e₂ := e₂) h)

  def isoRel (α : Type u) [hα : IsCategory type.{u} α] : MetaRelation α type.{u} := IsoDesc

  instance hasIsoRel (α : Type u) [hα : IsCategory type.{u} α] : HasIsoRel α :=
  { Iso         := isoRel α,
    desc        := id,
    defToHomFun := λ _ _ => HasTrivialFunctoriality.defFun,
    toHomInj    := IsoDesc.ext' }

  instance hasTrivialIsomorphismCondition (α : Type u) [hα : IsCategory type.{u} α] :
    HasTrivialIsomorphismCondition α :=
  ⟨λ e => { e    := e,
            toEq := rfl }⟩

  instance isoIsEquivalence (α : Type u) [hα : IsCategory type.{u} α] :
    IsEquivalence (isoRel α) :=
  HasIsoOp.isoIsEquivalence α

  instance isoInv {α : Type u} [hα : IsCategory type.{u} α] {a b : α} (e : IsoDesc a b) :
    IsInv (isoRel α) e (IsoDesc.symm e) :=
  { leftInv  := IsoDesc.ext e.isInv.leftInv  e.isInv.leftInv,
    rightInv := IsoDesc.ext e.isInv.rightInv e.isInv.rightInv }

  -- We need to replicate `HasIsoRel.toHomMetaFunctor` here to avoid an error from Lean that seems to be a bug.
  def toHomMetaFunctor (α : Type u) [hα : IsCategory type.{u} α] : MetaFunctor (isoRel α) hα.Hom :=
  ⟨λ _ _ => IsoDesc.toHom⟩

  instance toHomIsPreorderFunctor (α : Type u) [hα : IsCategory type.{u} α] :
    IsPreorderFunctor (toHomMetaFunctor α) :=
  { reflEq  := λ _   => rfl,
    transEq := λ _ _ => rfl }

  instance hasIsoGroupoid (α : Type u) [hα : IsCategory type.{u} α] : HasIsoGroupoid α :=
  { isoInv                 := isoInv,
    isoHasSymmFun          := HasTrivialFunctoriality.hasSymmFun (isoRel α),
    isoHasTransFun         := HasTrivialFunctoriality.hasTransFun (isoRel α),
    toHomIsPreorderFunctor := toHomIsPreorderFunctor α }

  instance isoIsGroupoidEquivalence (α : Type u) [hα : IsCategory type.{u} α] :
    IsGroupoidEquivalence (isoRel α) :=
  HasIsoGroupoid.isoIsGroupoidEquivalence α

  instance hasIsomorphisms (α : Type u) [hα : IsCategory type.{u} α] : HasIsomorphisms α :=
  { toHomIsTransFunctorExt      := HasTrivialExtensionality.isTransFunctorExt (toHomMetaFunctor α),
    isoIsGroupoidEquivalenceExt := HasTrivialExtensionality.isGroupoidEquivalenceExt (isoRel α) }

  instance isIsoUniverse : IsIsoUniverse.{u + 1} type.{u} :=
  { hasIso := hasIsomorphisms }

  def funProp (α β : Type u) [hα : IsCategory type.{u} α] [hβ : IsCategory type.{u} β] :
    MetaProperty (α → β) type.{u} :=
  IsCategoryFunctor

  instance hasFunProp (α β : Type u) [hα : IsCategory type.{u} α] [hβ : IsCategory type.{u} β] :
    HasFunProp α β :=
  { Fun               := funProp α β,
    isCategoryFunctor := id }

  def isoPreFunctor {α β : Type u} [hα : IsCategory type.{u} α] [hβ : IsCategory type.{u} β]
                    (φ : α → β) [hφ : IsCategoryFunctor φ] :
    PreFunctor (isoRel α) (isoRel β) φ :=
  ⟨λ _ _ => IsoDesc.map φ⟩

  instance isIsoFun {α β : Type u} [hα : IsCategory type.{u} α] [hβ : IsCategory type.{u} β]
                    (F : HasFunProp.Functor α β) :
    IsIsoFunctor F.φ :=
  { F              := isoPreFunctor F.φ,
    homIsoCongr    := λ _   => rfl,
    homIsoCongrExt := λ _ _ => rfl }

  instance hasIsoFun (α β : Type u) [hα : IsCategory type.{u} α] [hβ : IsCategory type.{u} β] :
    HasIsoFunctoriality α β :=
  { isIsoFun := isIsoFun }

  instance hasTrivialFunctorialityCondition (α β : Type u) [hα : IsCategory type.{u} α]
                                                           [hβ : IsCategory type.{u} β] :
    HasFunProp.HasTrivialFunctorialityCondition α β :=
  ⟨λ φ [hφ : IsCategoryFunctor φ] => { F  := hφ,
                                       eq := λ _ _ => rfl }⟩

  instance isFunUniverse : IsFunUniverse.{u + 1} type.{u} :=
  { hasFun      := hasIsoFun,
    defIdFun    := λ _               => HasFunProp.HasTrivialFunctorialityCondition.defFun,
    defConstFun := λ _ {_} [_] [_] _ => HasFunProp.HasTrivialFunctorialityCondition.defFun,
    defCompFun  := λ _ _             => HasFunProp.HasTrivialFunctorialityCondition.defFun }

  theorem IsNatural.ext {α β : Type u} {R : MetaRelation α type.{u}} {S : MetaRelation β type.{u}}
                        (φ ψ : α → β) {φ ψ : α → β} {F : PreFunctor R S φ} {G : PreFunctor R S ψ}
                        {η : MetaQuantification S φ ψ} [hTrans : HasTrans S]
                        (h₁ h₂ : MetaQuantification.IsNatural F G η) :
    h₁ = h₂ :=
  match h₁, h₂ with
  | ⟨_⟩, ⟨_⟩ => rfl

  theorem IsNaturalExt.ext {α β : Type u} {R : MetaRelation α type.{u}} {S : MetaRelation β type.{u}}
                           (φ ψ : α → β) {φ ψ : α → β} {F : PreFunctor R S φ} {G : PreFunctor R S ψ}
                           {η : MetaQuantification S φ ψ} [hTrans : HasTrans S] [hTransFun : HasTransFun S]
                           [hNat : MetaQuantification.IsNatural F G η]
                           (h₁ h₂ : MetaQuantification.IsNatural.IsNaturalExt F G η) :
    h₁ = h₂ :=
  match h₁, h₂ with
  | ⟨_⟩, ⟨_⟩ => rfl

  theorem IsNaturalTransformation.ext {α β : Type u} [hα : HasMorphisms type.{u} α] [hβ : IsSemicategory type.{u} β]
                                      {φ ψ : α → β} [hφ : IsMorphismFunctor (hα := hα) (hβ := hβ.toHasMorphisms) φ]
                                                    [hψ : IsMorphismFunctor (hα := hα) (hβ := hβ.toHasMorphisms) ψ]
                                      (η : MetaQuantification hβ.Hom φ ψ) (h₁ h₂ : IsNaturalTransformation η) :
    h₁ = h₂ :=
  match h₁, h₂ with
  | { isNatural := isNat₁, isNaturalExt := isNatExt₁ }, { isNatural := isNat₂, isNaturalExt := isNatExt₂ } =>
    by have hIsNat : isNat₁ = isNat₂ := IsNatural.ext φ ψ (hTrans := hβ.homHasTrans) isNat₁ isNat₂;
       subst hIsNat;
       have hIsNatExt : isNatExt₁ = isNatExt₂ :=
            IsNaturalExt.ext φ ψ (hTrans := hβ.homHasTrans) (hTransFun := hβ.homHasTransFun) (hNat := isNat₁)
                             isNatExt₁ isNatExt₂;
       subst hIsNatExt; rfl

  theorem NatDesc.ext {α β : Type u} [hα : IsCategory type.{u} α] [hβ : IsCategory type.{u} β]
                      {F G : HasFunProp.Functor α β} (η₁ η₂ : NatDesc F G) :
    (∀ a, η₁.nat a = η₂.nat a) → η₁ = η₂ :=
  match η₁, η₂ with
  | { nat := nat₁, isNat := isNat₁ }, { nat := nat₂, isNat := isNat₂ } =>
    λ h => by have hNat : nat₁ = nat₂ := funext h;
              subst hNat;
              have hIsNat : isNat₁ = isNat₂ :=
                   IsNaturalTransformation.ext (hα := hα.toHasMorphisms) (hβ := IsCategory.isSemicategory (h := hβ))
                                               nat₁ isNat₁ isNat₂;
              subst hIsNat; rfl

  def natRel (α β : Type u) [hα : IsCategory type.{u} α] [hβ : IsCategory type.{u} β] :
    MetaRelation (HasFunProp.Functor α β) type.{u} :=
  NatDesc

  instance hasNaturalityRelation (α β : Type u) [hα : IsCategory type.{u} α] [hβ : IsCategory type.{u} β] :
    HasNatRel.{u + 1} α β :=
  { Nat       := natRel α β,
    desc      := id,
    defNatFun := λ _ _ _ => HasTrivialFunctoriality.defFun }

  instance hasTrivialNaturalityCondition (α β : Type u) [hα : IsCategory type.{u} α]
                                                        [hβ : IsCategory type.{u} β] :
    HasNatRel.HasTrivialNaturalityCondition.{u + 1} α β :=
  ⟨λ η => { η     := η,
            natEq := λ a => rfl }⟩

  instance hasTrivialNatEquiv (α β : Type u) [hα : IsCategory type.{u} α] [hβ : IsCategory type.{u} β] :
    HasNatRel.HasTrivialNatEquiv.{u + 1} α β :=
  ⟨NatDesc.ext⟩

  instance natIsPreorder (α β : Type u) [hα : IsCategory type.{u} α] [hβ : IsCategory type.{u} β] :
    IsPreorder (natRel α β) :=
  HasNatOp.natIsPreorder α β

  instance natIsCategoricalPreorder (α β : Type u) [hα : IsCategory type.{u} α] [hβ : IsCategory type.{u} β] :
    IsCategoricalPreorder (natRel α β) :=
  HasNatOpEquiv.natIsCategoricalPreorder α β

  instance hasNaturality (α β : Type u) [hα : IsCategory type.{u} α] [hβ : IsCategory type.{u} β] :
    HasNaturality.{u + 1} α β :=
  { natHasTransFun              := HasTrivialFunctoriality.hasTransFun (natRel α β),
    natIsCategoricalPreorderExt := HasTrivialExtensionality.isCategoricalPreorderExt (natRel α β) }

  instance hasRevAppFun (α β : Type u) [hα : IsCategory type.{u} α] [hβ : IsCategory type.{u} β] :
    HasNaturality.HasRevAppFun.{u + 1} α β :=
  { defRevAppFun := λ _ => HasFunProp.HasTrivialFunctorialityCondition.defFun }

  instance hasRevAppFunFun (α β : Type u) [hα : IsCategory type.{u} α] [hβ : IsCategory type.{u} β] :
    HasNaturality.HasRevAppFunFun.{u + 1} α β :=
                                     -- TODO: Lean bug? Or is it due to a `sorry`?
  { defRevAppCongrArg    := λ _   => sorry, --HasNatRel.HasTrivialNaturalityCondition.defNat,
    defRevAppCongrArgFun := λ _ _ => HasTrivialFunctoriality.defFun,
    revAppEquivRefl      := λ _   => HasNatRel.HasTrivialNatEquiv.natEquiv,
    revAppEquivTrans     := λ _ _ => HasNatRel.HasTrivialNatEquiv.natEquiv,
    defRevAppFunFun      := HasFunProp.HasTrivialFunctorialityCondition.defFun (hφ := HasNaturality.revAppFunIsFun.{u + 1} α β _ _ _ _) }

  instance isNatUniverse : IsNatUniverse.{u + 1} type.{u} :=
  { hasNat          := hasNaturality,
    hasRevAppFunFun := hasRevAppFunFun }

end type
