import UniverseAbstractions.Instances.Basic
import UniverseAbstractions.Instances.Utils.TrivialCategoryTheory
import UniverseAbstractions.Axioms.CategoryTheory.Meta
import UniverseAbstractions.Axioms.CategoryTheory.Basic
import UniverseAbstractions.Axioms.CategoryTheory.Extended
import UniverseAbstractions.Axioms.CategoryTheory.Isomorphisms



set_option autoBoundImplicitLocal false
set_option synthInstance.maxHeartbeats 10000
--set_option pp.universes true

universe u v w



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

namespace type

  open MetaRelation MetaFunctor CategoryTheory IsCategory HasIsoRel

  instance isHomUniverse : IsHomUniverse type.{w} := ⟨⟩

  -- Functors

  def FunProp (α : Type u) (β : Sort v) [hα : IsCategory type.{w} α] [hβ : IsCategory type.{w} β] :
    MetaProperty (α → β) type.{max u w} :=
  FunDesc

  -- TODO: Is there really no way around the strangely restrictive universe constraint regarding `u`, here and below?
  --       (In particular, `type.{max u w}` seems like it should work.)
  instance hasFunProp (α : Type u) (β : Sort v) [hα : IsCategory type.{u} α]
                                                [hβ : IsCategory type.{u} β] :
    HasFunProp α β :=
  { Fun  := FunProp α β,
    desc := id }

  def defFun {α : Type u} {β : Sort v} [hα : IsCategory type.{u} α] [hβ : IsCategory type.{u} β]
             {φ : α → β} (F : FunDesc φ) :
    HasFunProp.DefFun F :=
  { F  := F,
    eq := λ _ _ => rfl }

  instance hasTrivialFunctorialityCondition (α : Type u) (β : Sort v) [hα : IsCategory type.{u} α]
                                                                      [hβ : IsCategory type.{u} β] :
    HasFunProp.HasTrivialFunctorialityCondition α β :=
  ⟨defFun⟩

  instance isFunUniverse : IsFunUniverse.{u + 1} type.{u} :=
  { hasFun := hasFunProp }

  instance isFunUniverse.hasAffineFunctors : IsFunUniverse.HasAffineFunctors type.{u} :=
  { hasIdFun    := λ α     => HasFunProp.HasIdFun.trivial    α,
    hasConstFun := λ α β   => HasFunProp.HasConstFun.trivial α β,
    hasCompFun  := λ α β γ => HasFunProp.HasCompFun.trivial  α β γ }

  -- Natural transformations

  theorem IsNaturalTransformation.ext {α : Type u} {β : Sort v} [hα : HasMorphisms type.{w} α]
                                                                [hβ : IsSemicategory type.{w} β]
                                      {F G : MorphismFunctor α β} (η : Quantification F G)
                                      (h₁ h₂ : IsNaturalTransformation η) :
    h₁ = h₂ :=
  match h₁, h₂ with
  | { toIsNatural := ⟨_⟩ }, { toIsNatural := ⟨_⟩ } => rfl

  theorem NatDesc.ext {α : Type u} {β : Sort v} [hα : IsCategory type.{u} α]
                                                [hβ : IsCategory type.{u} β]
                      {F G : α ⮕ β} (η₁ η₂ : NatDesc F G) :
    (∀ a, η₁.η a = η₂.η a) → η₁ = η₂ :=
  match η₁, η₂ with
  | { η := nat₁, isNat := isNat₁ }, { η := nat₂, isNat := isNat₂ } =>
    λ h => by have hNat : nat₁ = nat₂ := funext h;
              subst hNat;
              have hIsNat : isNat₁ = isNat₂ :=
                   IsNaturalTransformation.ext (hα := hα.toHasMorphisms)
                                               (hβ := IsCategory.isSemicategory (h := hβ))
                                               nat₁ isNat₁ isNat₂;
              subst hIsNat; rfl

  def NatRel (α : Type u) (β : Sort v) [hα : IsCategory type.{u} α] [hβ : IsCategory type.{u} β] :
    MetaRelation (α ⮕ β) type.{u} :=
  NatDesc

  instance hasNaturalityRelation (α : Type u) (β : Sort v) [hα : IsCategory type.{u} α]
                                                           [hβ : IsCategory type.{u} β] :
    HasNatRel.{u + 1} α β :=
  { Nat       := NatRel α β,
    desc      := id,
    defNatFun := λ _ _ _ => HasTrivialFunctoriality.defFun }

  def defNat {α : Type u} {β : Sort v} [hα : IsCategory type.{u} α] [hβ : IsCategory type.{u} β]
             {F G : α ⮕ β} (η : NatDesc F G) :
    HasNatRel.DefNat η :=
  { η     := η,
    natEq := λ _ => rfl }

  instance hasTrivialNaturalityCondition (α : Type u) (β : Sort v) [hα : IsCategory type.{u} α]
                                                                   [hβ : IsCategory type.{u} β] :
    HasNatRel.HasTrivialNaturalityCondition.{u + 1} α β :=
  ⟨defNat⟩

  instance hasTrivialNatEquiv (α : Type u) (β : Sort v) [hα : IsCategory type.{u} α]
                                                        [hβ : IsCategory type.{u} β] :
    HasNatRel.HasTrivialNatEquiv.{u + 1} α β :=
  ⟨NatDesc.ext⟩

  instance natIsPreorder (α : Type u) (β : Sort v) [hα : IsCategory type.{u} α]
                                                   [hβ : IsCategory type.{u} β] :
    IsPreorder (NatRel α β) :=
  HasNatOp.natIsPreorder α β

  instance hasNaturality (α : Type u) (β : Sort v) [hα : IsCategory type.{u} α]
                                                   [hβ : IsCategory type.{u} β] :
    HasNaturality.{u + 1} α β :=
  { natHasTransFun := HasTrivialFunctoriality.hasTransFun (NatRel α β) }

  def defFunFunBaseBase {α β : Type u} {γ : Sort v} [hα : IsCategory type.{u} α]
                        [hβ : IsCategory type.{u} β] [hγ : IsCategory type.{u} γ]
                        {F : α → (β ⮕ γ)} {desc : HasNaturality.FunFunDesc F} :
    HasNaturality.DefFunFunBaseBase desc :=
  { defNat     := λ _   => HasNatRel.HasTrivialNaturalityCondition.defNat,
    natReflEq  := λ _   => HasNatRel.HasTrivialNatEquiv.natEquiv,
    natTransEq := λ _ _ => HasNatRel.HasTrivialNatEquiv.natEquiv }

  def defFunFunBase {α β : Type u} {γ : Sort v} [hα : IsCategory type.{u} α]
                    [hβ : IsCategory type.{u} β] [hγ : IsCategory type.{u} γ]
                    {F : α → (β ⮕ γ)} {desc : HasNaturality.FunFunDesc F} :
    HasNaturality.DefFunFunBase desc :=
  { toDefFunFunBaseBase := defFunFunBaseBase,
    defNatFun  := λ _ _ => HasTrivialFunctoriality.defFun }

  def defFunFun {α β : Type u} {γ : Sort v} [hα : IsCategory type.{u} α]
                [hβ : IsCategory type.{u} β] [hγ : IsCategory type.{u} γ]
                {F : α → (β ⮕ γ)} {desc : HasNaturality.FunFunDesc F} :
    HasNaturality.DefFunFun desc :=
  { toDefFunFunBase := defFunFunBase,
    defFunFun       := HasFunProp.HasTrivialFunctorialityCondition.defFun }

  def defNatNatBase {α β : Type u} {γ : Sort v} [hα : IsCategory type.{u} α]
                    [hβ : IsCategory type.{u} β] [hγ : IsCategory type.{u} γ]
                    {F G : α ⮕ β ⮕ γ} {η : ∀ a, F.φ a ⇾ G.φ a}
                    {desc : HasNaturality.NatNatDesc F G η} :
    HasNaturality.DefNatNatBase desc :=
  { natEquiv := λ _ => HasNatRel.HasTrivialNatEquiv.natEquiv }

  def defNatNat {α β : Type u} {γ : Sort v} [hα : IsCategory type.{u} α]
                [hβ : IsCategory type.{u} β] [hγ : IsCategory type.{u} γ]
                {F G : α ⮕ β ⮕ γ} {η : ∀ a, F.φ a ⇾ G.φ a}
                {desc : HasNaturality.NatNatDesc F G η} :
    HasNaturality.DefNatNat desc :=
  { toDefNatNatBase := defNatNatBase,
    defNatNat       := HasNatRel.HasTrivialNaturalityCondition.defNat }

  def defFunFunFunBase {α β γ : Type u} {δ : Sort v} [hα : IsCategory type.{u} α]
                       [hβ : IsCategory type.{u} β] [hγ : IsCategory type.{u} γ]
                       [hδ : IsCategory type.{u} δ]
                       {F : α → (β ⮕ γ ⮕ δ)} {desc : HasNaturality.FunFunFunDesc F} :
    HasNaturality.DefFunFunFunBase desc :=
  { defRevFunFun := λ _ => defFunFunBaseBase,
    defNatNat    := λ _ => defNatNatBase }

  def defFunFunFun {α β γ : Type u} {δ : Sort v} [hα : IsCategory type.{u} α]
                   [hβ : IsCategory type.{u} β] [hγ : IsCategory type.{u} γ]
                   [hδ : IsCategory type.{u} δ]
                   {F : α → (β ⮕ γ ⮕ δ)} {desc : HasNaturality.FunFunFunDesc F} :
    HasNaturality.DefFunFunFun desc :=
  { toDefFunFunFunBase := defFunFunFunBase,
    defFunFunFun       := defFunFun }

  instance hasRevAppFunFun (α β : Type u) [hα : IsCategory type.{u} α] [hβ : IsCategory type.{u} β] :
    HasNaturality.HasRevAppFunFun α β :=
  { defRevAppFun    := λ _ => HasFunProp.HasTrivialFunctorialityCondition.defFun,
    defRevAppFunFun := defFunFun }

  instance hasCompFunFunFun (α β γ : Type u) [hα : IsCategory type.{u} α] [hβ : IsCategory type.{u} β]
                            [hγ : IsCategory type.{u} γ] :
    HasNaturality.HasCompFunFunFun α β γ :=
  { defCompFunFun    := λ _ => defFunFun,
    defCompFunFunFun := defFunFunFun }

  instance hasConstFunFun (α β : Type u) [hα : IsCategory type.{u} α] [hβ : IsCategory type.{u} β] :
    HasNaturality.HasConstFunFun α β :=
  { defConstFunFun := defFunFun }

  instance hasDupFunFun (α β : Type u) [hα : IsCategory type.{u} α] [hβ : IsCategory type.{u} β] :
    HasNaturality.HasDupFunFun α β :=
  { defDupFun    := λ _ => HasFunProp.HasTrivialFunctorialityCondition.defFun,
    defDupFunFun := defFunFun }

  instance isNatUniverse : IsNatUniverse.{u + 1} type.{u} :=
  { hasNat := hasNaturality }

  instance isNatUniverse.hasFullFunctors : IsNatUniverse.HasFullFunctors type.{u} :=
  { hasRevAppFunFun  := hasRevAppFunFun,
    hasCompFunFunFun := hasCompFunFunFun,
    hasConstFunFun   := hasConstFunFun,
    hasDupFunFun     := hasDupFunFun }

  -- Isomorphisms

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

  def IsoRel (α : Type u) [hα : IsCategory type.{u} α] : MetaRelation α type.{u} := IsoDesc

  instance hasIsoRel (α : Type u) [hα : IsCategory type.{u} α] : HasIsoRel α :=
  { Iso         := IsoRel α,
    desc        := id,
    defToHomFun := λ _ _ => HasTrivialFunctoriality.defFun,
    toHomInj    := IsoDesc.ext' }

  def defIso {α : Type u} [hα : IsCategory type.{u} α] {a b : α} (e : IsoDesc a b) :
    DefIso e :=
  { e    := e,
    toEq := rfl }

  instance hasTrivialIsomorphismCondition (α : Type u) [hα : IsCategory type.{u} α] :
    HasTrivialIsomorphismCondition α :=
  ⟨defIso⟩

  instance isoIsEquivalence (α : Type u) [hα : IsCategory type.{u} α] :
    IsEquivalence (IsoRel α) :=
  HasIsoOp.isoIsEquivalence α

  instance hasIsomorphisms (α : Type u) [hα : IsCategory type.{u} α] : HasIsomorphisms α :=
  { isoHasSymmFun  := HasTrivialFunctoriality.hasSymmFun  (IsoRel α),
    isoHasTransFun := HasTrivialFunctoriality.hasTransFun (IsoRel α) }

  instance hasIsoFun {α β : Type u} [hα : IsCategory type.{u} α] [hβ : IsCategory type.{u} β]
                     (F : α ⮕ β) :
    HasIsoFun F :=
  { defMapIso    := λ _   => HasTrivialIsomorphismCondition.defIso,
    defMapIsoFun := λ _ _ => HasTrivialFunctoriality.defFun,
    defIsoFun    := HasFunProp.HasTrivialFunctorialityCondition.defFun
                      (hα := HasIsomorphisms.isoCategory α) (hβ := HasIsomorphisms.isoCategory β) }

  instance hasIsoNat {α β : Type u} [hα : IsCategory type.{u} α] [hβ : IsCategory type.{u} β]
                     (F G : α ⮕ β) :
    HasIsoNat F G :=
  { defNatIso    := λ _ _ => HasTrivialIsomorphismCondition.defIso,
    defNatIsoFun := λ _   => HasTrivialFunctoriality.defFun }

  instance isIsoUniverse : IsIsoUniverse.{u + 1} type.{u} :=
  { hasIso    := hasIsomorphisms,
    hasIsoFun := hasIsoFun,
    hasIsoNat := hasIsoNat }

  instance hasIsoFunctoriality (α β : Type u) [hα : IsCategory type.{u} α]
                                              [hβ : IsCategory type.{u} β] :
    HasIsoFunctoriality α β :=
  IsIsoUniverse.hasIsoFunctoriality (W := type.{u}) α β

  instance hasIsoNaturality (α β : Type u) [hα : IsCategory type.{u} α]
                                           [hβ : IsCategory type.{u} β] :
    HasIsoNaturality α β :=
  IsIsoUniverse.hasIsoNaturality (W := type.{u}) α β

  def natIsoDescBuilder {α β : Type u} [hα : IsCategory type.{u} α] [hβ : IsCategory type.{u} β]
                        {F G : α ⮕ β} (η : NatIsoDesc F G) :
    NatIsoDesc.IsoDescBuilder η :=
  { defToNat  := HasNatRel.HasTrivialNaturalityCondition.defNat,
    defInvNat := HasNatRel.HasTrivialNaturalityCondition.defNat,
    leftInv   := HasNatRel.HasTrivialNatEquiv.natEquiv,
    rightInv  := HasNatRel.HasTrivialNatEquiv.natEquiv }

  def defNatIso {α β : Type u} [hα : IsCategory type.{u} α] [hβ : IsCategory type.{u} β]
                {F G : α ⮕ β} (η : NatIsoDesc F G) :
    HasIsoNat.DefNatIso η :=
  { η     := NatIsoDesc.IsoDescBuilder.isoDesc η (natIsoDescBuilder η),
    natEq := λ _ => rfl }

  instance hasTrivialNatIsoCondition (α β : Type u) [hα : IsCategory type.{u} α]
                                                    [hβ : IsCategory type.{u} β] :
    HasIsoNaturality.HasTrivialNaturalityCondition.{u + 1} α β :=
  ⟨defNatIso⟩

  def defNatNatIsoBase {α β γ : Type u} [hα : IsCategory type.{u} α]
                       [hβ : IsCategory type.{u} β] [hγ : IsCategory type.{u} γ]
                       {F G : α ⮕ β ⮕ γ} {η : ∀ a, F.φ a ⇿ G.φ a}
                       {desc : HasIsoNaturality.NatNatIsoDesc F G η} :
    HasIsoNaturality.DefNatNatIsoBase desc :=
  -- Lean bug :-(
  sorry
  --{ toDef  := defNatNatBase,
  --  invDef := defNatNatBase }

  def defNatNatIso {α β γ : Type u} [hα : IsCategory type.{u} α]
                   [hβ : IsCategory type.{u} β] [hγ : IsCategory type.{u} γ]
                   {F G : α ⮕ β ⮕ γ} {η : ∀ a, F.φ a ⇿ G.φ a}
                   {desc : HasIsoNaturality.NatNatIsoDesc F G η} :
    HasIsoNaturality.DefNatNatIso desc :=
  -- Lean bug :-(
  sorry
  --{ toDefNatNatIsoBase := defNatNatIsoBase,
  --  defNatNatIso       := HasIsoNaturality.HasTrivialNaturalityCondition.defNatIso }

  instance hasRightIdNatNat (α β : Type u) [hα : IsCategory type.{u} α]
                                           [hβ : IsCategory type.{u} β] :
    HasIsoNaturality.HasRightIdNatNat α β :=
  -- Lean bug :-(
  sorry
  --{ defRightIdNat    := λ _ => HasIsoNaturality.HasTrivialNaturalityCondition.defNatIso,
  --  defRightIdNatNat := defNatNatIso }

  instance hasLeftIdNat (α β : Type u) [hα : IsCategory type.{u} α]
                                       [hβ : IsCategory type.{u} β] :
    HasIsoNaturality.HasLeftIdNat α β :=
  -- Lean bug :-(
  sorry
  --{ defLeftIdNat := λ _ => HasIsoNaturality.HasTrivialNaturalityCondition.defNatIso }

  instance isIsoUniverse.hasFullNaturalIsomorphisms :
    IsIsoUniverse.HasFullNaturalIsomorphisms type.{u} :=
  { hasRightIdNatNat := hasRightIdNatNat,
    hasLeftIdNat     := hasLeftIdNat,
    hasSwapRevAppNat := sorry,
    hasCompAssocNat  := sorry }

end type
