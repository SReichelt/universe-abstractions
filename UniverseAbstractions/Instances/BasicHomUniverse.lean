import UniverseAbstractions.Instances.Basic
import UniverseAbstractions.Instances.Utils.TrivialCategoryTheory
import UniverseAbstractions.Axioms.CategoryTheory.Meta
import UniverseAbstractions.Axioms.CategoryTheory.Basic
import UniverseAbstractions.Axioms.CategoryTheory.Extended



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u



namespace type

  open MetaRelation MetaFunctor CategoryTheory IsCategory HasIsoRel

  def isoRel (α : Type u) [hα : IsCategory type.{u} α] : MetaRelation α type.{u} := IsoDesc

  theorem IsoDesc.ext {α : Type u} [hα : IsCategory type.{u} α] {a b : α} {e₁ e₂ : IsoDesc a b} :
    e₁.toHom = e₂.toHom ∧ e₁.invHom = e₂.invHom → e₁ = e₂ :=
  sorry

  theorem IsoDesc.ext' {α : Type u} [hα : IsCategory type.{u} α] {a b : α} {e₁ e₂ : IsoDesc a b}
                       (h : e₁.toHom = e₂.toHom) :
    e₁ = e₂ :=
  IsoDesc.ext ⟨h, IsoDesc.toInvEquiv (e₁ := e₁) (e₂ := e₂) h⟩

  instance isoIsEquivalence (α : Type u) [hα : IsCategory type.{u} α] :
    IsEquivalence (isoRel α) :=
  { refl  := IsoDesc.refl,
    symm  := IsoDesc.symm,
             -- TODO: Using `IsoDesc.trans` here results in a strange Lean error.
    trans := λ e f => ⟨f.toHom • e.toHom, e.invHom • f.invHom⟩ }

  instance isoInv {α : Type u} [hα : IsCategory type.{u} α] {a b : α} (e : IsoDesc a b) :
    IsInv (isoRel α) e (IsoDesc.symm e) :=
  { leftInv  := IsoDesc.ext ⟨e.isInv.leftInv,  e.isInv.leftInv⟩,
    rightInv := IsoDesc.ext ⟨e.isInv.rightInv, e.isInv.rightInv⟩ }

  def toHomMetaFunctor (α : Type u) [hα : IsCategory type.{u} α] : MetaFunctor (isoRel α) hα.Hom :=
  ⟨λ _ _ => IsoDesc.toHom⟩

  instance toHomIsPreorderFunctor (α : Type u) [hα : IsCategory type.{u} α] :
    IsPreorderFunctor (toHomMetaFunctor α) :=
  { reflEq  := λ _   => rfl,
    transEq := λ _ _ => rfl }

  instance hasIsoRel (α : Type u) [hα : IsCategory type.{u} α] : HasIsoRel α :=
  { Iso                    := isoRel α,
    isoIsEquivalence       := isoIsEquivalence α,
    isoInv                 := isoInv,
    isoHasSymmFun          := HasTrivialFunctoriality.hasSymmFun (isoRel α),
    isoHasTransFun         := HasTrivialFunctoriality.hasTransFun (isoRel α),
    desc                   := id,
    defToHomFun            := λ _ _ => HasTrivialFunctoriality.defFun,
    toHomIsPreorderFunctor := toHomIsPreorderFunctor α,
    toHomInj               := IsoDesc.ext' }

  instance isoIsGroupoidEquivalence (α : Type u) [hα : IsCategory type.{u} α] :
    IsGroupoidEquivalence (isoRel α) :=
  HasIsoRel.isoIsGroupoidEquivalence

  instance hasIsoRelExt (α : Type u) [hα : IsCategory type.{u} α] : HasIsoRelExt α :=
  { toHomIsTransFunctorExt      := HasTrivialExtensionality.isTransFunctorExt (toHomMetaFunctor α),
    isoIsGroupoidEquivalenceExt := HasTrivialExtensionality.isGroupoidEquivalenceExt (isoRel α) }

  instance hasIsomorphisms (α : Type u) [hα : IsCategory type.{u} α] : HasIsomorphisms α := ⟨⟩

  instance isIsoUniverse : IsIsoUniverse.{u} type.{u} :=
  { hasIsomorphisms := hasIsomorphisms }

  instance hasFunProp (α β : Type u) [hα : IsCategory type.{u} α] [hβ : IsCategory type.{u} β] :
    HasFunctorialityProperty α β :=
  { Fun               := IsCategoryFunctor,
    isCategoryFunctor := id }

  def isoPreFunctor {α β : Type u} [hα : IsCategory type.{u} α] [hβ : IsCategory type.{u} β]
                    (φ : α → β) [hφ : IsCategoryFunctor φ] :
    PreFunctor (isoRel α) (isoRel β) φ :=
  ⟨λ a b e => IsoDesc.map φ e⟩

  instance isIsoFun {α β : Type u} [hα : IsCategory type.{u} α] [hβ : IsCategory type.{u} β]
                    (F : HasFunctorialityProperty.Functor α β) :
    IsIsoFunctor F.φ :=
  { F              := isoPreFunctor F.φ,
    homIsoCongr    := λ _   => rfl,
    homIsoCongrExt := λ _ _ => rfl }

  instance hasIsoFun (α β : Type u) [hα : IsCategory type.{u} α] [hβ : IsCategory type.{u} β] :
    HasIsoFunctoriality α β :=
  { isIsoFun := isIsoFun }

  def defFun {α β : Type u} [hα : IsCategory type.{u} α] [hβ : IsCategory type.{u} β]
             {φ : α → β} [hφ : IsCategoryFunctor φ] :
    HasFunctorialityProperty.DefFun φ :=
  { F  := hφ,
    eq := λ a b => HasInstanceEquivalences.refl (hφ.F.baseFun a b) }

  instance isFunUniverse : IsFunUniverse.{u} type.{u} :=
  { hasFunProp  := hasIsoFun,
    defIdFun    := λ _               => defFun,
    defConstFun := λ _ {_} [_] [_] _ => defFun,
    defCompFun  := λ _ _             => defFun }

end type
