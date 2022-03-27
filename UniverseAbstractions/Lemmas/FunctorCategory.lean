import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.MetaRelations
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.FunctorExtensionality
import UniverseAbstractions.CategoryTheory.Meta
import UniverseAbstractions.CategoryTheory.Basic
import UniverseAbstractions.CategoryTheory.Extensional.Meta
import UniverseAbstractions.CategoryTheory.Extensional.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u uu iu iuu



namespace CategoryTheory

  open MetaRelation IsCategoricalPreorder CategoryTheory HasCatProp HasCatProp.Category
       HasLinearFunOp

  variable (U : Universe.{u, uu}) [hHomUniv : IsHomUniverse.{u, uu, iu, iuu} U]
           [h : HasLinearFunExt U]

  -- The axioms for composition and identity imply that types and functors form a weak
  -- "extensional" category, i.e. a weak bicategory.
  -- TODO: We should probably rename `FunctorCategory.lean`. The category corresponds to Set or
  -- Cat (depending on `U`).

  instance funIsCategoricalPreorder : IsCategoricalPreorder hHomUniv.Fun :=
  { assoc   := h.compAssoc,
    rightId := h.rightId,
    leftId  := h.leftId }

  instance funIsCategoricalPreorderExt : IsCategoricalPreorderExt hHomUniv.Fun :=
  { assocExt       := h.compAssocExt,
    assocExtExt    := h.compAssocExtExt,
    assocExtExtExt := h.compAssocExtExtExt,
    rightIdExt     := h.rightIdExt,
    leftIdExt      := h.leftIdExt }

  def funRel : BundledRelation.{uu, 0, u, uu} {U} U :=
  { A   := PUnit.unit,
    Hom := hHomUniv.Fun }

  def typeCatDesc : CatDesc (funRel U) :=
  { homIsPreorder            := HasLinearFunOp.isPreorder,
    homHasTransFun           := HasLinearFunOp.hasTransFun,
    homIsCategoricalPreorder := funIsCategoricalPreorder U }

  def typeCatDescExt : CatDesc.CatDescExt (funRel U) :=
  { homIsCategoricalPreorderExt := funIsCategoricalPreorderExt U }

  -- TODO: This cannot be implemented for `type` and `setoid` because of Lean universe
  -- restrictions. That's probably related to Set being a large category. Can we work around this
  -- e.g. by specifying a subset of types?
  class HasTypeCat [HasCatProp {U} U] where
  (defTypeCat : DefCat (typeCatDesc U))

  namespace HasTypeCat

    variable [HasCatProp {U} U] [h : HasTypeCat U]

    def typeCat : Category {U} U := DefCat.toCategory h.defTypeCat

  end HasTypeCat

end CategoryTheory
