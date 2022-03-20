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



namespace HasLinearFunOp.HasLinearFunExt

  open MetaRelation IsCategoricalPreorder CategoryTheory

  variable (U : Universe.{u, uu}) [hHomUniv : IsHomUniverse.{u, uu, iu, iuu} U]
           [h : HasLinearFunExt U]

  -- The axioms for composition and identity imply that types and functors form a weak
  -- "extensional" category, i.e. a weak bicategory.

  instance isCategoricalPreorder : IsCategoricalPreorder hHomUniv.Fun :=
  { assoc   := h.compAssoc,
    rightId := h.rightId,
    leftId  := h.leftId }

  instance isCategoricalPreorderExt : IsCategoricalPreorderExt hHomUniv.Fun :=
  { assocExt       := h.compAssocExt,
    assocExtExt    := h.compAssocExtExt,
    assocExtExtExt := h.compAssocExtExtExt,
    rightIdExt     := h.rightIdExt,
    leftIdExt      := h.leftIdExt }

  def funRel : BundledRelation.{uu, 0, u, uu} {U} U := ⟨PUnit.unit, hHomUniv.Fun⟩

  def category : CatDesc (funRel U) :=
  { homIsPreorder            := isPreorder,
    homHasTransFun           := hasTransFun,
    homIsCategoricalPreorder := isCategoricalPreorder U }

  def categoryExt : CatDesc.CatDescExt (funRel U) :=
  { homIsCategoricalPreorderExt := isCategoricalPreorderExt U }

end HasLinearFunOp.HasLinearFunExt
