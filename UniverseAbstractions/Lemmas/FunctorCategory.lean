import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.MetaRelations
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.FunctorExtensionality
import UniverseAbstractions.Axioms.CategoryTheory.Basic
import UniverseAbstractions.Axioms.CategoryTheory.Extensional.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true



namespace HasLinearFunOp.HasLinearFunExt

  open MetaRelation IsCategoricalPreorder CategoryTheory IsCategory

  variable {U : Universe} [hHomUniv : IsHomUniverse U] [h : HasLinearFunExt U]

  -- The axioms for composition and identity imply that types and functors form a (potentially
  -- higher) category.

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

  instance isCategory : IsCategory U U :=
  { Hom                      := hHomUniv.Fun,
    homIsPreorder            := isPreorder,
    homHasTransFun           := hasTransFun,
    homIsCategoricalPreorder := isCategoricalPreorder }

  instance isCategoryExt : IsCategoryExt U :=
  { homIsCategoricalPreorderExt := isCategoricalPreorderExt }

end HasLinearFunOp.HasLinearFunExt
