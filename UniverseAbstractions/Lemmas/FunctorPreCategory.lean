import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Relations
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.FunctorExtensionality
import UniverseAbstractions.Axioms.CategoryTheory.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true



namespace HasLinearFunOp.HasLinearFunExt

  open MetaRelation IsCategoricalPreorder CategoryTheory

  variable {U : Universe} [HasIdentity U] [hFun : HasInternalFunctors U] [HasLinearFunOp U]
           [h : HasLinearFunExt U]

  -- The axioms for composition and identity imply that types and functors form a (potentially
  -- higher) category.

  instance isCategoricalPreorder : IsCategoricalPreorder hFun.Fun :=
  { assoc          := h.compAssoc,
    rightId        := h.rightId,
    leftId         := h.leftId }

  instance isCategoricalPreorderExt : IsCategoricalPreorderExt hFun.Fun :=
  { assocExt       := h.compAssocExt,
    assocExtExt    := h.compAssocExtExt,
    assocExtExtExt := h.compAssocExtExtExt,
    rightIdExt     := h.rightIdExt,
    leftIdExt      := h.leftIdExt }

  instance isPreCategory : IsPreCategory ⟨U⟩ U := ⟨hFun.Fun⟩

end HasLinearFunOp.HasLinearFunExt
