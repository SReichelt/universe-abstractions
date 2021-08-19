import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Singletons



set_option autoBoundImplicitLocal false
--set_option pp.universes true



namespace HasFunctorialTop

  open HasEmbeddedTop

  variable {U : Universe} [HasEmbeddedFunctors U] [HasFunctorialTop U]

  def defIntroFun [HasSubLinearFunOp U] (α : U) : α ⟶[λ _ => top U] Top U :=
  HasSubLinearFunOp.defConstFun α (top U)

  @[reducible] def introFun [HasSubLinearFunOp U] (α : U) : α ⟶ Top U := defIntroFun α

  def defInvElimFun [HasLinearFunOp U] (α : U) : (Top U ⟶ α) ⟶[λ F => F (top U)] α :=
  HasLinearFunOp.defAppFun (top U) α

  @[reducible] def invElimFun [HasLinearFunOp U] (α : U) : (Top U ⟶ α) ⟶ α := defInvElimFun α

end HasFunctorialTop



namespace HasFunctorialBot

  open HasEmbeddedBot

  variable {U : Universe} [HasEmbeddedFunctors U] [HasFunctorialBot U]

  def contraIntroFun [HasLinearFunOp U] (α : U) : α ⟶ Not α ⟶ Bot U :=
  HasLinearFunOp.appFunFun α (Bot U)

  def notNotFun [HasLinearFunOp U] (α : U) : α ⟶ Not (Not α) := contraIntroFun α

  def notTopIntroFun [HasLinearFunOp U] [HasFunctorialTop U] : Not (HasEmbeddedTop.Top U) ⟶ Bot U :=
  HasFunctorialTop.invElimFun (Bot U)

end HasFunctorialBot
