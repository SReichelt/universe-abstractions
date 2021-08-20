import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Singletons



set_option autoBoundImplicitLocal false
--set_option pp.universes true



namespace HasEmbeddedTop

  open HasTop

  variable {U : Universe} [HasEmbeddedFunctors U] [HasEmbeddedTop U]

  def defIntroFun [HasSubLinearFunOp U] (α : U) : α ⟶[λ _ => top U] Top U :=
  HasSubLinearFunOp.defConstFun α (top U)

  @[reducible] def introFun [HasSubLinearFunOp U] (α : U) : α ⟶ Top U := defIntroFun α

  def defInvElimFun [HasLinearFunOp U] (α : U) : (Top U ⟶ α) ⟶[λ F => F (top U)] α :=
  HasLinearFunOp.defAppFun (top U) α

  @[reducible] def invElimFun [HasLinearFunOp U] (α : U) : (Top U ⟶ α) ⟶ α := defInvElimFun α

end HasEmbeddedTop



namespace HasEmbeddedBot

  open HasBot

  variable {U : Universe} [HasEmbeddedFunctors U] [HasEmbeddedBot U]

  def contraIntroFun [HasLinearFunOp U] (α : U) : α ⟶ Not α ⟶ Bot U :=
  HasLinearFunOp.appFunFun α (Bot U)

  def notNotFun [HasLinearFunOp U] (α : U) : α ⟶ Not (Not α) := contraIntroFun α

  def notTopIntroFun [HasLinearFunOp U] [HasEmbeddedTop U] : Not (HasTop.Top U) ⟶ Bot U :=
  HasEmbeddedTop.invElimFun (Bot U)

end HasEmbeddedBot
