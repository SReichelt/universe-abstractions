import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Singletons



set_option autoBoundImplicitLocal false
--set_option pp.universes true



namespace HasEmbeddedTop

  open HasTop

  variable {U : Universe} [HasEmbeddedFunctors U] [HasEmbeddedTop U]

  def defIntroFun [HasSubLinearFunOp U] (A : U) : A ⟶[λ _ => top U] Top U :=
  HasSubLinearFunOp.defConstFun A (top U)

  @[reducible] def introFun [HasSubLinearFunOp U] (A : U) : A ⟶ Top U := defIntroFun A

  def defInvElimFun [HasLinearFunOp U] (A : U) : (Top U ⟶ A) ⟶[λ F => F (top U)] A :=
  HasLinearFunOp.defAppFun (top U) A

  @[reducible] def invElimFun [HasLinearFunOp U] (A : U) : (Top U ⟶ A) ⟶ A := defInvElimFun A

end HasEmbeddedTop



namespace HasEmbeddedBot

  open HasBot

  variable {U : Universe} [HasEmbeddedFunctors U] [HasEmbeddedBot U]

  def contraIntroFun [HasLinearFunOp U] (A : U) : A ⟶ Not A ⟶ Bot U :=
  HasLinearFunOp.appFunFun A (Bot U)

  def notNotFun [HasLinearFunOp U] (A : U) : A ⟶ Not (Not A) := contraIntroFun A

  def notTopIntroFun [HasLinearFunOp U] [HasEmbeddedTop U] : Not (HasTop.Top U) ⟶ Bot U :=
  HasEmbeddedTop.invElimFun (Bot U)

end HasEmbeddedBot
