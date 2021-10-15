-- TODO: Adapt to `HasIdentity`.
#exit 0



import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Singletons



set_option autoBoundImplicitLocal false
--set_option pp.universes true



namespace HasInternalTop

  open HasTop

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasInternalTop U]

  def defIntroFun [HasConstFun U U] (A : U) : A ⟶[λ _ => top U] Top U :=
  HasConstFun.defConstFun A (top U)

  @[reducible] def introFun [HasConstFun U U] (A : U) : A ⟶ Top U := defIntroFun A

  def defInvElimFun [HasLinearFunOp U] (A : U) : (Top U ⟶ A) ⟶[λ F => F (top U)] A :=
  HasLinearFunOp.defAppFun (top U) A

  @[reducible] def invElimFun [HasLinearFunOp U] (A : U) : (Top U ⟶ A) ⟶ A := defInvElimFun A

end HasInternalTop



namespace HasInternalBot

  open HasBot

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasInternalBot U]

  def contraIntroFun [HasLinearFunOp U] (A : U) : A ⟶ Not A ⟶ Bot U :=
  HasLinearFunOp.appFunFun A (Bot U)

  def notNotFun [HasLinearFunOp U] (A : U) : A ⟶ Not (Not A) := contraIntroFun A

  def notTopIntroFun [HasLinearFunOp U] [HasInternalTop U] : Not (HasTop.Top U) ⟶ Bot U :=
  HasInternalTop.invElimFun (Bot U)

end HasInternalBot
