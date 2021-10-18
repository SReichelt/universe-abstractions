import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.FunctorExtensionality
import UniverseAbstractions.Axioms.Universe.Singletons
import UniverseAbstractions.Lemmas.DerivedFunctors
import UniverseAbstractions.Lemmas.DerivedFunctorExtensionality



set_option autoBoundImplicitLocal false
--set_option pp.universes true



namespace HasInternalTop

  open HasFunctors HasLinearFunOp HasLinearFunOp.HasLinearFunExt HasTop HasTopExt

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasInternalTop U]

  def defIntroFun [HasConstFun U U] (A : U) : A ⟶[λ _ => top U] Top U :=
  HasConstFun.defConstFun A (top U)

  @[reducible] def introFun [HasConstFun U U] (A : U) : A ⟶ Top U := defIntroFun A

  def defElimFunFun [HasLinearFunOp U] [HasTopExt U] (A : U) :
    A ⟶[λ a => defElimFun a] (Top U ⟶ A) :=
  swapFunFun (elimFun (idFun A))
  ◄ swapElim _

  @[reducible] def elimFunFun [HasLinearFunOp U] [HasTopExt U] (A : U) :
    A ⟶ Top U ⟶ A :=
  defElimFunFun A

  def defInvElimFun [HasLinearFunOp U] (A : U) : (Top U ⟶ A) ⟶[λ F => F (top U)] A :=
  defAppFun (top U) A

  @[reducible] def invElimFun [HasLinearFunOp U] (A : U) : (Top U ⟶ A) ⟶ A := defInvElimFun A

  namespace HasTopExt

    def topEqExtExt [HasLinearFunOp U] [HasLinearFunExt U] [HasTopExt U] {A : U}
                    (F : A ⟶ Top U ⟶ A) (h : swapFun F (top U) ≃ idFun A) :
      F ≃ elimFunFun A :=
    (reverseSwap (topEqExt (h • byDef)))⁻¹

  end HasTopExt

end HasInternalTop



namespace HasInternalBot

  open HasLinearFunOp HasBot

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasInternalBot U]

  def contraIntroFun [HasLinearFunOp U] (A : U) : A ⟶ Not A ⟶ Bot U :=
  appFunFun A (Bot U)

  def notNotFun [HasLinearFunOp U] (A : U) : A ⟶ Not (Not A) := contraIntroFun A

  def notTopIntroFun [HasLinearFunOp U] [HasInternalTop U] : Not (HasTop.Top U) ⟶ Bot U :=
  HasInternalTop.invElimFun (Bot U)

end HasInternalBot
