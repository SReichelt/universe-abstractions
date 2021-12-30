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

  open HasFunctors HasCongrArg HasCongrFun HasRevAppFun HasLinearFunOp HasSubLinearFunOp HasAffineFunOp
       HasSubsingletonExt HasLinearFunExt HasAffineFunExt HasTop HasTopEq HasTopExt

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasInternalTop U]

  def defIntroFun [HasConstFun U U] (A : U) : A ⟶{λ _ => top U} Top U :=
  HasConstFun.defConstFun A (top U)

  @[reducible] def introFun [HasConstFun U U] (A : U) : A ⟶ Top U := defIntroFun A

  def HasTopExt.introFunEq [HasConstFun U U] [HasSubsingletonExt U U] [HasTopEq U]
                           {A : U} (F : A ⟶ Top U) :
    F ≃{λ a => topEq (F a) ◅} introFun A :=
  eqExt F (introFun A)

  def HasTopExt.elimFunConstEq [HasConstFun U U] [HasTopExt U] {A : U} (a : A) :
    elimFun a ≃ HasConstFun.constFun (Top U) a :=
  (elimFunEq byDef)⁻¹

  def defElimFunFun [HasLinearFunOp U] [HasTopExt U] (A : U) :
    A ⟶{λ a => elimFun a} (Top U ⟶ A) :=
  swapFunFun (elimFun (idFun A))
  ◄ elimFunEq (F := swapFun (elimFun (idFun A)) _) (byDef₂ • byDef)

  @[reducible] def elimFunFun [HasLinearFunOp U] [HasTopExt U] (A : U) :
    A ⟶ Top U ⟶ A :=
  defElimFunFun A

  instance elimFun.isFunApp [HasLinearFunOp U] [HasTopExt U] {A : U} {a : A} :
    IsFunApp A (elimFun a) :=
  { F := elimFunFun A,
    a := a,
    e := byDef }

  def HasTopExt.elimFunEqExt [HasLinearFunOp U] [HasLinearFunExt U] [HasTopExt U] {A : U}
                             {F : A ⟶ Top U ⟶ A} (h : swapFun F (top U) ≃ idFun A) :
    F ≃ elimFunFun A :=
  (reverseSwap (elimFunEq (h • byDef)))⁻¹

  def HasTopExt.elimFunFunConstEq [HasAffineFunOp U] [HasAffineFunExt U] [HasTopExt U] (A : U) :
    elimFunFun A ≃ constFunFun (Top U) A :=
  (elimFunEqExt (swapConstFun (top U) A))⁻¹

  def defInvElimFun [HasLinearFunOp U] (A : U) : (Top U ⟶ A) ⟶{λ F => F (top U)} A :=
  defRevAppFun (top U) A

  @[reducible] def invElimFun [HasLinearFunOp U] (A : U) : (Top U ⟶ A) ⟶ A := defInvElimFun A

end HasInternalTop



namespace HasInternalBot

  open HasLinearFunOp HasBot

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasInternalBot U]

  def contraIntroFun [HasLinearFunOp U] (A : U) : A ⟶ Not A ⟶ Bot U :=
  revAppFunFun A (Bot U)

  def notNotFun [HasLinearFunOp U] (A : U) : A ⟶ Not (Not A) := contraIntroFun A

  def notTopIntroFun [HasLinearFunOp U] [HasInternalTop U] : Not (HasTop.Top U) ⟶ Bot U :=
  HasInternalTop.invElimFun (Bot U)

end HasInternalBot
