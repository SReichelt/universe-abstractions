import UniverseAbstractions.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Axioms.Singletons
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedFunctors



namespace UniverseAbstractions.Layer1

set_option autoBoundImplicitLocal false

open HasFunctors HasLinearLogic HasSubLinearLogic



namespace HasTop

  variable {U : Universe} [HasFunctors U] [HasTop U]

  def defIntroFun [HasSubLinearLogic U] (A : U) : A ⟶{λ _ => top U} Top U :=
  (defConstFun₂ A (Top U)).app (top U)

  @[reducible] def introFun [HasSubLinearLogic U] (A : U) : A ⟶ Top U := (defIntroFun A).F

  variable [HasLinearLogic U]

  def defElimFun₂ (A : U) : A ⟶ Top U ⟶{λ a _ => a} A :=
  ⟨defElimFun,
   ⟨swapFun₂ (elimFun (idFun A))⟩⟩

  @[reducible] def elimFun₂ (A : U) : A ⟶ Top U ⟶ A := (defElimFun₂ A).F

  instance elimFun.isFunApp {A : U} {a : A} : IsFunApp A (elimFun a) :=
  ⟨elimFun₂ A, a⟩

  def defInvElimFun (A : U) : (Top U ⟶ A) ⟶{λ F => F (top U)} A := ⟨revAppFun (top U) A⟩

  @[reducible] def invElimFun (A : U) : (Top U ⟶ A) ⟶ A := (defInvElimFun A).F

end HasTop



namespace HasBot

  variable {U : Universe} [HasFunctors U] [HasBot U] [HasLinearLogic U]

  def contraIntroFun (A : U) : A ⟶ Not A ⟶ Bot U := revAppFun₂ A (Bot U)

  def notNotFun (A : U) : A ⟶ Not (Not A) := contraIntroFun A

  def notTopIntroFun [HasTop U] : Not (HasTop.Top U) ⟶ Bot U := HasTop.invElimFun (Bot U)

end HasBot
