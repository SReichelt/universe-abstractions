import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Axioms.Singletons
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedFunctors



namespace UniverseAbstractions.Layer1

set_option autoBoundImplicitLocal false

open HasFunctors HasLinearLogic HasSubLinearLogic



namespace HasTop

  variable {U : Universe} [HasFunctors U] [HasTop U]

  def defIntroFun [HasSubLinearLogic U] (A : U) : A ⟶{λ _ => ∗_U} ⊤_U :=
  (defConstFun₂ A ⊤_U).app ∗_U

  @[reducible] def introFun [HasSubLinearLogic U] (A : U) : A ⟶ ⊤_U := (defIntroFun A).F

  variable [HasLinearLogic U]

  def defElimFun₂ (A : U) : A ⟶ ⊤_U ⟶{λ a _ => a} A :=
  ⟨defElimFun,
   ⟨swapFun₂ (elimFun (idFun A))⟩⟩

  @[reducible] def elimFun₂ (A : U) : A ⟶ ⊤_U ⟶ A := (defElimFun₂ A).F

  instance elimFun.isFunApp {A : U} {a : A} : IsFunApp A (elimFun a) :=
  ⟨elimFun₂ A, a⟩

  def defInvElimFun (A : U) : (⊤_U ⟶ A) ⟶{λ F => F ∗_U} A := ⟨revAppFun ∗_U A⟩

  @[reducible] def invElimFun (A : U) : (⊤_U ⟶ A) ⟶ A := (defInvElimFun A).F

end HasTop



namespace HasBot

  variable {U : Universe} [HasFunctors U] [HasBot U] [HasLinearLogic U]

  def contraIntroFun (A : U) : A ⟶ ~A ⟶ ⊥_U := revAppFun₂ A ⊥_U

  def notNotFun (A : U) : A ⟶ ~~A := contraIntroFun A

  def notTopIntroFun [HasTop U] : ~⊤_U ⟶ ⊥_U := HasTop.invElimFun ⊥_U

end HasBot
