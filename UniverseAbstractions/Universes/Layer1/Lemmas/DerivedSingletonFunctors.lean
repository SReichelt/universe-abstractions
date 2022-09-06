import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Axioms.Singletons
import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations
import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations.Cartesian
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedFunctors



namespace UniverseAbstractions.Layer1

set_option autoImplicit false

universe u

open HasFunctors HasIdFun HasPiAppFun HasPiAppFunPi HasSwapPi₂ HasPreorderRelation



namespace HasTop

  variable {U : Universe.{u}} [HasLinearLogic U] [HasTop U]

  def defIntroFun (α : Sort u) [HasFunctors α ⊤_U] [HasConstPi α ⊤_U] : α ⥤{λ _ => ∗_U} ⊤_U :=
    HasConstPi.defConstFun α ∗_U

  @[reducible] def introFun (α : Sort u) [HasFunctors α ⊤_U] [HasConstPi α ⊤_U] : α ⥤ ⊤_U :=
    (defIntroFun α).inst

  def defElimFun₂ (A : U) : A ⥤ ⊤_U ⥤{λ a _ => a} A :=
    ⟨defElimFun, ⟨swapFun₂ (elimFun (idFun A))⟩⟩

  @[reducible] def elimFun₂ (A : U) : A ⥤ ⊤_U ⥤ A := (defElimFun₂ A).inst

  instance elimFun.isFunApp {A : U} {a : A} : IsFunApp (elimFun a) := ⟨elimFun₂ A, a⟩

  def defInvElimFun (A : U) : (⊤_U ⥤ A) ⥤{λ F => F ∗_U} A := ⟨revAppFun ∗_U A⟩

  @[reducible] def invElimFun (A : U) : (⊤_U ⥤ A) ⥤ A := (defInvElimFun A).inst

end HasTop



namespace HasBot

  variable {U : Universe} [HasLinearLogic U] [HasBot U]

  def contraIntroFun (A : U) : A ⥤ ~A ⥤ ⊥_U := revAppFun₂ A ⊥_U

  def notNotFun (A : U) : A ⥤ ~~A := contraIntroFun A

  def notTopIntroFun [HasTop U] : ~⊤_U ⥤ ⊥_U := HasTop.invElimFun ⊥_U

end HasBot



namespace Prerelation

  def topRelation (α : Sort u) (V : Universe) [HasLinearLogic V] [HasTop V] : Prerelation α V :=
    unitRelation α ⊤_V

  instance topRelation.isFull (α : Sort u) {V : Universe} [HasLinearLogic V] [HasTop V] :
      IsFull (topRelation α V) where
    inst _ _ := ∗_V

  instance topRelation.isEquivalence (α : Sort u) {V : Universe} [HasLinearLogic V] [HasTop V] :
      IsEquivalence (topRelation α V) where
    refl         _     := ∗_V
    symmFun      _ _   := HasTop.elimFun ∗_V
    revTransFun₂ _ _ _ := HasTop.elimFun (idFun ⊤_V)

end Prerelation



namespace HasTop

  variable (U : Universe) [HasLinearLogic U] [HasSubLinearLogic U] [HasTop U]

  instance hasTopObject : HasTerminalObject U where
    trm           := ⊤_U
    trmIntroHom A := HasTop.introFun A

end HasTop

namespace HasBot

  variable (U : Universe) [HasLinearLogic U] [HasBot U]

  instance hasBotObject : HasInitialObject U where
    trm         := ⊥_U
    trmIntroHom := HasBot.elimFun

end HasBot
