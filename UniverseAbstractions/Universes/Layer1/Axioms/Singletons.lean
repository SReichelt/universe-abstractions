import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors

import UniverseAbstractions.MathlibFragments.Init.CoreExt



namespace UniverseAbstractions.Layer1

set_option autoImplicit false

open Universe HasFunctors

universe u



-- Eliminating from `Top` should not require `SubLinearLogic`, as conceptually, an instance of
-- `Top` does not hold any data. Therefore, we define a specialized version of `constFun`. Note
-- that a corresponding `elimFun₂` is derived from this in `DerivedSingletonFunctors.lean`.

class HasTop (U : Universe.{u}) [HasLinearLogic U] where
  defTopType : DefType U PUnit.{u}
  defTop : DefType.DefInst defTopType PUnit.unit
  defElimFun {A : U} (a : A) : defTopType.A ⥤{λ _ => a} A

namespace HasTop

  section

    variable (U : Universe) [HasLinearLogic U] [h : HasTop U] 

    @[reducible] def Top : U := h.defTopType
    prefix:max "⊤_" => HasTop.Top

    @[reducible] def top : ⊤_U := h.defTop
    prefix:max "∗_" => HasTop.top

  end

  variable {U : Universe} [HasLinearLogic U] [h : HasTop U] 

  @[reducible] def elimFun {A : U} (a : A) : ⊤_U ⥤ A := h.defElimFun a

end HasTop


class HasBot (U : Universe.{u}) [HasLinearLogic U] where
  defBotType : DefType U PEmpty.{u}
  defElimFun (A : U) : defBotType.A ⥤{λ b => PEmpty.elim (defBotType.elim b)} A

namespace HasBot

  section

    variable (U : Universe) [HasLinearLogic U] [h : HasBot U]

    @[reducible] def Bot : U := h.defBotType
    prefix:max "⊥_" => HasBot.Bot

  end

  variable {U : Universe} [HasLinearLogic U] [h : HasBot U]

  @[reducible] def elim (b : ⊥_U) (A : U) : A := PEmpty.elim (defBotType.elim b)

  @[reducible] def elimFun (A : U) : ⊥_U ⥤ A := h.defElimFun A

  instance elim.isFunApp {b : ⊥_U} {A : U} : IsFunApp (elim b A) := ⟨elimFun A, b⟩

  def Not (A : U) : U := A ⥤ ⊥_U
  prefix:max "~" => HasBot.Not

end HasBot

class HasClassicalLogic (U : Universe.{u}) [HasLinearLogic U] [HasBot U] where
  byContradictionFun (A : U) : ~~A ⥤ A

namespace HasClassicalLogic

  variable {U : Universe} [HasLinearLogic U] [HasBot U] [HasClassicalLogic U]

  @[reducible] def byContradiction {A : U} (F : ~~A) : A := (byContradictionFun A) F

end HasClassicalLogic
