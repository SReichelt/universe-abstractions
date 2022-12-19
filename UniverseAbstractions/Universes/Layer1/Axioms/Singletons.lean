import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors

import UniverseAbstractions.MathlibFragments.Init.CoreExt



namespace UniverseAbstractions.Layer1

set_option autoImplicit false

universe u

open HasFunctors



-- Eliminating from `Top` should not require `SubLinearLogic`, as conceptually, an instance of
-- `Top` does not hold any data. Therefore, we define a specialized version of `constFun`. Note
-- that a corresponding `elimFun₂` is derived from this in `DerivedSingletonFunctors.lean`.

class HasTop (U : Universe.{u}) [HasUnivFunctors U U] extends
    HasTypeWithIntro U PUnit.{u} where
  defElimFun {A : U} (a : A) : [T ⥤ A]_{λ _ : T => a}

namespace HasTop

  section

    variable (U : Universe) [HasUnivFunctors U U] [h : HasTop U] 

    @[reducible] def Top : U := h.T
    prefix:max "⊤_" => HasTop.Top

    @[reducible] def top : ⊤_U := h.hIntro.intro PUnit.unit
    prefix:max "∗_" => HasTop.top

  end

  variable {U : Universe} [HasUnivFunctors U U] [h : HasTop U] 

  @[reducible] def elimFun {A : U} (a : A) : ⊤_U ⥤ A := h.defElimFun a

end HasTop


class HasBot (U : Universe.{u}) [HasUnivFunctors U U] extends
    HasType U PEmpty.{u} where
  defElimFun (Y : U) : [T ⥤ Y]_{λ e : T => PEmpty.elim (α := Y) e}

namespace HasBot

  section

    variable (U : Universe) [HasUnivFunctors U U] [h : HasBot U]

    @[reducible] def Bot : U := h.T
    prefix:max "⊥_" => HasBot.Bot

    instance hasIntro : HasIntro ⊥_U PEmpty.{u} := ⟨PEmpty.elim⟩

  end

  variable {U : Universe} [HasUnivFunctors U U] [h : HasBot U]

  @[reducible] def elim (e : ⊥_U) (Y : U) : Y := PEmpty.elim (h.hElim.elim e)

  @[reducible] def elimFun (Y : U) : ⊥_U ⥤ Y := h.defElimFun Y

  instance elim.isFunApp {e : ⊥_U} {Y : U} : IsFunApp (elim e Y) := ⟨elimFun Y, e⟩

  def Not (A : U) : U := A ⥤ ⊥_U
  prefix:max "~" => HasBot.Not

end HasBot

class HasClassicalLogic (U : Universe.{u}) [HasUnivFunctors U U] [HasBot U] where
  byContradictionFun (A : U) : ~~A ⥤ A

namespace HasClassicalLogic

  variable {U : Universe} [HasUnivFunctors U U] [HasBot U] [HasClassicalLogic U]

  @[reducible] def byContradiction {A : U} (F : ~~A) : A := (byContradictionFun A) F

end HasClassicalLogic
