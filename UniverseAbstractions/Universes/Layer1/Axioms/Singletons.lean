import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors



namespace UniverseAbstractions.Layer1

set_option autoBoundImplicitLocal false



-- Eliminating from `Top` should not require `SubLinearLogic`, as conceptually, an instance of
-- `Top` does not hold any data. Therefore, we define a specialized version of `constFun`. Note
-- that a corresponding `elimFun₂` is derived from this in `DerivedSingletonFunctors.lean`.

class HasTop (U : Universe) [HasFunctors U] where
(T : U)
(t : T)
(defElimFun {A : U} (a : A) : T ⟶{λ _ => a} A)

namespace HasTop

  section

    variable (U : Universe) [HasFunctors U] [h : HasTop U] 

    @[reducible] def Top : U := h.T
    prefix:max "⊤_" => HasTop.Top

    @[reducible] def top : ⊤_U := h.t
    prefix:max "∗_" => HasTop.top

  end

  variable {U : Universe} [HasFunctors U] [HasTop U] 

  @[reducible] def elimFun {A : U} (a : A) : ⊤_U ⟶ A := (defElimFun a).F

end HasTop


class HasBot (U : Universe) [HasFunctors U] where
(B : U)
(elimFun (A : U) : B ⟶ A)

namespace HasBot

  section

    variable (U : Universe) [HasFunctors U] [h : HasBot U]

    @[reducible] def Bot : U := h.B

    prefix:max "⊥_" => HasBot.Bot

  end

  variable {U : Universe} [HasFunctors U] [HasBot U]

  @[reducible] def elim (b : ⊥_U) (A : U) : A := (elimFun A) b

  def Not (A : U) : U := A ⟶ ⊥_U
  prefix:max "~" => HasBot.Not

end HasBot

class HasClassicalLogic (U : Universe) [HasFunctors U] [HasBot U] where
(byContradictionFun (A : U) : ~~A ⟶ A)

namespace HasClassicalLogic

  variable {U : Universe} [HasFunctors U] [HasBot U] [HasClassicalLogic U]

  @[reducible] def byContradiction {A : U} (F : ~~A) : A := (byContradictionFun A) F

end HasClassicalLogic

class IsLogicallyConsistent (U : Universe) [HasFunctors U] [HasBot U] where
(botEmpty : ⊥_U → False)
