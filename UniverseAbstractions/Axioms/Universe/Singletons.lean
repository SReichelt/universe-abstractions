import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u w



class HasEmbeddedTop (U : Universe.{u}) where
[h : HasEmbeddedType.{u, 0} U True]

namespace HasEmbeddedTop

  instance hasEmbeddedType (U : Universe) [h : HasEmbeddedTop U] : HasEmbeddedType U True := h.h

  def Top (U : Universe) [HasEmbeddedTop U] : U := HasEmbeddedType.EmbeddedType U True

  def top (U : Universe) [HasEmbeddedTop U] : Top U := HasEmbeddedType.fromExternal U trivial

end HasEmbeddedTop

-- Eliminating from `Top` should not require `SubLinearFunOp`, as conceptually, an instance of
-- `Top` does not hold any data. Therefore, we define a specialized version of `constFun`.

class HasFunctorialTop (U : Universe.{u}) [HasEmbeddedFunctors.{u, w} U]
  extends HasEmbeddedTop U where
(defElimFun {α : U} (a : α) : HasEmbeddedTop.Top U ⟶[λ _ => a] α)
(defElimFunFun (α : U) : α ⟶[λ a => defElimFun a] (HasEmbeddedTop.Top U ⟶ α))

namespace HasFunctorialTop

  variable {U : Universe} [HasEmbeddedFunctors U] [HasFunctorialTop U]

  @[reducible] def elimFun {α : U} (a : α) : HasEmbeddedTop.Top U ⟶ α := HasFunctorialTop.defElimFun a
  @[reducible] def elimFunFun (α : U) : α ⟶ HasEmbeddedTop.Top U ⟶ α := defElimFunFun α

end HasFunctorialTop




class HasEmbeddedBot (U : Universe.{u}) where
[h : HasEmbeddedType.{u, 0} U False]

namespace HasEmbeddedBot

  instance hasEmbeddedType (U : Universe) [h : HasEmbeddedBot U] : HasEmbeddedType U False := h.h

  def Bot (U : Universe) [h : HasEmbeddedBot U] : U := HasEmbeddedType.EmbeddedType U False

  def elim {U : Universe} [h : HasEmbeddedBot U] (e : Bot U) {α : U} : α :=
  False.elim (HasEmbeddedType.toExternal U e)

end HasEmbeddedBot

class HasFunctorialBot (U : Universe.{u}) [HasEmbeddedFunctors.{u, w} U]
  extends HasEmbeddedBot U where
(defElimFun (α : U) : HasEmbeddedBot.Bot U ⟶[λ e => HasEmbeddedBot.elim e] α)

namespace HasFunctorialBot

  variable {U : Universe} [HasEmbeddedFunctors U] [HasFunctorialBot U]

  def elimFun (α : U) : HasEmbeddedBot.Bot U ⟶ α := HasFunctorialBot.defElimFun α

  def Not (α : U) : U := α ⟶ HasEmbeddedBot.Bot U

end HasFunctorialBot

class HasClassicalLogic (U : Universe.{u}) [HasEmbeddedFunctors U] [HasFunctorialBot U] where
(byContradictionFun (α : U) : HasFunctorialBot.Not (HasFunctorialBot.Not α) ⟶ α)
