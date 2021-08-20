import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u w



class HasTop (U : Universe.{u}) where
[embed : HasEmbeddedType.{u, 0} U True]

namespace HasTop

  variable (U : Universe) [h : HasTop U] 

  instance hasEmbeddedType : HasEmbeddedType U True := h.embed

  def Top : U := HasEmbeddedType.EmbeddedType U True

  def top : Top U := HasEmbeddedType.fromExternal U trivial

end HasTop

-- Eliminating from `Top` should not require `SubLinearFunOp`, as conceptually, an instance of
-- `Top` does not hold any data. Therefore, we define a specialized version of `constFun`.

class HasEmbeddedTop (U : Universe.{u}) [HasEmbeddedFunctors.{u, w} U]
  extends HasTop U where
(defElimFun {α : U} (a : α) : HasTop.Top U ⟶[λ _ => a] α)
(defElimFunFun (α : U) : α ⟶[λ a => defElimFun a] (HasTop.Top U ⟶ α))

namespace HasEmbeddedTop

  open HasTop

  variable {U : Universe} [HasEmbeddedFunctors U] [HasEmbeddedTop U]

  @[reducible] def elimFun {α : U} (a : α) : Top U ⟶ α := defElimFun a
  @[reducible] def elimFunFun (α : U) : α ⟶ Top U ⟶ α := defElimFunFun α

end HasEmbeddedTop




class HasBot (U : Universe.{u}) where
[embed : HasEmbeddedType.{u, 0} U False]

namespace HasBot

  section Init

    variable (U : Universe) [h : HasBot U]

    instance hasEmbeddedType : HasEmbeddedType U False := h.embed

    def Bot : U := HasEmbeddedType.EmbeddedType U False

  end Init

  variable {U : Universe} [h : HasBot U]

  def elim (e : Bot U) {α : U} : α := False.elim (HasEmbeddedType.toExternal U e)

end HasBot

class HasEmbeddedBot (U : Universe.{u}) [HasEmbeddedFunctors.{u, w} U]
  extends HasBot U where
(defElimFun (α : U) : HasBot.Bot U ⟶[λ e => HasBot.elim e] α)

namespace HasEmbeddedBot

  open HasBot

  variable {U : Universe} [HasEmbeddedFunctors U] [HasEmbeddedBot U]

  def elimFun (α : U) : Bot U ⟶ α := HasEmbeddedBot.defElimFun α

  def Not (α : U) : U := α ⟶ Bot U

end HasEmbeddedBot

class HasClassicalLogic (U : Universe.{u}) [HasEmbeddedFunctors.{u, w} U] [HasEmbeddedBot.{u, w} U] where
(byContradictionFun (α : U) : HasEmbeddedBot.Not (HasEmbeddedBot.Not α) ⟶ α)
