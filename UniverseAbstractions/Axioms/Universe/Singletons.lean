import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences



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

-- TODO: α ⟶ Top (via constFun)
-- TODO: (Top ⟶ α) ⟶ α (via appFun)



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

-- TODO: Prove `α ⟶ Not α ⟶ β` via `α ⟶ Not α ⟶ Bot`.

class HasClassicalLogic (U : Universe.{u}) [HasEmbeddedFunctors U] [HasFunctorialBot U] where
(byContradiction (α : U) : HasFunctorialBot.Not (HasFunctorialBot.Not α) ⟶ α)

-- TODO: byContradiction is equivalence
-- TODO: Bot equivalent Not Unit
-- TODO: Product/singleton equivalences
