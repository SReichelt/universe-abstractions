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
(defElimFun {A : U} (a : A) : HasTop.Top U ⟶[λ _ => a] A)
(defElimFunFun (A : U) : A ⟶[λ a => defElimFun a] (HasTop.Top U ⟶ A))

namespace HasEmbeddedTop

  open HasTop

  variable {U : Universe} [HasEmbeddedFunctors U] [HasEmbeddedTop U]

  @[reducible] def elimFun {A : U} (a : A) : Top U ⟶ A := defElimFun a
  @[reducible] def elimFunFun (A : U) : A ⟶ Top U ⟶ A := defElimFunFun A

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

  def elim (e : Bot U) {A : U} : A := False.elim (HasEmbeddedType.toExternal U e)

end HasBot

class HasEmbeddedBot (U : Universe.{u}) [HasEmbeddedFunctors.{u, w} U]
  extends HasBot U where
(defElimFun (A : U) : HasBot.Bot U ⟶[λ e => HasBot.elim e] A)

namespace HasEmbeddedBot

  open HasBot

  variable {U : Universe} [HasEmbeddedFunctors U] [HasEmbeddedBot U]

  def elimFun (A : U) : Bot U ⟶ A := HasEmbeddedBot.defElimFun A

  def Not (A : U) : U := A ⟶ Bot U

end HasEmbeddedBot

class HasClassicalLogic (U : Universe.{u}) [HasEmbeddedFunctors.{u, w} U] [HasEmbeddedBot.{u, w} U] where
(byContradictionFun (A : U) : HasEmbeddedBot.Not (HasEmbeddedBot.Not A) ⟶ A)
