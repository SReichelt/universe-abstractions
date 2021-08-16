import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w



-- The type class `HasExternalProduct` (analogously to `HasExternalFunctor` etc.) doesn't actually
-- exist because we assume that products never need to carry any additional data.

namespace HasExternalProduct

  def Product {U : Universe.{u}} {V : Universe.{v}} (α : U) (β : V) := PProd ⌈α⌉ ⌈β⌉

  infix:35 " ⊓' " => HasExternalProduct.Product

end HasExternalProduct



class HasEmbeddedProduct {U : Universe.{u}} (α β : U) where
[hType : HasEmbeddedType.{u, max 1 u} U (α ⊓' β)]

class HasEmbeddedProducts (U : Universe.{u}) where
[hasProd (α β : U) : HasEmbeddedProduct.{u} α β]

namespace HasEmbeddedProducts

  variable {U : Universe} [h : HasEmbeddedProducts U]

  instance hasEmbeddedType (α β : U) : HasEmbeddedType U (α ⊓' β) := (h.hasProd α β).hType

  def Product (α β : U) : U := HasEmbeddedType.EmbeddedType U (α ⊓' β)
  infix:35 " ⊓ " => HasEmbeddedProducts.Product

  variable {α β : U}

  def toExternal   (P : α ⊓  β) : α ⊓' β := HasEmbeddedType.toExternal   U P
  def fromExternal (P : α ⊓' β) : α ⊓  β := HasEmbeddedType.fromExternal U P

  @[simp] theorem fromToExternal (P : α ⊓  β) : fromExternal (toExternal P) = P := HasEmbeddedType.fromToExternal U P
  @[simp] theorem toFromExternal (P : α ⊓' β) : toExternal (fromExternal P) = P := HasEmbeddedType.toFromExternal U P

  def fst (P : α ⊓ β) : α := (toExternal P).fst
  def snd (P : α ⊓ β) : β := (toExternal P).snd

  def intro (a : α) (b : β) : α ⊓ β := fromExternal ⟨a, b⟩

end HasEmbeddedProducts



-- We would like to map in and out of products functorially. Introduction is simply given by
-- `α ⟶ β ⟶ α ⊓ β`, i.e. given an `α` and a `β`, we can construct their product. For elimination,
-- we take an indirect approach that works well with `HasLinearFunOp`, `HasAffineFunOp`, and
-- `HasFullFunOp`: If only `HasLinearFunOp` is given, it is both allowed and required to always use
-- both sides of a product; eliminating to either `α` or `β` requires `constFun`.

class HasFunctorialProducts (U : Universe.{u}) [HasEmbeddedFunctors.{u, w} U] extends HasEmbeddedProducts U where
(defIntroFun    {α : U} (a : α) (β : U)     : β ⟶[λ b => HasEmbeddedProducts.intro a b] α ⊓ β)
(defIntroFunFun (α β : U)                   : α ⟶[λ a => defIntroFun a β] (β ⟶ α ⊓ β))
(defElimFun     {α β γ : U} (F : α ⟶ β ⟶ γ) : α ⊓ β ⟶[λ P => F (HasEmbeddedProducts.fst P) (HasEmbeddedProducts.snd P)] γ)
(defElimFunFun  (α β γ : U)                 : (α ⟶ β ⟶ γ) ⟶[λ F => defElimFun F] (α ⊓ β ⟶ γ))

namespace HasFunctorialProducts

  variable {U : Universe} [HasEmbeddedFunctors U] [HasFunctorialProducts U]

  @[reducible] def introFun {α : U} (a : α) (β : U) : β ⟶ α ⊓ β := defIntroFun a β
  @[reducible] def introFunFun (α β : U) : α ⟶ β ⟶ α ⊓ β := defIntroFunFun α β

  @[reducible] def elimFun {α β γ : U} (F : α ⟶ β ⟶ γ) : α ⊓ β ⟶ γ := defElimFun F
  @[reducible] def elimFunFun (α β γ : U) : (α ⟶ β ⟶ γ) ⟶ (α ⊓ β ⟶ γ) := defElimFunFun α β γ

end HasFunctorialProducts
