import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w



def HasProducts.Prod {U : Universe.{u}} {V : Universe.{v}} (α : U) (β : V) := PProd ⌈α⌉ ⌈β⌉
infix:35 " ⊓' " => HasProducts.Prod

class HasProducts (U : Universe.{u}) (V : Universe.{v}) (X : outParam Universe.{w}) :
  Type (max u v w) where
[embed (α : U) (β : V) : HasEmbeddedType.{w, max 1 u v} X (α ⊓' β)]

namespace HasProducts

  variable {U V : Universe}

  @[simp] theorem ext' {α : U} {β : V} (P : α ⊓' β) : ⟨P.fst, P.snd⟩ = P :=
  by induction P; rfl

  variable {X : Universe} [h : HasProducts U V X]

  instance hasEmbeddedType (α : U) (β : V) : HasEmbeddedType X (α ⊓' β) := h.embed α β

  def Product (α : U) (β : V) : X := HasEmbeddedType.EmbeddedType X (α ⊓' β)
  infix:35 " ⊓ " => HasProducts.Product
  
  variable {α : U} {β : V}

  def toExternal   (P : α ⊓  β) : α ⊓' β := HasEmbeddedType.toExternal   X P
  def fromExternal (P : α ⊓' β) : α ⊓  β := HasEmbeddedType.fromExternal X P

  @[simp] theorem fromToExternal (P : α ⊓  β) : fromExternal (toExternal P) = P := HasEmbeddedType.fromToExternal X P
  @[simp] theorem toFromExternal (P : α ⊓' β) : toExternal (fromExternal P) = P := HasEmbeddedType.toFromExternal X P

  def fst (P : α ⊓ β) : α := (toExternal P).fst
  def snd (P : α ⊓ β) : β := (toExternal P).snd

  def intro (a : α) (b : β) : α ⊓ β := fromExternal ⟨a, b⟩

  @[simp] theorem fst_intro (a : α) (b : β) : fst (intro a b) = a := congrArg PProd.fst (toFromExternal ⟨a, b⟩)
  @[simp] theorem snd_intro (a : α) (b : β) : snd (intro a b) = b := congrArg PProd.snd (toFromExternal ⟨a, b⟩)

  @[simp] theorem ext (P : α ⊓ β) : intro (fst P) (snd P) = P :=
  Eq.trans (congrArg fromExternal (ext' (toExternal P))) (fromToExternal P)

end HasProducts



-- In many cases, the product of two universe instances is again an instance of the same universe.
--
-- Moreover, we would like to map in and out of products functorially. Introduction is simply given
-- by `α ⟶ β ⟶ α ⊓ β`, i.e. given an `α` and a `β`, we can construct their product. For
-- elimination, we take an indirect approach that works well with `HasLinearFunOp`,
-- `HasAffineFunOp`, and `HasFullFunOp`: If only `HasLinearFunOp` is given, it is both allowed and
-- required to always use both sides of a product; eliminating to either `α` or `β` requires
-- `constFun`.

class HasEmbeddedProducts (U : Universe.{u}) [HasEmbeddedFunctors.{u, w} U]
  extends HasProducts U U U : Type (max u w) where
(defIntroFun    {α : U} (a : α) (β : U)     : β ⟶[λ b => HasProducts.intro a b] α ⊓ β)
(defIntroFunFun (α β : U)                   : α ⟶[λ a => defIntroFun a β] (β ⟶ α ⊓ β))
(defElimFun     {α β γ : U} (F : α ⟶ β ⟶ γ) : α ⊓ β ⟶[λ P => F (HasProducts.fst P) (HasProducts.snd P)] γ)
(defElimFunFun  (α β γ : U)                 : (α ⟶ β ⟶ γ) ⟶[λ F => defElimFun F] (α ⊓ β ⟶ γ))

namespace HasEmbeddedProducts

  variable {U : Universe} [HasEmbeddedFunctors U] [HasEmbeddedProducts U]

  @[reducible] def introFun {α : U} (a : α) (β : U) : β ⟶ α ⊓ β := defIntroFun a β
  @[reducible] def introFunFun (α β : U) : α ⟶ β ⟶ α ⊓ β := defIntroFunFun α β

  @[reducible] def elimFun {α β γ : U} (F : α ⟶ β ⟶ γ) : α ⊓ β ⟶ γ := defElimFun F
  @[reducible] def elimFunFun (α β γ : U) : (α ⟶ β ⟶ γ) ⟶ (α ⊓ β ⟶ γ) := defElimFunFun α β γ

end HasEmbeddedProducts
