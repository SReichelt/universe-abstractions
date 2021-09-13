import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w



def HasProducts.Prod {U : Universe.{u}} {V : Universe.{v}} (A : U) (B : V) := PProd ⌈A⌉ ⌈B⌉
infix:35 " ⊓' " => HasProducts.Prod

class HasProducts (U : Universe.{u}) (V : Universe.{v}) (UxV : outParam Universe.{w}) :
  Type (max u v w) where
[embed (A : U) (B : V) : HasEmbeddedType.{w, max 1 u v} UxV (A ⊓' B)]

namespace HasProducts

  variable {U V : Universe}

  @[simp] theorem ext' {A : U} {B : V} (P : A ⊓' B) : ⟨P.fst, P.snd⟩ = P :=
  by induction P; rfl

  variable {UxV : Universe} [h : HasProducts U V UxV]

  instance hasEmbeddedType (A : U) (B : V) : HasEmbeddedType UxV (A ⊓' B) := h.embed A B

  def Product (A : U) (B : V) : UxV := HasEmbeddedType.EmbeddedType UxV (A ⊓' B)
  infix:35 " ⊓ " => HasProducts.Product
  
  variable {A : U} {B : V}

  def toExternal   (P : A ⊓  B) : A ⊓' B := HasEmbeddedType.toExternal   UxV P
  def fromExternal (P : A ⊓' B) : A ⊓  B := HasEmbeddedType.fromExternal UxV P

  @[simp] theorem fromToExternal (P : A ⊓  B) : fromExternal (toExternal P) = P := HasEmbeddedType.fromToExternal UxV P
  @[simp] theorem toFromExternal (P : A ⊓' B) : toExternal (fromExternal P) = P := HasEmbeddedType.toFromExternal UxV P

  def fst (P : A ⊓ B) : A := (toExternal P).fst
  def snd (P : A ⊓ B) : B := (toExternal P).snd

  def intro (a : A) (b : B) : A ⊓ B := fromExternal ⟨a, b⟩

  @[simp] theorem fst_intro (a : A) (b : B) : fst (intro a b) = a := congrArg PProd.fst (toFromExternal ⟨a, b⟩)
  @[simp] theorem snd_intro (a : A) (b : B) : snd (intro a b) = b := congrArg PProd.snd (toFromExternal ⟨a, b⟩)

  @[simp] theorem ext (P : A ⊓ B) : intro (fst P) (snd P) = P :=
  Eq.trans (congrArg fromExternal (ext' (toExternal P))) (fromToExternal P)

end HasProducts



-- In many cases, the product of two universe instances is again an instance of the same universe.
--
-- Moreover, we would like to map in and out of products functorially. Introduction is simply given
-- by `A ⟶ B ⟶ A ⊓ B`, i.e. given an `A` and a `B`, we can construct their product. For
-- elimination, we take an indirect approach that works well with `HasLinearFunOp`,
-- `HasAffineFunOp`, and `HasFullFunOp`: If only `HasLinearFunOp` is given, it is both allowed and
-- required to always use both sides of a product; eliminating to either `A` or `B` requires
-- `constFun`.

class HasEmbeddedProducts (U : Universe.{u}) [HasEmbeddedFunctors.{u, w} U]
  extends HasProducts U U U : Type (max u w) where
(defIntroFun    {A : U} (a : A) (B : U)     : B ⟶[λ b => HasProducts.intro a b] A ⊓ B)
(defIntroFunFun (A B : U)                   : A ⟶[λ a => defIntroFun a B] (B ⟶ A ⊓ B))
(defElimFun     {A B C : U} (F : A ⟶ B ⟶ C) : A ⊓ B ⟶[λ P => F (HasProducts.fst P) (HasProducts.snd P)] C)
(defElimFunFun  (A B C : U)                 : (A ⟶ B ⟶ C) ⟶[λ F => defElimFun F] (A ⊓ B ⟶ C))

namespace HasEmbeddedProducts

  variable {U : Universe} [HasEmbeddedFunctors U] [HasEmbeddedProducts U]

  @[reducible] def introFun {A : U} (a : A) (B : U) : B ⟶ A ⊓ B := defIntroFun a B
  @[reducible] def introFunFun (A B : U) : A ⟶ B ⟶ A ⊓ B := defIntroFunFun A B

  @[reducible] def elimFun {A B C : U} (F : A ⟶ B ⟶ C) : A ⊓ B ⟶ C := defElimFun F
  @[reducible] def elimFunFun (A B C : U) : (A ⟶ B ⟶ C) ⟶ (A ⊓ B ⟶ C) := defElimFunFun A B C

end HasEmbeddedProducts
