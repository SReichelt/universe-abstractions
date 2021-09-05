import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences
import UniverseAbstractions.Axioms.Universe.Properties
import UniverseAbstractions.Axioms.Universe.DependentFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w w'



def HasDependentProducts.Sigma' {U : Universe.{u}} {V : Universe.{v}} [HasProperties U V]
                                {α : U} (φ : α ⟿ V) :=
HasProperties.Sigma φ
notation:20 "Σ' " φ:21 => HasDependentProducts.Sigma' φ

class HasDependentProducts (U : Universe.{u}) (V : Universe.{v}) [HasProperties.{u, v, w} U V]
                           (X : outParam Universe.{w'}) :
  Type (max u v w w') where
[embed {α : U} (φ : α ⟿ V) : HasEmbeddedType.{w', max 1 u v} X (Σ' φ)]

namespace HasDependentProducts

  variable {U V X : Universe} [HasProperties U V] [h : HasDependentProducts U V X]

  instance hasEmbeddedType {α : U} (φ : α ⟿ V) : HasEmbeddedType X (Σ' φ) :=
  h.embed φ

  def Sigma {α : U} (φ : α ⟿ V) : X := HasEmbeddedType.EmbeddedType X (Σ' φ)
  notation:20 "Σ " φ:21 => HasDependentProducts.Sigma φ

  variable {α : U} {φ : α ⟿ V}

  def toExternal   (P : Σ  φ) : Σ' φ := HasEmbeddedType.toExternal   X P
  def fromExternal (P : Σ' φ) : Σ  φ := HasEmbeddedType.fromExternal X P

  @[simp] theorem fromToExternal (P : Σ  φ) : fromExternal (toExternal P) = P := HasEmbeddedType.fromToExternal X P
  @[simp] theorem toFromExternal (P : Σ' φ) : toExternal (fromExternal P) = P := HasEmbeddedType.toFromExternal X P

  def fst (P : Σ φ) : α         := (toExternal P).fst
  def snd (P : Σ φ) : φ (fst P) := (toExternal P).snd

  def intro (a : α) (b : φ a) : Σ φ := fromExternal ⟨a, b⟩

end HasDependentProducts



class HasSigmaProdEquiv (U : Universe.{u}) (V : Universe.{v}) (X : Universe.{w}) (Y : Universe.{w'})
                        [HasProperties U V] [HasDependentProducts U V X] [HasProducts U V X]
                        [HasFunctors X X Y] [HasEquivalenceCondition X Y] where
(defSigmaProdFun (α : U) (β : V) :
   (Σ α{β}) ⟶[λ P => HasProducts.intro (HasDependentProducts.fst P) (HasDependentProducts.snd P)] (α ⊓ β))
(defProdSigmaFun (α : U) (β : V) :
   (α ⊓ β) ⟶[λ φ => HasDependentProducts.intro (HasProducts.fst φ) (HasProducts.snd φ)] (Σ α{β}))
(defSigmaProdEquiv (α : U) (β : V) : (Σ α{β}) ⟷[defSigmaProdFun α β, defProdSigmaFun α β] (α ⊓ β))

namespace HasSigmaProdEquiv

  variable {U V X Y Z: Universe} [HasProperties U V] [HasDependentProducts U V X] [HasProducts U V X]
           [HasFunctors X X Y] [HasEquivalences X Y Z] [HasSigmaProdEquiv U V X Y]

  @[reducible] def sigmaProdFun (α : U) (β : V) : (Σ α{β}) ⟶ α ⊓ β := defSigmaProdFun α β
  @[reducible] def prodSigmaFun (α : U) (β : V) : α ⊓ β ⟶ Σ α{β} := defProdSigmaFun α β
  @[reducible] def sigmaProdEquiv (α : U) (β : V) : (Σ α{β}) ⟷ α ⊓ β := defSigmaProdEquiv α β

end HasSigmaProdEquiv



class HasEmbeddedDependentProducts (U : Universe.{u}) (V : Universe.{v}) [HasDependentFunctors.{u, v, v, w} U V V]
                                   [HasEmbeddedFunctors V] [HasFunProp U V V V]
  extends HasDependentProducts.{u, v, w, v} U V V where
(defIntroFun   {α : U} (φ : α ⟿ V) (a : α)                                   :
   φ a ⟶[λ b => HasDependentProducts.intro a b] (Σ φ))
(defIntroFunPi {α : U} (φ : α ⟿ V)                                           :
   Π[λ a => HasFunctors.fromDefFun (defIntroFun φ a)] {φ ⟶ α{Σ φ}})
(defElimFun    {α : U} {φ : α ⟿ V} {γ : V} (F : Π {φ ⟶ α{γ}}) :
   (Σ φ) ⟶[λ P => HasFunctors.funCoe (F (HasDependentProducts.fst P)) (HasDependentProducts.snd P)] γ)
(defElimFunFun {α : U} (φ : α ⟿ V) (γ : V)                                   :
   (Π {φ ⟶ α{γ}}) ⟶[λ F => defElimFun F] ((Σ φ) ⟶ γ))

namespace HasEmbeddedDependentProducts

  variable {U V : Universe} [HasDependentFunctors U V V] [HasEmbeddedFunctors V] [HasFunProp U V V V]
           [HasEmbeddedDependentProducts U V]

  @[reducible] def introFun {α : U} (φ : α ⟿ V) (a : α) : φ a ⟶ Σ φ := defIntroFun φ a
  @[reducible] def introFunPi {α : U} (φ : α ⟿ V) : Π {φ ⟶ α{Σ φ}} := defIntroFunPi φ
  @[reducible] def elimFun {α : U} {φ : α ⟿ V} {γ : V} (F : Π {φ ⟶ α{γ}}) : (Σ φ) ⟶ γ := defElimFun F
  @[reducible] def elimFunFun {α : U} (φ : α ⟿ V) (γ : V) : (Π {φ ⟶ α{γ}}) ⟶ ((Σ φ) ⟶ γ) := defElimFunFun φ γ

end HasEmbeddedDependentProducts
