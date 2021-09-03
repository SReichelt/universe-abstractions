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
                                {α : U} (P : HasProperties.Property α V) :=
HasProperties.Sigma P
notation:20 "Σ' " P:21 => HasDependentProducts.Sigma' P

class HasDependentProducts (U : Universe.{u}) (V : Universe.{v}) [HasProperties.{u, v, w} U V]
                           (X : outParam Universe.{w'}) :
  Type (max u v w w') where
[embed {α : U} (P : HasProperties.Property α V) : HasEmbeddedType.{w', max 1 u v} X (Σ' P)]

namespace HasDependentProducts

  variable {U V X : Universe} [HasProperties U V] [h : HasDependentProducts U V X]

  instance hasEmbeddedType {α : U} (P : HasProperties.Property α V) : HasEmbeddedType X (Σ' P) :=
  h.embed P

  def Sigma {α : U} (P : HasProperties.Property α V) : X := HasEmbeddedType.EmbeddedType X (Σ' P)
  notation:20 "Σ " P:21 => HasDependentProducts.Sigma P

  variable {α : U} {P : HasProperties.Property α V}

  def toExternal   (S : Σ  P) : Σ' P := HasEmbeddedType.toExternal   X S
  def fromExternal (S : Σ' P) : Σ  P := HasEmbeddedType.fromExternal X S

  @[simp] theorem fromToExternal (S : Σ  P) : fromExternal (toExternal S) = S := HasEmbeddedType.fromToExternal X S
  @[simp] theorem toFromExternal (S : Σ' P) : toExternal (fromExternal S) = S := HasEmbeddedType.toFromExternal X S

  def fst (S : Σ P) : α         := (toExternal S).fst
  def snd (S : Σ P) : P (fst S) := (toExternal S).snd

  def intro (a : α) (b : P a) : Σ P := fromExternal ⟨a, b⟩

end HasDependentProducts



class HasSigmaProdEquiv (U : Universe.{u}) (V : Universe.{v}) (X : Universe.{w}) (Y : Universe.{w'})
                        [HasProperties U V] [HasDependentProducts U V X] [HasProducts U V X]
                        [HasFunctors X X Y] [HasEquivalenceCondition X Y] where
(defSigmaProdFun (α : U) (β : V) :
   (Σ HasProperties.constProp α β) ⟶[λ S => HasProducts.intro (HasDependentProducts.fst S) (HasDependentProducts.snd S)] (α ⊓ β))
(defProdSigmaFun (α : U) (β : V) :
   (α ⊓ β) ⟶[λ P => HasDependentProducts.intro (HasProducts.fst P) (HasProducts.snd P)] (Σ HasProperties.constProp α β))
(defSigmaProdEquiv  (α : U) (β : V) : (Σ HasProperties.constProp α β) ⟷[defSigmaProdFun α β, defProdSigmaFun α β] (α ⊓ β))

namespace HasSigmaProdEquiv

  variable {U V X Y Z: Universe} [HasProperties U V] [HasDependentProducts U V X] [HasProducts U V X]
           [HasFunctors X X Y] [HasEquivalences X Y Z] [HasSigmaProdEquiv U V X Y]

  @[reducible] def sigmaProdFun (α : U) (β : V) : (Σ HasProperties.constProp α β) ⟶ α ⊓ β := defSigmaProdFun α β
  @[reducible] def prodSigmaFun (α : U) (β : V) : α ⊓ β ⟶ Σ HasProperties.constProp α β := defProdSigmaFun α β
  @[reducible] def sigmaProdEquiv (α : U) (β : V) : (Σ HasProperties.constProp α β) ⟷ α ⊓ β := defSigmaProdEquiv α β

end HasSigmaProdEquiv



class HasEmbeddedDependentProducts (U : Universe.{u}) (V : Universe.{v}) [HasDependentFunctors.{u, v, v, w} U V V]
                                   [HasEmbeddedFunctors V] [HasFunProp U V V V]
  extends HasDependentProducts.{u, v, w, v} U V V where
(defIntroFun   {α : U} (P : HasProperties.Property α V) (a : α)                                   :
   P a ⟶[λ b => HasDependentProducts.intro a b] (Σ P))
(defIntroFunPi {α : U} (P : HasProperties.Property α V)                                           :
   Π[λ a => HasFunctors.fromDefFun (defIntroFun P a)] HasFunProp.outFunProp P (Σ P))
(defElimFun    {α : U} {P : HasProperties.Property α V} {γ : V} (F : Π HasFunProp.outFunProp P γ) :
   (Σ P) ⟶[λ S => F (HasDependentProducts.fst S) (HasDependentProducts.snd S)] γ)
(defElimFunFun {α : U} (P : HasProperties.Property α V) (γ : V)                                   :
   (Π HasFunProp.outFunProp P γ) ⟶[λ F => defElimFun F] ((Σ P) ⟶ γ))

namespace HasEmbeddedDependentProducts

  variable {U V : Universe} [HasDependentFunctors U V V] [HasEmbeddedFunctors V] [HasFunProp U V V V]
           [HasEmbeddedDependentProducts U V]

  @[reducible] def introFun {α : U} (P : HasProperties.Property α V) (a : α) :
    P a ⟶ Σ P :=
  defIntroFun P a

  @[reducible] def introFunPi {α : U} (P : HasProperties.Property α V) :
    Π HasFunProp.outFunProp P (Σ P) :=
  defIntroFunPi P

  @[reducible] def elimFun {α : U} {P : HasProperties.Property α V} {γ : V} (F : Π HasFunProp.outFunProp P γ) :
    (Σ P) ⟶ γ :=
  defElimFun F

  @[reducible] def elimFunFun {α : U} (P : HasProperties.Property α V) (γ : V) :
    (Π HasFunProp.outFunProp P γ) ⟶ ((Σ P) ⟶ γ) :=
  defElimFunFun P γ

end HasEmbeddedDependentProducts
