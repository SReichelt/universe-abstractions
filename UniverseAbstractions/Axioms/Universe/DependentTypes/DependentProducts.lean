-- TODO: Adapt to `HasIdentity`.
#exit



import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences
import UniverseAbstractions.Axioms.Universe.DependentTypes.Properties
import UniverseAbstractions.Axioms.Universe.DependentTypes.DependentFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w w'



def HasDependentProducts.Sigma' {U : Universe.{u}} {V : Universe.{v}} [HasProperties U V]
                                {A : U} (φ : A ⟿ V) :=
HasProperties.Sigma φ
notation:20 "Σ' " φ:21 => HasDependentProducts.Sigma' φ

class HasDependentProducts (U : Universe.{u}) (V : Universe.{v}) [HasProperties.{u, v, w} U V]
                           (UxV : outParam Universe.{w'}) :
  Type (max 1 u v w w') where
[embed {A : U} (φ : A ⟿ V) : HasEmbeddedType.{w', max 1 u v} UxV (Σ' φ)]

namespace HasDependentProducts

  variable {U V UxV : Universe} [HasProperties U V] [h : HasDependentProducts U V UxV]

  instance hasEmbeddedType {A : U} (φ : A ⟿ V) : HasEmbeddedType UxV (Σ' φ) :=
  h.embed φ

  def Sigma {A : U} (φ : A ⟿ V) : UxV := HasEmbeddedType.EmbeddedType UxV (Σ' φ)
  notation:20 "Σ " φ:21 => HasDependentProducts.Sigma φ

  variable {A : U} {φ : A ⟿ V}

  def toExternal   (P : Σ  φ) : Σ' φ := HasEmbeddedType.toExternal   UxV P
  def fromExternal (P : Σ' φ) : Σ  φ := HasEmbeddedType.fromExternal UxV P

  @[simp] theorem fromToExternal (P : Σ  φ) : fromExternal (toExternal P) = P := HasEmbeddedType.fromToExternal UxV P
  @[simp] theorem toFromExternal (P : Σ' φ) : toExternal (fromExternal P) = P := HasEmbeddedType.toFromExternal UxV P

  def fst (P : Σ φ) : A         := (toExternal P).fst
  def snd (P : Σ φ) : φ (fst P) := (toExternal P).snd

  def intro (a : A) (b : φ a) : Σ φ := fromExternal ⟨a, b⟩

end HasDependentProducts



class HasInternalDependentProducts (U : Universe.{u}) (V : Universe.{v}) [HasDependentFunctors.{u, v, v, w} U V V]
                                   [HasInternalFunctors V] [HasFunProp U V V V]
  extends HasDependentProducts.{u, v, w, v} U V V where
(defIntroFun   {A : U} (φ : A ⟿ V) (a : A)                                   :
   φ a ⟶{λ b => HasDependentProducts.intro a b} (Σ φ))
(defIntroFunPi {A : U} (φ : A ⟿ V)                                           :
   Π{λ a => HasFunctors.fromDefFun (defIntroFun φ a)} {φ ⟶ A{Σ φ}})
(defElimFun    {A : U} {φ : A ⟿ V} {C : V} (F : Π {φ ⟶ A{C}}) :
   (Σ φ) ⟶{λ P => HasFunctors.funCoe (F (HasDependentProducts.fst P)) (HasDependentProducts.snd P)} C)
(defElimFunFun {A : U} (φ : A ⟿ V) (C : V)                                   :
   (Π {φ ⟶ A{C}}) ⟶{λ F => defElimFun F} ((Σ φ) ⟶ C))

namespace HasInternalDependentProducts

  variable {U V : Universe} [HasDependentFunctors U V V] [HasInternalFunctors V] [HasFunProp U V V V]
           [HasInternalDependentProducts U V]

  @[reducible] def introFun {A : U} (φ : A ⟿ V) (a : A) : φ a ⟶ Σ φ := defIntroFun φ a
  @[reducible] def introFunPi {A : U} (φ : A ⟿ V) : Π {φ ⟶ A{Σ φ}} := defIntroFunPi φ
  @[reducible] def elimFun {A : U} {φ : A ⟿ V} {C : V} (F : Π {φ ⟶ A{C}}) : (Σ φ) ⟶ C := defElimFun F
  @[reducible] def elimFunFun {A : U} (φ : A ⟿ V) (C : V) : (Π {φ ⟶ A{C}}) ⟶ ((Σ φ) ⟶ C) := defElimFunFun φ C

end HasInternalDependentProducts
