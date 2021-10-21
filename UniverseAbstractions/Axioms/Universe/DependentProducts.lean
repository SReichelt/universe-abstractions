-- TODO: Adapt to `HasIdentity`.
#exit



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



class HasSigmaProdEquiv (U : Universe.{u}) (V : Universe.{v}) (UxV : Universe.{w}) (UxVUxV : Universe.{w'})
                        [HasProperties U V] [HasDependentProducts U V UxV] [HasProducts U V UxV]
                        [HasFunctors UxV UxV UxVUxV] [HasEquivalenceCondition UxV UxVUxV] where
(defSigmaProdFun (A : U) (B : V) :
   (Σ A{B}) ⟶[λ P => HasProducts.intro (HasDependentProducts.fst P) (HasDependentProducts.snd P)] (A ⊓ B))
(defProdSigmaFun (A : U) (B : V) :
   (A ⊓ B) ⟶[λ φ => HasDependentProducts.intro (HasProducts.fst φ) (HasProducts.snd φ)] (Σ A{B}))
(defSigmaProdEquiv (A : U) (B : V) : (Σ A{B}) ⟷[defSigmaProdFun A B, defProdSigmaFun A B] (A ⊓ B))

namespace HasSigmaProdEquiv

  variable {U V UxV UxVUxV UxV_UxV : Universe} [HasProperties U V] [HasDependentProducts U V UxV] [HasProducts U V UxV]
           [HasFunctors UxV UxV UxVUxV] [HasEquivalences UxV UxVUxV UxV_UxV] [HasSigmaProdEquiv U V UxV UxVUxV]

  @[reducible] def sigmaProdFun (A : U) (B : V) : (Σ A{B}) ⟶ A ⊓ B := defSigmaProdFun A B
  @[reducible] def prodSigmaFun (A : U) (B : V) : A ⊓ B ⟶ Σ A{B} := defProdSigmaFun A B
  @[reducible] def sigmaProdEquiv (A : U) (B : V) : (Σ A{B}) ⟷ A ⊓ B := defSigmaProdEquiv A B

end HasSigmaProdEquiv



class HasInternalDependentProducts (U : Universe.{u}) (V : Universe.{v}) [HasDependentFunctors.{u, v, v, w} U V V]
                                   [HasInternalFunctors V] [HasFunProp U V V V]
  extends HasDependentProducts.{u, v, w, v} U V V where
(defIntroFun   {A : U} (φ : A ⟿ V) (a : A)                                   :
   φ a ⟶[λ b => HasDependentProducts.intro a b] (Σ φ))
(defIntroFunPi {A : U} (φ : A ⟿ V)                                           :
   Π[λ a => HasFunctors.fromDefFun (defIntroFun φ a)] {φ ⟶ A{Σ φ}})
(defElimFun    {A : U} {φ : A ⟿ V} {C : V} (F : Π {φ ⟶ A{C}}) :
   (Σ φ) ⟶[λ P => HasFunctors.funCoe (F (HasDependentProducts.fst P)) (HasDependentProducts.snd P)] C)
(defElimFunFun {A : U} (φ : A ⟿ V) (C : V)                                   :
   (Π {φ ⟶ A{C}}) ⟶[λ F => defElimFun F] ((Σ φ) ⟶ C))

namespace HasInternalDependentProducts

  variable {U V : Universe} [HasDependentFunctors U V V] [HasInternalFunctors V] [HasFunProp U V V V]
           [HasInternalDependentProducts U V]

  @[reducible] def introFun {A : U} (φ : A ⟿ V) (a : A) : φ a ⟶ Σ φ := defIntroFun φ a
  @[reducible] def introFunPi {A : U} (φ : A ⟿ V) : Π {φ ⟶ A{Σ φ}} := defIntroFunPi φ
  @[reducible] def elimFun {A : U} {φ : A ⟿ V} {C : V} (F : Π {φ ⟶ A{C}}) : (Σ φ) ⟶ C := defElimFun F
  @[reducible] def elimFunFun {A : U} (φ : A ⟿ V) (C : V) : (Π {φ ⟶ A{C}}) ⟶ ((Σ φ) ⟶ C) := defElimFunFun φ C

end HasInternalDependentProducts
