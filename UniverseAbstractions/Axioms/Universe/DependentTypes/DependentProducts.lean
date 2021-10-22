import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences
import UniverseAbstractions.Axioms.Universe.DependentTypes.Properties
import UniverseAbstractions.Axioms.Universe.DependentTypes.DependentFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v upv uv



class HasDependentProducts (U : Universe.{u}) (V : Universe.{v}) {UpV : Universe.{upv}}
                           [HasFunctors U {V} UpV] (UxV : outParam Universe.{uv}) where
(Sigma {A : U} (φ : A ⟶ ⌊V⌋)                     : UxV)
(intro {A : U} {φ : A ⟶ ⌊V⌋} (a : A) (b : ⌋φ⌊ a) : Sigma φ)
(fst   {A : U} {φ : A ⟶ ⌊V⌋} (P : Sigma φ)       : A)
(snd   {A : U} {φ : A ⟶ ⌊V⌋} (P : Sigma φ)       : ⌋φ⌊ (fst P))

namespace HasDependentProducts

  open HasFunctors HasCongrArg

  notation:20 "Σ " φ:21 => HasDependentProducts.Sigma φ
  
  class HasDependentProductEq (U : Universe.{u}) (V : Universe.{v}) {UpV : Universe.{upv}}
                              [HasFunctors U {V} UpV] {UxV : Universe.{uv}}
                              [HasDependentProducts U V UxV] [HasIdentity U]
                              [HasTypeIdentity V] [HasCongrArg U {V}] [HasIdentity UxV] where
  (introEq {A : U} {φ : A ⟶ ⌊V⌋} (P : Σ φ)           : intro (fst P) (snd P) ≃ P)
  (fstEq   {A : U} {φ : A ⟶ ⌊V⌋} (a : A) (b : ⌋φ⌊ a) : fst (intro a b) ≃ a)
  (sndEq   {A : U} {φ : A ⟶ ⌊V⌋} (a : A) (b : ⌋φ⌊ a) : snd (intro a b) ≃[propCongrArg φ (fstEq a b)] b)

end HasDependentProducts



#exit




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
