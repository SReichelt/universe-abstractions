import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences

import UniverseAbstractions.Lemmas.LeanEq

import mathlib4_experiments.Data.Equiv.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w w'



-- We define a "`V`-valued property" on a type `α` to be a function yielding a type in `V` with an
-- additional condition, similarly to the definition of functoriality. If `V` is the universe
-- `prop`, this is just a regular property, or equivalently `Set α` in Lean.

class HasProperties (U : Universe.{u}) (V : Universe.{v}) : Type (max u v w) where
(IsProp      {α : U}         : (α → V) → Sort w)
(constIsProp (α : U) (β : V) : IsProp (Function.const ⌈α⌉ β))

namespace HasProperties

  structure Property {U : Universe.{u}} (α : U) (V : Universe.{v}) [h : HasProperties.{u, v, w} U V] :
    Sort (max (u + 1) (v + 1) w) where
  {p : α → V}
  (P : h.IsProp p)

  variable {U : Universe.{u}} {V : Universe.{v}} [h : HasProperties U V]

  instance coeFun {α : U} : CoeFun (Property α V) (λ _ => α → V) := ⟨Property.p⟩

  section Properties

    variable {α : U} (φ : Property α V)

    -- Universality and existence with respect to generalized properties are given by `∀` and `Σ'`.

    def Pi    : Sort (imax u v)  := ∀  a, ⌈φ a⌉
    def Sigma : Sort (max 1 u v) := Σ' a, ⌈φ a⌉

    class IsUniversal where
    (h : Pi φ)

    class IsInhabited where
    (h : Sigma φ)

  end Properties

  -- Given a type `β : V`, we can define a constant property that always yields this type. `Pi`
  -- applied to this property is just the type of functions from `α` to `β`, and `Sigma` applied to
  -- this property is just the product of `α` and `β`.

  def constProp (α : U) (β : V) : Property α V := ⟨h.constIsProp α β⟩

  namespace constProp

    variable (α : U) (β : V)

    def piEquivFun : Pi (constProp α β) ≃ (α → β) := Equiv.refl (α → β)

    def sigmaEquivProd : Sigma (constProp α β) ≃ PProd ⌈α⌉ ⌈β⌉ :=
    { toFun    := λ s => ⟨s.fst, s.snd⟩,
      invFun   := λ p => ⟨p.fst, p.snd⟩,
      leftInv  := λ ⟨_, _⟩ => rfl,
      rightInv := λ ⟨_, _⟩ => rfl }

  end constProp

end HasProperties



class HasCompFunProp' (U V W : Universe) [HasFunctoriality U V] [HasProperties V W]
                      [h : HasProperties U W] where
(compIsProp {α : U} {β : V} (F : α ⟶' β) (φ : HasProperties.Property β W) :
   h.IsProp (λ a => φ (F a)))
(compConstEq {α : U} {β : V} (F : α ⟶' β) (γ : W) :
   compIsProp F (HasProperties.constProp β γ) = h.constIsProp α γ)

namespace HasCompFunProp'

  variable {U V W : Universe} [HasFunctoriality U V] [HasProperties V W] [HasProperties U W]
           [h : HasCompFunProp' U V W]

  @[reducible] def compProp' {α : U} {β : V} (F : α ⟶' β) (φ : HasProperties.Property β W) :
    HasProperties.Property α W :=
  ⟨h.compIsProp F φ⟩

  theorem compPropConstEq' {α : U} {β : V} (F : α ⟶' β) (γ : W) :
    compProp' F (HasProperties.constProp β γ) = HasProperties.constProp α γ :=
  congrArg HasProperties.Property.mk (h.compConstEq F γ)

end HasCompFunProp'

class HasCompFunProp (U V W X : Universe) [HasFunctors U V X] [HasProperties V W]
                     [h : HasProperties U W] where
(compIsProp {α : U} {β : V} (F : α ⟶ β) (φ : HasProperties.Property β W) :
   h.IsProp (λ a => φ (F a)))
(compConstEq {α : U} {β : V} (F : α ⟶ β) (γ : W) :
   compIsProp F (HasProperties.constProp β γ) = h.constIsProp α γ)

namespace HasCompFunProp

  variable {U V W X : Universe} [HasFunctors U V X] [HasProperties V W] [HasProperties U W]
           [h : HasCompFunProp U V W X]

  @[reducible] def compProp {α : U} {β : V} (F : α ⟶ β) (φ : HasProperties.Property β W) :
    HasProperties.Property α W :=
  ⟨h.compIsProp F φ⟩

  theorem compPropConstEq {α : U} {β : V} (F : α ⟶ β) (γ : W) :
    compProp F (HasProperties.constProp β γ) = HasProperties.constProp α γ :=
  congrArg HasProperties.Property.mk (h.compConstEq F γ)

  instance hasCompFunProp' : HasCompFunProp' U V W :=
  { compIsProp  := λ F φ => funext (λ a => congrArg φ.p (HasFunctors.fromExternal.eff F a)) ▸
                            h.compIsProp (HasFunctors.fromExternal F) φ,
    compConstEq := λ F γ => h.compConstEq (HasFunctors.fromExternal F) γ }

end HasCompFunProp



class HasFunProp (U V W X : Universe) [HasProperties U V] [HasProperties U W] [HasFunctors V W X]
                 [h : HasProperties U X] where
(funIsProp {α : U} (φ : HasProperties.Property α V) (ψ : HasProperties.Property α W) :
   h.IsProp (λ a => φ a ⟶ ψ a))
(funConstEq (α : U) (β : V) (γ : W) :
   funIsProp (HasProperties.constProp α β) (HasProperties.constProp α γ) = h.constIsProp α (β ⟶ γ))

namespace HasFunProp

  variable {U V W X : Universe} [HasProperties U V] [HasProperties U W] [HasFunctors V W X]
           [HasProperties U X] [h : HasFunProp U V W X]

  @[reducible] def funProp {α : U} (φ : HasProperties.Property α V) (ψ : HasProperties.Property α W) :
    HasProperties.Property α X :=
  ⟨h.funIsProp φ ψ⟩

  @[reducible] def inFunProp {α : U} (β : V) (ψ : HasProperties.Property α W) :=
  HasFunProp.funProp (HasProperties.constProp α β) ψ
  @[reducible] def outFunProp {α : U} (φ : HasProperties.Property α V) (β : W) :=
  HasFunProp.funProp φ (HasProperties.constProp α β)

  theorem funPropConstEq (α : U) (β : V) (γ : W) :
    funProp (HasProperties.constProp α β) (HasProperties.constProp α γ) = HasProperties.constProp α (β ⟶ γ) :=
  congrArg HasProperties.Property.mk (h.funConstEq α β γ)

end HasFunProp



class HasProdProp (U V W X : Universe) [HasProperties U V] [HasProperties U W] [HasProducts V W X]
                  [h : HasProperties U X] where
(prodIsProp {α : U} (φ : HasProperties.Property α V) (ψ : HasProperties.Property α W) :
   h.IsProp (λ a => φ a ⊓ ψ a))
(prodConstEq (α : U) (β : V) (γ : W) :
   prodIsProp (HasProperties.constProp α β) (HasProperties.constProp α γ) = h.constIsProp α (β ⊓ γ))

namespace HasProdProp

  variable {U V W X : Universe} [HasProperties U V] [HasProperties U W] [HasProducts V W X]
           [HasProperties U X] [h : HasProdProp U V W X]

  @[reducible] def prodProp {α : U} (φ : HasProperties.Property α V) (ψ : HasProperties.Property α W) :
    HasProperties.Property α X :=
  ⟨h.prodIsProp φ ψ⟩

  theorem prodPropConstEq (α : U) (β : V) (γ : W) :
    prodProp (HasProperties.constProp α β) (HasProperties.constProp α γ) = HasProperties.constProp α (β ⊓ γ) :=
  congrArg HasProperties.Property.mk (h.prodConstEq α β γ)

end HasProdProp



class HasEquivProp (U V X : Universe) [HasProperties U V] [HasEmbeddedFunctors V]
                   [HasEquivalences V V X] [h : HasProperties U X] where
(equivIsProp {α : U} (φ ψ : HasProperties.Property α V) : h.IsProp (λ a => φ a ⟷ ψ a))
(equivConstEq (α : U) (β γ : V) :
   equivIsProp (HasProperties.constProp α β) (HasProperties.constProp α γ) = h.constIsProp α (β ⟷ γ))

namespace HasEquivProp

  variable {U V X : Universe} [HasProperties U V] [HasEmbeddedFunctors V] [HasEquivalences V V X]
           [HasProperties U X] [h : HasEquivProp U V X]

  @[reducible] def equivProp {α : U} (φ ψ : HasProperties.Property α V) : HasProperties.Property α X :=
  ⟨h.equivIsProp φ ψ⟩

  theorem equivPropConstEq (α : U) (β γ : V) :
    equivProp (HasProperties.constProp α β) (HasProperties.constProp α γ) = HasProperties.constProp α (β ⟷ γ) :=
  congrArg HasProperties.Property.mk (h.equivConstEq α β γ)

end HasEquivProp
