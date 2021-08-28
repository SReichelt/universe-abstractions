import UniverseAbstractions.Axioms.Universes

import mathlib4_experiments.Data.Equiv.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w w'



-- We define a "`V`-valued property" on a type `α` to be a function yielding a type in `V` with an
-- additional condition. If `V` is the universe `prop`, this is just a regular property, or
-- equivalently `Set α` in Lean.

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

    variable {α : U} (P : Property α V)

    -- Universality and existence with respect to generalized properties are given by `∀` and `Σ'`.

    def Pi    : Sort (imax u v)  := ∀  a, ⌈P a⌉
    def Sigma : Sort (max 1 u v) := Σ' a, ⌈P a⌉

    class IsUniversal where
    (h : Pi P)

    class IsInhabited where
    (h : Sigma P)

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
