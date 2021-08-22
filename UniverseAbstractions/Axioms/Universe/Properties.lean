import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors

import mathlib4_experiments.Data.Equiv.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w



-- We define a "`V`-valued property" on a type `α` to be a functor targetting a universe `V`. If
-- `V` is the universe `prop`, this is just a regular property, or equivalently `Set α` in Lean.

class HasGeneralizedProperties (U : Universe.{u})
  extends HasFunctoriality.{u, v + 1, w} U univ.{v}, HasConstFun U univ.{v}

namespace HasGeneralizedProperties

  variable {U : Universe.{u}} [HasGeneralizedProperties.{u, v, w} U]

  def Property (V : univ.{v}) (α : U) : Sort (max u (v + 1) w) := α ⟶' V

  variable {V : univ.{v}}

  instance coeFun {α : U} : CoeFun (Property V α) (λ _ => α → V) := HasFunctoriality.coeFun

  section Properties

    variable {α : U} (P : Property V α)

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

  def constProp (α : U) (β : V) : Property V α := HasConstFun.constFun' α β

  namespace constProp

    variable (α : U) (β : V)

    def piEquivFun : Pi (constProp α β) ≃ (α → β) := Equiv.refl (α → β)

    def sigmaEquivProd : Sigma (constProp α β) ≃ PProd ⌈α⌉ ⌈β⌉ :=
    { toFun    := λ s => ⟨s.fst, s.snd⟩,
      invFun   := λ p => ⟨p.fst, p.snd⟩,
      leftInv  := λ ⟨_, _⟩ => rfl,
      rightInv := λ ⟨_, _⟩ => rfl }

  end constProp

end HasGeneralizedProperties



-- We can define a "`V`-valued set" with base universe `U` as a bundled version of `Property V`
-- when treated as a type class on `U`. In other words, a set is a type `α : U` together with a
-- `V`-valued property `P` on `α`.
--
-- This gives us a universe of all `V`-valued sets with base universe `U`, where we can define
-- functors etc.
--
-- (TODO: How does this relate to embedded sigma types, i.e. subtypes?)

def HasGeneralizedProperties.asTypeClass (U : Universe.{u}) [HasGeneralizedProperties.{u, v, w} U]
                                         (V : Universe.{v}) :
  GeneralizedTypeClass ⌈U⌉ :=
HasGeneralizedProperties.Property V

def GeneralizedSet (U : Universe.{u}) [HasGeneralizedProperties.{u, v, w} U] (V : Universe.{v}) :
  Type (max u (v + 1) w) :=
Bundled (HasGeneralizedProperties.asTypeClass U V)
