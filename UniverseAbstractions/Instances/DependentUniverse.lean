import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences
import UniverseAbstractions.Axioms.Universe.Properties

import mathlib4_experiments.Data.Equiv.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w w'



-- For a given `α` and `V`, the properties in `α ⟿ V` form a universe that inherits many features
-- from `V`, if we fix an `a : α`. Essentially, we just apply `a` to every property, yielding a
-- type in `V`. We use the properties as type indices, and only apply `a` when determining the type
-- for a given type index. Therefore we can use universe infrastructure such as the functoriality
-- tactic to produce properties.
--
-- Essentially, this is the universe where the expression under a quantifier "lives".
-- TODO: Figure out what this means exactly.

-- TODO: Finish this formalization. (Does this really do what we want though? Can't we produce
-- properties using the functoriality tactic _without_ fixing `a`?)

structure DependentInstance {U : Universe.{u}} (α : U) (a : α) (V : Universe.{v})
                            [HasProperties.{u, v, w} U V] (φ : α ⟿ V) :
  Sort (max 1 u v w) where
(b : φ a)

namespace DependentInstance

  @[simp] theorem mk_elim {U : Universe.{u}} (α : U) (a : α) (V : Universe.{v})
                          [HasProperties.{u, v, w} U V] (φ : α ⟿ V) (x : DependentInstance α a V φ) :
    DependentInstance.mk x.b = x :=
  by induction x; rfl

end DependentInstance

def dependentUniverse {U : Universe.{u}} (α : U) (a : α) (V : Universe.{v}) [HasProperties.{u, v, w} U V] :
  Universe.{max 1 u v w} :=
{ α    := α ⟿ V,
  inst := ⟨DependentInstance α a V⟩ }

namespace dependentUniverse

  variable {U : Universe.{u}} (α : U) (a : α)

  section

    variable (V W : Universe) [HasProperties U V] [HasProperties U W]

    instance hasFunctoriality [h : HasFunctoriality V W] :
      HasFunctoriality (dependentUniverse α a V) (dependentUniverse α a W) :=
    ⟨λ f => h.IsFun (λ b => (f ⟨b⟩).b)⟩

    variable (X : Universe) [HasFunctors V W X] [HasProperties U X] [HasFunProp U V W X]

    def funEquiv (φ : dependentUniverse α a V) (ψ : dependentUniverse α a W) :
      DependentInstance α a X (HasFunProp.funProp φ ψ) ≃ (φ ⟶' ψ) :=
    { toFun    := λ F => ⟨λ b => ⟨HasFunctors.funCoe F.b b.b⟩, HasFunctors.toDefFun F.b⟩,
      invFun   := λ F => ⟨HasFunctors.fromDefFun F.F⟩,
      leftInv  := λ ⟨_⟩ => by simp,
      rightInv := λ ⟨f, F⟩ => by simp; exact HasFunctors.toFromDefFun F }

    instance hasEmbeddedFunctorType (φ : dependentUniverse α a V) (ψ : dependentUniverse α a W) :
      HasEmbeddedType (dependentUniverse α a X) (φ ⟶' ψ) :=
    ⟨funEquiv α a V W X φ ψ⟩

    instance hasFunctors : HasFunctors (dependentUniverse α a V) (dependentUniverse α a W)
                                       (dependentUniverse α a X) :=
    ⟨⟩

  end

  instance hasEmbeddedFunctors (V : Universe) [HasProperties U V] [HasEmbeddedFunctors V]
                               [HasFunProp U V V V] :
    HasEmbeddedFunctors (dependentUniverse α a V) :=
  ⟨⟩

end dependentUniverse
