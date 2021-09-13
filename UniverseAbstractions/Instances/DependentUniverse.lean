import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences
import UniverseAbstractions.Axioms.Universe.Properties
import UniverseAbstractions.Axioms.Universe.DependentFunctors

import mathlib4_experiments.Data.Equiv.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w w'



-- For a given `A` and `V`, the properties in `A ⟿ V` form a universe that inherits many features
-- from `V`, if we fix an `a : A`. Essentially, we just apply `a` to every property, yielding a
-- type in `V`. We use the properties as type indices, and only apply `a` when determining the type
-- for a given type index. Therefore we can use universe infrastructure such as the functoriality
-- tactic to produce properties.
--
-- Essentially, this is the universe where the expression under a quantifier "lives".
-- TODO: Figure out what this means exactly.
--       Maybe it allows us to assert something like: If something can be proved/constructed for
--       arbitrary `a`, then we can universally quantify over it.

-- TODO: Finish this formalization. (Does this really do what we want though? Can't we produce
-- properties using the functoriality tactic _without_ fixing `a`?)
-- Maybe replace all `φ` with some sort of arbitrary type-producing functions, based on an arbitrary
-- index type? Then we can say: "If something can be proved for arbitrary index types, we can
-- universally quantify over it."
-- However, with an arbitrary index type, we run into trouble finding an index for e.g. the functor
-- type between two types, because we can no longer rely on `funProp`.
-- Can we formalize the concept of a "context"? Seems related to Sigma/Pi equivalences: Context is
-- stacked sigmas, dependency on context is pi.

structure DependentInstance {U : Universe.{u}} (A : U) (a : A) (V : Universe.{v})
                            [HasProperties.{u, v, w} U V] (φ : A ⟿ V) :
  Sort (max 1 u v w) where
(b : φ a)

namespace DependentInstance

  @[simp] theorem mk_elim {U : Universe.{u}} (A : U) (a : A) (V : Universe.{v})
                          [HasProperties.{u, v, w} U V] (φ : A ⟿ V) (x : DependentInstance A a V φ) :
    DependentInstance.mk x.b = x :=
  by induction x; rfl

end DependentInstance

def dependentUniverse {U : Universe.{u}} (A : U) (a : A) (V : Universe.{v}) [HasProperties.{u, v, w} U V] :
  Universe.{max 1 u v w} :=
{ A    := A ⟿ V,
  inst := ⟨DependentInstance A a V⟩ }

namespace dependentUniverse

  def type {U V : Universe} [HasProperties U V] {A : U} (φ : A ⟿ V) (a : A) : dependentUniverse A a V := φ

  variable {U : Universe.{u}} (A : U) (a : A)

  section

    variable (V W : Universe) [HasProperties U V] [HasProperties U W]

    instance hasFunctoriality [h : HasFunctoriality V W] :
      HasFunctoriality (dependentUniverse A a V) (dependentUniverse A a W) :=
    ⟨λ f => h.IsFun (λ b => (f ⟨b⟩).b)⟩

    variable (VW : Universe) [HasFunctors V W VW] [HasProperties U VW] [HasFunProp U V W VW]

    def funEquiv (φ : dependentUniverse A a V) (ψ : dependentUniverse A a W) :
      DependentInstance A a VW (HasFunProp.funProp φ ψ) ≃ (φ ⟶' ψ) :=
    { toFun    := λ F => ⟨λ b => ⟨HasFunctors.funCoe F.b b.b⟩, HasFunctors.toDefFun F.b⟩,
      invFun   := λ F => ⟨HasFunctors.fromDefFun F.F⟩,
      leftInv  := λ ⟨_⟩ => by simp,
      rightInv := λ ⟨f, F⟩ => by simp; exact HasFunctors.toFromDefFun F }

    instance hasEmbeddedFunctorType (φ : dependentUniverse A a V) (ψ : dependentUniverse A a W) :
      HasEmbeddedType (dependentUniverse A a VW) (φ ⟶' ψ) :=
    ⟨funEquiv A a V W VW φ ψ⟩

    instance hasFunctors : HasFunctors (dependentUniverse A a V) (dependentUniverse A a W)
                                       (dependentUniverse A a VW) := ⟨⟩

  end

  section

    variable (V : Universe) [HasProperties U V] [HasEmbeddedFunctors V] [HasFunProp U V V V]

    instance hasEmbeddedFunctors : HasEmbeddedFunctors (dependentUniverse A a V) := ⟨⟩

    instance hasLinearFunOp [h : HasLinearFunOp V] : HasLinearFunOp (dependentUniverse A a V) :=
    { defIdFun         := λ (φ : A ⟿ V) => h.defIdFun (φ a),
      defAppFun        := λ b (ψ : A ⟿ V) => h.defAppFun b.b (ψ a),
      defAppFunFun     := λ (φ : A ⟿ V) (ψ : A ⟿ V) => h.defAppFunFun (φ a) (ψ a),
      defCompFun       := λ F G => h.defCompFun F.b G.b,
      defCompFunFun    := λ F (χ : A ⟿ V) => h.defCompFunFun F.b (χ a),
      defCompFunFunFun := λ (φ : A ⟿ V) (ψ : A ⟿ V) (χ : A ⟿ V) => h.defCompFunFunFun (φ a) (ψ a) (χ a) }

    instance hasAffineFunOp [h : HasAffineFunOp V] : HasAffineFunOp (dependentUniverse A a V) :=
    { defConstFun    := λ (φ : A ⟿ V) {_} b => h.defConstFun (φ a) b.b,
      defConstFunFun := λ (φ : A ⟿ V) (ψ : A ⟿ V) => h.defConstFunFun (φ a) (ψ a) }

    instance hasFullFunOp [h : HasFullFunOp V] : HasFullFunOp (dependentUniverse A a V) :=
    { defDupFun    := λ F => h.defDupFun F.b,
      defDupFunFun := λ (φ : A ⟿ V) (ψ : A ⟿ V) => h.defDupFunFun (φ a) (ψ a) }

    instance hasFunOp [HasFullFunOp V] : HasFunOp (dependentUniverse A a V) := ⟨⟩

  end

end dependentUniverse
