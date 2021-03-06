# Universe Abstractions

A Lean 4 project to automate proofs that follow from structural properties, based on a simple generalized `Universe` concept.

This is still work in progress and subject to frequent refactoring.

For a mathematical description, see [UniverseAbstractions.pdf](Doc/UniverseAbstractions.pdf).

## Directory Structure

* `Axioms`: Abstract definition of a universe and of structure on universes.
  * `Universe`: Basic structure that most universes should have in some form: identities (also called "instance equivalences"), functors, products, (type) equivalences.
    * `DependentTypes`: Dependent versions of functors and products, i.e. Π and Σ types. These tend to involve multiple universes.
    * `FunctorialIdentities`: Properties that arise if operations on identities are assumed to be functorial (currently very experimental).
* `Lemmas`: Derived definitions and proofs that work generically on universes (with structure).
* `Instances`: Definitions of specific universes, including native Lean universes with their structure.
* `Meta`: Meta-level code to work with universes.
  * `Tactics`: Currently just one tactic, which builds a functor from a lambda term.
* `CategoryTheory`: Standard constructions from category theory, generalized to use instance equivalences instead of equality, so that they are compatible with higher categories.
* `MathlibFragments`: Small parts of mathlib ported to Lean 4; slightly generalized so we can use the `≃` notation for instance equivalences.
