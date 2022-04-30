import UniverseAbstractions.Meta.TypedExpr

import UniverseAbstractions.Universes.Layer1.Axioms.Universes



namespace UniverseAbstractions.Layer1.Meta

set_option autoBoundImplicitLocal false

open Lean



-- On the meta level, we can define several different universes of expressions. In particular:
-- * All object-level universes along with their structure are reflected on the meta level by
--   universes with the same structure.
-- * Of course, the above includes each universe `sort.{u}`. However, for these we can go a
--   little further and combine them into a single universe `_sort` by bundling a `Level` with
--   each `Expr` that denotes a type.
--
-- Using universe-based structures on the meta level has the advantage that we have all "proofs"
-- about universes (which are actually definitions) at our disposal, and we can be certain that
-- this code is error-free.

structure _Sort where
{u : Level}
(α : ⌜Sort u⌝)

def exprUniverse {β : Type} (inst : β → _Sort) : Universe.{1, 1} :=
{ I := β,
  h := ⟨λ A => (inst A).α⟩ }
