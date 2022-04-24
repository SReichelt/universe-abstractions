import Lean

import Qq.Typ
import Qq.Macro



namespace Lean

set_option autoBoundImplicitLocal false

open Meta Elab Tactic Qq



-- `QQ` doesn't really have anything to do with quotation, so we use a different name in our
-- code.
-- It would be nice to restrict `α` to a `TypeExpr` (see below), but at the moment we don't
-- always have all necessary data.
@[reducible] def TypedExpr (α : Expr) := QQ α

namespace TypedExpr

  -- Typed wrappers around some Lean functions we need.
  -- The type is an implicit parameter so that e.g. a typed parameter can be filled with
  -- just `← mkFreshMVar`.

  def mkFreshMVar   {α : Expr} : MetaM (TypedExpr α) := mkFreshExprMVar α
  def instantiate   {α α' : Expr} : TypedExpr α → MetaM (TypedExpr α') := instantiateMVars
  def elaborate'    {α : Expr} (a : Syntax) : TermElabM (TypedExpr α) := Term.elabTermAndSynthesize a α
  def elaborate     {α : Expr} (a : Syntax) : TacticM (TypedExpr α) := elabTerm a α
  def synthesize    {α : Expr} : MetaM (TypedExpr α) := synthInstance α
  def trySynthesize {α : Expr} : MetaM (LOption (TypedExpr α)) := trySynthInstance α

  def unfold_whnf   {α : Expr} : TypedExpr α → MetaM (TypedExpr α) := whnf
  def unfold_whnfR  {α : Expr} : TypedExpr α → MetaM (TypedExpr α) := whnfR
  def unfold_whnfD  {α : Expr} : TypedExpr α → MetaM (TypedExpr α) := whnfD
  def unfold_whnfI  {α : Expr} : TypedExpr α → MetaM (TypedExpr α) := whnfI
  def unfold_reduce {α : Expr} : TypedExpr α → MetaM (TypedExpr α) := reduce

  def unfold_whnfHeadPred {α : Expr} (a : TypedExpr α) (pred : TypedExpr α → MetaM Bool) :
    MetaM (TypedExpr α) :=
  whnfHeadPred α pred

  def unfold_once {α : Expr} (a : TypedExpr α) : MetaM (TypedExpr α) :=
  withReducibleAndInstances do
    let a ← whnfCore a
    match ← unfoldDefinition? a with
    | some a' => a'
    | none    => a

end TypedExpr



-- The most generic `QQ`-based expression that can be considered a type, i.e. we know that its
-- type is `mkSort u` for some `u`.
-- `type_u` should always be `q(Type u)`, but currently the `q` macro sometimes produces
-- something different.
@[reducible] def TypeExpr (u : Level) (type_u : Expr := q(Type u)) :=
QQ (@QQ.qq type_u (mkSort u))

-- We eliminate the distinction between `Q(⬝)` and `q(⬝)` by always using `q(⬝)` and treating
-- quoted types (i.e. object-level expressions of type `Sort u`) as types on the meta level,
-- via `CoeSort`.
-- This makes `Q(⬝)` mostly obsolete, and in particular instead of `Q($α)` we can just write `α`
-- (just like `q($a)` can be shortened to `a`).
scoped instance (u : Level) (type_u : Expr) : CoeSort (TypeExpr u type_u) Type := ⟨TypedExpr⟩

-- As we only need a single quotation macro, we use symbols instead.
scoped macro "⌜" t:incQuotDepth(term) "⌝" : term => `(q($t))



-- We handle type classes a bit specially because we want to reflect them as type classes on the
-- meta level.
-- It would be nice to make `α` more restrictive (`⌜Sort u⌝` or at least `TypeExpr`), and the
-- purpose of `ClassExpr` a structure is actually to be able to add a universe level field, but
-- currently we get a metavariable error from the quotation mechanism if we try this.
structure ClassExpr where
(α : Expr)

-- A generic meta-level type class to reflect an object-level type class instance.
-- (Unfortunately, this ignores `outParam` specifiers, so for type classes with `outParam`s we
-- extend `InstanceExpr`.)
class InstanceExpr (C : ClassExpr) where
(h : TypedExpr C.α)

instance (C : ClassExpr) : Inhabited (InstanceExpr C) := ⟨⟨arbitrary⟩⟩

instance : CoeSort ClassExpr Type := ⟨InstanceExpr⟩
instance (C : ClassExpr) : Coe C (TypedExpr C.α) := ⟨λ h => h.h⟩

namespace InstanceExpr

  def mkFreshMVar {C : ClassExpr} : MetaM C := do
    pure ⟨← TypedExpr.mkFreshMVar⟩

  def instantiate {C C' : ClassExpr} (h : InstanceExpr C) : MetaM C' := do
    pure ⟨← h.h.instantiate⟩

  def synthesize {C : ClassExpr} : MetaM C := do
    pure ⟨← TypedExpr.synthesize⟩

  def synthesize? {C : ClassExpr} : MetaM (Option C) := do
    match ← TypedExpr.trySynthesize with
    | LOption.some h => some ⟨h⟩
    | LOption.none   => none
    | LOption.undef  => none

end InstanceExpr
