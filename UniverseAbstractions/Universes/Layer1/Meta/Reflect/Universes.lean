import UniverseAbstractions.Meta.Helpers

import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Meta.ExprUniverse



namespace UniverseAbstractions.Layer1.Meta

set_option autoBoundImplicitLocal false

open Lean Lean.Meta Qq



def mkHasInstances' (u : Level) {v : Level} (I : ⌜Sort v⌝) : ClassExpr :=
⟨⌜HasInstances.{u, v} $I⌝⟩

class mkHasInstances (u : outParam Level) {v : Level} (I : ⌜Sort v⌝) extends
mkHasInstances' u I

namespace mkHasInstances

  def mkInst {u v : Level} {I : ⌜Sort v⌝} [h : mkHasInstances u I] (A : I) : ⌜Sort u⌝ :=
  let _ := h.h
  ⌜$A⌝

  instance reflect {u v : Level} (I : ⌜Sort v⌝) [h : mkHasInstances u I] : HasInstances I :=
  ⟨λ A => mkInst A⟩

end mkHasInstances



structure _Universe where
{u v : Level}
(U   : ⌜Universe.{u, v}⌝)

namespace _Universe

  instance : Coe _Universe Expr := ⟨_Universe.U⟩

  def mkFreshMVar : MetaM _Universe := do
    let u ← mkFreshLevelMVar
    let v ← mkFreshLevelMVar
    let U : ⌜Universe.{u, v}⌝ ← TypedExpr.mkFreshMVar
    pure ⟨U⟩

  def instantiate (U : _Universe) : MetaM _Universe := do
    let u ← instantiateLevelMVars U.u
    let v ← instantiateLevelMVars U.v
    let U : ⌜Universe.{u, v}⌝ ← TypedExpr.instantiate U.U
    pure ⟨U⟩

  def mkInst (U : _Universe) : ⌜Sort $U.v⌝ := ⌜$U.U⌝

  instance hasInstInst (U : _Universe) : mkHasInstances U.u (mkInst U) :=
  { h := ⌜Universe.instInst _⌝ }

  @[reducible] def LeanUniv (U : _Universe) := ⌜Sort $U.u⌝

  def instInst {U : _Universe} (A : mkInst U) : _Sort := ⟨mkHasInstances.mkInst A⟩

  def reflect (U : _Universe) := exprUniverse (instInst (U := U))
  notation "_(" U:0 ")" => _Universe.reflect U

  def mkInstInst {U : _Universe} (A : _(U)) : LeanUniv U :=
  mkHasInstances.mkInst (h := hasInstInst U) A
  notation "_⌈" A:0 "⌉" => _Universe.mkInstInst A

  variable {U : _Universe}

  def mkFreshTypeMVar : MetaM _(U) := TypedExpr.mkFreshMVar (α := mkInst U)
  def mkFreshInstMVar {A : _(U)} : MetaM A := TypedExpr.mkFreshMVar (α := _⌈A⌉)

  def instantiateTypeMVars : _(U) → MetaM _(U) :=
  TypedExpr.instantiate (α := mkInst U) (α' := mkInst U)
  def instantiateInstMVars' {A A' : _(U)} : A → MetaM A' :=
  TypedExpr.instantiate (α := _⌈A⌉) (α' := _⌈A'⌉)
  def instantiateInstMVars {A : _(U)} : A → MetaM A := U.instantiateInstMVars'

  @[reducible] def FVar (A : _(U)) := Lean.FVar _⌈A⌉

end _Universe
