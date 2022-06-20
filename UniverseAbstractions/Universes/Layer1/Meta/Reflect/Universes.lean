import UniverseAbstractions.Meta.Helpers

import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Meta.ExprUniverse
import UniverseAbstractions.Universes.Layer1.Meta.Sort



namespace UniverseAbstractions.Layer1.Meta

set_option autoImplicit false

open Lean Lean.Meta Qq UniverseAbstractions.Meta



@[reducible] def _Universe.typedExpr (u uu : Level) : ⌜Type (max u uu)⌝ := ⌜Universe.{u, uu}⌝
def _Universe.sort (u uu : Level) : _sort := ⟨typedExpr u uu⟩



def mkHasInstances'' (u : Level) {v : Level} (I : Q(Sort v)) := ⌜HasInstances.{u, v} $I⌝

namespace mkHasInstances''

  def mkInst {u v : Level} {I : Q(Sort v)} (h : mkHasInstances'' u I) (A : Q($I)) : Q(Sort u) := ⌜$A⌝

  def mkInstFun {u v : Level} {I : Q(Sort v)} (h : mkHasInstances'' u I) : Q($I → Sort u) :=
    ⌜λ A => A⌝

  instance univInst (u uu : Level) : mkHasInstances'' uu ⌜Universe.{u, uu}⌝ :=
    ⌜Universe.hasInstances⌝

  def univInstInst {u uu : Level} (U : Q(Universe.{u, uu})) : mkHasInstances'' u ⌜$U⌝ :=
    ⌜Universe.instInst $U⌝

end mkHasInstances''

def mkHasInstances' (u : Level) (I : _sort) : ClassExpr := ⟨mkHasInstances'' u I.α⟩

class mkHasInstances (u : outParam Level) (I : _sort) extends mkHasInstances' u I

namespace mkHasInstances

  def mkInst' {u : Level} {I : _sort} [h : mkHasInstances u I] (A : I) : _sort.mkSortType u :=
    mkHasInstances''.mkInst h.h A
  @[reducible] def mkInst {u : Level} {I : _sort} [mkHasInstances u I] (A : I) : _sort :=
    mkInst' A

  def defInstFun {u : Level} (I : _sort) [h : mkHasInstances u I] :
      I ⥤{mkInst'} _sort.mkSortType u :=
    ⟨mkHasInstances''.mkInstFun h.h⟩

  @[reducible] def instFun {u : Level} (I : _sort) [mkHasInstances u I] : I ⥤ _sort.mkSortType u :=
    defInstFun I

  instance reflect {u : Level} (I : _sort) [mkHasInstances u I] : HasInstances I :=
    ⟨λ A => mkInst A⟩

  instance univInst (u uu : Level) : mkHasInstances uu (_Universe.sort u uu) :=
    { h := mkHasInstances''.univInst u uu }

  instance univInstInst {u uu : Level} (U : _Universe.sort u uu) : mkHasInstances u (mkInst U) :=
    { h := mkHasInstances''.univInstInst (u := u) (uu := uu) U }

end mkHasInstances



structure _Universe (u : Level) where
  {uu : Level}
  U   : _Universe.typedExpr u uu

namespace _Universe

  instance (u : Level) : Coe (_Universe u) Expr := ⟨_Universe.U⟩

  def mkFreshMVar (u : Level) : MetaM (_Universe u) := do
    let uu ← mkFreshLevelMVar
    let U : typedExpr u uu ← TypedExpr.mkFreshMVar
    pure ⟨U⟩

  variable {u : Level}

  def instantiate (U : _Universe u) (u' : Level) : MetaM (_Universe u') := do
    let uu ← instantiateLevelMVars U.uu
    let U : typedExpr u' uu ← U.U.instantiate
    pure ⟨U⟩

  def mkInst' (U : _Universe u) : _sort.mkSortType U.uu :=
    mkHasInstances.mkInst' (I := sort u U.uu) U.U
  @[reducible] def mkInst (U : _Universe u) : _sort := mkInst' U
  notation "_[" U:0 "]" => _Universe.mkInst U

  instance hasInstInst (U : _Universe u) : mkHasInstances u _[U] := mkHasInstances.univInstInst U.U

  @[reducible] def mkInstInst' {U : _Universe u} (A : _[U]) : _sort := mkHasInstances.mkInst A

  def reflect (U : _Universe u) := exprUniverse (mkInstInst' (U := U))
  instance : Coe (_Universe u) Universe := ⟨_Universe.reflect⟩
  instance : CoeSort (_Universe u) Type := ⟨λ U => U⟩

  variable {U : _Universe u}

  @[reducible] def reflectInst (A : _[U]) : U := A
  notation "_|" A:0 "|" => _Universe.reflectInst A

  @[reducible] def unreflectInst (A : U) : _[U] := A
  notation "_(" A:0 ")" => _Universe.unreflectInst A

  @[reducible] def mkInstInst (A : U) : _sort := mkInstInst' _(A)
  notation "_⌈" A:0 "⌉" => _Universe.mkInstInst A

  def defInstInstFun (U : _Universe u) : _[U] ⥤{λ A : U => _⌈A⌉.α} _sort.mkSortType u :=
    mkHasInstances.defInstFun _[U]

  @[reducible] def instInstFun (U : _Universe u) : _[U] ⥤ _sort.mkSortType u := defInstInstFun U

  def mkFreshTypeMVar : MetaM U := TypedExpr.mkFreshMVar (α := _[U].α)
  def mkFreshInstMVar {A : U} : MetaM A := TypedExpr.mkFreshMVar (α := _⌈A⌉.α)

  def instantiateTypeMVars : U → MetaM U :=
    TypedExpr.instantiate (α := _[U].α) (α' := _[U].α)
  def instantiateInstMVars' {A A' : U} : A → MetaM A' :=
    TypedExpr.instantiate (α := _⌈A⌉.α) (α' := _⌈A'⌉.α)
  def instantiateInstMVars {A : U} : A → MetaM A := U.instantiateInstMVars'

end _Universe
