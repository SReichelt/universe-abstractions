import UniverseAbstractions.Meta.TypedExpr



namespace UniverseAbstractions.Meta

set_option autoImplicit false

open Lean Lean.Meta Elab Tactic Qq



def mkFun {u v : Level} (α : ⌜Sort u⌝) (β : ⌜Sort v⌝) : ⌜Sort (imax u v)⌝ := ⌜$α → $β⌝
def mkFun.mkApp {u v : Level} {α : ⌜Sort u⌝} {β : ⌜Sort v⌝} (f : mkFun α β) (a : α) : β := ⌜$f $a⌝

def mkForAll {u v : Level} (α : ⌜Sort u⌝) (β : ⌜$α → Sort v⌝) : ⌜Sort (imax u v)⌝ :=
  ⌜(a : $α) → $β a⌝

def mkForAll.mkApp {u v : Level} {α : ⌜Sort u⌝} {β : ⌜$α → Sort v⌝} (f : mkForAll α β) (a : α) :
    ⌜$β $a⌝ :=
  ⌜$f $a⌝
