import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Meta.ExprUniverse



namespace UniverseAbstractions.Layer1.Meta

set_option autoBoundImplicitLocal false

open Lean



def _sort := exprUniverse id

namespace _sort

  def mkFun {u v : Level} (α : ⌜Sort u⌝) (β : ⌜Sort v⌝) : ⌜Sort (imax u v)⌝ := ⌜$α → $β⌝
  def mkApp {u v : Level} {α : ⌜Sort u⌝} {β : ⌜Sort v⌝} (f : mkFun α β) (a : α) : β := ⌜$f $a⌝

  instance hasFunctors : HasFunctors _sort :=
  { Fun   := λ A B => ⟨mkFun A.α B.α⟩,
    apply := λ {A B} (f : mkFun A.α B.α) (a : A.α) => mkApp f a }

  -- When using this, make sure that `f` is defeq to what `f'` specifies.
  def defFun {A B : _sort} {f' : A → B} (f : mkFun A.α B.α) : A ⟶{f'} B := ⟨f⟩

  def defFun₂ {A B C : _sort} {f' : A → B → C} (f : mkFun A.α (mkFun B.α C.α)) : A ⟶ B ⟶{f'} C :=
  ⟨λ a => defFun (mkApp f a), defFun f⟩

  def defFun₃ {A B C D : _sort} {f' : A → B → C → D} (f : mkFun A.α (mkFun B.α (mkFun C.α D.α))) :
    A ⟶ B ⟶ C ⟶{f'} D :=
  ⟨λ a => defFun₂ (mkApp f a), defFun f⟩

  instance hasFullLogic : HasFullLogic _sort :=
  { defIdFun      := λ _     => defFun  ⌜id⌝,
    defRevAppFun₂ := λ _ _   => defFun₂ ⌜λ a f => f a⌝,
    defCompFun₃   := λ _ _ _ => defFun₃ ⌜λ f g => g ∘ f⌝,
    defConstFun₂  := λ _ _   => defFun₂ ⌜Function.const _⌝,
    defDupFun₂    := λ _ _   => defFun₂ ⌜λ f a => f a a⌝ }

end _sort
