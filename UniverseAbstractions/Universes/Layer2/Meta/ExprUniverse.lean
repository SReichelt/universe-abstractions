import UniverseAbstractions.Universes.Layer2.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Meta.ExprUniverse
import UniverseAbstractions.Universes.Layer1.Meta.OptionalExprUniverse



namespace UniverseAbstractions.Layer2.Meta

set_option autoBoundImplicitLocal false

open Lean Layer1 Layer1.Meta



def exprUniverse {β γ : Type} (inst : β → _Sort) (eqInst : γ → _Sort)
                 [HasFunctors (Layer1.Meta.exprUniverse eqInst)]
                 (hasEq : ∀ A, HasEquivalenceRelation (inst A).α (Layer1.Meta.exprUniverse eqInst)) :
  Universe.{1, 1, 1, 1} :=
{ toUniverse := Layer1.Meta.exprUniverse inst,
  V          := Layer1.Meta.optionalExprUniverse eqInst,
  hasFun     := inferInstance,
  hasLin     := inferInstance,
  hasEq      := λ A => ⟨optionalRelation (hasEq A).R⟩ }
