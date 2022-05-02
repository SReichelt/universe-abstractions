import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Axioms.Singletons
import UniverseAbstractions.Universes.Layer1.Axioms.Products
import UniverseAbstractions.Universes.Layer1.Axioms.Coproducts
import UniverseAbstractions.Universes.Layer1.Axioms.Equivalences
import UniverseAbstractions.Universes.Layer1.Instances.Utils.Trivial



namespace UniverseAbstractions.Layer1

set_option autoBoundImplicitLocal false



-- A universe with exactly two types `true` and `false`. The function that maps a type to its
-- instances is exactly the same as the coercion from `Bool` to `Prop`. `bool` can be regarded as a
-- subuniverse of `prop` that is restricted to all decidable propositions.

def bool : Universe.{0, 1} :=
{ I := Bool,
  h := ⟨λ b => cond b True False⟩ }

namespace bool

  def T : bool := true
  def F : bool := false

  def inst : T := trivial
  def elim {α : Sort _} (h : F) : α := False.elim h

  instance decidable (b : bool) : Decidable ⌈b⌉ := match b with
  | true  => isTrue  inst
  | false => isFalse elim

  instance hasFunctors : HasFunctors bool :=
  { Fun   := λ b c => cond b c true,
    apply := λ {b c} f a => match b with
                            | true  => f
                            | false => elim a }

  instance hasTrivialFunctoriality : HasTrivialFunctoriality bool :=
  ⟨λ {b c} f => ⟨match b with
                 | true  => f inst
                 | false => inst⟩⟩

  instance hasFullLogic : HasFullLogic bool := inferInstance

  instance hasTop : HasTop bool :=
  { T          := true,
    t          := inst,
    defElimFun := λ _ => HasTrivialFunctoriality.defFun }

  instance hasBot : HasBot bool :=
  { B       := false,
    elimFun := λ b => inst }

  instance hasClassicalLogic : HasClassicalLogic bool :=
  ⟨λ b => match b with
          | true  => inst
          | false => inst⟩

  instance hasProducts : HasProducts bool :=
  { Prod      := and,
    introFun₂ := λ b c => match b, c with
                          | true,  true  => inst
                          | true,  false => inst
                          | false, _     => inst,
    elimFun₂  := λ b c d => match b, c, d with
                            | true,  true,  true  => inst
                            | true,  true,  false => inst
                            | true,  false, _     => inst
                            | false, _,     _     => inst }

  instance hasCoproducts : HasCoproducts bool :=
  { Coprod        := or,
    leftIntroFun  := λ b c => match b with
                              | true  => inst
                              | false => inst,
    rightIntroFun := λ b c => match b, c with
                              | true,  true  => inst
                              | false, true  => inst
                              | _,     false => inst,
    elimFun₃      := λ b c d => match b, c, d with
                                | true,  true,  true  => inst
                                | true,  true,  false => inst
                                | true,  false, true  => inst
                                | true,  false, false => inst
                                | false, true,  true  => inst
                                | false, true,  false => inst
                                | false, false, _     => inst }

  instance hasEquivalences : HasEquivalences bool :=
  { Equiv   := λ b c => match b, c with
                        | true,  true  => true
                        | false, false => true
                        | _,     _     => false,
    toFun₂  := λ b c => match b, c with
                        | true,  true  => inst
                        | true,  false => inst
                        | false, true  => inst
                        | false, false => inst,
    invFun₂ := λ b c => match b, c with
                        | true,  true  => inst
                        | true,  false => inst
                        | false, true  => inst
                        | false, false => inst }

  instance hasTrivialEquivalenceCondition : HasTrivialEquivalenceCondition bool :=
  ⟨λ {b c} to inv => ⟨match b, c with
                      | true,  true  => inst
                      | true,  false => elim to
                      | false, true  => elim inv
                      | false, false => inst⟩⟩

  instance hasEquivOp : HasEquivOp bool := inferInstance

end bool
