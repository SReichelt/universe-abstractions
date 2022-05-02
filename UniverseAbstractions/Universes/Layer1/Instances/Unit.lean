import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Axioms.Singletons
import UniverseAbstractions.Universes.Layer1.Axioms.Products
import UniverseAbstractions.Universes.Layer1.Axioms.Coproducts
import UniverseAbstractions.Universes.Layer1.Axioms.Equivalences
import UniverseAbstractions.Universes.Layer1.Instances.Utils.Trivial



namespace UniverseAbstractions.Layer1

set_option autoBoundImplicitLocal false



def unit : Universe.{0, 0} :=
{ I := True,
  h := ⟨λ _ => True⟩ }

namespace unit

  def Inst : unit := trivial
  def inst : Inst := trivial

  instance hasFunctors : HasFunctors unit :=
  { Fun   := λ _ _ => Inst,
    apply := λ _ _ => inst }

  instance hasTrivialFunctoriality : HasTrivialFunctoriality unit := ⟨λ _ => ⟨inst⟩⟩

  instance hasFullLogic : HasFullLogic unit := inferInstance

  instance hasTop : HasTop unit :=
  { T          := Inst,
    t          := inst,
    defElimFun := λ _ => HasTrivialFunctoriality.defFun }

  instance hasBot : HasBot unit :=
  { B       := Inst,
    elimFun := λ _ => inst }

  instance hasClassicalLogic : HasClassicalLogic unit := ⟨λ _ => inst⟩

  instance hasProducts : HasProducts unit :=
  { Prod      := λ _ _   => Inst,
    introFun₂ := λ _ _   => inst,
    elimFun₂  := λ _ _ _ => inst }

  instance hasCoproducts : HasCoproducts unit :=
  { Coprod        := λ _ _   => Inst,
    leftIntroFun  := λ _ _   => inst,
    rightIntroFun := λ _ _   => inst,
    elimFun₃      := λ _ _ _ => inst }

  instance hasEquivalences : HasEquivalences unit :=
  { Equiv   := λ _ _ => Inst,
    toFun₂  := λ _ _ => inst,
    invFun₂ := λ _ _ => inst }

  instance hasTrivialEquivalenceCondition : HasTrivialEquivalenceCondition unit := ⟨λ _ _ => ⟨inst⟩⟩

  instance hasEquivOp : HasEquivOp unit := inferInstance

end unit
