import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Axioms.Singletons
import UniverseAbstractions.Universes.Layer1.Axioms.Products
import UniverseAbstractions.Universes.Layer1.Axioms.Coproducts
import UniverseAbstractions.Universes.Layer1.Axioms.Equivalences
import UniverseAbstractions.Universes.Layer1.Instances.Utils.Trivial



namespace UniverseAbstractions.Layer1

set_option autoBoundImplicitLocal false

universe u



def unit : Universe.{0, 0} where
  I := True
  h := ⟨λ _ => True⟩

namespace unit

  def Inst : unit := trivial
  def inst : Inst := trivial

  instance hasInFunctors (U : Universe) : HasFunctors U unit where
    Fun   _ _ := Inst
    apply _ _ := inst

  instance (priority := low) hasOutFunctors (U : Universe) : HasFunctors unit U where
    Fun   _ B := B
    apply b _ := b

  instance hasInnerFunctors : HasInnerFunctors unit := ⟨⟩

  instance hasTrivialInFunctoriality (U : Universe) : HasTrivialFunctoriality U unit :=
    ⟨λ _ => ⟨inst⟩⟩

  instance hasTrivialOutFunctoriality (U : Universe) : HasTrivialFunctoriality unit U :=
    ⟨λ f => ⟨f inst⟩⟩

  instance hasFullLogic (U : Universe) : HasFullLogic U unit := inferInstance
  instance hasFullInnerLogic : HasFullInnerLogic unit := inferInstance

  instance hasTop : HasTop unit where
    T            := Inst
    t            := inst
    defElimFun _ := HasTrivialFunctoriality.defFun

  instance hasBot : HasBot unit where
    B         := Inst
    elimFun _ := inst

  instance hasClassicalLogic : HasClassicalLogic unit := ⟨λ _ => inst⟩

  instance hasProducts (U : Universe) [HasInnerFunctors U] [HasIdFun U] : HasProducts unit U where
    Prod         _ B   := B
    fst          _     := inst
    snd          b     := b
    intro        _ b   := b
    defIntroFun  _ B   := ⟨HasIdFun.idFun B⟩
    defIntroFun₂ _ _   := HasTrivialFunctoriality.defFun
    defElimFun   F     := ⟨F⟩
    defElimFun₂  _ B C := ⟨HasIdFun.appFun₂ B C⟩

  instance hasInnerProducts : HasInnerProducts unit := ⟨⟩

  instance hasCoproducts (U : Universe) : HasCoproducts U unit where
    Coprod        _ _   := Inst
    leftIntroFun  _ _   := inst
    rightIntroFun _ _   := inst
    elimFun₃      _ _ _ := inst

  instance hasInnerCoproducts : HasInnerCoproducts unit := ⟨⟩

  instance hasTrivialIsomorphismCondition : HasTrivialIsomorphismCondition unit := ⟨λ _ _ => ⟨inst⟩⟩

  instance isIsoRelBase {α : Sort u} (Hom Iso : Prerelation α unit) :
      Prerelation.IsIsoRelBase Hom Iso where
    to  := ⟨λ _ _ => inst⟩
    inv := ⟨λ _ _ => inst⟩

  instance hasEquivalences : HasEquivalences unit where
    Equiv _ _ := Inst
    hIso      := HasTrivialIsomorphismCondition.isIsoRel

  instance hasFullEquivalences : HasFullEquivalences unit := inferInstance
  instance hasPropEquivalences : HasPropEquivalences unit := inferInstance
  instance hasClassicalEquivalences : HasClassicalEquivalences unit := inferInstance

  instance isPositiveUniverse : IsPositiveUniverse unit := ⟨⟩
  instance isNegativeUniverse : IsNegativeUniverse unit := ⟨⟩
  instance isStandardUniverse : IsStandardUniverse unit := ⟨⟩

end unit
