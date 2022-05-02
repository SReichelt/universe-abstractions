import UniverseAbstractions.Universes.Layer1.Instances.Unit
import UniverseAbstractions.Universes.Layer1.Instances.Prop
import UniverseAbstractions.Universes.Layer1.Instances.Bool

import UniverseAbstractions.Universes.Layer2.Axioms.Universes
import UniverseAbstractions.Universes.Layer2.Axioms.Functors
import UniverseAbstractions.Universes.Layer2.Axioms.FunctorialImplications
import UniverseAbstractions.Universes.Layer2.Instances.Utils.Trivial



namespace UniverseAbstractions.Layer2

set_option autoBoundImplicitLocal false

universe u uu



def unitEqUniverse (U : Layer1.Universe.{u, uu}) : Universe.{u, uu, 0, 0} :=
{ toUniverse := U,
  V          := Layer1.unit,
  hasFun     := inferInstance,
  hasLin     := inferInstance,
  hasEq      := λ A => ⟨Layer1.Prerelation.topRelation A Layer1.unit⟩ }

namespace unitEqUniverse

  variable (U : Layer1.Universe)

  instance : Layer1.HasTrivialFunctoriality (unitEqUniverse U).V :=
  Layer1.unit.hasTrivialFunctoriality

  variable [hFun : Layer1.HasFunctors U]

  instance hasFunctors : HasFunctors (unitEqUniverse U) :=
  { toHasFunctors := hFun,
    congrArgFun   := λ _ _ _ => Layer1.unit.inst,
    congrFunFun   := λ _ _ _ => Layer1.unit.inst }

  instance hasTrivialExtensionality : HasTrivialExtensionality (unitEqUniverse U) :=
  ⟨λ _ _ _ => ⟨Layer1.unit.inst⟩⟩

  def defFunEq {A B : unitEqUniverse U} {f : A → B} {F : A ⟶{f} B} : HasFunctors.DefFun.DefEq F :=
  ⟨λ _ => Layer1.unit.inst⟩

  def defFunEq₂ {A B C : unitEqUniverse U} {f : A → B → C} {F : A ⟶ B ⟶{f} C} :
    HasFunctors.DefFun₂.DefEq F :=
  ⟨λ _ => defFunEq U, defFunEq U⟩

  def defFunEq₃ {A B C D : unitEqUniverse U} {f : A → B → C → D} {F : A ⟶ B ⟶ C ⟶{f} D} :
    HasFunctors.DefFun₃.DefEq F :=
  ⟨λ _ => defFunEq₂ U, defFunEq U⟩

  instance hasLinearLogic [h : Layer1.HasLinearLogic U] : HasLinearLogic (unitEqUniverse U) :=
  { defIdFun      := λ A     => ⟨h.defIdFun A,        defFunEq  U⟩,
    defRevAppFun₂ := λ A B   => ⟨h.defRevAppFun₂ A B, defFunEq₂ U⟩,
    defCompFun₃   := λ A B C => ⟨h.defCompFun₃ A B C, defFunEq₃ U⟩ }

  instance hasAffineLogic [h : Layer1.HasAffineLogic U] : HasAffineLogic (unitEqUniverse U) :=
  { defConstFun₂ := λ A B => ⟨h.defConstFun₂ A B, defFunEq₂ U⟩ }

  instance hasFullLogic [h : Layer1.HasFullLogic U] : HasFullLogic (unitEqUniverse U) :=
  { defDupFun₂ := λ A B => ⟨h.defDupFun₂ A B, defFunEq₂ U⟩ }

  instance hasFunctorialImplication : HasFunctorialImplication (unitEqUniverse U) :=
  { FunImp   := λ f g => Layer1.unit.Inst,
    elimFun₂ := λ f g a b => Layer1.unit.inst }

  instance hasTrivialFunctorialImplication : HasTrivialFunctorialImplication (unitEqUniverse U) :=
  ⟨λ f g i => ⟨Layer1.unit.inst⟩⟩

  instance hasLinearFunImp [Layer1.HasLinearLogic U] : HasLinearFunImp (unitEqUniverse U) := inferInstance
  instance hasAffineFunImp [Layer1.HasAffineLogic U] : HasAffineFunImp (unitEqUniverse U) := inferInstance
  instance hasFullFunImp   [Layer1.HasFullLogic   U] : HasFullFunImp   (unitEqUniverse U) := inferInstance

end unitEqUniverse



def unit : Universe.{0, 0, 0, 0} := unitEqUniverse Layer1.unit
def prop : Universe.{0, 1, 0, 0} := unitEqUniverse Layer1.prop
def bool : Universe.{0, 1, 0, 0} := unitEqUniverse Layer1.bool
