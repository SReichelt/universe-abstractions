import UniverseAbstractions.Universes.Layer1.Instances.Utils.Bundled
import UniverseAbstractions.Universes.Layer1.Instances.Prop

import UniverseAbstractions.Universes.Layer2.Axioms.Universes
import UniverseAbstractions.Universes.Layer2.Axioms.Functors
import UniverseAbstractions.Universes.Layer2.Axioms.FunctorialImplications
import UniverseAbstractions.Universes.Layer2.Instances.Utils.Trivial



namespace UniverseAbstractions.Layer2

set_option autoBoundImplicitLocal false

universe u



@[reducible] def layer1Setoid : Layer1.Universe.{u + 1, u + 2} :=
Layer1.Bundled.univ.{u + 1, u + 1, 0} Setoid

namespace layer1Setoid

  instance (A : layer1Setoid.{u}) : Setoid A := A.h
  instance hasEq (A : layer1Setoid.{u}) : Layer1.HasEquivalenceRelation A Layer1.prop := ⟨A.h.r⟩

end layer1Setoid

def setoid : Universe.{u + 1, u + 2, 0, 1} :=
{ toUniverse := layer1Setoid,
  V          := Layer1.prop,
  hV         := inferInstance,
  hasEq      := layer1Setoid.hasEq }

namespace setoid

  instance (A : setoid.{u}) : Setoid A.α := A.h
  instance (A : setoid.{u}) : Setoid A := A.h

  instance : Layer1.HasTrivialFunctoriality setoid.{u}.V := Layer1.prop.hasTrivialFunctoriality

  class IsFunctor {A B : setoid.{u}} (f : A → B) : Prop where
  (congrArg {a b : A} : a ≈ b → f a ≈ f b)

  instance hasFunctorInstances : Layer1.Bundled.HasFunctorInstances Setoid :=
  { IsFun   := IsFunctor,
    funInst := λ A B => { r     := λ F G => ∀ a, F.f a ≈ G.f a,
                          iseqv := { refl  := λ F   a => Setoid.refl  (F.f a),
                                     symm  := λ e   a => Setoid.symm  (e a),
                                     trans := λ e f a => Setoid.trans (e a) (f a) } } }

  instance hasFunctors : HasFunctors setoid.{u} :=
  { toHasFunctors := Layer1.Bundled.hasFunctors Setoid,
    congrArgFun   := λ F a b e => F.isFun.congrArg e,
    congrFunFun   := λ F G a e => e a }

  instance hasTrivialExtensionality : HasTrivialExtensionality setoid.{u} :=
  ⟨λ f g hfg => ⟨hfg⟩⟩

  instance hasTrivialFunctoriality : HasTrivialFunctoriality setoid.{u} :=
  ⟨λ f hf => ⟨Layer1.Bundled.mkDefFun Setoid ⟨λ {a b} => hf.congr a b⟩, ⟨λ a => Setoid.refl (f a)⟩⟩⟩

  instance hasFullLogic : HasFullLogic setoid.{u} := inferInstance

--  instance hasFunctorialImplication : HasFunctorialImplication setoid.{u} :=
--  { FunImp   := λ {A B C} f g => let _ : Setoid B := inferInstance;
--                                 let _ : Setoid C := inferInstance;
--                                 ∀ a b, f a ≈ f b → g a ≈ g b,
--    elimFun₂ := λ f g a b i => i a b }
--
--  instance hasTrivialFunctorialImplication : HasTrivialFunctorialImplication setoid.{u} :=
--  ⟨λ f g i => ⟨i⟩⟩
--
--  instance hasFullFunImp : HasFullFunImp setoid.{u} := inferInstance

end setoid
