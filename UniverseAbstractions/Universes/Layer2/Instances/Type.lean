import UniverseAbstractions.Universes.Layer1.Instances.Prop

import UniverseAbstractions.Universes.Layer2.Axioms.Universes
import UniverseAbstractions.Universes.Layer2.Axioms.Functors
import UniverseAbstractions.Universes.Layer2.Axioms.FunctorialImplications
import UniverseAbstractions.Universes.Layer2.Instances.Utils.Trivial



namespace UniverseAbstractions.Layer2

set_option autoBoundImplicitLocal false

universe u



def type : Universe.{u + 1, u + 2, 0, 1} :=
{ toUniverse := ⟨Type u⟩,
  V          := Layer1.prop,
  hV         := inferInstance,
  hasEq      := λ α => ⟨@Eq α⟩ }

namespace type

  instance : Layer1.HasTrivialFunctoriality type.{u}.V := Layer1.prop.hasTrivialFunctoriality

  instance hasFunctors : HasFunctors type.{u} :=
  { Fun         := λ α β => α → β,
    apply       := id,
    congrArgFun := λ f a b e => congrArg f e,
    congrFunFun := λ f g a e => congrFun e a }

  instance hasTrivialExtensionality : HasTrivialExtensionality type.{u} :=
  ⟨λ f g hfg => ⟨funext hfg⟩⟩

  instance hasTrivialFunctoriality : HasTrivialFunctoriality type.{u} :=
  ⟨λ f hf => ⟨⟨f⟩, ⟨λ _ => rfl⟩⟩⟩

  instance hasFullLogic : HasFullLogic type.{u} := inferInstance

--  instance hasFunctorialImplication : HasFunctorialImplication type.{u} :=
--  { FunImp   := λ f g => ∀ a b, f a = f b → g a = g b,
--    elimFun₂ := λ f g a b i => i a b }
--
--  instance hasTrivialFunctorialImplication : HasTrivialFunctorialImplication type.{u} :=
--  ⟨λ f g i => ⟨i⟩⟩
--
--  instance hasFullFunImp : HasFullFunImp type.{u} := inferInstance

end type
