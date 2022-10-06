import UniverseAbstractions.Universes.Layer2.Axioms.Universes
import UniverseAbstractions.Universes.Layer2.Axioms.Functors



namespace UniverseAbstractions.Layer2

set_option autoImplicit false
set_option maxHeartbeats 2000000

universe u

open Layer1.HasFunctors Layer1.HasPiAppFun HasPiTypeBase HasFunctors HasExternalLinearLogic

variable {Prp : Universe} [Layer1.HasLinearLogic Prp] [Layer1.HasEquivalences Prp]



namespace HasExternalLinearLogic

  section

    variable (α β : Sort u) [Layer1.HasEquivalenceRelationBase Prp α]
             [Layer1.HasEquivalenceRelationBase Prp β] {U : Universe.{u}} [HasPropositions Prp U]
             [HasLinearLogic U] [HasExternalLinearLogic α U] [HasExternalLinearLogic β U]

    instance hasSwapPi (C : U) : HasSwapPi (Function.const α (Function.const β C)) :=
      ⟨λ F b => DefPi.mk (Layer1.HasExternalLinearLogic.defSwapFun F b)
                         (λ _ => revAppFun.byDef β • compFun.byDef α)⟩

    instance swapFun.hasDefInstEq {C : U} (F : α ⥤ β ⥤ C) (b : β) :
        DefType.HasDefInstEq (Layer1.HasSwapPi.defSwapFun F b) :=
      HasSwapPi.hasDefInstEq (P := Function.const α (Function.const β C)) F b

    compiler_slow def swapFun.byDef {C : U} {F : α ⥤ β ⥤ C} {b : β} {a : α} :
        (Layer1.HasSwapPi.swapFun F b) a ≃ F a b :=
      HasFunctors.byDef

  end

  section

    variable (α : Sort u) [Layer1.HasEquivalenceRelationBase Prp α] {U : Universe.{u}}
             [HasPropositions Prp U] [HasLinearLogic U] [h : HasExternalLinearLogic α U]

    compiler_slow instance compFun₂.hasDefInstEq {B : U} (F : α ⥤ B) (C : U) :
        DefType.HasDefInstEq (Layer1.HasRevCompFunPiFun.defCompFun₂ F C).toDefFun :=
      HasRevCompFunPiFun.compFun₂.hasDefInstEq F C

    compiler_slow def compFun₂.byDef {B C : U} {F : α ⥤ B} {G : B ⥤ C} :
        (Layer1.HasRevCompFunPiFun.compFun₂ F C) G ≃ G ⊙ F :=
      HasFunctors.byDef

    compiler_slow def compFun₂.byDef₂ {B C : U} {F : α ⥤ B} {G : B ⥤ C} {a : α} :
        (Layer1.HasRevCompFunPiFun.compFun₂ F C) G a ≃ G (F a) :=
      HasFunctors.byDef₂ (F := Layer1.HasRevCompFunPiFun.defCompFun₂ F C)
                         (hFa := compFun.hasDefInstEq α F) (hF := compFun₂.hasDefInstEq α F C)

  end

  section

    variable (α β : Sort u) [Layer1.HasEquivalenceRelationBase Prp α]
             [Layer1.HasEquivalenceRelationBase Prp β] {U : Universe.{u}} [HasPropositions Prp U]
             [HasLinearLogic U] [HasExternalLinearLogic α U] [HasExternalLinearLogic β U]

    compiler_slow instance hasSwapPi₂ (C : U) : HasSwapPi₂ (Function.const α (Function.const β C)) :=
      ⟨λ F => DefPi.mk (Layer1.HasExternalLinearLogic.defSwapFun₂ F)
                       (λ _ => compFun₂.byDef α • congrArg (Layer1.HasRevCompFunPiFun.compFun₂ F C) (revAppFun₂.byDef β) • compFun.byDef β)⟩

    compiler_slow instance swapFun₂.hasDefInstEq {C : U} (F : α ⥤ β ⥤ C) :
        DefType.HasDefInstEq (Layer1.HasSwapPi₂.defSwapFun₂ F).toDefFun :=
      HasSwapPi₂.hasDefInstEq (P := Function.const α (Function.const β C)) F

    compiler_slow def swapFun₂.byDef {C : U} {F : α ⥤ β ⥤ C} {b : β} :
        (Layer1.HasSwapPi₂.swapFun₂ F) b ≃ Layer1.HasSwapPi.swapFun F b :=
      HasFunctors.byDef

    compiler_slow def swapFun₂.byDef₂ {C : U} {F : α ⥤ β ⥤ C} {b : β} {a : α} :
        (Layer1.HasSwapPi₂.swapFun₂ F) b a ≃ F a b :=
      HasFunctors.byDef₂ (F := Layer1.HasSwapPi₂.defSwapFun₂ F)
                         (hFa := swapFun.hasDefInstEq α β F) (hF := swapFun₂.hasDefInstEq α β F)

  end

  section

    variable (α : Sort u) [Layer1.HasEquivalenceRelationBase Prp α] {U : Universe.{u}}
             [HasPropositions Prp U] [HasLinearLogic U] [h : HasExternalLinearLogic α U]

    compiler_slow instance compFun₃.hasDefInstEq (B C : U) :
        DefType.HasDefInstEq (Layer1.HasRevCompFunPiFun.defCompFun₃ α B C).toDefFun :=
      HasRevCompFunPiFun.compFun₃.hasDefInstEq α B C

    compiler_slow def compFun₃.byDef {B C : U} {F : α ⥤ B} :
        (Layer1.HasRevCompFunPiFun.compFun₃ α B C) F ≃ Layer1.HasRevCompFunPiFun.compFun₂ F C :=
      HasFunctors.byDef

    compiler_slow def compFun₃.byDef₂ {B C : U} {F : α ⥤ B} {G : B ⥤ C} :
        (Layer1.HasRevCompFunPiFun.compFun₃ α B C) F G ≃ G ⊙ F :=
      HasFunctors.byDef₂ (α := α ⥤ B) (β := B ⥤ C) (Y := α ⥤ C)
                         (F := (Layer1.HasRevCompFunPiFun.defCompFun₃ α B C).toDefFun₂)
                         (hFa := λ F => compFun₂.hasDefInstEq α F C)
                         (hF := compFun₃.hasDefInstEq α B C)

    compiler_slow def compFun₃.byDef₃ {B C : U} {F : α ⥤ B} {G : B ⥤ C} {a : α} :
        (Layer1.HasRevCompFunPiFun.compFun₃ α B C) F G a ≃ G (F a) :=
      HasFunctors.byDef₃ (F := Layer1.HasRevCompFunPiFun.defCompFun₃ α B C)
                         (hFab := compFun.hasDefInstEq α)
                         (hFa := λ F => compFun₂.hasDefInstEq α F C)
                         (hF := compFun₃.hasDefInstEq α B C)

  end

end HasExternalLinearLogic


-- TODO non-linear logic
