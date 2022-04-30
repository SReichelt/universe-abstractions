import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors



namespace UniverseAbstractions.Layer1

set_option autoBoundImplicitLocal false



class HasTrivialFunctoriality (U : Universe) [HasFunctors U] where
(mkDefFun {A B : U} (f : A → B) : A ⟶{f} B)

namespace HasTrivialFunctoriality

  section

    variable {U : Universe} [HasFunctors U] [h : HasTrivialFunctoriality U]

    def defFun {A B : U} {f : A → B} : A ⟶{f} B := h.mkDefFun f
    def defFun₂ {A B C : U} {f : A → B → C} : A ⟶ B ⟶{f} C := ⟨λ _ => defFun, defFun⟩
    def defFun₃ {A B C D : U} {f : A → B → C → D} : A ⟶ B ⟶ C ⟶{f} D := ⟨λ _ => defFun₂, defFun⟩

  end

  variable (U : Universe) [HasFunctors U] [h : HasTrivialFunctoriality U]

  instance hasFullLogic : HasFullLogic U :=
  { defIdFun      := λ _     => defFun,
    defRevAppFun₂ := λ _ _   => defFun₂,
    defCompFun₃   := λ _ _ _ => defFun₃,
    defConstFun₂  := λ _ _   => defFun₂,
    defDupFun₂    := λ _ _   => defFun₂ }

end HasTrivialFunctoriality
