import UniverseAbstractions.Universes.Layer1.Instances.Utils.Trivial

import UniverseAbstractions.Universes.Layer2.Axioms.Universes
import UniverseAbstractions.Universes.Layer2.Axioms.Functors
import UniverseAbstractions.Universes.Layer2.Axioms.FunctorialImplications



namespace UniverseAbstractions.Layer2

set_option autoImplicit false

open HasFunctors



class HasTrivialExtensionality (U : Universe) [HasFunctors U] where
(mkFunEquiv {A B : U} (F G : A ⟶ B) (hFG : ∀ a, F a ≃ G a) : F ≃{hFG} G)

namespace HasTrivialExtensionality

  variable {U : Universe} [HasFunctors U] [h : HasTrivialExtensionality U]

  def funEquiv {A B : U} {F G : A ⟶ B} {hFG : ∀ a, F a ≃ G a} : F ≃{hFG} G :=
  h.mkFunEquiv F G hFG

  def funEquiv₂ {A B C : U} {F G : A ⟶ B ⟶ C} {hFG : ∀ a b, F a b ≃ G a b} : F ≃≃{hFG} G :=
  ⟨λ _ => funEquiv, funEquiv⟩

  def funEquiv₃ {A B C D : U} {F G : A ⟶ B ⟶ C ⟶ D} {hFG : ∀ a b c, F a b c ≃ G a b c} :
    F ≃≃≃{hFG} G :=
  ⟨λ _ => funEquiv₂, funEquiv⟩

  def funEquiv₄ {A B C D E : U} {F G : A ⟶ B ⟶ C ⟶ D ⟶ E} {hFG : ∀ a b c d, F a b c d ≃ G a b c d} :
    F ≃≃≃≃{hFG} G :=
  ⟨λ _ => funEquiv₃, funEquiv⟩

end HasTrivialExtensionality



class HasTrivialFunctoriality (U : Universe) [HasFunctors U] where
(mkDefFun {A B : U} (f : A → B) (hf : CongrProof f) : A ⟶{f, hf} B)

namespace HasTrivialFunctoriality

  section

    variable {U : Universe} [HasFunctors U] [h : HasTrivialFunctoriality U]

    def defFun {A B : U} {f : A → B} {hf : CongrProof f} : A ⟶{f, hf} B := h.mkDefFun f hf

    variable [HasTrivialExtensionality U] [Layer1.HasTrivialFunctoriality U.V]

    def defFun₂ {A B C : U} {f : A → B → C} {hf : CongrProof₂ f} : A ⟶ B ⟶{f, hf} C :=
    DefFunEx₂.construct (λ _ => defFun)
                        (λ _ => HasTrivialExtensionality.funEquiv)
                        (λ _ _ => Layer1.HasTrivialFunctoriality.defFun)
                        defFun

    def defFun₃ {A B C D : U} {f : A → B → C → D} {hf : CongrProof₃ f} : A ⟶ B ⟶ C ⟶{f, hf} D :=
    DefFunEx₃.construct (λ _ => defFun₂)
                        (λ _ => HasTrivialExtensionality.funEquiv₂)
                        (λ _ _ => Layer1.HasTrivialFunctoriality.defFun)
                        defFun

  end

  variable (U : Universe) [Layer1.HasTrivialFunctoriality U.V] [HasFunctors U]
           [HasTrivialFunctoriality U] [HasTrivialExtensionality U]

  instance hasFullLogic : HasFullLogic U :=
  { defIdFun      := λ _     => defFun,
    defRevAppFun₂ := λ _ _   => defFun₂,
    defCompFun₃   := λ _ _ _ => defFun₃,
    defConstFun₂  := λ _ _   => defFun₂,
    defDupFun₂    := λ _ _   => defFun₂ }

end HasTrivialFunctoriality



class HasTrivialFunctorialImplication (U : Universe) [HasFunctors U] [HasFunctorialImplication U]
                                      where
(mkDefFunImp {A B C : U} (F : A ⟶ B) (G : A ⟶ C) (congr : ∀ a b, F a ≃ F b ⟶ G a ≃ G b) :
   F −≃→{congr} G)

namespace HasTrivialFunctorialImplication

  section

    variable {U : Universe} [HasFunctors U] [HasFunctorialImplication U]
             [h : HasTrivialFunctorialImplication U]

    def defFunImp {A B C : U} {F : A ⟶ B} {G : A ⟶ C} {congr : ∀ a b, F a ≃ F b ⟶ G a ≃ G b} :
      F −≃→{congr} G :=
    h.mkDefFunImp F G congr

  end

  variable (U : Universe) [Layer1.HasTrivialFunctoriality U.V] [HasFunctors U]
           [HasFunctorialImplication U] [HasTrivialFunctorialImplication U]

  instance hasLinearFunImp [HasLinearLogic U] : HasLinearFunImp U :=
  { defEqFunImp           := λ _     => defFunImp,
    defEqFunImpFun        := λ _ _   => Layer1.HasTrivialFunctoriality.defFun,
    defCompFunImp         := λ _ _   => defFunImp,
    defCompFunImpFun₂     := λ _ _ _ => Layer1.HasTrivialFunctoriality.defFun₂,
    defRightCompFunImp    := λ _ _   => defFunImp,
    defLeftCompFunImp     := λ _     => defFunImp,
    defLeftCompFunImpFun  := λ _ _ _ => Layer1.HasTrivialFunctoriality.defFun }

  instance hasAffineFunImp [HasAffineLogic U] : HasAffineFunImp U :=
  { defConstFunImp := λ _ _ => defFunImp }

  instance hasFullFunImp [HasFullLogic U] : HasFullFunImp U :=
  { defRightSubstFunImp    := λ _     => defFunImp,
    defRightSubstFunImpFun := λ _ _   => Layer1.HasTrivialFunctoriality.defFun,
    defLeftSubstFunImp     := λ _ _   => defFunImp,
    defLeftSubstFunImpFun₂ := λ _ _ _ => Layer1.HasTrivialFunctoriality.defFun₂ }

end HasTrivialFunctorialImplication
