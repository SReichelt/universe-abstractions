import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Axioms.Equivalences
import UniverseAbstractions.Universes.Layer1.Axioms.StandardEquivalences



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

  variable (U : Universe) [HasFunctors U] [HasTrivialFunctoriality U]

  instance hasFullLogic : HasFullLogic U :=
  { defIdFun      := λ _     => defFun,
    defRevAppFun₂ := λ _ _   => defFun₂,
    defCompFun₃   := λ _ _ _ => defFun₃,
    defConstFun₂  := λ _ _   => defFun₂,
    defDupFun₂    := λ _ _   => defFun₂ }

end HasTrivialFunctoriality



class HasTrivialEquivalenceCondition (U : Universe) [HasFunctors U] [HasEquivalences U] where
(mkDefEquiv {A B : U} (toFun : A ⟶ B) (invFun : B ⟶ A) : A ⟷{toFun, invFun} B)

namespace HasTrivialEquivalenceCondition

  section

    variable {U : Universe} [HasFunctors U] [HasEquivalences U]
             [h : HasTrivialEquivalenceCondition U]

    def defEquiv {A B : U} {toFun : A ⟶ B} {invFun : B ⟶ A} : A ⟷{toFun, invFun} B :=
    h.mkDefEquiv toFun invFun

  end

  variable (U : Universe) [HasFunctors U] [HasEquivalences U] [HasTrivialFunctoriality U]
           [HasTrivialEquivalenceCondition U]

  instance hasEquivOp : HasEquivOp U :=
  { defRefl      := λ _     => defEquiv,
    defSymm      := λ _     => defEquiv,
    defSymmFun   := λ _ _   => HasTrivialFunctoriality.defFun,
    defTrans     := λ _ _   => defEquiv,
    defTransFun₂ := λ _ _ _ => HasTrivialFunctoriality.defFun₂ }

  def defTypeFun {φ : U → U} {hφ : HasEquivOp.TypeFunProof φ} : HasEquivOp.DefTypeFun φ hφ :=
  { defEquiv    := λ _   => defEquiv,
    defEquivFun := λ _ _ => HasTrivialFunctoriality.defFun }

  def defTypeFun₂ {φ : U → U → U} {hφ : HasEquivOp.TypeFunProof₂ φ} : HasEquivOp.DefTypeFun₂ φ hφ :=
  { app  := λ _ => defTypeFun U,
    app₂ := λ _ => defTypeFun U }

  instance hasFunctorEquivalences : HasFunctorEquivalences U :=
  { defFunTypeFun₂  := defTypeFun₂ U,
    defSwapFunEquiv := λ _ _ _ => defEquiv }

  instance hasTopEquivalences [HasTop U] : HasTopEquivalences U :=
  { defTopElimEquiv := λ _ => defEquiv }

  instance hasBotEquivalences [HasBot U] : HasBotEquivalences U :=
  { defBotIntroEquiv    := λ _ => defEquiv,
    defBotIntroEquivFun := λ _ => HasTrivialFunctoriality.defFun,
    defBotIntroEquiv₂   := λ _ => defEquiv }

  instance hasProductEquivalences [HasProducts U] : HasProductEquivalences U :=
  { defProdTypeFun₂   := defTypeFun₂ U,
    defProdElimEquiv  := λ _ _ _ => defEquiv,
    defProdCommEquiv  := λ _ _   => defEquiv,
    defProdAssocEquiv := λ _ _ _ => defEquiv }

  instance hasProductDistrEquivalences [HasProducts U] : HasProductDistrEquivalences U :=
  { defProdDistrEquiv := λ _ _ _ => defEquiv }

  instance hasProductTopEquivalences [HasTop U] [HasProducts U] : HasProductTopEquivalences U :=
  { defProdTopEquiv := λ _ => defEquiv }

  instance hasProductBotEquivalences [HasBot U] [HasProducts U] : HasProductBotEquivalences U :=
  { defProdBotEquiv := λ _ => defEquiv }

  instance hasCoproductEquivalences [HasCoproducts U] : HasCoproductEquivalences U :=
  { defCoprodTypeFun₂   := defTypeFun₂ U,
    defCoprodCommEquiv  := λ _ _   => defEquiv,
    defCoprodAssocEquiv := λ _ _ _ => defEquiv }

  instance hasCoproductDistrEquivalences [HasProducts U] [HasCoproducts U] :
    HasCoproductDistrEquivalences U :=
  { defCoprodDistrEquiv := λ _ _ _ => defEquiv }

  instance hasCoproductBotEquivalences [HasBot U] [HasCoproducts U] :
    HasCoproductBotEquivalences U :=
  { defCoprodBotEquiv := λ _ => defEquiv }

  instance hasEquivalenceEquivalences : HasEquivalenceEquivalences U :=
  { defEquivTypeFun₂  := defTypeFun₂ U,
    defEquivSymmEquiv := λ _ _ => defEquiv }

  instance hasLinearEquivalences [HasTop U] [HasBot U] [HasProducts U] [HasCoproducts U] :
    HasLinearEquivalences U :=
  ⟨⟩

  instance hasFullEquivalences [HasTop U] [HasBot U] [HasProducts U] [HasCoproducts U] :
    HasFullEquivalences U :=
  ⟨⟩

  instance hasPropEquivalences [HasTop U] [HasProducts U] [HasCoproducts U] :
    HasPropEquivalences U :=
  { defDupFunEquiv    := λ _ _ => defEquiv,
    defDupProdEquiv   := λ _   => defEquiv,
    defDupCoprodEquiv := λ _   => defEquiv,
    defTopEquiv       := λ _   => defEquiv,
    defTopEquivFun    := λ _   => HasTrivialFunctoriality.defFun,
    defTopEquivEquiv  := λ _   => defEquiv }

  instance hasClassicalEquivalences [HasBot U] [HasClassicalLogic U] : HasClassicalEquivalences U :=
  { defNotNotEquiv := λ _ => defEquiv }

end HasTrivialEquivalenceCondition
