import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations
import UniverseAbstractions.Universes.Layer1.Axioms.Equivalences
import UniverseAbstractions.Universes.Layer1.Axioms.StandardEquivalences



namespace UniverseAbstractions.Layer1

set_option autoImplicit false

universe u u' u''

open Prerelation HasEquivalences



class HasTrivialFunctoriality (U V : Universe) [HasFunctors U V] where
  mkDefFun {A : U} {B : V} (f : A → B) : A ⟶{f} B

namespace HasTrivialFunctoriality

  section

    variable {U V : Universe} [HasFunctors U V] [h : HasTrivialFunctoriality U V]

    def defFun {A : U} {B : V} {f : A → B} : A ⟶{f} B := h.mkDefFun f
    def defFun₂ {A B : U} {C : V} {f : A → B → C} : A ⟶ B ⟶{f} C := ⟨λ _ => defFun, defFun⟩
    def defFun₃ {A B C : U} {D : V} {f : A → B → C → D} : A ⟶ B ⟶ C ⟶{f} D := ⟨λ _ => defFun₂, defFun⟩

  end

  instance hasIdFun (U : Universe) [HasFunctors U U] [HasTrivialFunctoriality U U] : HasIdFun U :=
    ⟨λ _ => defFun⟩

  instance hasRevAppFun (U V : Universe) [HasFunctors U V] [HasFunctors V V]
                        [HasTrivialFunctoriality V V] :
      HasRevAppFun U V :=
    ⟨λ _ _ => defFun⟩

  instance hasConstFun (U V : Universe) [HasFunctors U V] [HasTrivialFunctoriality U V] :
      HasConstFun U V :=
    ⟨λ _ {_} _ => defFun⟩

  instance hasSwapFun (U V W : Universe) [HasFunctors V W] [HasFunctors U W]
                      [HasTrivialFunctoriality U W] :
      HasSwapFun U V W :=
    ⟨λ _ _ => defFun⟩

  instance hasSwapFun₂ (U V W : Universe) [HasFunctors V W] [HasFunctors U W]
                       [HasTrivialFunctoriality U W] [HasTrivialFunctoriality V W] :
      HasSwapFun₂ U V W :=
    ⟨λ _ => defFun⟩

  instance hasCompFun (U V W : Universe) [HasFunctors U V] [HasFunctors V W] [HasFunctors U W]
                      [HasTrivialFunctoriality U W] :
      HasCompFun U V W :=
    ⟨λ _ _ => defFun⟩

  instance hasRevCompFun₂ (U V W : Universe) [HasFunctors U V] [HasFunctors V W] [HasFunctors U W]
                          [HasTrivialFunctoriality U W] [HasTrivialFunctoriality V W] :
      HasRevCompFun₂ U V W :=
    ⟨λ _ {_ _} _ => defFun⟩

  instance hasDupFun (U V : Universe) [HasFunctors U V] [HasTrivialFunctoriality U V] :
      HasDupFun U V :=
    ⟨λ _ => defFun⟩

  instance hasRevSelfAppFun (U V : Universe) [HasFunctors U V] [HasFunctors V U] [HasFunctors V V]
                            [HasTrivialFunctoriality V V] :
      HasRevSelfAppFun U V :=
    ⟨λ _ => defFun⟩

  instance hasSubstFun (U V W : Universe) [HasFunctors U V] [HasFunctors V W] [HasFunctors U W]
                       [HasTrivialFunctoriality U W] :
      HasSubstFun U V W :=
    ⟨λ _ _ => defFun⟩

  instance hasRevSubstFun₂ (U V W : Universe) [HasFunctors U V] [HasFunctors V W] [HasFunctors U W]
                           [HasTrivialFunctoriality U W] [HasTrivialFunctoriality V W] :
      HasRevSubstFun₂ U V W :=
    ⟨λ _ {_ _} _ => defFun⟩

  instance hasFullLogic (U V : Universe) [HasFunctors U V] [HasInnerFunctors V]
                        [HasTrivialFunctoriality U V] [HasTrivialFunctoriality V V] :
      HasFullLogic U V where
    defRevAppFun₂  _ _   := defFun
    defRevCompFun₃ _ _ _ := defFun₂
    defConstFun₂   _ _   := defFun
    defDupFun₂     _ _   := defFun

  instance hasFullInnerLogic (U : Universe) [HasInnerFunctors U] [HasTrivialFunctoriality U U] :
      HasFullInnerLogic U := ⟨⟩

end HasTrivialFunctoriality



class HasTrivialIsomorphismCondition (V : Universe) [HasInnerFunctors V] where
  mkDefIso {α : Sort u} {Hom Iso : Prerelation α V} {a b : α} (toHom : Hom a b) (invHom : Hom b a) :
    DefIsoInst Hom Iso toHom invHom

namespace HasTrivialIsomorphismCondition

  section

    variable {V : Universe} [HasInnerFunctors V] [h : HasTrivialIsomorphismCondition V]

    def defIso {α : Sort u} {Hom Iso : Prerelation α V} {a b : α} {toHom : Hom a b}
               {invHom : Hom b a} :
        DefIsoInst Hom Iso toHom invHom :=
      h.mkDefIso toHom invHom

  end

  section

    variable {α : Sort u} {V : Universe} [HasInnerFunctors V] [HasTrivialFunctoriality V V]
             [HasTrivialIsomorphismCondition V]

    instance isIsoRel {Hom Iso : Prerelation α V} [IsPreorder Hom] [hBase : IsIsoRelBase Hom Iso] :
        IsIsoRel Hom Iso where
      defRefl         _     := defIso
      defSymm         _     := defIso
      defSymmFun      _ _   := HasTrivialFunctoriality.defFun
      defTrans        _ _   := defIso
      defRevTransFun₂ _ _ _ := HasTrivialFunctoriality.defFun₂

  end

  section

    variable {α : Sort u} {β : Sort u'} {V W : Universe} [HasInnerFunctors V] [HasInnerFunctors W]
             [HasFunctors V W] [HasTrivialFunctoriality V W] [HasTrivialIsomorphismCondition W]
             {R : Prerelation α V} {S : Prerelation β W} [IsEquivalence R] [IsPreorder S]
             {SIso : Prerelation β W} [hS : IsIsoRel S SIso] {φ : α → β}

    instance isIsoFunctor {F : Prerelation.Functor R S φ} : IsIsoRel.IsIsoFunctor SIso F where
      defIsoCongrArg    _   := defIso
      defIsoCongrArgFun _ _ := HasTrivialFunctoriality.defFun

  end

  section

    variable {α : Sort u} {β : Sort u'} {γ : Sort u''} {V W X : Universe} [HasInnerFunctors V]
             [HasInnerFunctors W] [HasInnerFunctors X] [HasFunctors W X] [HasFunctors V X]
             [HasTrivialFunctoriality W X] [HasTrivialFunctoriality V X]
             [HasTrivialIsomorphismCondition X] {R : Prerelation α V} {S : Prerelation β W}
             {T : Prerelation γ X} [IsEquivalence R] [IsEquivalence S] [IsPreorder T]
             {TIso : Prerelation γ X} [hT : IsIsoRel T TIso] {φ : α → β → γ}

    instance isIsoFunctor₂ {F : Functor₂ R S T φ} : IsIsoRel.IsIsoFunctor₂ TIso F where
      app  _ := isIsoFunctor
      app₂ _ := isIsoFunctor

  end

  section

    variable {U V : Universe} [HasFunctors U V] [HasInnerFunctors U] [HasLinearInnerLogic U]
             [HasEquivalences U] [HasInnerFunctors V] [HasLinearInnerLogic V] [HasEquivalences V]
             [HasTrivialFunctoriality U V] [HasTrivialIsomorphismCondition V]

    instance isTypeCtor {φ : U → V} {Φ : TypeCtorFun φ} : IsTypeCtor Φ := ⟨⟩

  end

  section

    variable {U V W : Universe} [HasFunctors V W] [HasFunctors U W] [HasInnerFunctors U]
             [HasLinearInnerLogic U] [HasEquivalences U] [HasInnerFunctors V]
             [HasLinearInnerLogic V] [HasEquivalences V] [HasInnerFunctors W]
             [HasLinearInnerLogic W] [HasEquivalences W] [HasTrivialFunctoriality V W]
             [HasTrivialFunctoriality U W] [HasTrivialIsomorphismCondition W]

    instance isTypeCtor₂ {φ : U → V → W} {Φ : TypeCtorFun₂ φ} : IsTypeCtor₂ Φ where
      app  _ := isTypeCtor
      app₂ _ := isTypeCtor

  end

  section

    variable (U : Universe) [HasInnerFunctors U] [HasTrivialFunctoriality U U] [HasEquivalences U]
             [HasTrivialIsomorphismCondition U]

    instance hasFunctorEquivalences : HasFunctorEquivalences U where
      hFunCtor₂             := isTypeCtor₂
      defSwapFunEquiv _ _ _ := defIso

    instance hasEquivRelEquivalences {α : Sort u} (R : Prerelation α U) [IsEquivalence R] :
        HasEquivRelEquivalences U R where
      hEquivRelCtor₂           := isIsoFunctor₂
      defEquivRelSymmEquiv _ _ := defIso

    instance hasEquivalenceEquivalences : HasEquivalenceEquivalences U := ⟨⟩

    instance hasTopEquivalences [HasTop U] : HasTopEquivalences U where
      defTopElimEquiv _ := defIso

    instance hasBotEquivalences [HasBot U] : HasBotEquivalences U where
      defBotIntroEquiv    _ := defIso
      defBotIntroEquivFun _ := HasTrivialFunctoriality.defFun
      defBotIntroEquiv₂   _ := defIso

    instance hasProductEquivalences [HasInnerProducts U] : HasProductEquivalences U where
      hProdCtor₂              := isTypeCtor₂
      defProdElimEquiv  _ _ _ := defIso
      defProdCommEquiv  _ _   := defIso
      defProdAssocEquiv _ _ _ := defIso

    instance hasProductDistrEquivalences [HasInnerProducts U] : HasProductDistrEquivalences U where
      defProdDistrEquiv _ _ _ := defIso

    instance hasProductTopEquivalences [HasTop U] [HasInnerProducts U] :
        HasProductTopEquivalences U where
      defProdTopEquiv _ := defIso

    instance hasProductBotEquivalences [HasBot U] [HasInnerProducts U] :
        HasProductBotEquivalences U where
      defProdBotEquiv _ := defIso

    instance hasCoproductEquivalences [HasInnerCoproducts U] : HasCoproductEquivalences U where
      hCoprodCtor₂              := isTypeCtor₂
      defCoprodCommEquiv  _ _   := defIso
      defCoprodAssocEquiv _ _ _ := defIso

    instance hasCoproductDistrEquivalences [HasInnerProducts U] [HasInnerCoproducts U] :
        HasCoproductDistrEquivalences U where
      defCoprodDistrEquiv _ _ _ := defIso

    instance hasCoproductBotEquivalences [HasBot U] [HasInnerCoproducts U] :
        HasCoproductBotEquivalences U where
      defCoprodBotEquiv _ := defIso

    instance hasLinearPositiveEquivalences [HasTop U] [HasInnerProducts U] :
        HasLinearPositiveEquivalences U := ⟨⟩

    instance hasLinearNegativeEquivalences [HasTop U] [HasBot U] [HasInnerProducts U]
                                           [HasInnerCoproducts U] :
        HasLinearNegativeEquivalences U := ⟨⟩

    instance hasLinearEquivalences [HasTop U] [HasBot U] [HasInnerProducts U] [HasInnerCoproducts U] :
        HasLinearEquivalences U := ⟨⟩

    instance hasFullPositiveEquivalences [HasTop U] [HasInnerProducts U] :
        HasFullPositiveEquivalences U := ⟨⟩

    instance hasFullNegativeEquivalences [HasTop U] [HasBot U] [HasInnerProducts U]
                                         [HasInnerCoproducts U] :
        HasFullNegativeEquivalences U := ⟨⟩

    instance hasFullEquivalences [HasTop U] [HasBot U] [HasInnerProducts U] [HasInnerCoproducts U] :
        HasFullEquivalences U := ⟨⟩

    instance hasPropEquivalences [HasTop U] [HasInnerProducts U] [HasInnerCoproducts U] :
        HasPropEquivalences U where
      defDupFunEquiv    _ _ := defIso
      defDupProdEquiv   _   := defIso
      defDupCoprodEquiv _   := defIso
      defTopEquiv       _   := defIso
      defTopEquivFun    _   := HasTrivialFunctoriality.defFun
      defTopEquivEquiv  _   := defIso

    instance hasClassicalEquivalences [HasBot U] [HasClassicalLogic U] :
        HasClassicalEquivalences U where
      defNotNotEquiv _ := defIso

  end

end HasTrivialIsomorphismCondition
