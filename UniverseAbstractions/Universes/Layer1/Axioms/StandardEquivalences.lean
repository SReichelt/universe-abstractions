import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Axioms.Singletons
import UniverseAbstractions.Universes.Layer1.Axioms.Products
import UniverseAbstractions.Universes.Layer1.Axioms.Coproducts
import UniverseAbstractions.Universes.Layer1.Axioms.Equivalences
import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations.AttachedRelations
import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations.AttachedEquivalences
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedFunctors
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedSingletonFunctors
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedProductFunctors
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedCoproductFunctors
import UniverseAbstractions.Universes.Layer1.Meta.Tactics.Functoriality



namespace UniverseAbstractions.Layer1

set_option autoImplicit false

open HasFunctors HasLinearLogic HasExternalLinearLogic HasExternalSubLinearLogic
     HasExternalNonLinearLogic
     HasEquivalences HasPreorderRelation HasIsomorphisms HasEquivalenceRelationBase



namespace HasEquivalences

  open HasProducts HasCoproducts

  variable (U : Universe) [HasLinearLogic U] [HasEquivalences U]

  @[reducible] def notCtorFun [HasBot U] := (homFun₂ U).app₂ ⊥_U

  def prodCtorFun₂ [HasProducts U] : PreorderFunctor₂ U U U where
    φ  := prodRel U
    hφ := { app  := λ A => { inst := λ B₁ B₂ => HasProducts.replaceSndFun₂ A B₁ B₂ },
            app₂ := λ B => { inst := λ A₁ A₂ => HasProducts.replaceFstFun₂ A₁ A₂ B } }

  def coprodCtorFun₂ [HasCoproducts U] : PreorderFunctor₂ U U U where
    φ  := coprodRel U
    hφ := { app  := λ A => { inst := λ B₁ B₂ => HasCoproducts.replaceSndFun₂ A B₁ B₂ },
            app₂ := λ B => { inst := λ A₁ A₂ => HasCoproducts.replaceFstFun₂ A₁ A₂ B } }

end HasEquivalences



class HasFunEquivEquivalences (U : Universe) [HasLinearLogic U] [HasEquivalences U] extends
    HasHomIsoEquivalences U where
  defSwapFunEquiv (A B C : U) : [(A ⥤ B ⥤ C) ≃ (B ⥤ A ⥤ C)]_{⟨swapFun₃ A B C, swapFun₃ B A C⟩}

namespace HasFunEquivEquivalences

  instance hasEquivalenceRelation (U : Universe) [HasLinearLogic U] [HasEquivalences U]
                                  [HasFunEquivEquivalences U] :
      HasEquivalenceRelation U U := ⟨⟩

  variable {U : Universe} [HasLinearLogic U] [HasEquivalences U] [h : HasFunEquivEquivalences U]

  @[reducible] def swapFunEquiv (A B C : U) : (A ⥤ B ⥤ C) ≃ (B ⥤ A ⥤ C) := h.defSwapFunEquiv A B C

end HasFunEquivEquivalences


class HasTopEquivalences (U : Universe) [HasLinearLogic U] [HasEquivalences U] [HasTop U] where
  defTopElimEquiv (A : U) : [(⊤_U ⥤ A) ≃ A]_{⟨HasTop.invElimFun A, HasTop.elimFun₂ A⟩}

namespace HasTopEquivalences

  section

    variable {U : Universe} [HasLinearLogic U] [HasEquivalences U] [HasTop U]
             [h : HasTopEquivalences U]

    @[reducible] def topElimEquiv (A : U) : (⊤_U ⥤ A) ≃ A := h.defTopElimEquiv A

  end

  def notTopBotEquiv (U : Universe) [HasLinearLogic U] [HasTop U]
                     [HasBot U] [HasEquivalences U] [HasTopEquivalences U] :
      ~(⊤_U) ≃ ⊥_U :=
    topElimEquiv ⊥_U

end HasTopEquivalences


class HasBotEquivalences (U : Universe) [HasLinearLogic U] [HasEquivalences U] [HasBot U] where
  defBotIntroEquiv {A : U} (F : A ⥤ ⊥_U) : [A ≃ ⊥_U]_{⟨F, HasBot.elimFun A⟩}
  defBotIntroEquivFun (A : U) : [(A ⥤ ⊥_U) ⥤ (A ≃ ⊥_U)]_{defBotIntroEquiv}
  defBotIntroEquiv₂ (A : U) : [(A ⥤ ⊥_U) ≃ (A ≃ ⊥_U)]_{⟨asHom (defBotIntroEquivFun A), toFun₂ A ⊥_U⟩}

namespace HasBotEquivalences

  instance notIsCtor (U : Universe) [HasLinearLogic U] [HasEquivalences U] [HasBot U]
                     [HasFunEquivEquivalences U] :
      IsIsoFunctor (notCtorFun U) :=
    inferInstance

  variable {U : Universe} [HasLinearLogic U] [HasEquivalences U] [HasBot U]
           [h : HasBotEquivalences U]

  @[reducible] def botIntroEquiv {A : U} (F : A ⥤ ⊥_U) : A ≃ ⊥_U := h.defBotIntroEquiv F
  @[reducible] def botIntroEquivFun (A : U) : (A ⥤ ⊥_U) ⥤ (A ≃ ⊥_U) := h.defBotIntroEquivFun A
  @[reducible] def botIntroEquiv₂ (A : U) : (A ⥤ ⊥_U) ≃ (A ≃ ⊥_U) := h.defBotIntroEquiv₂ A

  instance botIntroEquiv.isFunApp {A : U} {F : A ⥤ ⊥_U} : IsFunApp (botIntroEquiv F) :=
    ⟨botIntroEquivFun A, F⟩

end HasBotEquivalences


class HasProductEquivalences (U : Universe) [HasLinearLogic U] [HasEquivalences U]
                             [HasProducts U] where
  hProdCtor₂ : IsIsoFunctor₂ (prodCtorFun₂ U)
  defProdElimEquiv (A B C : U) :
    [(A ⊓ B ⥤ C) ≃ (A ⥤ B ⥤ C)]_{⟨HasProducts.invElimFun₃ A B C, HasProducts.elimFun₂ A B C⟩}
  defProdCommEquiv (A B : U) :
    [A ⊓ B ≃ B ⊓ A]_{⟨HasProducts.commFun A B, HasProducts.commFun B A⟩}
  defProdAssocEquiv (A B C : U) :
    [(A ⊓ B) ⊓ C ≃ A ⊓ (B ⊓ C)]_{⟨HasProducts.assocLRFun A B C, HasProducts.assocRLFun A B C⟩}

namespace HasProductEquivalences

  variable {U : Universe} [HasLinearLogic U] [HasEquivalences U] [HasProducts U]
           [h : HasProductEquivalences U]

  instance : IsIsoFunctor₂ (prodCtorFun₂ U) := h.hProdCtor₂

  @[reducible] def prodElimEquiv (A B C : U) : (A ⊓ B ⥤ C) ≃ (A ⥤ B ⥤ C) :=
    h.defProdElimEquiv A B C

  @[reducible] def prodCommEquiv (A B : U) : A ⊓ B ≃ B ⊓ A := h.defProdCommEquiv A B

  @[reducible] def prodAssocEquiv (A B C : U) : (A ⊓ B) ⊓ C ≃ A ⊓ (B ⊓ C) :=
    h.defProdAssocEquiv A B C

end HasProductEquivalences

class HasProductDistrEquivalences (U : Universe) [HasFullLogic U] [HasEquivalences U]
                                  [HasProducts U] where
  defProdDistrEquiv (A B C : U) :
    [(A ⥤ B ⊓ C) ≃ (A ⥤ B) ⊓ (A ⥤ C)]_{⟨HasProducts.distrFun A B C, HasProducts.invDistrFun₂ A B C⟩}

namespace HasProductDistrEquivalences

  variable {U : Universe} [HasFullLogic U] [HasEquivalences U] [HasProducts U]
           [h : HasProductDistrEquivalences U]

  @[reducible] def prodDistrEquiv (A B C : U) : (A ⥤ B ⊓ C) ≃ (A ⥤ B) ⊓ (A ⥤ C) :=
    h.defProdDistrEquiv A B C

end HasProductDistrEquivalences


class HasProductTopEquivalences (U : Universe) [HasLinearLogic U] [HasEquivalences U] [HasTop U]
                                [HasProducts U] where
  defProdTopEquiv (A : U) :
    [⊤_U ⊓ A ≃ A]_{⟨HasProducts.prodTopElimFun A, HasProducts.prodTopIntroFun A⟩}

namespace HasProductTopEquivalences

  variable {U : Universe} [HasLinearLogic U] [HasEquivalences U] [HasTop U] [HasProducts U]
           [h : HasProductTopEquivalences U]

  @[reducible] def prodTopEquiv (A : U) : ⊤_U ⊓ A ≃ A := h.defProdTopEquiv A

  def prodTopEquiv' [HasProductEquivalences U] (A : U) : A ⊓ ⊤_U ≃ A :=
    prodTopEquiv A • HasProductEquivalences.prodCommEquiv A ⊤_U

end HasProductTopEquivalences


class HasProductBotEquivalences (U : Universe) [HasLinearLogic U] [HasEquivalences U] [HasBot U]
                                [HasProducts U] where
  defProdBotEquiv (A : U) :
    [⊥_U ⊓ A ≃ ⊥_U]_{⟨HasProducts.prodBotElimFun A, HasProducts.prodBotIntroFun A⟩}

namespace HasProductBotEquivalences

  variable {U : Universe} [HasLinearLogic U] [HasEquivalences U] [HasBot U] [HasProducts U]
           [h : HasProductBotEquivalences U]

  @[reducible] def prodBotEquiv (A : U) : ⊥_U ⊓ A ≃ ⊥_U := h.defProdBotEquiv A

  def prodBotEquiv' [HasProductEquivalences U] (A : U) : A ⊓ ⊥_U ≃ ⊥_U :=
    prodBotEquiv A • HasProductEquivalences.prodCommEquiv A ⊥_U

end HasProductBotEquivalences


class HasCoproductEquivalences (U : Universe) [HasLinearLogic U] [HasEquivalences U]
                               [HasCoproducts U] where
  hCoprodCtor₂ : IsIsoFunctor₂ (coprodCtorFun₂ U)
  defCoprodCommEquiv (A B : U) :
    [A ⊔ B ≃ B ⊔ A]_{⟨HasCoproducts.commFun A B, HasCoproducts.commFun B A⟩}
  defCoprodAssocEquiv (A B C : U) :
    [(A ⊔ B) ⊔ C ≃ A ⊔ (B ⊔ C)]_{⟨HasCoproducts.assocLRFun A B C, HasCoproducts.assocRLFun A B C⟩}

namespace HasCoproductEquivalences

  variable {U : Universe} [HasLinearLogic U] [HasEquivalences U] [HasCoproducts U]
           [h : HasCoproductEquivalences U]

  instance : IsIsoFunctor₂ (coprodCtorFun₂ U) := h.hCoprodCtor₂

  @[reducible] def coprodCommEquiv (A B : U) : A ⊔ B ≃ B ⊔ A := h.defCoprodCommEquiv A B

  @[reducible] def coprodAssocEquiv (A B C : U) : (A ⊔ B) ⊔ C ≃ A ⊔ (B ⊔ C) :=
    h.defCoprodAssocEquiv A B C

end HasCoproductEquivalences

class HasCoproductDistrEquivalences (U : Universe) [HasFullLogic U] [HasEquivalences U]
                                    [HasProducts U] [HasCoproducts U] where
  defCoprodDistrEquiv (A B C : U) :
    [(A ⊔ B ⥤ C) ≃ (A ⥤ C) ⊓ (B ⥤ C)]_{⟨HasCoproducts.distrFun A B C, HasCoproducts.invDistrFun₂ A B C⟩}

namespace HasCoproductDistrEquivalences

  variable {U : Universe} [HasFullLogic U] [HasEquivalences U] [HasProducts U]
           [HasCoproducts U] [h : HasCoproductDistrEquivalences U]

  @[reducible] def coprodDistrEquiv (A B C : U) : (A ⊔ B ⥤ C) ≃ (A ⥤ C) ⊓ (B ⥤ C) :=
    h.defCoprodDistrEquiv A B C

end HasCoproductDistrEquivalences


class HasCoproductBotEquivalences (U : Universe) [HasLinearLogic U] [HasEquivalences U] [HasBot U]
                                  [HasCoproducts U] where
  defCoprodBotEquiv (A : U) :
    [⊥_U ⊔ A ≃ A]_{⟨HasCoproducts.coprodBotElimFun A, HasCoproducts.coprodBotIntroFun A⟩}

namespace HasCoproductBotEquivalences

  variable {U : Universe} [HasLinearLogic U] [HasEquivalences U] [HasBot U] [HasCoproducts U]
           [h : HasCoproductBotEquivalences U]

  @[reducible] def coprodBotEquiv (A : U) : ⊥_U ⊔ A ≃ A := h.defCoprodBotEquiv A

  def coprodBotEquiv' [HasCoproductEquivalences U] (A : U) : A ⊔ ⊥_U ≃ A :=
    coprodBotEquiv A • HasCoproductEquivalences.coprodCommEquiv A ⊥_U

end HasCoproductBotEquivalences


class HasLinearPositiveEquivalences (U : Universe) [HasLinearLogic U] [HasEquivalences U]
                                    [HasTop U] [HasProducts U] extends
  HasFunEquivEquivalences U, HasTopEquivalences U, HasProductEquivalences U,
  HasProductTopEquivalences U

class HasLinearNegativeEquivalences (U : Universe) [HasLinearLogic U] [HasEquivalences U]
                                    [HasTop U] [HasBot U] [HasProducts U] [HasCoproducts U]
                                    [HasLinearPositiveEquivalences U] extends
  HasBotEquivalences U, HasProductBotEquivalences U, HasCoproductEquivalences U,
  HasCoproductBotEquivalences U

class HasLinearEquivalences (U : Universe) [HasLinearLogic U] [HasEquivalences U] [HasTop U]
                            [HasBot U] [HasProducts U] [HasCoproducts U] extends
  HasLinearPositiveEquivalences U, HasLinearNegativeEquivalences U

class HasFullPositiveEquivalences (U : Universe) [HasFullLogic U] [HasEquivalences U] [HasTop U]
                                  [HasProducts U] extends
  HasLinearPositiveEquivalences U, HasProductDistrEquivalences U

class HasFullNegativeEquivalences (U : Universe) [HasFullLogic U] [HasEquivalences U] [HasTop U]
                                  [HasBot U] [HasProducts U] [HasCoproducts U]
                                  [HasFullPositiveEquivalences U] extends
  HasLinearNegativeEquivalences U, HasCoproductDistrEquivalences U

class HasFullEquivalences (U : Universe) [HasFullLogic U] [HasEquivalences U] [HasTop U] [HasBot U]
                          [HasProducts U] [HasCoproducts U] extends
  HasFullPositiveEquivalences U, HasFullNegativeEquivalences U, HasLinearEquivalences U

class IsPositiveUniverse (U : Universe) where
  [hFun      : HasFullLogic                U]
  [hEquiv    : HasEquivalences             U]
  [hTop      : HasTop                      U]
  [hProd     : HasProducts                 U]
  [hPosEquiv : HasFullPositiveEquivalences U]

namespace IsPositiveUniverse

  variable (U : Universe) [h : IsPositiveUniverse U]

  instance : HasFullLogic                U := h.hFun
  instance : HasEquivalences             U := h.hEquiv
  instance : HasTop                      U := h.hTop
  instance : HasProducts                 U := h.hProd
  instance : HasFullPositiveEquivalences U := h.hPosEquiv

end IsPositiveUniverse

class IsNegativeUniverse (U : Universe) [IsPositiveUniverse U] where
  [hBot      : HasBot                      U]
  [hCoprod   : HasCoproducts               U]
  [hNegEquiv : HasFullNegativeEquivalences U]

namespace IsNegativeUniverse

  variable (U : Universe) [IsPositiveUniverse U] [h : IsNegativeUniverse U]

  instance : HasBot                      U := h.hBot
  instance : HasCoproducts               U := h.hCoprod
  instance : HasFullNegativeEquivalences U := h.hNegEquiv

end IsNegativeUniverse

class IsStandardUniverse (U : Universe) extends IsPositiveUniverse U, IsNegativeUniverse U

namespace IsStandardUniverse

  variable (U : Universe) [IsStandardUniverse U]

  instance hasFullEquivalences : HasFullEquivalences U := ⟨⟩

end IsStandardUniverse


-- This is only implemented by universes of propositions, where all inhabited types are equivalent.
class HasPropEquivalences (U : Universe) [HasFullLogic U] [HasEquivalences U] [HasTop U]
                          [HasProducts U] [HasCoproducts U] where
  defDupFunEquiv (A B : U) : [(A ⥤ A ⥤ B) ≃ (A ⥤ B)]_{⟨dupFun₂ A B, constFun₂ A (A ⥤ B)⟩}
  defDupProdEquiv (A : U) : [A ⊓ A ≃ A]_{⟨HasProducts.fstFun A A, HasProducts.dupIntroFun A⟩}
  defDupCoprodEquiv (A : U) :
    [A ⊔ A ≃ A]_{⟨asHom (HasCoproducts.elimFun (idFun A) (idFun A)), HasCoproducts.leftIntroFun A A⟩}
  defTopEquiv {A : U} (a : A) : [A ≃ ⊤_U]_{⟨constFun A ∗_U, HasTop.elimFun a⟩}
  defTopEquivFun (A : U) : [A ⥤ (A ≃ ⊤_U)]_{defTopEquiv}
  defTopEquivEquiv (A : U) : [(A ≃ ⊤_U) ≃ A]_{⟨asHom (Λ E => inv E ∗_U), asHom (defTopEquivFun A)⟩}

namespace HasPropEquivalences

  variable {U : Universe} [HasFullLogic U] [HasEquivalences U] [HasTop U]
           [HasProducts U] [HasCoproducts U] [h : HasPropEquivalences U]

  @[reducible] def dupFunEquiv (A B : U) : (A ⥤ A ⥤ B) ≃ (A ⥤ B) := h.defDupFunEquiv A B
  @[reducible] def dupProdEquiv (A : U) : A ⊓ A ≃ A := h.defDupProdEquiv A
  @[reducible] def dupCoprodEquiv (A : U) : A ⊔ A ≃ A := h.defDupCoprodEquiv A
  @[reducible] def topEquiv {A : U} (a : A) : A ≃ ⊤_U := h.defTopEquiv a
  @[reducible] def topEquivFun (A : U) : A ⥤ (A ≃ ⊤_U) := h.defTopEquivFun A
  @[reducible] def topEquivEquiv (A : U) : (A ≃ ⊤_U) ≃ A := h.defTopEquivEquiv A

  instance topEquiv.isFunApp {A : U} {a : A} : IsFunApp (topEquiv a) := ⟨topEquivFun A, a⟩

  @[reducible] def idFunTopEquiv (A : U) : (A ⥤ A) ≃ ⊤_U := topEquiv (idFun A)
  @[reducible] def notBotTopEquiv [HasBot U] : ~⊥_U ≃ ⊤_U := idFunTopEquiv ⊥_U
  @[reducible] def coprodTopEquiv (A : U) : ⊤_U ⊔ A ≃ ⊤_U := topEquiv (HasCoproducts.leftIntro ∗_U A)
  @[reducible] def coprodTopEquiv' (A : U) : A ⊔ ⊤_U ≃ ⊤_U := topEquiv (HasCoproducts.rightIntro A ∗_U)
  @[reducible] def reflEquivTopEquiv (A : U) : (A ≃ A) ≃ ⊤_U := topEquiv (idIso A)

  def inhabEquiv {A B : U} (a : A) (b : B) : A ≃ B := (topEquiv b)⁻¹ • topEquiv a

end HasPropEquivalences

class HasClassicalEquivalences (U : Universe) [HasLinearLogic U] [HasEquivalences U] [HasBot U]
                               [HasClassicalLogic U] where
  defNotNotEquiv (A : U) :
    [~~A ≃ A]_{⟨asHom (HasClassicalLogic.byContradictionFun A), HasBot.notNotFun A⟩}

namespace HasClassicalEquivalences

  variable {U : Universe} [HasLinearLogic U] [HasEquivalences U] [HasBot U] [HasClassicalLogic U]
           [h : HasClassicalEquivalences U]

  @[reducible] def notNotEquiv (A : U) : ~~A ≃ A := h.defNotNotEquiv A

  section

    variable [HasFunEquivEquivalences U]

    @[reducible] def notElimEquiv {A B : U} (E : ~B ≃ ~A) : A ≃ B :=
      notNotEquiv B • IsIsoFunctor.iso (notCtorFun U) E • (notNotEquiv A)⁻¹

    def notElimEquivFun (A B : U) : (~B ≃ ~A) ⥤ (A ≃ B) := Λ E => notElimEquiv E

    instance notElimEquiv.isFunApp {A B : U} {E : ~B ≃ ~A} : IsFunApp (notElimEquiv E) :=
      ⟨notElimEquivFun A B, E⟩

  end

end HasClassicalEquivalences
