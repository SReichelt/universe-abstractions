import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Axioms.Singletons
import UniverseAbstractions.Universes.Layer1.Axioms.Products
import UniverseAbstractions.Universes.Layer1.Axioms.Coproducts
import UniverseAbstractions.Universes.Layer1.Axioms.Equivalences
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedFunctors
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedSingletonFunctors
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedProductFunctors
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedCoproductFunctors
import UniverseAbstractions.Universes.Layer1.Meta.Tactics.Functoriality



namespace UniverseAbstractions.Layer1

set_option autoBoundImplicitLocal false

open HasFunctors HasLinearLogic HasSubLinearLogic HasNonLinearLogic HasEquivalences HasEquivOp



class HasFunctorEquivalences (U : Universe) [hFun : HasFunctors U] [HasLinearLogic U] [HasEquivOp U]
                             where
(defFunTypeFun₂ : DefTypeFun₂ hFun.Fun ⟨λ A => ⟨λ EB => revCompFun₂ A (toFun EB)⟩,
                                        λ B => ⟨λ EA => compFun₂ (invFun EA) B⟩⟩)
(defSwapFunEquiv (A B C : U) : (A ⟶ B ⟶ C) ⟷{swapFun₃ A B C, swapFun₃ B A C} (B ⟶ A ⟶ C))

namespace HasFunctorEquivalences

  variable {U : Universe} [HasFunctors U] [HasLinearLogic U] [HasEquivOp U]
           [HasFunctorEquivalences U]

  @[reducible] def swapFunEquiv (A B C : U) : (A ⟶ B ⟶ C) ⟷ (B ⟶ A ⟶ C) :=
  (defSwapFunEquiv A B C).E

end HasFunctorEquivalences


class HasTopEquivalences (U : Universe) [HasFunctors U] [HasLinearLogic U] [HasTop U]
                         [HasEquivalences U] where
(defTopElimEquiv (A : U) : (⊤_U ⟶ A) ⟷{HasTop.invElimFun A, HasTop.elimFun₂ A} A)

namespace HasTopEquivalences

  section

    variable {U : Universe} [HasFunctors U] [HasLinearLogic U] [HasTop U] [HasEquivalences U]
             [HasTopEquivalences U]

    @[reducible] def topElimEquiv (A : U) : (⊤_U ⟶ A) ⟷ A := (defTopElimEquiv A).E

  end

  def notTopBotEquiv (U : Universe) [HasFunctors U] [HasLinearLogic U] [HasTop U] [HasBot U]
                     [HasEquivalences U] [HasTopEquivalences U] :
    ~(⊤_U) ⟷ ⊥_U :=
  topElimEquiv ⊥_U

end HasTopEquivalences


class HasBotEquivalences (U : Universe) [HasFunctors U] [HasBot U] [HasEquivalences U] where
(defBotIntroEquiv {A : U} (F : A ⟶ ⊥_U) : A ⟷{F, HasBot.elimFun A} ⊥_U)
(defBotIntroEquivFun (A : U) : (A ⟶ ⊥_U) ⟶{λ F => (defBotIntroEquiv F).E} (A ⟷ ⊥_U))
(defBotIntroEquiv₂ (A : U) : (A ⟶ ⊥_U) ⟷{(defBotIntroEquivFun A).F, toFun₂ A ⊥_U} (A ⟷ ⊥_U))

namespace HasBotEquivalences

  def defNotTypeFun (U : Universe) [HasFunctors U] [HasLinearLogic U] [HasBot U] [HasEquivOp U]
                    [h : HasFunctorEquivalences U] :
    DefTypeFun (HasBot.Not (U := U)) ⟨λ E => compFun₂ (invFun E) (HasBot.Bot U)⟩ :=
  h.defFunTypeFun₂.app₂ ⊥_U

  variable {U : Universe} [HasFunctors U] [HasBot U] [HasEquivalences U] [HasBotEquivalences U]

  @[reducible] def botIntroEquiv {A : U} (F : A ⟶ ⊥_U) : A ⟷ ⊥_U := (defBotIntroEquiv F).E
  @[reducible] def botIntroEquivFun (A : U) : (A ⟶ ⊥_U) ⟶ (A ⟷ ⊥_U) := (defBotIntroEquivFun A).F
  @[reducible] def botIntroEquiv₂ (A : U) : (A ⟶ ⊥_U) ⟷ (A ⟷ ⊥_U) := (defBotIntroEquiv₂ A).E

  instance botIntroEquiv.isFunApp {A : U} {F : A ⟶ ⊥_U} : IsFunApp (A ⟶ ⊥_U) (botIntroEquiv F) :=
  ⟨botIntroEquivFun A, F⟩

end HasBotEquivalences


class HasProductEquivalences (U : Universe) [HasFunctors U] [HasLinearLogic U]
                             [hProd : HasProducts U] [HasEquivOp U] where
(defProdTypeFun₂ : DefTypeFun₂ hProd.Prod ⟨λ A => ⟨λ EB => HasProducts.replaceSndFun A (toFun EB)⟩,
                                           λ B => ⟨λ EA => HasProducts.replaceFstFun (toFun EA) B⟩⟩)
(defProdElimEquiv (A B C : U) :
   (A ⊓ B ⟶ C) ⟷{HasProducts.invElimFun₃ A B C, HasProducts.elimFun₂ A B C} (A ⟶ B ⟶ C))
(defProdCommEquiv (A B : U) :
   A ⊓ B ⟷{HasProducts.commFun A B, HasProducts.commFun B A} B ⊓ A)
(defProdAssocEquiv (A B C : U) :
   (A ⊓ B) ⊓ C ⟷{HasProducts.assocLRFun A B C, HasProducts.assocRLFun A B C} A ⊓ (B ⊓ C))

namespace HasProductEquivalences

  variable {U : Universe} [HasFunctors U] [HasLinearLogic U] [HasProducts U] [HasEquivOp U]
           [HasProductEquivalences U]

  @[reducible] def prodElimEquiv (A B C : U) : (A ⊓ B ⟶ C) ⟷ (A ⟶ B ⟶ C) :=
  (defProdElimEquiv A B C).E

  @[reducible] def prodCommEquiv (A B : U) : A ⊓ B ⟷ B ⊓ A := (defProdCommEquiv A B).E

  @[reducible] def prodAssocEquiv (A B C : U) : (A ⊓ B) ⊓ C ⟷ A ⊓ (B ⊓ C) :=
  (defProdAssocEquiv A B C).E

end HasProductEquivalences

class HasProductDistrEquivalences (U : Universe) [HasFunctors U] [HasFullLogic U] [HasProducts U]
                                  [HasEquivalences U] where
(defProdDistrEquiv (A B C : U) :
   (A ⟶ B ⊓ C) ⟷{HasProducts.distrFun A B C, HasProducts.invDistrFun₂ A B C} (A ⟶ B) ⊓ (A ⟶ C))

namespace HasProductDistrEquivalences

  variable {U : Universe} [HasFunctors U] [HasFullLogic U] [HasProducts U] [HasEquivalences U]
           [HasProductDistrEquivalences U]

  @[reducible] def prodDistrEquiv (A B C : U) : (A ⟶ B ⊓ C) ⟷ (A ⟶ B) ⊓ (A ⟶ C) :=
  (defProdDistrEquiv A B C).E

end HasProductDistrEquivalences


class HasProductTopEquivalences (U : Universe) [HasFunctors U] [HasLinearLogic U]
                                [HasTop U] [HasProducts U] [HasEquivalences U] where
(defProdTopEquiv (A : U) : ⊤_U ⊓ A ⟷{HasProducts.prodTopElimFun A, HasProducts.prodTopIntroFun A} A)

namespace HasProductTopEquivalences

  variable {U : Universe} [HasFunctors U] [HasLinearLogic U] [HasTop U] [HasProducts U]
           [HasEquivOp U] [HasProductTopEquivalences U]

  @[reducible] def prodTopEquiv (A : U) : ⊤_U ⊓ A ⟷ A := (defProdTopEquiv A).E

  def prodTopEquiv' [HasProductEquivalences U] (A : U) : A ⊓ ⊤_U ⟷ A :=
  HasEquivOp.trans (HasProductEquivalences.prodCommEquiv A ⊤_U) (prodTopEquiv A)

end HasProductTopEquivalences


class HasProductBotEquivalences (U : Universe) [HasFunctors U] [HasBot U] [HasProducts U]
                                [HasEquivalences U] where
(defProdBotEquiv (A : U) :
   ⊥_U ⊓ A ⟷{HasProducts.prodBotElimFun A, HasProducts.prodBotIntroFun A} ⊥_U)

namespace HasProductBotEquivalences

  variable {U : Universe} [HasFunctors U] [HasLinearLogic U] [HasBot U] [HasProducts U]
           [HasEquivOp U] [HasProductBotEquivalences U]

  @[reducible] def prodBotEquiv (A : U) : ⊥_U ⊓ A ⟷ ⊥_U := (defProdBotEquiv A).E

  def prodBotEquiv' [HasProductEquivalences U] (A : U) : A ⊓ ⊥_U ⟷ ⊥_U :=
  HasEquivOp.trans (HasProductEquivalences.prodCommEquiv A ⊥_U) (prodBotEquiv A)

end HasProductBotEquivalences


class HasCoproductEquivalences (U : Universe) [HasFunctors U] [HasLinearLogic U]
                               [hCoprod : HasCoproducts U] [HasEquivOp U] where
(defCoprodTypeFun₂ :
   DefTypeFun₂ hCoprod.Coprod
               ⟨λ A => ⟨λ {B₁ B₂} EB => HasCoproducts.elimFun (HasCoproducts.leftIntroFun A B₂)
                                                              (HasCoproducts.rightIntroFun A B₂ ⊙
                                                               toFun EB)⟩,
                λ B => ⟨λ {A₁ A₂} EA => HasCoproducts.elimFun (HasCoproducts.leftIntroFun A₂ B ⊙
                                                               toFun EA)
                                                              (HasCoproducts.rightIntroFun A₂ B)⟩⟩)
(defCoprodCommEquiv (A B : U) :
   A ⊔ B ⟷{HasCoproducts.commFun A B, HasCoproducts.commFun B A} B ⊔ A)
(defCoprodAssocEquiv (A B C : U) :
   (A ⊔ B) ⊔ C ⟷{HasCoproducts.assocLRFun A B C, HasCoproducts.assocRLFun A B C} A ⊔ (B ⊔ C))

namespace HasCoproductEquivalences

  variable {U : Universe} [HasFunctors U] [HasLinearLogic U] [HasCoproducts U] [HasEquivOp U]
           [HasCoproductEquivalences U]

  @[reducible] def coprodCommEquiv (A B : U) : A ⊔ B ⟷ B ⊔ A := (defCoprodCommEquiv A B).E

  @[reducible] def coprodAssocEquiv (A B C : U) : (A ⊔ B) ⊔ C ⟷ A ⊔ (B ⊔ C) :=
  (defCoprodAssocEquiv A B C).E

end HasCoproductEquivalences

class HasCoproductDistrEquivalences (U : Universe) [HasFunctors U] [HasFullLogic U] [HasProducts U]
                                    [HasCoproducts U] [HasEquivalences U] where
(defCoprodDistrEquiv (A B C : U) :
   (A ⊔ B ⟶ C) ⟷{HasCoproducts.distrFun A B C, HasCoproducts.invDistrFun₂ A B C} (A ⟶ C) ⊓ (B ⟶ C))

namespace HasCoproductDistrEquivalences

  variable {U : Universe} [HasFunctors U] [HasFullLogic U] [HasProducts U] [HasCoproducts U]
           [HasEquivalences U] [HasCoproductDistrEquivalences U]

  @[reducible] def coprodDistrEquiv (A B C : U) : (A ⊔ B ⟶ C) ⟷ (A ⟶ C) ⊓ (B ⟶ C) :=
  (defCoprodDistrEquiv A B C).E

end HasCoproductDistrEquivalences


class HasCoproductBotEquivalences (U : Universe) [HasFunctors U] [HasLinearLogic U] [HasBot U]
                                  [HasCoproducts U] [HasEquivalences U] where
(defCoprodBotEquiv (A : U) :
   ⊥_U ⊔ A ⟷{HasCoproducts.coprodBotElimFun A, HasCoproducts.coprodBotIntroFun A} A)

namespace HasCoproductBotEquivalences

  variable {U : Universe} [HasFunctors U] [HasLinearLogic U] [HasBot U] [HasCoproducts U]
           [HasEquivOp U] [HasCoproductBotEquivalences U]

  @[reducible] def coprodBotEquiv (A : U) : ⊥_U ⊔ A ⟷ A := (defCoprodBotEquiv A).E

  def coprodBotEquiv' [HasCoproductEquivalences U] (A : U) : A ⊔ ⊥_U ⟷ A :=
  HasEquivOp.trans (HasCoproductEquivalences.coprodCommEquiv A ⊥_U) (coprodBotEquiv A)

end HasCoproductBotEquivalences


class HasEquivalenceEquivalences (U : Universe) [HasFunctors U] [HasLinearLogic U]
                                 [hEquiv : HasEquivOp U] where
(defEquivTypeFun₂ :
   DefTypeFun₂ hEquiv.Equiv ⟨λ A => ⟨λ EB => Λ E => HasEquivOp.trans E EB⟩,
                             λ B => ⟨λ EA => Λ E => HasEquivOp.trans (HasEquivOp.symm EA) E⟩⟩)
(defEquivSymmEquiv (A B : U) : (A ⟷ B) ⟷{HasEquivOp.symmFun A B, HasEquivOp.symmFun B A} (B ⟷ A))

namespace HasEquivalenceEquivalences

  variable {U : Universe} [HasFunctors U] [HasLinearLogic U] [HasEquivOp U]
           [HasEquivalenceEquivalences U]

  @[reducible] def equivSymmEquiv (A B : U) : (A ⟷ B) ⟷ (B ⟷ A) := (defEquivSymmEquiv A B).E

end HasEquivalenceEquivalences


class HasLinearEquivalences (U : Universe) [HasFunctors U] [HasLinearLogic U] [HasTop U] [HasBot U]
                            [HasProducts U] [HasCoproducts U] [HasEquivOp U] extends
  HasFunctorEquivalences U, HasTopEquivalences U, HasBotEquivalences U, HasProductEquivalences U,
  HasProductTopEquivalences U, HasProductBotEquivalences U, HasCoproductEquivalences U,
  HasCoproductBotEquivalences U, HasEquivalenceEquivalences U

class HasFullEquivalences (U : Universe) [HasFunctors U] [HasFullLogic U] [HasTop U] [HasBot U]
                          [HasProducts U] [HasCoproducts U] [HasEquivOp U] extends
  HasLinearEquivalences U, HasProductDistrEquivalences U, HasCoproductDistrEquivalences U

class IsStandardUniverse (U : Universe) extends
  HasFunctors U, HasFullLogic U, HasTop U, HasBot U, HasProducts U, HasCoproducts U, HasEquivOp U,
  HasFullEquivalences U


-- This is only implemented by universes of propositions, where all inhabited types are equivalent.
class HasPropEquivalences (U : Universe) [HasFunctors U] [HasFullLogic U] [HasTop U] [HasProducts U]
                          [HasCoproducts U] [HasEquivalences U] where
(defDupFunEquiv (A B : U) : (A ⟶ A ⟶ B) ⟷{dupFun₂ A B, constFun₂ A (A ⟶ B)} (A ⟶ B))
(defDupProdEquiv (A : U) : A ⊓ A ⟷{HasProducts.fstFun A A, HasProducts.dupIntroFun A} A)
(defDupCoprodEquiv (A : U) :
   A ⊔ A ⟷{HasCoproducts.elimFun (idFun A) (idFun A), HasCoproducts.leftIntroFun A A} A)
(defTopEquiv {A : U} (a : A) : A ⟷{constFun A ∗_U, HasTop.elimFun a} ⊤_U)
(defTopEquivFun (A : U) : A ⟶{λ a => (defTopEquiv a).E} (A ⟷ ⊤_U))
(defTopEquivEquiv (A : U) : (A ⟷ ⊤_U) ⟷{Λ E => inv E ∗_U, (defTopEquivFun A).F} A)

namespace HasPropEquivalences

  variable {U : Universe} [HasFunctors U] [HasFullLogic U] [HasTop U] [HasBot U] [HasProducts U]
           [HasCoproducts U] [HasEquivOp U] [HasPropEquivalences U]

  @[reducible] def dupFunEquiv (A B : U) : (A ⟶ A ⟶ B) ⟷ (A ⟶ B) := (defDupFunEquiv A B).E
  @[reducible] def dupProdEquiv (A : U) : A ⊓ A ⟷ A := (defDupProdEquiv A).E
  @[reducible] def dupCoprodEquiv (A : U) : A ⊔ A ⟷ A := (defDupCoprodEquiv A).E
  @[reducible] def topEquiv {A : U} (a : A) : A ⟷ ⊤_U := (defTopEquiv a).E
  @[reducible] def topEquivFun (A : U) : A ⟶ (A ⟷ ⊤_U) := (defTopEquivFun A).F
  @[reducible] def topEquivEquiv (A : U) : (A ⟷ ⊤_U) ⟷ A := (defTopEquivEquiv A).E

  instance topEquiv.isFunApp {A : U} {a : A} : IsFunApp A (topEquiv a) := ⟨topEquivFun A, a⟩

  @[reducible] def idFunTopEquiv (A : U) : (A ⟶ A) ⟷ ⊤_U := topEquiv (idFun A)
  @[reducible] def notBotTopEquiv : ~⊥_U ⟷ ⊤_U := idFunTopEquiv ⊥_U
  @[reducible] def coprodTopEquiv (A : U) : ⊤_U ⊔ A ⟷ ⊤_U := topEquiv (HasCoproducts.leftIntro ∗_U A)
  @[reducible] def coprodTopEquiv' (A : U) : A ⊔ ⊤_U ⟷ ⊤_U := topEquiv (HasCoproducts.rightIntro A ∗_U)
  @[reducible] def reflEquivTopEquiv (A : U) : (A ⟷ A) ⟷ ⊤_U := topEquiv (HasEquivOp.refl A)

  def inhabEquiv {A B : U} (a : A) (b : B) : A ⟷ B :=
  HasEquivOp.trans (topEquiv a) (HasEquivOp.symm (topEquiv b))

end HasPropEquivalences

class HasClassicalEquivalences (U : Universe) [HasFunctors U] [HasLinearLogic U] [HasBot U]
                               [HasClassicalLogic U] [HasEquivalences U] where
(defNotNotEquiv (A : U) : ~~A ⟷{HasClassicalLogic.byContradictionFun A, HasBot.notNotFun A} A)

namespace HasClassicalEquivalences

  variable {U : Universe} [HasFunctors U] [HasLinearLogic U] [HasBot U] [HasClassicalLogic U]

  section

    variable [HasEquivalences U] [HasClassicalEquivalences U]

    @[reducible] def notNotEquiv (A : U) : ~~A ⟷ A := (defNotNotEquiv A).E

  end

  section

    variable [HasEquivOp U] [HasFunctorEquivalences U] [HasClassicalEquivalences U]

    @[reducible] def notElimEquiv {A B : U} (E : ~A ⟷ ~B) :
      A ⟷ B :=
    HasEquivOp.trans (HasEquivOp.trans (HasEquivOp.symm (notNotEquiv A))
                                       (DefTypeFun.equiv (HasBotEquivalences.defNotTypeFun U) E))
                     (notNotEquiv B)

    def notElimEquivFun (A B : U) : (~A ⟷ ~B) ⟶ (A ⟷ B) := Λ E => notElimEquiv E

    instance notElimEquiv.isFunApp {A B : U} {E : ~A ⟷ ~B} : IsFunApp (~A ⟷ ~B) (notElimEquiv E) :=
    ⟨notElimEquivFun A B, E⟩

  end

end HasClassicalEquivalences
