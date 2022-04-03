import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Equivalences
import UniverseAbstractions.Axioms.Universe.Singletons
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Lemmas.DerivedFunctors
import UniverseAbstractions.Lemmas.DerivedSingletonFunctors
import UniverseAbstractions.Lemmas.DerivedProductFunctors



-- TODO:
--
--  instance hasLinearStandardEquivalences : HasLinearStandardEquivalences type.{u} :=
--  { defFunDomainEquiv      := λ e _   => ⟨λ f => funext λ b => congrArg f (e.rightInv b),
--                                          λ f => funext λ a => congrArg f (e.leftInv  a)⟩,
--    defFunDomainEquivFun   := λ _ _ _ => HasTrivialFunctoriality.defFun,
--    defFunCodomainEquiv    := λ e _   => ⟨λ f => funext λ c => e.leftInv  (f c),
--                                          λ f => funext λ c => e.rightInv (f c)⟩,
--    defFunCodomainEquivFun := λ _ _ _ => HasTrivialFunctoriality.defFun,
--    defSwapFunFunEquiv     := λ _ _ _ => ⟨λ _ => funext λ _ => funext λ _ => rfl,
--                                          λ _ => funext λ _ => funext λ _ => rfl⟩,
--    defTopElimEquiv        := λ _     => ⟨λ _ => rfl, λ f => funext λ () => rfl⟩,
--    defProdElimFunEquiv    := λ _ _ _ => ⟨λ _ => funext λ _ => funext λ _ => rfl,
--                                          λ _ => funext λ (_, _) => rfl⟩,
--    defProdFstEquiv        := λ e _   => ⟨λ p => prodExt (e.leftInv  p.fst) rfl,
--                                          λ p => prodExt (e.rightInv p.fst) rfl⟩,
--    defProdFstEquivFun     := λ _ _ _ => HasTrivialFunctoriality.defFun,
--    defProdSndEquiv        := λ e _   => ⟨λ p => prodExt rfl (e.leftInv  p.snd),
--                                          λ p => prodExt rfl (e.rightInv p.snd)⟩,
--    defProdSndEquivFun     := λ _ _ _ => HasTrivialFunctoriality.defFun,
--    defProdCommEquiv       := λ _ _   => ⟨λ (_, _) => rfl, λ (_, _) => rfl⟩,
--    defProdAssocEquiv      := λ _ _ _ => ⟨λ ((_, _), _) => rfl, λ (_, (_, _)) => rfl⟩,
--    defProdTopEquiv        := λ _     => ⟨λ _ => rfl, λ ((), _) => rfl⟩,
--    defCompEquivEquiv      := λ e _   => ⟨Equiv.symm_trans_trans e, Equiv.trans_symm_trans e⟩,
--    defCompEquivEquivFun   := λ _ _ _ => HasTrivialFunctoriality.defFun,
--    defInvEquivEquiv       := λ _ _   => ⟨Equiv.symm_symm, Equiv.symm_symm⟩ }
--
--  instance hasNonLinearStandardEquivalences : HasNonLinearStandardEquivalences type.{u} :=
--  { defProdDistrEquiv := λ _ _ _ => ⟨λ _ => funext λ _ => prodExt rfl rfl,
--                                     λ _ => prodExt (funext λ _ => rfl) (funext λ _ => rfl)⟩ }
--
--  instance hasBotEquivalences : HasBotEquivalences type.{u} :=
--  { defBotNotTopEquiv := ⟨λ e => Empty.elim e, λ f => Empty.elim (f ())⟩,
--    defProdBotEquiv   := λ _ => ⟨λ e => Empty.elim e, λ p => Empty.elim p.fst⟩,
--    defBotContraEquiv := λ _ => ⟨λ e => Empty.elim e, λ p => Empty.elim (p.snd p.fst)⟩ }

namespace HasLinearFunOp

  open HasFunctors HasCongrArg HasLinearFunExt HasEquivalences HasInternalEquivalences

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasLinearFunOp U]
           [HasLinearFunExt U] [HasInternalEquivalences U]

  def funDomainDesc {A B : U} (e : A ⮂ B) [he : EquivDesc.IsExtensional e] (C : U) :
    HalfEquivDesc (compFunFun e.toFun C) (compFunFun e.invFun C) :=
  ⟨λ F => rightId F •
          revCompFun.congrArg F he.rightExt.invExt •
          compAssoc e.invFun e.toFun F •
          byDefDef⟩

  instance funDomainDesc.isExt {A B : U} (e : A ⮂ B) [he : EquivDesc.IsExtensional e] (C : U) :
    HalfEquivDesc.IsExtensional (funDomainDesc e C) :=
  ⟨rightIdExt B C •
   compFunFun.congrArg he.rightExt.invExt C •
   compAssocExt e.invFun e.toFun C⟩

  def funCodomainDesc {A B : U} (e : A ⮂ B) [he : EquivDesc.IsExtensional e] (C : U) :
    HalfEquivDesc (revCompFunFun C e.toFun) (revCompFunFun C e.invFun) :=
  ⟨λ F => leftId F •
          defCongrArg (HasCompFunFun.defCompFunFun F A) he.leftExt.invExt •
          (compAssoc F e.toFun e.invFun)⁻¹ •
          byDefDef⟩

  instance funCodomainDesc.isExt {A B : U} (e : A ⮂ B) [he : EquivDesc.IsExtensional e] (C : U) :
    HalfEquivDesc.IsExtensional (funCodomainDesc e C) :=
  ⟨leftIdExt C A •
   revCompFunFun.congrArg C he.leftExt.invExt •
   (compAssocRightExt C e.toFun e.invFun)⁻¹⟩

  class HasLinearStandardEquivalences where
  (defFunDomainEquiv      {A B : U} (E : A ⟷ B) (C : U) :
     (B ⟶ C) ⟷{funDomainDesc (desc E) C, funDomainDesc (symmDesc E) C} (A ⟶ C))
  (defFunDomainEquivFun   (A B C : U)                   :
     (A ⟷ B) ⟶{λ E => defFunDomainEquiv E C} ((B ⟶ C) ⟷ (A ⟶ C)))
  (defFunCodomainEquiv    {A B : U} (E : A ⟷ B) (C : U) :
     (C ⟶ A) ⟷{funCodomainDesc (desc E) C, funCodomainDesc (symmDesc E) C} (C ⟶ B))
  (defFunCodomainEquivFun (A B C : U)                   :
     (A ⟷ B) ⟶{λ E => defFunCodomainEquiv E C} ((C ⟶ A) ⟷ (C ⟶ B)))

#exit

  (defSwapFunFunEquiv     (A B C : U)                   :
     (A ⟶ B ⟶ C) ⟷{swapFunFunFun A B C, swapFunFunFun B A C} (B ⟶ A ⟶ C))
  (defTopElimEquiv        (A : U)                       :
     A ⟷{HasInternalTop.elimFunFun A,
         HasInternalTop.invElimFun A} (HasTop.Top U ⟶ A))
  (defProdElimFunEquiv    (A B C : U)                   :
     (A ⟶ B ⟶ C) ⟷{HasInternalProducts.elimFunFun A B C,
                   HasInternalProducts.invElimFunFunFun A B C} (A ⊓ B ⟶ C))
  (defProdFstEquiv        {A B : U} (E : A ⟷ B) (C : U) :
     A ⊓ C ⟷{HasInternalProducts.replaceFstFun (toFun  E) C,
             HasInternalProducts.replaceFstFun (invFun E) C} B ⊓ C)
  (defProdFstEquivFun     (A B C : U)                   :
     (A ⟷ B) ⟶{λ E => defProdFstEquiv E C} (A ⊓ C ⟷ B ⊓ C))
  (defProdSndEquiv        {A B : U} (E : A ⟷ B) (C : U) :
     C ⊓ A ⟷{HasInternalProducts.replaceSndFun (toFun  E) C,
             HasInternalProducts.replaceSndFun (invFun E) C} C ⊓ B)
  (defProdSndEquivFun     (A B C : U)                   :
     (A ⟷ B) ⟶{λ E => defProdSndEquiv E C} (C ⊓ A ⟷ C ⊓ B))
  (defProdCommEquiv       (A B : U)                     :
     A ⊓ B ⟷{HasInternalProducts.commFun A B, HasInternalProducts.commFun B A} B ⊓ A)
  (defProdAssocEquiv      (A B C : U)                   :
     (A ⊓ B) ⊓ C ⟷{HasInternalProducts.assocLRFun A B C, HasInternalProducts.assocRLFun A B C} A ⊓ (B ⊓ C))
  (defProdTopEquiv        (A : U)                       :
     A ⟷{HasInternalProducts.prodTopIntroFun A,
         HasInternalProducts.prodTopElimFun A} HasTop.Top U ⊓ A)
  (defCompEquivEquiv      {A B : U} (E : A ⟷ B) (C : U) :
     (B ⟷ C) ⟷{HasEquivOp.compEquivFun E C, HasEquivOp.compEquivFun (HasEquivOp.invEquiv E) C} (A ⟷ C))
  (defCompEquivEquivFun   (A B C : U)                   :
     (A ⟷ B) ⟶{λ E => defCompEquivEquiv E C} ((B ⟷ C) ⟷ (A ⟷ C)))
  (defInvEquivEquiv       (A B : U)                     :
     (A ⟷ B) ⟷{HasEquivOp.invEquivFun A B, HasEquivOp.invEquivFun B A} (B ⟷ A))

  namespace HasLinearStandardEquivalences

    variable {U : Universe.{u}} [HasInternalFunctors U] [HasLinearFunOp U] [HasInternalTop U]
             [HasInternalProducts U] [HasEquivOp U] [HasLinearStandardEquivalences U]

    @[reducible] def funDomainEquiv {A B : U} (E : A ⟷ B) (C : U) : (B ⟶ C) ⟷ (A ⟶ C) := defFunDomainEquiv E C
    @[reducible] def funDomainEquivFun (A B C : U) : (A ⟷ B) ⟶ ((B ⟶ C) ⟷ (A ⟶ C)) := defFunDomainEquivFun A B C
    @[reducible] def funCodomainEquiv {A B : U} (E : A ⟷ B) (C : U) : (C ⟶ A) ⟷ (C ⟶ B) := defFunCodomainEquiv E C
    @[reducible] def funCodomainEquivFun (A B C : U) : (A ⟷ B) ⟶ ((C ⟶ A) ⟷ (C ⟶ B)) := defFunCodomainEquivFun A B C
    @[reducible] def swapFunFunEquiv (A B C : U) : (A ⟶ B ⟶ C) ⟷ (B ⟶ A ⟶ C) := defSwapFunFunEquiv A B C

    @[reducible] def topElimEquiv (A : U) : A ⟷ (HasTop.Top U ⟶ A) := defTopElimEquiv A

    @[reducible] def prodElimFunEquiv (A B C : U) : (A ⟶ B ⟶ C) ⟷ (A ⊓ B ⟶ C) := defProdElimFunEquiv A B C
    @[reducible] def prodFstEquiv {A B : U} (E : A ⟷ B) (C : U) : A ⊓ C ⟷ B ⊓ C := defProdFstEquiv E C
    @[reducible] def prodFstEquivFun (A B C : U) : (A ⟷ B) ⟶ (A ⊓ C ⟷ B ⊓ C) := defProdFstEquivFun A B C
    @[reducible] def prodSndEquiv {A B : U} (E : A ⟷ B) (C : U) : C ⊓ A ⟷ C ⊓ B := defProdSndEquiv E C
    @[reducible] def prodSndEquivFun (A B C : U) : (A ⟷ B) ⟶ (C ⊓ A ⟷ C ⊓ B) := defProdSndEquivFun A B C
    @[reducible] def prodCommEquiv (A B : U) : A ⊓ B ⟷ B ⊓ A := defProdCommEquiv A B
    @[reducible] def prodAssocEquiv (A B C : U) : (A ⊓ B) ⊓ C ⟷ A ⊓ (B ⊓ C) := defProdAssocEquiv A B C
    @[reducible] def prodTopEquiv (A : U) : A ⟷ HasTop.Top U ⊓ A := defProdTopEquiv A

    @[reducible] def compEquivEquiv {A B : U} (E : A ⟷ B) (C : U) : (B ⟷ C) ⟷ (A ⟷ C) := defCompEquivEquiv E C
    @[reducible] def compEquivEquivFun (A B C : U) : (A ⟷ B) ⟶ ((B ⟷ C) ⟷ (A ⟷ C)) := defCompEquivEquivFun A B C
    @[reducible] def invEquivEquiv (A B : U) : (A ⟷ B) ⟷ (B ⟷ A) := defInvEquivEquiv A B

  end HasLinearStandardEquivalences

end HasLinearFunOp

namespace HasFullFunOp

  class HasNonLinearStandardEquivalences (U : Universe) [HasFunOp U] [HasInternalTop U]
                                         [HasInternalProducts U] [HasEquivOp U] where
  (defProdDistrEquiv (A B C : U) :
     (A ⟶ B ⊓ C) ⟷{HasInternalProducts.distrFun A B C,
                   HasInternalProducts.invDistrFunFun A B C} (A ⟶ B) ⊓ (A ⟶ C))

  namespace HasNonLinearStandardEquivalences

    variable {U : Universe} [HasFunOp U] [HasInternalTop U] [HasInternalProducts U]
             [HasEquivOp U] [HasNonLinearStandardEquivalences U]

    @[reducible] def prodDistrEquiv (A B C : U) : (A ⟶ B ⊓ C) ⟷ (A ⟶ B) ⊓ (A ⟶ C):= defProdDistrEquiv A B C

  end HasNonLinearStandardEquivalences

end HasFullFunOp

namespace HasInternalBot

  class HasBotEquivalences (U : Universe) [HasInternalFunctors U] [HasAffineFunOp U]
                           [HasInternalTop U] [HasInternalBot U] [HasInternalProducts U]
                           [HasEquivOp U] where
  (defBotNotTopEquiv         :
     HasBot.Bot U ⟷{HasInternalBot.elimFun (HasInternalBot.Not (HasTop.Top U)),
                    HasInternalBot.notTopIntroFun} HasInternalBot.Not (HasTop.Top U))
  (defProdBotEquiv   (A : U) :
     HasBot.Bot U ⟷{HasInternalBot.elimFun (HasBot.Bot U ⊓ A),
                    HasInternalProducts.fstFun (HasBot.Bot U) A} HasBot.Bot U ⊓ A)
  (defBotContraEquiv (A : U) :
     HasBot.Bot U ⟷{HasInternalBot.elimFun (A ⊓ HasInternalBot.Not A),
                    HasInternalProducts.elimFun (HasInternalBot.contraIntroFun A)} A ⊓ HasInternalBot.Not A)

  namespace HasBotEquivalences

    variable {U : Universe} [HasInternalFunctors U] [HasAffineFunOp U] [HasInternalTop U]
             [HasInternalBot U] [HasInternalProducts U] [HasEquivOp U] [HasBotEquivalences U]

    @[reducible] def botNotTopEquiv : HasBot.Bot U ⟷ HasInternalBot.Not (HasTop.Top U) := defBotNotTopEquiv (U := U)
    @[reducible] def prodBotEquiv (A : U) : HasBot.Bot U ⟷ HasBot.Bot U ⊓ A := defProdBotEquiv A
    @[reducible] def botContraEquiv (A : U) : HasBot.Bot U ⟷ A ⊓ HasInternalBot.Not A := defBotContraEquiv A

  end HasBotEquivalences

end HasInternalBot

namespace HasClassicalLogic

  class HasClassicalEquivalences (U : Universe) [HasInternalFunctors U] [HasLinearFunOp U]
                                 [HasInternalBot U] [HasClassicalLogic U]
                                 [HasInternalProducts U] [HasEquivOp U] where
  (defByContradictionEquiv (A : U) :
     A ⟷{HasInternalBot.notNotFun A,
         HasClassicalLogic.byContradictionFun A} HasInternalBot.Not (HasInternalBot.Not A))

  namespace HasClassicalEquivalences

    variable {U : Universe} [HasInternalFunctors U] [HasLinearFunOp U] [HasInternalBot U]
             [HasClassicalLogic U] [HasInternalProducts U] [HasEquivOp U] [HasClassicalEquivalences U]

    @[reducible] def byContradictionEquiv (A : U) : A ⟷ HasInternalBot.Not (HasInternalBot.Not A) :=
    defByContradictionEquiv A

  end HasClassicalEquivalences

end HasClassicalLogic
