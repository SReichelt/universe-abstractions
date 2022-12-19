import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Axioms.Singletons
import UniverseAbstractions.Universes.Layer1.Axioms.Products
import UniverseAbstractions.Universes.Layer1.Axioms.Coproducts
import UniverseAbstractions.Universes.Layer1.Axioms.Equivalences
import UniverseAbstractions.Universes.Layer1.Axioms.StandardEquivalences



namespace UniverseAbstractions.Layer1

set_option autoImplicit false

universe u u' u'' v

open HasTypeWithIntro HasPiType



namespace HasPiTypeWithIntro

  instance hasSwapPi {α : Sort u} {β : Sort u'} {V : Universe} (P : α → β → V)
                     [∀ a, HasType V (∀ b, P a b)] [HasType V (∀ a, Pi (P a))]
                     [∀ b, HasTypeWithIntro V (∀ a, P a b)] :
      HasSwapPi P :=
    ⟨λ _ _ => defInst⟩

  instance hasSwapPi₂ {α : Sort u} {β : Sort u'} {V : Universe} (P : α → β → V)
                      [∀ a, HasType V (∀ b, P a b)] [HasType V (∀ a, Pi (P a))]
                      [∀ b, HasTypeWithIntro V (∀ a, P a b)]
                      [HasTypeWithIntro V (∀ b, [∀ a, P a b | V])] :
      HasSwapPi₂ P :=
    ⟨λ _ => defInst⟩

  instance hasCompFunPi (α : Sort u) {V W : Universe} [HasFunctors α V] {B : V} (Q : B → W)
                        [HasType W (∀ b, Q b)] [∀ F : α ⥤ B, HasTypeWithIntro W (∀ a, Q (F a))] :
      HasCompFunPi α Q :=
    ⟨λ _ _ => defInst⟩

  instance hasRevCompFunPi₂ (α : Sort u) {V W : Universe} [HasFunctors α V] {B : V} (Q : B → W)
                            [HasType W (∀ b, Q b)] [∀ F : α ⥤ B, HasTypeWithIntro W (∀ a, Q (F a))]
                            [HasTypeWithIntro W (∀ F : α ⥤ B, [∀ a, Q (F a) | W])] :
      HasRevCompFunPi₂ α Q :=
    ⟨λ _ => defInst⟩

  instance hasConstPi (α : Sort u) {V : Universe} (B : V) [HasTypeWithIntro V (α → B)] :
      HasConstPi α B :=
    ⟨λ _ => defInst⟩

  instance hasDupPi {α : Sort u} {V : Universe} (P : α → α → V) [∀ a, HasType V (∀ a', P a a')]
                    [HasType V (∀ a, Pi (P a))] [HasTypeWithIntro V (∀ a, P a a)] :
      HasDupPi P :=
    ⟨λ _ => defInst⟩

  instance hasPiSelfAppPi {U V : Universe} [HasUnivFunctors V U] {A : U} (Q : A → V)
                          [HasType V (∀ a, Q a)]
                          [∀ F : Pi Q ⥤ A, HasTypeWithIntro V (∀ G, Q (F G))] :
      HasPiSelfAppPi Q :=
    ⟨λ _ => defInst⟩

  instance hasPiSelfAppPi₂ {U V : Universe} [HasUnivFunctors V U] {A : U} (Q : A → V)
                           [HasType V (∀ a, Q a)]
                           [∀ F : Pi Q ⥤ A, HasTypeWithIntro V (∀ G, Q (F G))]
                           [HasTypeWithIntro V (∀ F : Pi Q ⥤ A, [∀ G, Q (F G) | V])] :
      HasPiSelfAppPi₂ Q :=
    ⟨defInst⟩

  instance hasSubstPi {α : Sort u} {V W : Universe} {P : α → V} [HasType V (∀ a, P a)]
                      (Q : ∀ a, P a → W) [∀ a, HasType W (∀ b, Q a b)] [HasType W (∀ a, Pi (Q a))]
                      [∀ F : Pi P, HasTypeWithIntro W (∀ a, Q a (F a))] :
      HasSubstPi Q :=
    ⟨λ _ _ => defInst⟩

  instance hasRevSubstPi₂ {α : Sort u} {V W : Universe} {P : α → V} [HasType V (∀ a, P a)]
                          (Q : ∀ a, P a → W) [∀ a, HasType W (∀ b, Q a b)]
                          [HasType W (∀ a, Pi (Q a))]
                          [∀ F : Pi P, HasTypeWithIntro W (∀ a, Q a (F a))]
                          [HasTypeWithIntro W (∀ F : Pi P, [∀ a, Q a (F a) | W])] :
      HasRevSubstPi₂ Q :=
    ⟨λ _ => defInst⟩

end HasPiTypeWithIntro


class HasFunctorsWithIntro (α : Sort u) (V : Universe) where
  [hFun (Y : V) : HasTypeWithIntro V (α → Y)]

namespace HasFunctorsWithIntro

  instance (α : Sort u) {V : Universe} [h : HasFunctorsWithIntro α V] (Y : V) :
      HasTypeWithIntro V (α → Y) :=
    h.hFun Y

  instance (α : Sort u) (V : Universe) [HasFunctorsWithIntro α V] : HasFunctors α V := ⟨⟩

  def defInst₂ {α : Sort u} {β : Sort u'} {V : Universe} [HasFunctorsWithIntro α V]
               [HasFunctorsWithIntro β V] {Y : V} {f : α → β → Y} :
      [α ⥤ β ⥤ Y]__{f} :=
    defInst (α := α → (β ⥤ Y)) (a := λ a => defInst (a := f a))

  def defInst₃ {α : Sort u} {β : Sort u'} {γ : Sort u''} {V : Universe} [HasFunctorsWithIntro α V]
               [HasFunctorsWithIntro β V] [HasFunctorsWithIntro γ V] {Y : V} {f : α → β → γ → Y} :
      [α ⥤ β ⥤ γ ⥤ Y]___{f} :=
    defInst (α := α → (β ⥤ γ ⥤ Y)) (a := λ a => defInst₂ (f := f a))

end HasFunctorsWithIntro

open HasFunctorsWithIntro


class HasUnivFunctorsWithIntro (U V : Universe) where
  [hFun (A : U) : HasFunctorsWithIntro A V]

namespace HasUnivFunctorsWithIntro

  instance {U : Universe} (A : U) (V : Universe) [h : HasUnivFunctorsWithIntro U V] :
      HasFunctorsWithIntro A V :=
    h.hFun A

  instance (U V : Universe) [HasUnivFunctorsWithIntro U V] : HasUnivFunctors U V := ⟨⟩

  instance hasIdFun {U : Universe} [HasUnivFunctorsWithIntro U U] (A : U) : HasIdFun A := ⟨defInst⟩

  instance hasPiAppFun {α : Sort u} {V : Universe} [HasUnivFunctorsWithIntro V V] (P : α → V)
                       [HasType V (∀ a, P a)] :
      HasPiAppFun P :=
    ⟨λ _ => defInst⟩

  instance hasSwapPiFun {α : Sort u} {β : Sort u'} {V : Universe} [HasUnivFunctorsWithIntro V V]
                        (P : α → β → V) [∀ a, HasType V (∀ b, P a b)] [HasType V (∀ a, Pi (P a))]
                        [∀ b, HasTypeWithIntro V (∀ a, P a b)]
                        [HasTypeWithIntro V (∀ b, [∀ a, P a b | V])] :
      HasSwapPiFun P :=
    ⟨defInst⟩

  instance hasRevCompFunPiFun (α : Sort u) {V W : Universe} [HasUnivFunctorsWithIntro W W]
                              [HasFunctors α V] {B : V} (Q : B → W) [HasType W (∀ b, Q b)]
                              [∀ F : α ⥤ B, HasTypeWithIntro W (∀ a, Q (F a))]
                              [HasTypeWithIntro W (∀ F : α ⥤ B, [∀ a, Q (F a) | W])] :
      HasRevCompFunPiFun α Q :=
    ⟨defInst⟩

  instance hasDupPiFun {α : Sort u} {V : Universe} [HasUnivFunctorsWithIntro V V] (P : α → α → V)
                       [∀ a, HasType V (∀ a', P a a')] [HasType V (∀ a, Pi (P a))]
                       [HasTypeWithIntro V (∀ a, P a a)] :
      HasDupPiFun P :=
    ⟨defInst⟩

  instance hasRevSubstPiFun {α : Sort u} {V W : Universe} [HasUnivFunctorsWithIntro W W] {P : α → V}
                            [HasType V (∀ a, P a)] (Q : ∀ a, P a → W) [∀ a, HasType W (∀ b, Q a b)]
                            [HasType W (∀ a, Pi (Q a))]
                            [∀ F : Pi P, HasTypeWithIntro W (∀ a, Q a (F a))]
                            [HasTypeWithIntro W (∀ F : Pi P, [∀ a, Q a (F a) | W])] :
      HasRevSubstPiFun Q :=
    ⟨defInst⟩

  instance hasFullLogic (U : Universe) [HasUnivFunctorsWithIntro U U] : HasFullLogic U where
    defIdFun       _     := defInst
    defRevAppFun₂  _ _   := defInst₂
    defRevCompFun₃ _ _ _ := defInst₃
    defConstFun₂   _ _   := defInst₂
    defDupFun₂     _ _   := defInst₂

  instance hasTop (U : Universe.{u}) [HasUnivFunctorsWithIntro U U] [HasTypeWithIntro U PUnit.{u}] :
      HasTop U where
    defElimFun _ := defInst

  instance hasBot (U : Universe.{u}) [HasUnivFunctorsWithIntro U U] [HasType U PEmpty.{u}] :
      HasBot U where
    defElimFun _ := defInst

  instance hasExternalSigmaType (U : Universe) [HasUnivFunctorsWithIntro U U] {α : Sort u}
                                (β : α → Sort v) [∀ a, HasFunctorsWithIntro (β a) U]
                                [∀ Y : U, HasTypeWithIntro U (∀ a, β a ⥤ Y)]
                                [HasTypeWithIntro U (PSigma β)] :
      HasExternalSigmaType U β where
    defIntroFun   _ := defInst
    defIntroFunPi   := defInst
    defElimFun₂   _ := defInst₂

  instance hasExternalProducts (U : Universe) [HasUnivFunctorsWithIntro U U] (α : Sort u)
                               (β : Sort v) [HasFunctorsWithIntro α U] [HasFunctorsWithIntro β U]
                               [HasTypeWithIntro U (PProd α β)] :
      HasExternalProducts U α β where
    defIntroFun₂   := defInst₂
    defElimFun₂  _ := defInst₂

  instance hasProducts (U : Universe) [HasUnivFunctorsWithIntro U U]
                       [∀ (A B : U), HasTypeWithIntro U (PProd A B)] :
      HasProducts U := ⟨⟩

  instance hasExternalCoproducts (U : Universe) [HasUnivFunctorsWithIntro U U]  (α : Sort u)
                                 (β : Sort v) [HasFunctorsWithIntro α U] [HasFunctorsWithIntro β U]
                                 [HasTypeWithIntro U (PSum α β)] :
      HasExternalCoproducts U α β where
    defLeftIntroFun    := defInst
    defRightIntroFun   := defInst
    defElimFun₃      _ := defInst₃

  instance hasCoproducts (U : Universe) [HasUnivFunctorsWithIntro U U]
                         [∀ (A B : U), HasTypeWithIntro U (PSum A B)] :
      HasCoproducts U := ⟨⟩

end HasUnivFunctorsWithIntro


namespace HasPiTypeWithIntro

  instance hasPiAppFunPi {α : Sort u} {V : Universe} [HasUnivFunctorsWithIntro V V] (P : α → V)
                         [HasType V (∀ a, P a)] [HasTypeWithIntro V (∀ a, Pi P ⥤ P a)] :
      HasPiAppFunPi P :=
    ⟨defInst⟩

  instance hasConstPiFun (α : Sort u) {V : Universe} [HasUnivFunctorsWithIntro V V] (B : V)
                         [HasTypeWithIntro V (α → B)] :
      HasConstPiFun α B :=
    ⟨defInst⟩

end HasPiTypeWithIntro


namespace HasFunctorsWithIntro

  instance hasExternalFullLogic (α : Sort u) (V : Universe) [HasUnivFunctorsWithIntro V V]
                                [HasFunctorsWithIntro α V] :
      HasExternalFullLogic α V where
    defRevAppFun₂  _   := defInst₂
    defRevCompFun₃ _ _ := defInst₃
    defConstFun₂   _   := defInst₂
    defDupFun₂     _   := defInst₂

end HasFunctorsWithIntro



namespace HasPreorderRelation

  class HasIsomorphismsWithIntro (α : Sort u) {V : Universe} [HasUnivFunctorsWithIntro V V]
                                 [HasPreorderRelation V α] where
    [hIsoType (a b : α) : HasTypeWithIntro V (DefIso a b)]

  namespace HasIsomorphismsWithIntro

    section

      variable {V : Universe} [HasUnivFunctorsWithIntro V V]

      instance {α : Sort u} [HasPreorderRelation V α] [h : HasIsomorphismsWithIntro α] (a b : α) :
          HasTypeWithIntro V (DefIso a b) :=
        h.hIsoType a b

      instance hasIsomorphisms (α : Sort u) [HasPreorderRelation V α] [HasIsomorphismsWithIntro α] :
          HasIsomorphisms α where
        defToHomFun     _ _   := defInst
        defRefl         _     := defInst
        defSymm         _     := defInst
        defSymmFun      _ _   := defInst
        defTrans        _ _   := defInst
        defRevTransFun₂ _ _ _ := defInst₂

      instance isIsoFunctor {α : Sort u} {β : Sort u'} [HasPreorderRelation V α] [HasIsomorphisms α]
                            [HasPreorderRelation V β] [HasIsomorphismsWithIntro β]
                            {F : PreorderFunctor α β} :
          HasIsomorphisms.IsIsoFunctor F where
        defIso    _   := defInst
        defIsoFun _ _ := defInst

      instance isIsoFunctor₂ {α : Sort u} {β : Sort u'} {γ : Sort u''} [HasPreorderRelation V α]
                             [HasIsomorphisms α] [HasPreorderRelation V β] [HasIsomorphisms β]
                             [HasPreorderRelation V γ] [HasIsomorphismsWithIntro γ]
                             {F : PreorderFunctor₂ α β γ} :
          HasIsomorphisms.IsIsoFunctor₂ F where
        app  _ := isIsoFunctor
        app₂ _ := isIsoFunctor

    end

    section

      variable (U : Universe) [HasUnivFunctorsWithIntro U U] [HasIsomorphismsWithIntro U]

      instance hasEquivalences : HasEquivalences U := ⟨⟩

    end

    section

      variable {V : Universe} [HasUnivFunctorsWithIntro V V] [HasIsomorphismsWithIntro V]

      instance hasHomEquivalences (α : Sort u) [HasPreorderRelation V α] [HasIsomorphisms α] :
          HasHomEquivalences α := ⟨⟩

      instance hasEquivRelEquivalences (α : Sort u) [HasEquivalenceRelationBase V α] :
          HasEquivRelEquivalences α where
        hEquivEquiv              := hasHomEquivalences (HasEquivalenceRelationBase.asPreorder α)
        defEquivRelSymmEquiv _ _ := defInst

      instance hasHomIsoEquivalences (α : Sort u) [HasPreorderRelation V α] [HasIsomorphisms α] :
          HasHomIsoEquivalences α := ⟨⟩

    end

    section

      variable (U : Universe) [HasUnivFunctorsWithIntro U U] [HasIsomorphismsWithIntro U]

      instance hasFunEquivEquivalences : HasFunEquivEquivalences U where
        defSwapFunEquiv _ _ _ := defInst

      instance hasTopEquivalences [HasTop U] : HasTopEquivalences U where
        defTopElimEquiv _ := defInst

      instance hasBotEquivalences [HasBot U] : HasBotEquivalences U where
        defBotIntroEquiv    _ := defInst
        defBotIntroEquivFun _ := defInst
        defBotIntroEquiv₂   _ := defInst

      instance hasProductEquivalences [HasProducts U] : HasProductEquivalences U where
        hProdCtor₂              := isIsoFunctor₂
        defProdElimEquiv  _ _ _ := defInst
        defProdCommEquiv  _ _   := defInst
        defProdAssocEquiv _ _ _ := defInst

      instance hasProductDistrEquivalences [HasProducts U] : HasProductDistrEquivalences U where
        defProdDistrEquiv _ _ _ := defInst

      instance hasProductTopEquivalences [HasTop U] [HasProducts U] :
          HasProductTopEquivalences U where
        defProdTopEquiv _ := defInst

      instance hasProductBotEquivalences [HasBot U] [HasProducts U] :
          HasProductBotEquivalences U where
        defProdBotEquiv _ := defInst

      instance hasCoproductEquivalences [HasCoproducts U] : HasCoproductEquivalences U where
        hCoprodCtor₂              := isIsoFunctor₂
        defCoprodCommEquiv  _ _   := defInst
        defCoprodAssocEquiv _ _ _ := defInst

      instance hasCoproductDistrEquivalences [HasProducts U] [HasCoproducts U] :
          HasCoproductDistrEquivalences U where
        defCoprodDistrEquiv _ _ _ := defInst

      instance hasCoproductBotEquivalences [HasBot U] [HasCoproducts U] :
          HasCoproductBotEquivalences U where
        defCoprodBotEquiv _ := defInst

      instance hasLinearPositiveEquivalences [HasTop U] [HasProducts U] :
          HasLinearPositiveEquivalences U := ⟨⟩

      instance hasLinearNegativeEquivalences [HasTop U] [HasBot U] [HasProducts U]
                                            [HasCoproducts U] :
          HasLinearNegativeEquivalences U := ⟨⟩

      instance hasLinearEquivalences [HasTop U] [HasBot U] [HasProducts U] [HasCoproducts U] :
          HasLinearEquivalences U := ⟨⟩

      instance hasFullPositiveEquivalences [HasTop U] [HasProducts U] :
          HasFullPositiveEquivalences U := ⟨⟩

      instance hasFullNegativeEquivalences [HasTop U] [HasBot U] [HasProducts U] [HasCoproducts U] :
          HasFullNegativeEquivalences U := ⟨⟩

      instance hasFullEquivalences [HasTop U] [HasBot U] [HasProducts U] [HasCoproducts U] :
          HasFullEquivalences U := ⟨⟩

      instance hasPropEquivalences [HasTop U] [HasProducts U] [HasCoproducts U] :
          HasPropEquivalences U where
        defDupFunEquiv    _ _ := defInst
        defDupProdEquiv   _   := defInst
        defDupCoprodEquiv _   := defInst
        defTopEquiv       _   := defInst
        defTopEquivFun    _   := defInst
        defTopEquivEquiv  _   := defInst

      instance hasClassicalEquivalences [HasBot U] [HasClassicalLogic U] :
          HasClassicalEquivalences U where
        defNotNotEquiv _ := defInst

    end

  end HasIsomorphismsWithIntro

end HasPreorderRelation



namespace HasProducts

  -- Convenience definition for cases where isomorphisms are just products.
  def hasIsomorphismsWithIntro (α : Sort u) {V : Universe} [HasUnivFunctorsWithIntro V V]
                               [HasProducts V] [HasPreorderRelation V α] :
      HasPreorderRelation.HasIsomorphismsWithIntro α where
    hIsoType a b := { T      := (a ⟶ b) ⊓ (b ⟶ a)
                      hElim  := ⟨λ P => ⟨fst P, snd P⟩⟩,
                      hIntro := ⟨λ ⟨toHom, invHom⟩ => intro toHom invHom⟩ }

end HasProducts
