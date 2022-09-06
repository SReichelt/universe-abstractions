import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Axioms.Products
import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations
import UniverseAbstractions.Universes.Layer1.Axioms.Equivalences
import UniverseAbstractions.Universes.Layer1.Axioms.StandardEquivalences
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedProductFunctors



namespace UniverseAbstractions.Layer1

set_option autoImplicit false

universe u u' u''

open Universe HasPiType Prerelation HasPreorderRelation HasEquivalenceRelationBase HasEquivalences



namespace Universe.DefType

  def native {U : Universe} (A : U) : DefType U A where
    A    := A
    elim := id

end Universe.DefType



class HasTrivialDefInst {U : Universe} {α : Sort u'} (A : DefType U α) where
  mkDefInst (a : α) : DefType.DefInst A a

namespace HasTrivialDefInst

  def defInst {U : Universe} {α : Sort u'} {A : DefType U α} [h : HasTrivialDefInst A] {a : α} :
      DefType.DefInst A a :=
    h.mkDefInst a

  instance native {U : Universe} (A : U) : HasTrivialDefInst (DefType.native A) := ⟨λ a => ⟨a⟩⟩

end HasTrivialDefInst

open HasTrivialDefInst



class HasTrivialDefPi {α : Sort u} {V : Universe} (P : α → V) [h : HasPiType P] extends
  HasTrivialDefInst h.defPiType

class HasTrivialDefFun (α : Sort u) {U : Universe.{u}} (Y : U) [HasFunctors α Y] extends
  HasTrivialDefPi (Function.const α Y)

class HasTrivialFunctoriality (U V : Universe.{u}) [HasUnivFunctors U V] where
  [hDefFun (A : U) (B : V) : HasTrivialDefFun A B]

namespace HasTrivialDefPi

  def defPi {α : Sort u} {V : Universe} {P : α → V} [HasPiType P] [HasTrivialDefPi P]
            {f : ∀ a, P a} :
      DefPi P f :=
    defInst

  def defFun {α : Sort u} {U : Universe.{u}} {Y : U} [HasFunctors α Y] [HasTrivialDefFun α Y]
             {f : α → Y} :
      α ⥤{f} Y :=
    defPi

  def defFun₂ {α β : Sort u} {U : Universe.{u}} {Y : U} [HasFunctors β Y] [HasFunctors α (β ⥤ Y)]
              [HasTrivialDefFun β Y] [HasTrivialDefFun α (β ⥤ Y)] {f : α → β → Y} :
      α ⥤ β ⥤{f} Y :=
    ⟨λ _ => defFun, defFun⟩

  def defFun₃ {α β γ : Sort u} {U : Universe.{u}} {Y : U} [HasFunctors γ Y] [HasFunctors β (γ ⥤ Y)]
              [HasFunctors α (β ⥤ γ ⥤ Y)] [HasTrivialDefFun γ Y] [HasTrivialDefFun β (γ ⥤ Y)]
              [HasTrivialDefFun α (β ⥤ γ ⥤ Y)] {f : α → β → γ → Y} :
      α ⥤ β ⥤ γ ⥤{f} Y :=
    ⟨λ _ => defFun₂, defFun⟩

  instance {U V : Universe.{u}} [HasUnivFunctors U V] [h : HasTrivialFunctoriality U V]
           (A : U) (B : V) :
      HasTrivialDefFun A B :=
    h.hDefFun A B

  instance hasIdFun {U : Universe} (A : U) [HasFunctors A A] [HasTrivialDefFun A A] : HasIdFun A :=
    ⟨defFun⟩

  instance hasPiAppFun {α : Sort u} {V : Universe} [HasUnivFunctors V V] (P : α → V) [HasPiType P]
                       [HasTrivialFunctoriality V V] :
      HasPiAppFun P :=
    ⟨λ _ => defFun⟩

  instance hasPiAppFunPi {α : Sort u} {V : Universe} [HasUnivFunctors V V] (P : α → V) [HasPiType P]
                         [HasPiType (λ a => Pi P ⥤ P a)] [HasTrivialFunctoriality V V]
                         [HasTrivialDefPi (λ a => Pi P ⥤ P a)] :
      HasPiAppFunPi P :=
    ⟨defPi⟩

  instance hasSwapPi {α : Sort u} {β : Sort u'} {V : Universe} (P : α → β → V)
                     [∀ a, HasPiType (P a)] [HasPiType (λ a => Pi (P a))]
                     [∀ b, HasPiType (λ a => P a b)] [∀ b, HasTrivialDefPi (λ a => P a b)] :
      HasSwapPi P :=
    ⟨λ _ _ => defPi⟩

  instance hasSwapPi₂ {α : Sort u} {β : Sort u'} {V : Universe} (P : α → β → V)
                      [∀ a, HasPiType (P a)] [HasPiType (λ a => Pi (P a))]
                      [∀ b, HasPiType (λ a => P a b)] [HasPiType (λ b => Pi (λ a => P a b))]
                      [∀ b, HasTrivialDefPi (λ a => P a b)]
                      [HasTrivialDefPi (λ b => Pi (λ a => P a b))] :
      HasSwapPi₂ P :=
    ⟨λ _ => defPi⟩

  instance hasSwapPiFun {α : Sort u} {β : Sort u'} {V : Universe} [HasUnivFunctors V V]
                        (P : α → β → V) [∀ a, HasPiType (P a)] [HasPiType (λ a => Pi (P a))]
                        [∀ b, HasPiType (λ a => P a b)] [HasPiType (λ b => Pi (λ a => P a b))]
                        [∀ b, HasTrivialDefPi (λ a => P a b)]
                        [HasTrivialDefPi (λ b => Pi (λ a => P a b))] [HasTrivialFunctoriality V V] :
      HasSwapPiFun P :=
    ⟨defFun⟩

  instance hasCompFunPi (α : Sort u) {V : Universe.{u}} {W : Universe} {B : V} [HasFunctors α B]
                        (Q : B → W) [HasPiType Q] [∀ F : α ⥤ B, HasPiType (λ a => Q (F a))]
                        [∀ F : α ⥤ B, HasTrivialDefPi (λ a => Q (F a))] :
      HasCompFunPi α Q :=
    ⟨λ _ _ => defPi⟩

  instance hasRevCompFunPi₂ (α : Sort u) {V : Universe.{u}} {W : Universe} {B : V} [HasFunctors α B]
                            (Q : B → W) [HasPiType Q] [∀ F : α ⥤ B, HasPiType (λ a => Q (F a))]
                            [HasPiType (λ F : α ⥤ B => Pi (λ a => Q (F a)))]
                            [∀ F : α ⥤ B, HasTrivialDefPi (λ a => Q (F a))]
                            [HasTrivialDefPi (λ F : α ⥤ B => Pi (λ a => Q (F a)))] :
      HasRevCompFunPi₂ α Q :=
    ⟨λ _ => defPi⟩

  instance hasRevCompFunPiFun (α : Sort u) {V : Universe.{u}} {W : Universe} [HasUnivFunctors W W]
                              {B : V} [HasFunctors α B] (Q : B → W) [HasPiType Q]
                              [∀ F : α ⥤ B, HasPiType (λ a => Q (F a))]
                              [HasPiType (λ F : α ⥤ B => Pi (λ a => Q (F a)))]
                              [∀ F : α ⥤ B, HasTrivialDefPi (λ a => Q (F a))]
                              [HasTrivialDefPi (λ F : α ⥤ B => Pi (λ a => Q (F a)))]
                              [HasTrivialFunctoriality W W] :
      HasRevCompFunPiFun α Q :=
    ⟨defFun⟩

  instance hasConstPi (α : Sort u) {V : Universe} (B : V) [HasPiType (Function.const α B)]
                      [HasTrivialDefPi (Function.const α B)] :
      HasConstPi α B :=
    ⟨λ _ => defPi⟩

  instance hasConstPiFun (α : Sort u) {V : Universe} [HasUnivFunctors V V] (B : V)
                         [HasPiType (Function.const α B)] [HasTrivialDefPi (Function.const α B)]
                         [HasTrivialFunctoriality V V] :
      HasConstPiFun α B :=
    ⟨defFun⟩

  instance hasDupPi {α : Sort u} {V : Universe} (P : α → α → V) [∀ a, HasPiType (P a)]
                    [HasPiType (λ a => Pi (P a))] [HasPiType (λ a => P a a)]
                    [HasTrivialDefPi (λ a => P a a)] :
      HasDupPi P :=
    ⟨λ _ => defPi⟩

  instance hasDupPiFun {α : Sort u} {V : Universe} [HasUnivFunctors V V] (P : α → α → V)
                       [∀ a, HasPiType (P a)] [HasPiType (λ a => Pi (P a))]
                       [HasPiType (λ a => P a a)] [HasTrivialDefPi (λ a => P a a)]
                       [HasTrivialFunctoriality V V] :
      HasDupPiFun P :=
    ⟨defFun⟩

  instance hasPiSelfAppPi {U V : Universe.{u}} [HasUnivFunctors V U] {A : U} (Q : A → V)
                          [HasPiType Q] [∀ F : Pi Q ⥤ A, HasPiType (λ G => Q (F G))]
                          [∀ F : Pi Q ⥤ A, HasTrivialDefPi (λ G => Q (F G))] :
      HasPiSelfAppPi Q :=
    ⟨λ _ => defPi⟩

  instance hasPiSelfAppPi₂ {U V : Universe.{u}} [HasUnivFunctors V U] {A : U} (Q : A → V)
                           [HasPiType Q] [∀ F : Pi Q ⥤ A, HasPiType (λ G => Q (F G))]
                           [HasPiType (λ (F : Pi Q ⥤ A) => Pi (λ G => Q (F G)))]
                           [∀ F : Pi Q ⥤ A, HasTrivialDefPi (λ G => Q (F G))]
                           [HasTrivialDefPi (λ (F : Pi Q ⥤ A) => Pi (λ G => Q (F G)))] :
      HasPiSelfAppPi₂ Q :=
    ⟨defPi⟩

  instance hasSubstPi {α : Sort u} {V W : Universe} {P : α → V} [HasPiType P] (Q : ∀ a, P a → W)
                      [∀ a, HasPiType (Q a)] [HasPiType (λ a => Pi (Q a))]
                      [∀ F : Pi P, HasPiType (λ a => Q a (F a))]
                      [∀ F : Pi P, HasTrivialDefPi (λ a => Q a (F a))] :
      HasSubstPi Q :=
    ⟨λ _ _ => defPi⟩

  instance hasRevSubstPi₂ {α : Sort u} {V W : Universe} {P : α → V} [HasPiType P] (Q : ∀ a, P a → W)
                          [∀ a, HasPiType (Q a)] [HasPiType (λ a => Pi (Q a))]
                          [∀ F : Pi P, HasPiType (λ a => Q a (F a))]
                          [HasPiType (λ F : Pi P => Pi (λ a => Q a (F a)))]
                          [∀ F : Pi P, HasTrivialDefPi (λ a => Q a (F a))]
                          [HasTrivialDefPi (λ F : Pi P => Pi (λ a => Q a (F a)))] :
      HasRevSubstPi₂ Q :=
    ⟨λ _ => defPi⟩

  instance hasRevSubstPiFun {α : Sort u} {V W : Universe} [HasUnivFunctors W W] {P : α → V}
                            [HasPiType P] (Q : ∀ a, P a → W) [∀ a, HasPiType (Q a)]
                            [HasPiType (λ a => Pi (Q a))] [∀ F : Pi P, HasPiType (λ a => Q a (F a))]
                            [HasPiType (λ F : Pi P => Pi (λ a => Q a (F a)))]
                            [∀ F : Pi P, HasTrivialDefPi (λ a => Q a (F a))]
                            [HasTrivialDefPi (λ F : Pi P => Pi (λ a => Q a (F a)))]
                            [HasTrivialFunctoriality W W] :
      HasRevSubstPiFun Q :=
    ⟨defFun⟩

end HasTrivialDefPi

open HasTrivialDefPi

namespace HasTrivialFunctoriality

  instance hasFullLogic (U : Universe) [HasUnivFunctors U U] [HasTrivialFunctoriality U U] :
      HasFullLogic U where
    defIdFun       _     := defFun
    defRevAppFun₂  _ _   := defFun₂
    defRevCompFun₃ _ _ _ := defFun₃
    defConstFun₂   _ _   := defFun₂
    defDupFun₂     _ _   := defFun₂

end HasTrivialFunctoriality



class HasTrivialIsomorphismCondition (α : Sort u) {V : Universe} [HasLinearLogic V]
                                     [HasPreorderRelation V α] [h : HasIsomorphismsBase α] where
  [hDefIso (a b : α) : HasTrivialDefInst (h.defIsoType a b)]

namespace HasTrivialIsomorphismCondition

  section

    variable {V : Universe} [HasLinearLogic V]

    instance {α : Sort u} [HasPreorderRelation V α] [hα : HasIsomorphismsBase α]
             [h : HasTrivialIsomorphismCondition α] (a b : α) :
        HasTrivialDefInst (hα.defIsoType a b) :=
      h.hDefIso a b

    def defIso {α : Sort u} [HasPreorderRelation V α] [HasIsomorphismsBase α]
               [HasTrivialIsomorphismCondition α] {a b : α} {toHom : Hom a b} {invHom : Hom b a} :
        a ≃{toHom,invHom} b :=
      defInst

    instance hasIsomorphisms (α : Sort u) [HasPreorderRelation V α] [HasIsomorphismsBase α]
                             [HasTrivialIsomorphismCondition α] [HasTrivialFunctoriality V V] :
        HasIsomorphisms α where
    defRefl         _     := defInst
    defSymm         _     := defInst
    defSymmFun      _ _   := defFun
    defTrans        _ _   := defInst
    defRevTransFun₂ _ _ _ := defFun₂

    instance isIsoFunctor {α : Sort u} {β : Sort u'} [HasPreorderRelation V α] [HasIsomorphisms α]
                          [HasPreorderRelation V β] [HasIsomorphismsBase β]
                          [HasTrivialIsomorphismCondition β] [HasTrivialFunctoriality V V]
                          {F : PreorderFunctor α β} :
        HasIsomorphisms.IsIsoFunctor F where
      defIso    _   := defIso
      defIsoFun _ _ := defFun

    instance isIsoFunctor₂ {α : Sort u} {β : Sort u'} {γ : Sort u''} [HasPreorderRelation V α]
                           [HasIsomorphisms α] [HasPreorderRelation V β] [HasIsomorphisms β]
                           [HasPreorderRelation V γ] [HasIsomorphismsBase γ]
                           [HasTrivialIsomorphismCondition γ] [HasTrivialFunctoriality V V]
                           {F : PreorderFunctor₂ α β γ} :
        HasIsomorphisms.IsIsoFunctor₂ F where
      app  _ := isIsoFunctor
      app₂ _ := isIsoFunctor

  end

  section

    variable (U : Universe) [HasUnivFunctors U U] [HasTrivialFunctoriality U U]
             [HasIsomorphismsBase U] [HasTrivialIsomorphismCondition U]

    instance hasEquivalences : HasEquivalences U := ⟨⟩

  end

  section

    variable {V : Universe} [HasUnivFunctors V V] [HasTrivialFunctoriality V V]
             [HasIsomorphismsBase V] [HasTrivialIsomorphismCondition V]

    instance hasHomEquivalences (α : Sort u) [HasPreorderRelation V α] [HasIsomorphisms α] :
        HasHomEquivalences α := ⟨⟩

    instance hasEquivRelEquivalences (α : Sort u) [HasEquivalenceRelationBase V α] :
        HasEquivRelEquivalences α where
      hEquivEquiv              := hasHomEquivalences (asPreorder α)
      defEquivRelSymmEquiv _ _ := defIso

    instance hasHomIsoEquivalences (α : Sort u) [HasPreorderRelation V α] [HasIsomorphisms α] :
        HasHomIsoEquivalences α := ⟨⟩

  end

  section

    variable (U : Universe) [HasUnivFunctors U U] [HasTrivialFunctoriality U U]
             [HasIsomorphismsBase U] [HasTrivialIsomorphismCondition U]

    instance hasFunEquivEquivalences : HasFunEquivEquivalences U where
      defSwapFunEquiv _ _ _ := defIso

    instance hasTopEquivalences [HasTop U] : HasTopEquivalences U where
      defTopElimEquiv _ := defIso

    instance hasBotEquivalences [HasBot U] : HasBotEquivalences U where
      defBotIntroEquiv    _ := defIso
      defBotIntroEquivFun _ := defFun
      defBotIntroEquiv₂   _ := defIso

    instance hasProductEquivalences [HasInnerProducts U] : HasProductEquivalences U where
      hProdCtor₂              := isIsoFunctor₂
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
      hCoprodCtor₂              := isIsoFunctor₂
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
      defTopEquivFun    _   := defFun
      defTopEquivEquiv  _   := defIso

    instance hasClassicalEquivalences [HasBot U] [HasClassicalLogic U] :
        HasClassicalEquivalences U where
      defNotNotEquiv _ := defIso

  end

end HasTrivialIsomorphismCondition



namespace HasInnerProducts

  -- Convenience definition for cases where isomorphisms are just products.
  def hasIsomorphismsBase (α : Sort u) {V : Universe} [HasAffineLogic V] [HasInnerProducts V]
                          [HasPreorderRelation V α] :
      HasIsomorphismsBase α where
    defIsoType  a b := ⟨(a ⟶ b) ⊓ (b ⟶ a), λ P => ⟨HasProducts.fst P, HasProducts.snd P⟩⟩
    defToHomFun a b := ⟨HasInnerProducts.fstFun (a ⟶ b) (b ⟶ a)⟩

  instance hasTrivialDefIso {α : Sort u} {V : Universe} [HasAffineLogic V] [HasInnerProducts V]
                            [HasPreorderRelation V α] (a b : α) :
      HasTrivialDefInst ((hasIsomorphismsBase α).defIsoType a b) :=
    ⟨λ ⟨toHom, invHom⟩ => ⟨HasProducts.intro toHom invHom⟩⟩

end HasInnerProducts
