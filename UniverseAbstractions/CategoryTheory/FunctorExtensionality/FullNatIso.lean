import UniverseAbstractions.CategoryTheory.Basic
import UniverseAbstractions.CategoryTheory.Functors
import UniverseAbstractions.CategoryTheory.NaturalTransformations
import UniverseAbstractions.CategoryTheory.MultiFunctors
import UniverseAbstractions.CategoryTheory.MultiFunctorIsomorphisms
import UniverseAbstractions.CategoryTheory.Functors.Nested
import UniverseAbstractions.CategoryTheory.Functors.FunDef



set_option autoBoundImplicitLocal false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 2000
--set_option pp.universes true

universe u w ww iw iww



namespace CategoryTheory

  open MetaRelation HasTransFun IsAssociative IsCategoricalPreorder
       HasCatProp HasCatProp.Category HasFunProp HasFunProp.Functor HasNatRel HasNaturality HasIsoNat
       HasLinearFunOp HasSubLinearFunOp HasNonLinearFunOp

  namespace IsSortNatUniverse

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W] [HasSubLinearFunOp W]
             [HasNonLinearFunOp W] [IsSortNatUniverse.{u} W] [HasFullCatFun.{u} W]

    def dupSwapNat {A B : univ.{u} W} (F : A ⟶ A ⟶ B) {a₁ a₂ : A} (f : a₁ ⇾ a₂) :
      mapHom (dupFun (swapFunFun F)) f
      ≃'{dup F a₁ ⇾ dup F a₂}
      mapHom (dupFun F) f :=
    congrArgTrans bySwapFunDef bySwapFunFunDef •
    byDupFunDef' (F := swapFunFun F)
    ▹{mapDupHom F f}◃
    byDupFunDef

    def dupSwapNatNat (A B : univ.{u} W) {F₁ F₂ : A ⟶ A ⟶ B} (η : F₁ ⇾ F₂) (a : A) :
      nat (mapHom (dupFunFun A B • swapFunFunFun A A B) η) a
      ≃'{dup F₁ a ⇾ dup F₂ a}
      nat (mapHom (dupFunFun A B) η) a :=
    bySwapFunFunFunDef •
    byDupFunFunDef (η := mapHom (swapFunFunFun A A B) η) •
    nat.congrArg (byCompFunDef (F := swapFunFunFun A A B) (G := dupFunFun A B)) a
    ▹{nat (nat η a) a}◃
    byDupFunFunDef

    class HasDupSwapNat (A B : univ.{u} W) where
    (defDupSwapNat (F : A ⟶ A ⟶ B) : StrictDefNatIso (φ := λ a => F a a) (dupSwapNat F))
    (defDupSwapNatNat : StrictDefNatNatIso defDupSwapNat (dupSwapNatNat A B))

    def dupConstNat {A B : univ.{u} W} (F : A ⟶ B) {a₁ a₂ : A} (f : a₁ ⇾ a₂) :
      mapHom (dupFun (constFun A F)) f
      ≃'{F a₁ ⇾ F a₂}
      mapHom F f :=
    cancelRightId (nat.reflEq' F a₁ • nat.congrArg (byConstFunDef (b := F) (f := f)) a₁) (mapHom F f) •
    byDupFunDef

    def dupConstNatNat (A B : univ.{u} W) {F₁ F₂ : A ⟶ B} (η : F₁ ⇾ F₂) (a : A) :
      nat (mapHom (dupFunFun A B • constFunFun A (A ⟶ B)) η) a
      ≃'{F₁ a ⇾ F₂ a}
      nat (mapHom (idFun (A ⟶ B)) η) a :=
    nat.congrArg byConstFunFunDef a •
    byDupFunFunDef •
    nat.congrArg (byCompFunDef (F := constFunFun A (A ⟶ B)) (G := dupFunFun A B)) a
    ▹{nat η a}◃
    byAppFunFunDef

    class HasDupConstNat (A B : univ.{u} W) where
    (defDupConstNat (F : A ⟶ B) : StrictDefNatIso (φ := F.φ) (dupConstNat F))
    (defDupConstNatNat : StrictDefNatNatIso defDupConstNat (dupConstNatNat A B))

    def rightDupNat {A B C : univ.{u} W} (F : A ⟶ A ⟶ B) (G : B ⟶ C) {a₁ a₂ : A} (f : a₁ ⇾ a₂) :
      mapHom (dupFun (revCompFunFun A G • F)) f
      ≃'{G (F a₁ a₁) ⇾ G (F a₂ a₂)}
      mapHom (G • dupFun F) f :=
    congrArgTrans (byRevCompFunFunDef • nat.congrArg (byCompFunDef (F := F) (G := revCompFunFun A G)) a₁)
                  (byCompFunDef (F := F a₂) (G := G)) •
    byDupFunDef (F := revCompFunFun A G • F)
    ▹{mapHom G (mapHom (F a₂) f) • mapHom G (nat (mapHom F f) a₁)}◃
    mapHom.transEq G (nat (mapHom F f) a₁) (mapHom (F a₂) f) •
    mapHom.congrArg G byDupFunDef •
    byCompFunDef (F := dupFun F) (G := G)

    def rightDupNatNat {A B : univ.{u} W} (F : A ⟶ A ⟶ B) (C : univ.{u} W) {G₁ G₂ : B ⟶ C} (ε : G₁ ⇾ G₂) (a : A) :
      nat (mapHom (dupFunFun A C • compFunFun F (A ⟶ C) • revCompFunFunFun A B C) ε) a
      ≃'{G₁ (F a a) ⇾ G₂ (F a a)}
      nat (mapHom (compFunFun (dupFun F) C) ε) a :=
    byRevCompFunFunFunDef (F := F a) •
    nat.congrArg (byCompFunFunDef (ε := mapHom (revCompFunFunFun A B C) ε) •
                 nat.congrArg (byCompFunDef (F := revCompFunFunFun A B C) (G := compFunFun F (A ⟶ C))) a) a •
    byDupFunFunDef (η := mapHom (compFunFun F (A ⟶ C) • revCompFunFunFun A B C) ε) •
    nat.congrArg (byCompFunDef (F := compFunFun F (A ⟶ C) • revCompFunFunFun A B C) (G := dupFunFun A C)) a
    ▹{nat ε (F a a)}◃
    byCompFunFunDef (F := dupFun F)

    def rightDupNatNatNat (A B C : univ.{u} W) {F₁ F₂ : A ⟶ A ⟶ B} (η : F₁ ⇾ F₂) (G : B ⟶ C) (a : A) :
      nat (nat (mapHom (revCompFunFun (B ⟶ C) (dupFunFun A C) •
                        compFunFun (revCompFunFunFun A B C) (A ⟶ A ⟶ C) •
                        compFunFunFun A (A ⟶ B) (A ⟶ C)) η) G) a
      ≃'{G (F₁ a a) ⇾ G (F₂ a a)}
      nat (nat (mapHom (compFunFunFun A B C • dupFunFun A B) η) G) a :=
    byRevCompFunFunDef •
    nat.congrArg (byCompFunFunFunDef (G := revCompFunFun A G) •
                  nat.congrArg (byCompFunFunDef (F := revCompFunFunFun A B C)
                                                (ε := mapHom (compFunFunFun A (A ⟶ B) (A ⟶ C)) η) •
                                nat.congrArg (byCompFunDef (F := compFunFunFun A (A ⟶ B) (A ⟶ C))
                                                           (G := compFunFun (revCompFunFunFun A B C) (A ⟶ A ⟶ C))) G) a) a •
    byDupFunFunDef (η := nat (mapHom (compFunFun (revCompFunFunFun A B C) (A ⟶ A ⟶ C) •
                                      compFunFunFun A (A ⟶ B) (A ⟶ C)) η) G) •
    nat.congrArg (byRevCompFunFunDef (G := dupFunFun A C)
                                     (η := mapHom (compFunFun (revCompFunFunFun A B C) (A ⟶ A ⟶ C) •
                                                   compFunFunFun A (A ⟶ B) (A ⟶ C)) η) •
                  nat.congrArg (byCompFunDef (F := compFunFun (revCompFunFunFun A B C) (A ⟶ A ⟶ C) •
                                                   compFunFunFun A (A ⟶ B) (A ⟶ C))
                                             (G := revCompFunFun (B ⟶ C) (dupFunFun A C))) G) a
    ▹{mapHom G (nat (nat η a) a)}◃
    mapHom.congrArg G byDupFunFunDef •
    byCompFunFunFunDef (η := mapHom (dupFunFun A B) η) •
    nat.congrArg (nat.congrArg (byCompFunDef (F := dupFunFun A B) (G := compFunFunFun A B C)) G) a

    class HasRightDupNat (A B C : univ.{u} W) where
    (defRightDupNat (F : A ⟶ A ⟶ B) (G : B ⟶ C) : StrictDefNatIso (φ := λ a => G (F a a)) (rightDupNat F G))
    (defRightDupNatNat (F : A ⟶ A ⟶ B) : StrictDefNatNatIso (defRightDupNat F) (rightDupNatNat F C))
    (defRightDupNatNatNat : StrictDefNatNatNatIso defRightDupNatNat (rightDupNatNatNat A B C))

    def substDupNat {A B C : univ.{u} W} (F : A ⟶ B) (G : A ⟶ B ⟶ B ⟶ C) {a₁ a₂ : A} (f : a₁ ⇾ a₂) :
      mapHom (substFun F (dupFunFun B C • G)) f
      ≃'{G a₁ (F a₁) (F a₁) ⇾ G a₂ (F a₂) (F a₂)}
      mapHom (substFun F (substFun F G)) f :=
    assoc (nat (nat (mapHom G f) (F a₁)) (F a₁))
          (nat (mapHom (G a₂) (mapHom F f)) (F a₁))
          (mapHom (G a₂ (F a₂)) (mapHom F f)) •
    congrArgTrans (byDupFunFunDef (η := mapHom G f) (a := F a₁) •
                   nat.congrArg (byCompFunDef (F := G) (G := dupFunFun B C)) (F a₁))
                  (byDupFunDef (F := G a₂)) •
    bySubstFunDef (F := F) (G := dupFunFun B C • G) (f := f)
    ▹{mapHom (G a₂ (F a₂)) (mapHom F f) •
      nat (mapHom (G a₂) (mapHom F f)) (F a₁) •
      nat (nat (mapHom G f) (F a₁)) (F a₁)}◃
    congrArgTransRight (nat.transEq' (nat (mapHom G f) (F a₁)) (mapHom (G a₂) (mapHom F f)) (F a₁) •
                        nat.congrArg (bySubstFunDef (F := F) (G := G) (f := f)) (F a₁)) (mapHom (G a₂ (F a₂))
                       (mapHom F f)) •
    bySubstFunDef (F := F) (G := substFun F G) (f := f)

    def substDupNatNat {A B : univ.{u} W} (F : A ⟶ B) (C : univ.{u} W) {G₁ G₂ : A ⟶ B ⟶ B ⟶ C} (ε : G₁ ⇾ G₂) (a : A) :
      nat (mapHom (substFunFun F C • revCompFunFun A (dupFunFun B C)) ε) a
      ≃'{G₁ a (F a) (F a) ⇾ G₂ a (F a) (F a)}
      nat (mapHom (substFunFun F C • substFunFun F (B ⟶ C)) ε) a :=
    let e₁ : nat (mapHom (substFunFun F C) (mapHom (revCompFunFun A (dupFunFun B C)) ε)) a ≃'
             nat (nat (nat ε a) (F a)) (F a) :=
        byDupFunFunDef (η := nat ε a) (a := F a) •
        nat.congrArg (byRevCompFunFunDef (G := dupFunFun B C)) (F a) •
        bySubstFunFunDef (ε := mapHom (revCompFunFun A (dupFunFun B C)) ε);
    let e₂ : nat (mapHom (substFunFun F C) (mapHom (substFunFun F (B ⟶ C)) ε)) a ≃'
             nat (nat (nat ε a) (F a)) (F a) :=
        nat.congrArg bySubstFunFunDef (F a) •
        bySubstFunFunDef (ε := mapHom (substFunFun F (B ⟶ C)) ε);
    e₁ •
    nat.congrArg (byCompFunDef (F := revCompFunFun A (dupFunFun B C))) a
    ▹{nat (nat (nat ε a) (F a)) (F a)}◃
    e₂ •
    nat.congrArg (byCompFunDef (F := substFunFun F (B ⟶ C))) a

    def substDupNatNatNat (A B C : univ.{u} W) {F₁ F₂ : A ⟶ B} (η : F₁ ⇾ F₂) (G : A ⟶ B ⟶ B ⟶ C) (a : A) :
      nat (nat (mapHom (compFunFun (revCompFunFun A (dupFunFun B C)) (A ⟶ C) • substFunFunFun A B C) η) G) a
      ≃'{G a (F₁ a) (F₁ a) ⇾ G a (F₂ a) (F₂ a)}
      nat (nat (mapHom (substFun (substFunFunFun A B C) (compFunFunFun (A ⟶ B ⟶ B ⟶ C) (A ⟶ B ⟶ C) (A ⟶ C) •
                                                         substFunFunFun A B (B ⟶ C))) η) G) a :=
    byDupFunDef (F := G a) (f := nat η a) •
    bySubstFunFunFunDef (G := dupFunFun B C • G) •
    nat.congrArg (byCompFunFunDef (F := revCompFunFun A (dupFunFun B C))
                                  (ε := mapHom (substFunFunFun A B C) η) •
                  nat.congrArg (byCompFunDef (F := substFunFunFun A B C)
                                             (G := compFunFun (revCompFunFun A (dupFunFun B C)) (A ⟶ C))) G) a
    ▹{mapDupHom (G a) (nat η a)}◃
    congrArgTrans (nat.congrArg bySubstFunFunFunDef (F₁ a) •
                   bySubstFunFunDef (ε := nat (mapHom (substFunFunFun A B (B ⟶ C)) η) G))
                  (bySubstFunFunFunDef (G := substFun F₂ G)) •
    nat.transEq' (mapHom (substFunFun F₁ C) (nat (mapHom (substFunFunFun A B (B ⟶ C)) η) G))
                 (nat (mapHom (substFunFunFun A B C) η) (HasFunctors.apply (substFunFun F₂ (B ⟶ C)) G))
                 a •
    nat.congrArg (congrArgTrans (byCompFunFunFunDef (η := mapHom (substFunFunFun A B (B ⟶ C)) η))
                                (byCompFunFunDef (ε := mapHom (substFunFunFun A B C) η)) •
                  nat.transEq' (nat (mapHom (compFunFunFun (A ⟶ B ⟶ B ⟶ C) (A ⟶ B ⟶ C) (A ⟶ C))
                                            (mapHom (substFunFunFun A B (B ⟶ C)) η))
                                    (substFunFun F₁ C))
                               (mapHom (compFunFun (substFunFun F₂ (B ⟶ C)) (A ⟶ C))
                                       (mapHom (substFunFunFun A B C) η))
                               G •
                  nat.congrArg (congrArgTransRight (nat.congrArg (byCompFunDef (F := substFunFunFun A B (B ⟶ C))
                                                                               (G := compFunFunFun (A ⟶ B ⟶ B ⟶ C) (A ⟶ B ⟶ C) (A ⟶ C)))
                                                                 (substFunFun F₁ C))
                                                   (mapHom (compFunFun (substFunFun F₂ (B ⟶ C)) (A ⟶ C))
                                                           (mapHom (substFunFunFun A B C) η)) •
                                bySubstFunDef (F := substFunFunFun A B C)) G) a

    class HasSubstDupNat (A B C : univ.{u} W) where
    (defSubstDupNat (F : A ⟶ B) (G : A ⟶ B ⟶ B ⟶ C) : StrictDefNatIso (φ := λ a => G a (F a) (F a)) (substDupNat F G))
    (defSubstDupNatNat (F : A ⟶ B) : StrictDefNatNatIso (defSubstDupNat F) (substDupNatNat F C))
    (defSubstDupNatNatNat : StrictDefNatNatNatIso defSubstDupNatNat (substDupNatNatNat A B C))

  end IsSortNatUniverse

end CategoryTheory
