import UniverseAbstractions.CategoryTheory.Basic
import UniverseAbstractions.CategoryTheory.Functors
import UniverseAbstractions.CategoryTheory.NaturalTransformations
import UniverseAbstractions.CategoryTheory.MultiFunctors
import UniverseAbstractions.CategoryTheory.MultiFunctorIsomorphisms
import UniverseAbstractions.CategoryTheory.Functors.Nested
import UniverseAbstractions.CategoryTheory.Functors.FunDef



set_option autoBoundImplicitLocal false
set_option maxHeartbeats 500000
--set_option pp.universes true

universe u w ww iw iww



namespace CategoryTheory

  open HasCatProp HasCatProp.Category HasFunProp HasFunProp.Functor HasNatRel HasIsoNat
       HasFunctors HasCongrArg HasLinearFunOp

  namespace IsSortNatUniverse

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W] [IsSortNatUniverse.{u} W]
             [HasLinearCatFun.{u} W]

    def rightIdNat {A B : univ.{u} W} (F : A ⟶ B) {a₁ a₂ : A} (f : a₁ ⇾ a₂) :
      mapHom (F • idFun A) f
      ≃'{F a₁ ⇾ F a₂}
      mapHom F f :=
    mapHom.congrArg F byIdFunDef • byCompFunDef

    def rightIdNatNat (A B : univ.{u} W) {F₁ F₂ : A ⟶ B} (η : F₁ ⇾ F₂) (a : A) :
      nat (mapHom (compFunFun (idFun A) B) η) a
      ≃'{F₁ a ⇾ F₂ a}
      nat (mapHom (idFun (A ⟶ B)) η) a :=
    byCompFunFunDef ▹{nat η a}◃ byAppFunFunDef

    class HasRightIdNat (A B : univ.{u} W) where
    (defRightIdNat (F : A ⟶ B) : StrictDefNatIso (rightIdNat F))
    (defRightIdNatNat : StrictDefNatNatIso defRightIdNat (rightIdNatNat A B))

    def leftIdNat {A B : univ.{u} W} (F : A ⟶ B) {a₁ a₂ : A} (f : a₁ ⇾ a₂) :
      mapHom (idFun B • F) f
      ≃'{F a₁ ⇾ F a₂}
      mapHom F f :=
    byIdFunDef • byCompFunDef

    def leftIdNatNat (A B : univ.{u} W) {F₁ F₂ : A ⟶ B} (η : F₁ ⇾ F₂) (a : A) :
      nat (mapHom (revCompFunFun A (idFun B)) η) a
      ≃'{F₁ a ⇾ F₂ a}
      nat (mapHom (idFun (A ⟶ B)) η) a :=
    byIdFunDef • byRevCompFunFunDef ▹{nat η a}◃ byAppFunFunDef

    class HasLeftIdNat (A B : univ.{u} W) where
    (defLeftIdNat (F : A ⟶ B) : StrictDefNatIso (leftIdNat F))
    (defLeftIdNatNat : StrictDefNatNatIso defLeftIdNat (leftIdNatNat A B))

    def swapRevAppNat {A B : univ.{u} W} (F : A ⟶ B) {a₁ a₂ : A} (f : a₁ ⇾ a₂) :
      mapHom (swapFun (revAppFunFun A B) F) f
      ≃'{F a₁ ⇾ F a₂}
      mapHom F f :=
    byRevAppFunFunDef • bySwapFunDef (F := revAppFunFun A B)

    def swapRevAppNatNat (A B : univ.{u} W) {F₁ F₂ : A ⟶ B} (η : F₁ ⇾ F₂) (a : A) :
      nat (mapHom (swapFunFun (revAppFunFun A B)) η) a
      ≃'{F₁ a ⇾ F₂ a}
      nat (mapHom (appFunFun A B) η) a :=
    byRevAppFunDef • bySwapFunFunDef (F := revAppFunFun A B) ▹{nat η a}◃ byAppFunFunDef

    class HasSwapRevAppNat (A B : univ.{u} W) where
    (defSwapRevAppNat (F : A ⟶ B) : StrictDefNatIso (swapRevAppNat F))
    (defSwapRevAppNatNat : StrictDefNatNatIso defSwapRevAppNat (swapRevAppNatNat A B))

    def swapCompFunNat {A B : univ.{u} W} (F : A ⟶ B) (a : A) (C : univ.{u} W) {G₁ G₂ : B ⟶ C} (ε : G₁ ⇾ G₂) :
      mapHom (swapFun (compFunFun F C) a) ε
      ≃'{G₁ (F a) ⇾ G₂ (F a)}
      mapHom (revAppFun (F a) C) ε :=
    byCompFunFunDef • bySwapFunDef ▹{nat ε (F a)}◃ byRevAppFunDef

    def swapCompFunNatNat {A B : univ.{u} W} (F : A ⟶ B) (C : univ.{u} W) {a₁ a₂ : A} (f : a₁ ⇾ a₂) (G : B ⟶ C) :
      nat (mapHom (swapFunFun (compFunFun F C)) f) G
      ≃'{G (F a₁) ⇾ G (F a₂)}
      nat (mapHom (revAppFunFun B C • F) f) G :=
    byCompFunDef • bySwapFunFunDef (F := compFunFun F C)
    ▹{mapHom G (mapHom F f)}◃
    byRevAppFunFunDef • nat.congrArg (byCompFunDef (G := revAppFunFun B C)) G

    def swapCompFunNatNatNat (A B C : univ.{u} W) {F₁ F₂ : A ⟶ B} (η : F₁ ⇾ F₂) (a : A) (G : B ⟶ C) :
      nat (nat (mapHom (swapFunFunFun (B ⟶ C) A C • compFunFunFun A B C) η) a) G
      ≃'{G (F₁ a) ⇾ G (F₂ a)}
      nat (nat (mapHom (revCompFunFun A (revAppFunFun B C)) η) a) G :=
    byCompFunFunFunDef •
    bySwapFunFunFunDef (η := mapHom (compFunFunFun A B C) η) •
    nat.congrArg (nat.congrArg (byCompFunDef (F := compFunFunFun A B C)
                                             (G := swapFunFunFun (B ⟶ C) A C)
                                             (f := η)) a) G
    ▹{mapHom G (nat η a)}◃
    byRevAppFunFunDef (f := nat η a) •
    nat.congrArg (byRevCompFunFunDef (G := revAppFunFun B C)) G

    class HasSwapCompFunNat (A B C : univ.{u} W) where
    (defSwapCompFunNat (F : A ⟶ B) (a : A) : StrictDefNatIso (swapCompFunNat F a C))
    (defSwapCompFunNatNat (F : A ⟶ B) : StrictDefNatNatIso (defSwapCompFunNat F) (swapCompFunNatNat F C))
    (defSwapCompFunNatNatNat : StrictDefNatNatNatIso defSwapCompFunNatNat (swapCompFunNatNatNat A B C))

    def swapRevCompFunNat {A B C : univ.{u} W} (G : B ⟶ C) (a : A) {F₁ F₂ : A ⟶ B} (η : F₁ ⇾ F₂) :
      mapHom (swapFun (revCompFunFun A G) a) η
      ≃'{G (F₁ a) ⇾ G (F₂ a)}
      mapHom (G • revAppFun a B) η :=
    byRevCompFunFunDef • bySwapFunDef
    ▹{mapHom G (nat η a)}◃
    mapHom.congrArg G byRevAppFunDef • byCompFunDef

    def swapRevCompFunNatNat (A : univ.{u} W) {B C : univ.{u} W} (G : B ⟶ C) {a₁ a₂ : A} (f : a₁ ⇾ a₂) (F : A ⟶ B) :
      nat (mapHom (swapFunFun (revCompFunFun A G)) f) F
      ≃'{G (F a₁) ⇾ G (F a₂)}
      nat (mapHom (revCompFunFun (A ⟶ B) G • revAppFunFun A B) f) F :=
    byCompFunDef •
    bySwapFunFunDef (F := revCompFunFun A G)
    ▹{mapHom G (mapHom F f)}◃
    mapHom.congrArg G byRevAppFunFunDef •
    byRevCompFunFunDef •
    nat.congrArg (byCompFunDef (F := revAppFunFun A B) (G := revCompFunFun (A ⟶ B) G)) F

    def swapRevCompFunNatNatNat (A B C : univ.{u} W) {G₁ G₂ : B ⟶ C} (ε : G₁ ⇾ G₂) (a : A) (F : A ⟶ B) :
      nat (nat (mapHom (swapFunFunFun (A ⟶ B) A C • revCompFunFunFun A B C) ε) a) F
      ≃'{G₁ (F a) ⇾ G₂ (F a)}
      nat (nat (mapHom (compFunFun (revAppFunFun A B) ((A ⟶ B) ⟶ C) • revCompFunFunFun (A ⟶ B) B C) ε) a) F :=
    byRevCompFunFunFunDef •
    bySwapFunFunFunDef (η := mapHom (revCompFunFunFun A B C) ε) •
    nat.congrArg (nat.congrArg (byCompFunDef (F := revCompFunFunFun A B C)
                                             (G := swapFunFunFun (A ⟶ B) A C)
                                             (f := ε)) a) F
    ▹{nat ε (F a)}◃
    byRevCompFunFunFunDef •
    nat.congrArg (byCompFunFunDef (F := revAppFunFun A B) •
                 nat.congrArg (byCompFunDef (F := revCompFunFunFun (A ⟶ B) B C)
                                            (G := compFunFun (revAppFunFun A B) ((A ⟶ B) ⟶ C))
                                            (f := ε)) a) F

    class HasSwapRevCompFunNat (A B C : univ.{u} W) where
    (defSwapRevCompFunNat (G : B ⟶ C) (a : A) : StrictDefNatIso (swapRevCompFunNat G a))
    (defSwapRevCompFunNatNat (G : B ⟶ C) : StrictDefNatNatIso (defSwapRevCompFunNat G) (swapRevCompFunNatNat A G))
    (defSwapRevCompFunNatNatNat : StrictDefNatNatNatIso defSwapRevCompFunNatNat (swapRevCompFunNatNatNat A B C))

    def compAssocNat {A B C D : univ.{u} W} (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) {a₁ a₂ : A} (f : a₁ ⇾ a₂) :
      mapHom ((H • G) • F) f
      ≃'{H (G (F a₁)) ⇾ H (G (F a₂))}
      mapHom (H • (G • F)) f :=
    byCompFunDef • byCompFunDef
    ▹{mapHom H (mapHom G (mapHom F f))}◃
    mapHom.congrArg H byCompFunDef • byCompFunDef

    def compAssocNatNat {A B C : univ.{u} W} (F : A ⟶ B) (G : B ⟶ C) (D : univ.{u} W) {H₁ H₂ : C ⟶ D} (θ : H₁ ⇾ H₂) (a : A) :
      nat (mapHom (compFunFun F D • compFunFun G D) θ) a
      ≃'{H₁ (G (F a)) ⇾ H₂ (G (F a))}
      nat (mapHom (compFunFun (G • F) D) θ) a :=
    byCompFunFunDef • byCompFunFunDef • nat.congrArg byCompFunDef a
    ▹{nat θ (G (F a))}◃
    byCompFunFunDef

    def compAssocNatNatNat {A B : univ.{u} W} (F : A ⟶ B) (C D : univ.{u} W) {G₁ G₂ : B ⟶ C} (ε : G₁ ⇾ G₂) (H : C ⟶ D) (a : A) :
      nat (nat (mapHom (revCompFunFun (C ⟶ D) (compFunFun F D) • compFunFunFun B C D) ε) H) a
      ≃'{H (G₁ (F a)) ⇾ H (G₂ (F a))}
      nat (nat (mapHom (compFunFunFun A C D • compFunFun F C) ε) H) a :=
    byCompFunFunFunDef •
    byCompFunFunDef (ε := nat (mapHom (compFunFunFun B C D) ε) H) •
    nat.congrArg (byRevCompFunFunDef (G := compFunFun F D) •
                  nat.congrArg (byCompFunDef (F := compFunFunFun B C D)
                                             (G := revCompFunFun (C ⟶ D) (compFunFun F D))
                                             (f := ε)) H) a
    ▹{mapHom H (nat ε (F a))}◃
    mapHom.congrArg H byCompFunFunDef •
    byCompFunFunFunDef (η := mapHom (compFunFun F C) ε) •
    nat.congrArg (nat.congrArg (byCompFunDef (F := compFunFun F C)
                                             (G := compFunFunFun A C D)
                                             (f := ε)) H) a

    def compAssocNatNatNatNat (A B C D : univ.{u} W) {F₁ F₂ : A ⟶ B} (η : F₁ ⇾ F₂) (G : B ⟶ C) (H : C ⟶ D) (a : A) :
      nat (nat (nat (mapHom (compFunFun (compFunFunFun B C D) ((C ⟶ D) ⟶ (A ⟶ D)) •
                             revCompFunFunFun (C ⟶ D) (B ⟶ D) (A ⟶ D) •
                             compFunFunFun A B D) η) G) H) a
      ≃'{H (G (F₁ a)) ⇾ H (G (F₂ a))}
      nat (nat (nat (mapHom (revCompFunFun (B ⟶ C) (compFunFunFun A C D) •
                             compFunFunFun A B C) η) G) H) a :=
    byCompFunDef (f := nat η a) •
    byCompFunFunFunDef (G := H • G) •
    nat.congrArg (byRevCompFunFunFunDef (ε := mapHom (compFunFunFun A B D) η)
                                        (F := compFunFun G D) •
                  nat.congrArg (nat.congrArg (byCompFunDef (F := compFunFunFun A B D)
                                                           (G := revCompFunFunFun (C ⟶ D) (B ⟶ D) (A ⟶ D))) (compFunFun G D) •
                                byCompFunFunDef (F := compFunFunFun B C D)
                                                (ε := mapHom (revCompFunFunFun (C ⟶ D) (B ⟶ D) (A ⟶ D) •
                                                              compFunFunFun A B D) η) •
                                nat.congrArg (byCompFunDef (F := revCompFunFunFun (C ⟶ D) (B ⟶ D) (A ⟶ D) •
                                                                 compFunFunFun A B D)
                                                           (G := compFunFun (compFunFunFun B C D) ((C ⟶ D) ⟶ (A ⟶ D)))) G) H) a
    ▹{mapHom H (mapHom G (nat η a))}◃
    mapHom.congrArg H byCompFunFunFunDef •
    byCompFunFunFunDef (η := nat (mapHom (compFunFunFun A B C) η) G) •
    nat.congrArg (nat.congrArg (byRevCompFunFunDef (G := compFunFunFun A C D)
                                                   (η := mapHom (compFunFunFun A B C) η) •
                                nat.congrArg (byCompFunDef (F := compFunFunFun A B C)
                                                           (G := revCompFunFun (B ⟶ C) (compFunFunFun A C D))) G) H) a

    class HasCompAssocNat (A B C D : univ.{u} W) where
    (defCompAssocNat (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) : StrictDefNatIso (compAssocNat F G H))
    (defCompAssocNatNat (F : A ⟶ B) (G : B ⟶ C) : StrictDefNatNatIso (defCompAssocNat F G) (compAssocNatNat F G D))
    (defCompAssocNatNatNat (F : A ⟶ B) : StrictDefNatNatNatIso (defCompAssocNatNat F) (compAssocNatNatNat F C D))
    (defCompAssocNatNatNatNat : StrictDefNatNatNatNatIso defCompAssocNatNatNat (compAssocNatNatNatNat A B C D))

  end IsSortNatUniverse

end CategoryTheory
