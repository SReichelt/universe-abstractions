import UniverseAbstractions.Axioms.CategoryTheory.Basic
import UniverseAbstractions.Axioms.CategoryTheory.Functors
import UniverseAbstractions.Axioms.CategoryTheory.NaturalTransformations
import UniverseAbstractions.Axioms.CategoryTheory.Isomorphisms



set_option autoBoundImplicitLocal false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000
--set_option pp.universes true

universe u w ww iw iww



namespace CategoryTheory

  open MetaRelation HasTransFun HasSymmFun IsAssociative IsCategoricalPreorder
       HasCatProp HasCatProp.Category HasFunProp HasFunProp.Functor HasNatRel HasNatOp HasNatOpEquiv HasNaturality
       HasIsoRel HasIsoOp HasIsomorphisms HasIsoNat HasIsoNaturality
       HasFunctors HasCongrArg HasLinearFunOp HasSubLinearFunOp HasNonLinearFunOp

  namespace IsIsoUniverse

    section

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W] [IsCatUniverse.{u} W]
               [IsFunUniverse.{u} W] [IsNatUniverse.{u} W] [h : IsIsoUniverse.{u} W]

      section

        variable [IsFunUniverse.HasLinearFunctors W] [IsNatUniverse.HasLinearFunctors W]

        -- `mapHom` definitions of linear combinators

        def byIdFunDef {A : univ W} {a₁ a₂ : A} {f : a₁ ⇾ a₂} :
          mapHom (idFun A) f ≃' f :=
        DefFun.byMapHomDef

        def byAppFunFunDef {A B : univ W} {F₁ F₂ : A ⟶ B} {η : F₁ ⇾ F₂} {a : A} :
          nat (mapHom (appFunFun A B) η) a ≃' nat η a :=
        natCongrArg byIdFunDef a

        def byRevAppFunDef {A B : univ W} {a : A} {F₁ F₂ : A ⟶ B} {η : F₁ ⇾ F₂} :
          mapHom (revAppFun a B) η ≃' nat η a :=
        DefFun.byMapHomDef

        def byRevAppFunFunDef {A B : univ W} {a₁ a₂ : A} {f : a₁ ⇾ a₂} {F : A ⟶ B} :
          nat (mapHom (revAppFunFun A B) f) F ≃' mapHom F f :=
        DefFunFun.byFunFunDef

        def byCompFunDef {A B C : univ W} {F : A ⟶ B} {G : B ⟶ C} {a₁ a₂ : A} {f : a₁ ⇾ a₂} :
          mapHom (G • F) f ≃' mapHom G (mapHom F f) :=
        DefFun.byMapHomDef

        def byCompFunFunDef {A B C : univ W} {F : A ⟶ B} {G₁ G₂ : B ⟶ C} {ε : G₁ ⇾ G₂} {a : A} :
          nat (mapHom (compFunFun F C) ε) a ≃' nat ε (F a) :=
        DefFunFun.byFunFunDef

        def byCompFunFunFunDef {A B C : univ W} {F₁ F₂ : A ⟶ B} {η : F₁ ⇾ F₂} {G : B ⟶ C} {a : A} :
          nat (nat (mapHom (compFunFunFun A B C) η) G) a ≃' mapHom G (nat η a) :=
        DefFunFunFun.byFunFunFunDef

        def bySwapFunDef {A B C : univ W} {F : A ⟶ B ⟶ C} {b : B} {a₁ a₂ : A} {f : a₁ ⇾ a₂} :
          mapHom (swapFun F b) f ≃' nat (mapHom F f) b :=
        byRevAppFunDef • byCompFunDef

        def bySwapFunFunDef {A B C : univ W} {F : A ⟶ B ⟶ C} {b₁ b₂ : B} {g : b₁ ⇾ b₂} {a : A} :
          nat (mapHom (swapFunFun F) g) a ≃' mapHom (F a) g :=
        byRevAppFunFunDef • byCompFunFunDef • natCongrArg byCompFunDef a

        def bySwapFunFunFunDef {A B C : univ W} {F₁ F₂ : A ⟶ B ⟶ C} {η : F₁ ⇾ F₂} {a : A} {b : B} :
          nat (nat (mapHom (swapFunFunFun A B C) η) b) a ≃' nat (nat η a) b :=
        byRevAppFunDef •
        byCompFunFunFunDef •
        natCongrArg (byCompFunFunDef • natCongrArg byCompFunDef b) a

        def byRevCompFunFunDef {A B C : univ W} {G : B ⟶ C} {F₁ F₂ : A ⟶ B} {η : F₁ ⇾ F₂} {a : A} :
          nat (mapHom (revCompFunFun A G) η) a ≃' mapHom G (nat η a) :=
        byCompFunFunFunDef • natCongrArg bySwapFunDef a

        def byRevCompFunFunFunDef {A B C : univ W} {G₁ G₂ : B ⟶ C} {ε : G₁ ⇾ G₂} {F : A ⟶ B} {a : A} :
          nat (nat (mapHom (revCompFunFunFun A B C) ε) F) a ≃' nat ε (F a) :=
        byCompFunFunDef • natCongrArg bySwapFunFunDef a

        -- `NatIsoDesc` instances for axioms in `HasLinearFunExt`

        def rightIdNatDesc {A B : univ W} (F : A ⟶ B) : NatIsoDesc (F • idFun A) F :=
        NatIsoDesc.strict (λ _ => mapHomCongrArg F byIdFunDef • byCompFunDef)

        class HasRightIdNat (A B : univ W) where
        (defRightIdNat (F : A ⟶ B) : DefNatIso (rightIdNatDesc F))

        def rightIdNatNatDesc (A B : univ W) [h : HasRightIdNat A B] :
          NatNatIsoDesc (compFunFun (idFun A) B) (idFun (A ⟶ B)) (λ F => (h.defRightIdNat F).η) :=
        NatNatIsoDesc.strict (λ _ _ => byCompFunFunDef ⑅ byAppFunFunDef)

        class HasRightIdNatNat (A B : univ W) extends HasRightIdNat A B where
        (defRightIdNatNat : DefNatNatIso (rightIdNatNatDesc A B))

        def leftIdNatDesc {A B : univ W} (F : A ⟶ B) : NatIsoDesc (idFun B • F) F :=
        NatIsoDesc.strict (λ _ => byIdFunDef • byCompFunDef)

        class HasLeftIdNat (A B : univ W) where
        (defLeftIdNat (F : A ⟶ B) : DefNatIso (leftIdNatDesc F))

        def leftIdNatNatDesc (A B : univ W) [h : HasLeftIdNat A B] :
          NatNatIsoDesc (revCompFunFun A (idFun B)) (idFun (A ⟶ B)) (λ F => (h.defLeftIdNat F).η) :=
        NatNatIsoDesc.strict (λ _ _ => byIdFunDef • byRevCompFunFunDef ⑅ byAppFunFunDef)

        class HasLeftIdNatNat (A B : univ W) extends HasLeftIdNat A B where
        (defLeftIdNatNat : DefNatNatIso (leftIdNatNatDesc A B))

        def swapRevAppNatDesc {A B : univ W} (F : A ⟶ B) :
          NatIsoDesc (swapFun (revAppFunFun A B) F) F :=
        NatIsoDesc.strict (λ _ => byRevAppFunFunDef • bySwapFunDef)

        class HasSwapRevAppNat (A B : univ W) where
        (defSwapRevAppNat (F : A ⟶ B) : DefNatIso (swapRevAppNatDesc F))

        def swapRevAppNatNatDesc (A B : univ W) [h : HasSwapRevAppNat A B] :
          NatNatIsoDesc (swapFunFun (revAppFunFun A B)) (appFunFun A B) (λ F => (h.defSwapRevAppNat F).η) :=
        NatNatIsoDesc.strict (λ η a => byRevAppFunDef (a := a) (η := η) • bySwapFunFunDef (F := revAppFunFun A B) ⑅
                                       byAppFunFunDef (η := η) (a := a))

        class HasSwapRevAppNatNat (A B : univ W) extends HasSwapRevAppNat A B where
        (defSwapRevAppNatNat : DefNatNatIso (swapRevAppNatNatDesc A B))

        def swapCompFunNatDesc {A B : univ W} (F : A ⟶ B) (a : A) (C : univ W) :
          NatIsoDesc (swapFun (compFunFun F C) a) (revAppFun (F a) C) :=
        NatIsoDesc.strict (λ _ => byCompFunFunDef • bySwapFunDef ⑅ byRevAppFunDef)

        class HasSwapCompFunNat (A B C : univ W) where
        (defSwapCompFunNat (F : A ⟶ B) (a : A) : DefNatIso (swapCompFunNatDesc F a C))

        def swapCompFunNatNatDesc {A B : univ W} (F : A ⟶ B) (C : univ W) [h : HasSwapCompFunNat A B C] :
          NatNatIsoDesc (swapFunFun (compFunFun F C)) (revAppFunFun B C • F)
                        (λ a => (h.defSwapCompFunNat F a).η) :=
        NatNatIsoDesc.strict (λ _ G => byCompFunDef • bySwapFunFunDef (F := compFunFun F C) ⑅
                                       byRevAppFunFunDef • natCongrArg byCompFunDef G)

        class HasSwapCompFunNatNat (A B C : univ W) extends HasSwapCompFunNat A B C where
        (defSwapCompFunNatNat (F : A ⟶ B) : DefNatNatIso (swapCompFunNatNatDesc F C))

        def swapCompFunNatNatNat₁ {A B C : univ W} {F₁ F₂ : A ⟶ B} (η : F₁ ⇾ F₂) (a : A) (G : B ⟶ C) :
          nat (nat (mapHom (swapFunFunFun (B ⟶ C) A C • compFunFunFun A B C) η) a) G ≃'
          mapHom G (nat η a) :=
        byCompFunFunFunDef •'
        bySwapFunFunFunDef (η := mapHom (compFunFunFun A B C) η) •'
        natCongrArg (natCongrArg (byCompFunDef (F := compFunFunFun A B C) (G := swapFunFunFun (B ⟶ C) A C) (f := η)) a) G

        def swapCompFunNatNatNat₂ {A B C : univ W} {F₁ F₂ : A ⟶ B} (η : F₁ ⇾ F₂) (a : A) (G : B ⟶ C) :
          nat (nat (mapHom (revCompFunFun A (revAppFunFun B C)) η) a) G ≃'
          mapHom G (nat η a) :=
        byRevAppFunFunDef (f := nat η a) •'
        natCongrArg (byRevCompFunFunDef (G := revAppFunFun B C)) G

        def swapCompFunNatNatNatDesc (A B C : univ W) [h : HasSwapCompFunNatNat A B C] :
          NatNatNatIsoDesc (swapFunFunFun (B ⟶ C) A C • compFunFunFun A B C)
                           (revCompFunFun A (revAppFunFun B C))
                           (λ F => (h.defSwapCompFunNatNat F).η) :=
        NatNatNatIsoDesc.strict (λ η a G => swapCompFunNatNatNat₁ η a G ⑅ swapCompFunNatNatNat₂ η a G)

        class HasSwapCompFunNatNatNat (A B C : univ W) extends HasSwapCompFunNatNat A B C where
        (defSwapCompFunNatNatNat : DefNatNatNatIso (swapCompFunNatNatNatDesc A B C))

        def swapRevCompFunNatDesc {A B C : univ W} (F : B ⟶ C) (a : A) :
          NatIsoDesc (swapFun (revCompFunFun A F) a) (F • revAppFun a B) :=
        NatIsoDesc.strict (λ _ => byRevCompFunFunDef • bySwapFunDef ⑅
                                  mapHomCongrArg F byRevAppFunDef • byCompFunDef)

        class HasSwapRevCompFunNat (A B C : univ W) where
        (defSwapRevCompFunNat (F : B ⟶ C) (a : A) : DefNatIso (swapRevCompFunNatDesc F a))

        def swapRevCompFunNatNatDesc (A : univ W) {B C : univ W} (G : B ⟶ C) [h : HasSwapRevCompFunNat A B C] :
          NatNatIsoDesc (swapFunFun (revCompFunFun A G)) (revCompFunFun (A ⟶ B) G • revAppFunFun A B)
                        (λ a => (h.defSwapRevCompFunNat G a).η) :=
        NatNatIsoDesc.strict (λ _ F => byCompFunDef •
                                       bySwapFunFunDef (F := revCompFunFun A G)
                                       ⑅
                                       mapHomCongrArg G byRevAppFunFunDef •
                                       byRevCompFunFunDef •
                                       natCongrArg byCompFunDef F)

        class HasSwapRevCompFunNatNat (A B C : univ W) extends HasSwapRevCompFunNat A B C where
        (defSwapRevCompFunNatNat (G : B ⟶ C) : DefNatNatIso (swapRevCompFunNatNatDesc A G))

        def swapRevCompFunNatNatNat₁ {A B C : univ W} {G₁ G₂ : B ⟶ C} (ε : G₁ ⇾ G₂) (a : A) (F : A ⟶ B) :
          nat (nat (mapHom (swapFunFunFun (A ⟶ B) A C • revCompFunFunFun A B C) ε) a) F ≃'
          nat ε (F a) :=
        byRevCompFunFunFunDef •'
        bySwapFunFunFunDef (η := mapHom (revCompFunFunFun A B C) ε) •'
        natCongrArg (natCongrArg (byCompFunDef (F := revCompFunFunFun A B C)
                                               (G := swapFunFunFun (A ⟶ B) A C)
                                               (f := ε)) a) F

        def swapRevCompFunNatNatNat₂ {A B C : univ W} {G₁ G₂ : B ⟶ C} (ε : G₁ ⇾ G₂) (a : A) (F : A ⟶ B) :
          nat (nat (mapHom (compFunFun (revAppFunFun A B) ((A ⟶ B) ⟶ C) • revCompFunFunFun (A ⟶ B) B C) ε) a) F ≃'
          nat ε (F a) :=
        byRevCompFunFunFunDef •'
        natCongrArg (byCompFunFunDef (F := revAppFunFun A B) •'
                     natCongrArg (byCompFunDef (F := revCompFunFunFun (A ⟶ B) B C)
                                               (G := compFunFun (revAppFunFun A B) ((A ⟶ B) ⟶ C))
                                               (f := ε)) a) F

        def swapRevCompFunNatNatNatDesc (A B C : univ W) [h : HasSwapRevCompFunNatNat A B C] :
          NatNatNatIsoDesc (swapFunFunFun (A ⟶ B) A C • revCompFunFunFun A B C)
                           (compFunFun (revAppFunFun A B) ((A ⟶ B) ⟶ C) • revCompFunFunFun (A ⟶ B) B C)
                           (λ G => (h.defSwapRevCompFunNatNat G).η) :=
        NatNatNatIsoDesc.strict (λ ε a F => swapRevCompFunNatNatNat₁ ε a F ⑅ swapRevCompFunNatNatNat₂ ε a F)

        class HasSwapRevCompFunNatNatNat (A B C : univ W) extends HasSwapRevCompFunNatNat A B C where
        (defSwapRevCompFunNatNatNat : DefNatNatNatIso (swapRevCompFunNatNatNatDesc A B C))

        def compAssocNatDesc {A B C D : univ W} (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) :
          NatIsoDesc ((H • G) • F) (H • (G • F)) :=
        NatIsoDesc.strict (λ _ => byCompFunDef • byCompFunDef ⑅
                                  mapHomCongrArg H byCompFunDef • byCompFunDef)

        class HasCompAssocNat (A B C D : univ W) where
        (defCompAssocNat (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) : DefNatIso (compAssocNatDesc F G H))

        def compAssocNatNatDesc {A B C : univ W} (F : A ⟶ B) (G : B ⟶ C) (D : univ W)
                                [h : HasCompAssocNat A B C D] :
          NatNatIsoDesc (compFunFun F D • compFunFun G D) (compFunFun (G • F) D)
                        (λ H => (h.defCompAssocNat F G H).η) :=
        NatNatIsoDesc.strict (λ _ b => byCompFunFunDef • byCompFunFunDef • natCongrArg byCompFunDef b ⑅
                                       byCompFunFunDef)

        class HasCompAssocNatNat (A B C D : univ W) extends HasCompAssocNat A B C D where
        (defCompAssocNatNat (F : A ⟶ B) (G : B ⟶ C) : DefNatNatIso (compAssocNatNatDesc F G D))

        def compAssocNatNatNatDesc {A B : univ W} (F : A ⟶ B) (C D : univ W)
                                   [h : HasCompAssocNatNat A B C D] :
          NatNatNatIsoDesc (revCompFunFun (C ⟶ D) (compFunFun F D) • compFunFunFun B C D)
                           (compFunFunFun A C D • compFunFun F C)
                           (λ G => (h.defCompAssocNatNat F G).η) :=
        NatNatNatIsoDesc.strict (λ ε H a => byCompFunFunFunDef •
                                            byCompFunFunDef •
                                            natCongrArg (byRevCompFunFunDef •
                                                         natCongrArg byCompFunDef H) a
                                            ⑅
                                            mapHomCongrArg H byCompFunFunDef •
                                            byCompFunFunFunDef •
                                            natCongrArg (natCongrArg byCompFunDef H) a)

        class HasCompAssocNatNatNat (A B C D : univ W) extends HasCompAssocNatNat A B C D where
        (defCompAssocNatNatNat (F : A ⟶ B) : DefNatNatNatIso (compAssocNatNatNatDesc F C D))

        class HasCompAssocNatNatNatNat (A B C D : univ W) extends HasCompAssocNatNatNat A B C D where

      end

      section

        variable [HasSubLinearFunOp W] [IsFunUniverse.HasAffineFunctors W]
                 [IsNatUniverse.HasAffineFunctors W]

        -- `mapHom` definitions of sublinear combinators

        def byConstFunDef {A B : univ W} {b : B} {a₁ a₂ : A} {f : a₁ ⇾ a₂} :
          mapHom (constFun A b) f ≃' idHom b :=
        DefFun.byMapHomDef

        def byConstFunFunDef {A B : univ W} {b₁ b₂ : B} {g : b₁ ⇾ b₂} {a : A} :
          nat (mapHom (constFunFun A B) g) a ≃' g :=
        DefFunFun.byFunFunDef

        -- `NatIsoDesc` instances for axioms in `HasAffineFunExt`

        def rightConstNatDesc (A : univ W) {B C : univ W} (b : B) (G : B ⟶ C) :
          NatIsoDesc (G • constFun A b) (constFun A (G b)) :=
        NatIsoDesc.strict (λ _ => reflEq G b • mapHomCongrArg G byConstFunDef • byCompFunDef ⑅
                                  byConstFunDef)

        class HasRightConstNat (A B C : univ W) where
        (defRightConstNat (b : B) (G : B ⟶ C) : DefNatIso (rightConstNatDesc A b G))

        def rightConstNatNatDesc (A : univ W) {B : univ W} (b : B) (C : univ W)
                                 [h : HasRightConstNat A B C] :
          NatNatIsoDesc (compFunFun (constFun A b) C) (constFunFun A C • revAppFun b C)
                        (λ G => (h.defRightConstNat b G).η) :=
        NatNatIsoDesc.strict (λ _ a => byCompFunFunDef
                                       ⑅
                                       byRevAppFunDef •
                                       byConstFunFunDef •
                                       natCongrArg byCompFunDef a)

        class HasRightConstNatNat (A B C : univ W) extends HasRightConstNat A B C where
        (defRightConstNatNat (b : B) : DefNatNatIso (rightConstNatNatDesc A b C))

        def rightConstNatNatNatDesc (A B C : univ W) [h : HasRightConstNatNat A B C] :
          NatNatNatIsoDesc (compFunFunFun A B C • constFunFun A B)
                           (revCompFunFun (B ⟶ C) (constFunFun A C) • revAppFunFun B C)
                           (λ b => (h.defRightConstNatNat b).η) :=
        NatNatNatIsoDesc.strict (λ _ G a => mapHomCongrArg G byConstFunFunDef •
                                            byCompFunFunFunDef •
                                            natCongrArg (natCongrArg byCompFunDef G) a
                                            ⑅
                                            byRevAppFunFunDef •
                                            byConstFunFunDef •
                                            natCongrArg (byRevCompFunFunDef •
                                                         natCongrArg byCompFunDef G) a)

        class HasRightConstNatNatNat (A B C : univ W) extends HasRightConstNatNat A B C where
        (defRightConstNatNatNat : DefNatNatNatIso (rightConstNatNatNatDesc A B C))

        def leftConstNatDesc {A B C : univ W} (F : A ⟶ B) (c : C) :
          NatIsoDesc (constFun B c • F) (constFun A c) :=
        NatIsoDesc.strict (λ _ => byConstFunDef • byCompFunDef ⑅ byConstFunDef)

        class HasLeftConstNat (A B C : univ W) where
        (defLeftConstNat (F : A ⟶ B) (c : C) : DefNatIso (leftConstNatDesc F c))

        class HasLeftConstNatNat (A B C : univ W) extends HasLeftConstNat A B C where

        class HasLeftConstNatNatNat (A B C : univ W) extends HasLeftConstNatNat A B C where

      end

      section

        variable [HasSubLinearFunOp W] [HasNonLinearFunOp W] [IsFunUniverse.HasAffineFunctors W]
                 [IsNatUniverse.HasFullFunctors W]

        -- `mapHom` definitions of nonlinear combinators

        def byDupFunDef {A B : univ W} {F : A ⟶ A ⟶ B} {a₁ a₂ : A} {f : a₁ ⇾ a₂} :
          mapHom (dupFun F) f ≃' mapDupHom F f :=
        DefFun.byMapHomDef

        def byDupFunDef' {A B : univ W} {F : A ⟶ A ⟶ B} {a₁ a₂ : A} {f : a₁ ⇾ a₂} :
          mapHom (dupFun F) f ≃' mapDupHom' F f :=
        (mapDupHomEq F f)⁻¹ • byDupFunDef

        def byDupFunFunDef {A B : univ W} {F₁ F₂ : A ⟶ A ⟶ B} {η : F₁ ⇾ F₂} {a : A} :
          nat (mapHom (dupFunFun A B) η) a ≃' nat (nat η a) a :=
        DefFunFun.byFunFunDef

        def bySubstFunDef {A B C : univ W} {F : A ⟶ B} {G : A ⟶ B ⟶ C} {a₁ a₂ : A} {f : a₁ ⇾ a₂} :
          mapHom (substFun F G) f ≃' mapHom (G a₂) (mapHom F f) • nat (mapHom G f) (F a₁) :=
        congrArgTrans (byCompFunFunDef • natCongrArg byCompFunDef a₁) byCompFunDef • byDupFunDef

        def bySubstFunDef' {A B C : univ W} {F : A ⟶ B} {G : A ⟶ B ⟶ C} {a₁ a₂ : A} {f : a₁ ⇾ a₂} :
          mapHom (substFun F G) f ≃' nat (mapHom G f) (F a₂) • mapHom (G a₁) (mapHom F f) :=
        congrArgTrans byCompFunDef (byCompFunFunDef • natCongrArg byCompFunDef a₂) • byDupFunDef'

        -- `NatIsoDesc` instances for axioms in `HasFullFunExt`

        def dupSwapNatDesc {A B : univ W} (F : A ⟶ A ⟶ B) :
          NatIsoDesc (dupFun (swapFunFun F)) (dupFun F) :=
        NatIsoDesc.strict (λ _ => congrArgTrans bySwapFunDef bySwapFunFunDef •
                                  byDupFunDef' (F := swapFunFun F)
                                  ⑅
                                  byDupFunDef)

        class HasDupSwapNat (A B : univ W) where
        (defDupSwapNat (F : A ⟶ A ⟶ B) : DefNatIso (dupSwapNatDesc F))

        def dupSwapNatNatDesc (A B : univ W) [h : HasDupSwapNat A B] :
          NatNatIsoDesc (dupFunFun A B • swapFunFunFun A A B) (dupFunFun A B)
                        (λ F => (h.defDupSwapNat F).η) :=
        NatNatIsoDesc.strict (λ η a => bySwapFunFunFunDef •
                                       byDupFunFunDef (η := mapHom (swapFunFunFun A A B) η) •
                                       natCongrArg byCompFunDef a
                                       ⑅
                                       byDupFunFunDef)

        class HasDupSwapNatNat (A B : univ W) extends HasDupSwapNat A B where
        (defDupSwapNatNat : DefNatNatIso (dupSwapNatNatDesc A B))

        def dupConstNatDesc {A B : univ W} (F : A ⟶ B) :
          NatIsoDesc (dupFun (constFun A F)) F :=
        NatIsoDesc.strict (λ {a₁ a₂} f => cancelRightId (natReflEq' F a₁ • natCongrArg byConstFunDef a₁)
                                                        (mapHom F f) •
                                          byDupFunDef)

        class HasDupConstNat (A B : univ W) where
        (defDupConstNat (F : A ⟶ B) : DefNatIso (dupConstNatDesc F))

        def dupConstNatNatDesc (A B : univ W) [h : HasDupConstNat A B] :
          NatNatIsoDesc (dupFunFun A B • constFunFun A (A ⟶ B)) (idFun (A ⟶ B))
                        (λ F => (h.defDupConstNat F).η) :=
        NatNatIsoDesc.strict (λ f a => natCongrArg (byIdFunDef⁻¹ • byConstFunFunDef) a •
                                       byDupFunFunDef •
                                       natCongrArg byCompFunDef a)

        class HasDupConstNatNat (A B : univ W) extends HasDupConstNat A B where
        (defDupConstNatNat : DefNatNatIso (dupConstNatNatDesc A B))

        def rightDupNat₁ {A B C : univ W} (F : A ⟶ A ⟶ B) (G : B ⟶ C) {a₁ a₂ : A} (f : a₁ ⇾ a₂) :
          mapHom (dupFun (revCompFunFun A G • F)) f ≃'
          mapHom G (mapHom (F a₂) f) • mapHom G (nat (mapHom F f) a₁) :=
        congrArgTrans (byRevCompFunFunDef • natCongrArg byCompFunDef a₁) byCompFunDef •
        byDupFunDef

        def rightDupNat₂ {A B C : univ W} (F : A ⟶ A ⟶ B) (G : B ⟶ C) {a₁ a₂ : A} (f : a₁ ⇾ a₂) :
          mapHom (G • dupFun F) f ≃'
          mapHom G (mapHom (F a₂) f) • mapHom G (nat (mapHom F f) a₁) :=
        transEq G (nat (mapHom F f) a₁) (mapHom (F a₂) f) •
        mapHomCongrArg G byDupFunDef •
        byCompFunDef

        def rightDupNatDesc {A B C : univ W} (F : A ⟶ A ⟶ B) (G : B ⟶ C) :
          NatIsoDesc (dupFun (revCompFunFun A G • F)) (G • dupFun F) :=
        NatIsoDesc.strict (λ f => rightDupNat₁ F G f ⑅ rightDupNat₂ F G f)

        class HasRightDupNat (A B C : univ W) where
        (defRightDupNat (F : A ⟶ A ⟶ B) (G : B ⟶ C) : DefNatIso (rightDupNatDesc F G))

        class HasRightDupNatNat (A B C : univ W) extends HasRightDupNat A B C where

        class HasRightDupNatNatNat (A B C : univ W) extends HasRightDupNatNat A B C where

        def substDupNat₁ {A B C : univ W} (F : A ⟶ B) (G : A ⟶ B ⟶ B ⟶ C) {a₁ a₂ : A} (f : a₁ ⇾ a₂) :
          mapHom (substFun F (dupFunFun B C • G)) f ≃'
          mapHom (G a₂ (F a₂)) (mapHom F f) •
          nat (mapHom (G a₂) (mapHom F f)) (F a₁) •
          nat (nat (mapHom G f) (F a₁)) (F a₁) :=
        assoc (nat (nat (mapHom G f) (F a₁)) (F a₁))
              (nat (mapHom (G a₂) (mapHom F f)) (F a₁))
              (mapHom (G a₂ (F a₂)) (mapHom F f)) •
        congrArgTrans (byDupFunFunDef (η := mapHom G f) (a := F a₁) •
                       natCongrArg (byCompFunDef (F := G) (G := dupFunFun B C)) (F a₁))
                      (byDupFunDef (F := G a₂)) •
        bySubstFunDef (F := F) (G := dupFunFun B C • G) (f := f)

        def substDupNat₂ {A B C : univ W} (F : A ⟶ B) (G : A ⟶ B ⟶ B ⟶ C) {a₁ a₂ : A} (f : a₁ ⇾ a₂) :
          mapHom (substFun F (substFun F G)) f ≃'
          mapHom (G a₂ (F a₂)) (mapHom F f) •
          nat (mapHom (G a₂) (mapHom F f)) (F a₁) •
          nat (nat (mapHom G f) (F a₁)) (F a₁) :=
        congrArgTransRight (natTransEq' (nat (mapHom G f) (F a₁)) (mapHom (G a₂) (mapHom F f)) (F a₁) •
                            natCongrArg (bySubstFunDef (F := F) (G := G) (f := f)) (F a₁)) (mapHom (G a₂ (F a₂))
                           (mapHom F f)) •
        bySubstFunDef (F := F) (G := substFun F G) (f := f)

        def substDupNatDesc {A B C : univ W} (F : A ⟶ B) (G : A ⟶ B ⟶ B ⟶ C) :
          NatIsoDesc (substFun F (dupFunFun B C • G)) (substFun F (substFun F G)) :=
        NatIsoDesc.strict (λ f => substDupNat₁ F G f ⑅ substDupNat₂ F G f)

        class HasSubstDupNat (A B C : univ W) where
        (defSubstDupNat (F : A ⟶ B) (G : A ⟶ B ⟶ B ⟶ C) : DefNatIso (substDupNatDesc F G))

        class HasSubstDupNatNat (A B C : univ W) extends HasSubstDupNat A B C where

        class HasSubstDupNatNatNat (A B C : univ W) extends HasSubstDupNatNat A B C where

      end

    end

    section

      variable (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw, iww} W] [IsCatUniverse.{u} W]
               [IsFunUniverse.{u} W] [IsNatUniverse.{u} W] [h : IsIsoUniverse.{u} W]

      class HasLinearNaturalIsomorphisms [hLinFun : IsFunUniverse.HasLinearFunctors W]
                                         [hNatLinFun : IsNatUniverse.HasLinearFunctors W] where
      [hasRightIdNatNat           (A B     : Category W) : HasRightIdNatNat           A B]
      [hasLeftIdNatNat            (A B     : Category W) : HasLeftIdNatNat            A B]
      [hasSwapRevAppNatNat        (A B     : Category W) : HasSwapRevAppNatNat        A B]
      [hasSwapCompFunNatNatNat    (A B C   : Category W) : HasSwapCompFunNatNatNat    A B C]
      [hasSwapRevCompFunNatNatNat (A B C   : Category W) : HasSwapRevCompFunNatNatNat A B C]
      [hasCompAssocNatNatNatNat   (A B C D : Category W) : HasCompAssocNatNatNatNat   A B C D]

      namespace HasLinearNaturalIsomorphisms

        variable [IsFunUniverse.HasLinearFunctors W] [IsNatUniverse.HasLinearFunctors W]

        instance trivial [h : HasTrivialNaturalIsomorphisms W] : HasLinearNaturalIsomorphisms W :=
        { hasRightIdNatNat           := λ _ _     => { defRightIdNat              := λ _ => HasTrivialNaturalityCondition.defNatIso,
                                                       defRightIdNatNat           := DefNatNatIso.trivial DefNatNatIsoBase.trivial },
          hasLeftIdNatNat            := λ _ _     => { defLeftIdNat               := λ _ => HasTrivialNaturalityCondition.defNatIso,
                                                       defLeftIdNatNat            := DefNatNatIso.trivial DefNatNatIsoBase.trivial },
          hasSwapRevAppNatNat        := λ _ _     => { defSwapRevAppNat           := λ _ => HasTrivialNaturalityCondition.defNatIso,
                                                       defSwapRevAppNatNat        := DefNatNatIso.trivial DefNatNatIsoBase.trivial },
          hasSwapCompFunNatNatNat    := λ _ _ _   => { defSwapCompFunNat          := λ _ _ => HasTrivialNaturalityCondition.defNatIso,
                                                       defSwapCompFunNatNat       := λ _ => DefNatNatIso.trivial DefNatNatIsoBase.trivial,
                                                       defSwapCompFunNatNatNat    := DefNatNatNatIso.trivial DefNatNatNatIsoBase.trivial DefNatNatIsoBase.trivial },
          hasSwapRevCompFunNatNatNat := λ _ _ _   => { defSwapRevCompFunNat       := λ _ _ => HasTrivialNaturalityCondition.defNatIso,
                                                       defSwapRevCompFunNatNat    := λ _ => DefNatNatIso.trivial DefNatNatIsoBase.trivial,
                                                       defSwapRevCompFunNatNatNat := DefNatNatNatIso.trivial DefNatNatNatIsoBase.trivial DefNatNatIsoBase.trivial },
          hasCompAssocNatNatNatNat   := λ _ _ _ _ => { defCompAssocNat            := λ _ _ _ => HasTrivialNaturalityCondition.defNatIso,
                                                       defCompAssocNatNat         := λ _ _ => DefNatNatIso.trivial DefNatNatIsoBase.trivial,
                                                       defCompAssocNatNatNat      := λ _ => DefNatNatNatIso.trivial DefNatNatNatIsoBase.trivial DefNatNatIsoBase.trivial } }

        instance hasLinearFunExt [h : HasLinearNaturalIsomorphisms W] :
          HasLinearFunOp.HasLinearFunExt (univ W) :=
        { rightId              := λ {A B} F         => ((h.hasRightIdNatNat A B).defRightIdNat F).η,
          rightIdExt           := λ A B             => (h.hasRightIdNatNat A B).defRightIdNatNat.η,
          leftId               := λ {A B} F         => ((h.hasLeftIdNatNat A B).defLeftIdNat F).η,
          leftIdExt            := λ A B             => (h.hasLeftIdNatNat A B).defLeftIdNatNat.η,
          swapRevApp           := λ {A B} F         => ((h.hasSwapRevAppNatNat A B).defSwapRevAppNat F).η,
          swapRevAppExt        := λ A B             => (h.hasSwapRevAppNatNat A B).defSwapRevAppNatNat.η,
          swapCompFun          := λ {A B} F a C     => ((h.hasSwapCompFunNatNatNat A B C).defSwapCompFunNat F a).η,
          swapCompFunExt       := λ {A B} F C       => ((h.hasSwapCompFunNatNatNat A B C).defSwapCompFunNatNat F).η,
          swapCompFunExtExt    := λ A B C           => (h.hasSwapCompFunNatNatNat A B C).defSwapCompFunNatNatNat.η,
          swapRevCompFun       := λ {A B C} G a     => ((h.hasSwapRevCompFunNatNatNat A B C).defSwapRevCompFunNat G a).η,
          swapRevCompFunExt    := λ A {B C} G       => ((h.hasSwapRevCompFunNatNatNat A B C).defSwapRevCompFunNatNat G).η,
          swapRevCompFunExtExt := λ A B C           => (h.hasSwapRevCompFunNatNatNat A B C).defSwapRevCompFunNatNatNat.η,
          compAssoc            := λ {A B C D} F G H => ((h.hasCompAssocNatNatNatNat A B C D).defCompAssocNat F G H).η,
          compAssocExt         := λ {A B C} F G D   => ((h.hasCompAssocNatNatNatNat A B C D).defCompAssocNatNat F G).η,
          compAssocExtExt      := λ {A B} F C D     => ((h.hasCompAssocNatNatNatNat A B C D).defCompAssocNatNatNat F).η,
          compAssocExtExtExt   := λ A B C D         => sorry }

      end HasLinearNaturalIsomorphisms

      instance hasLinearFunctors [IsFunUniverse.HasLinearFunctors W] [IsNatUniverse.HasLinearFunctors W]
                                 [h : HasLinearNaturalIsomorphisms W] :
        HasLinearFunctors (univ W) :=
      ⟨⟩

      class HasAffineNaturalIsomorphisms [HasSubLinearFunOp W]
                                         [hAffFun : IsFunUniverse.HasAffineFunctors W]
                                         [hNatAffFun : IsNatUniverse.HasAffineFunctors W] extends
        HasLinearNaturalIsomorphisms W where
      [hasRightConstNatNatNat (A B C : Category W) : HasRightConstNatNatNat A B C]
      [hasLeftConstNatNatNat  (A B C : Category W) : HasLeftConstNatNatNat  A B C]

      namespace HasAffineNaturalIsomorphisms

        variable [HasSubLinearFunOp W] [IsFunUniverse.HasAffineFunctors W]
                 [IsNatUniverse.HasAffineFunctors W]

        instance trivial [h : HasTrivialNaturalIsomorphisms W] : HasAffineNaturalIsomorphisms W :=
        { hasRightConstNatNatNat := λ _ _ _ => { defRightConstNat       := λ _ _ => HasTrivialNaturalityCondition.defNatIso,
                                                 defRightConstNatNat    := λ _ => DefNatNatIso.trivial DefNatNatIsoBase.trivial,
                                                 defRightConstNatNatNat := DefNatNatNatIso.trivial DefNatNatNatIsoBase.trivial DefNatNatIsoBase.trivial },
          hasLeftConstNatNatNat  := λ _ _ _ => { defLeftConstNat        := λ _ _ => HasTrivialNaturalityCondition.defNatIso } }

        instance hasAffineFunExt [h : HasAffineNaturalIsomorphisms W] :
          HasAffineFunOp.HasAffineFunExt (univ W) :=
        { rightConst       := λ A {B C} b G => ((h.hasRightConstNatNatNat A B C).defRightConstNat b G).η,
          rightConstExt    := λ A {B} b C   => ((h.hasRightConstNatNatNat A B C).defRightConstNatNat b).η,
          rightConstExtExt := λ A B C       => (h.hasRightConstNatNatNat A B C).defRightConstNatNatNat.η,
          leftConst        := λ {A B C} F c => ((h.hasLeftConstNatNatNat A B C).defLeftConstNat F c).η,
          leftConstExt     := λ {A B} F C   => sorry,
          leftConstExtExt  := λ A B C       => sorry }

      end HasAffineNaturalIsomorphisms

      instance hasAffineFunctors [HasSubLinearFunOp W]
                                 [IsFunUniverse.HasAffineFunctors W] [IsNatUniverse.HasAffineFunctors W]
                                 [h : HasAffineNaturalIsomorphisms W] :
        HasAffineFunctors (univ W) :=
      ⟨⟩

      class HasFullNaturalIsomorphisms [HasSubLinearFunOp W] [HasNonLinearFunOp W]
                                       [hAffFun : IsFunUniverse.HasAffineFunctors W]
                                       [hNatFullFun : IsNatUniverse.HasFullFunctors W] extends
        HasAffineNaturalIsomorphisms W where
      [hasDupSwapNatNat     (A B   : Category W) : HasDupSwapNatNat     A B]
      [hasDupConstNatNat    (A B   : Category W) : HasDupConstNatNat    A B]
      [hasRightDupNatNatNat (A B C : Category W) : HasRightDupNatNatNat A B C]
      [hasSubstDupNatNatNat (A B C : Category W) : HasSubstDupNatNatNat A B C]

      namespace HasFullNaturalIsomorphisms

        variable [HasSubLinearFunOp W] [HasNonLinearFunOp W] [IsFunUniverse.HasAffineFunctors W]
                 [IsNatUniverse.HasFullFunctors W]

        instance trivial [h : HasTrivialNaturalIsomorphisms W] : HasFullNaturalIsomorphisms W :=
        { hasDupSwapNatNat     := λ _ _   => { defDupSwapNat     := λ _ => HasTrivialNaturalityCondition.defNatIso,
                                               defDupSwapNatNat  := DefNatNatIso.trivial DefNatNatIsoBase.trivial },
          hasDupConstNatNat    := λ _ _   => { defDupConstNat    := λ _ => HasTrivialNaturalityCondition.defNatIso,
                                               defDupConstNatNat := DefNatNatIso.trivial DefNatNatIsoBase.trivial },
          hasRightDupNatNatNat := λ _ _ _ => { defRightDupNat    := λ _ _ => HasTrivialNaturalityCondition.defNatIso },
          hasSubstDupNatNatNat := λ _ _ _ => { defSubstDupNat    := λ _ _ => HasTrivialNaturalityCondition.defNatIso } }

        instance hasFullFunExt [h : HasFullNaturalIsomorphisms W] :
          HasFullFunOp.HasFullFunExt (univ W) :=
        { dupSwap        := λ {A B} F     => ((h.hasDupSwapNatNat A B).defDupSwapNat F).η,
          dupSwapExt     := λ A B         => (h.hasDupSwapNatNat A B).defDupSwapNatNat.η,
          dupConst       := λ {A B} F     => ((h.hasDupConstNatNat A B).defDupConstNat F).η,
          dupConstExt    := λ A B         => (h.hasDupConstNatNat A B).defDupConstNatNat.η,
          rightDup       := λ {A B C} F G => ((h.hasRightDupNatNatNat A B C).defRightDupNat F G).η,
          rightDupExt    := λ {A B} F C   => sorry,
          rightDupExtExt := λ A B C       => sorry,
          substDup       := λ {A B C} F G => ((h.hasSubstDupNatNatNat A B C).defSubstDupNat F G).η,
          substDupExt    := λ {A B} F C   => sorry,
          substDupExtExt := λ A B C       => sorry }

      end HasFullNaturalIsomorphisms

      instance hasStandardFunctors [HasSubLinearFunOp W] [HasNonLinearFunOp W]
                                   [IsFunUniverse.HasAffineFunctors W] [IsNatUniverse.HasFullFunctors W]
                                   [h : HasFullNaturalIsomorphisms W] :
        HasStandardFunctors (univ W) :=
      ⟨⟩

    end

  end IsIsoUniverse

end CategoryTheory
