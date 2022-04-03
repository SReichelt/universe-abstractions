import UniverseAbstractions.CategoryTheory.Functors.Nested



set_option autoBoundImplicitLocal false
set_option maxHeartbeats 500000
--set_option pp.universes true

universe u w ww iw iww



namespace CategoryTheory

  open MetaRelation HasTransFun
       HasCatProp HasCatProp.Category HasFunProp HasFunProp.Functor HasNatRel HasNaturality
       HasLinearFunOp HasSubLinearFunOp HasNonLinearFunOp

  namespace IsSortNatUniverse

    open IsSortNatUniverse

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]
             [IsSortNatUniverse.{u} W]

    section

      variable [HasLinearCatFun.{u} W]

      def byIdFunDef {A : univ.{u} W} {a₁ a₂ : A} {f : a₁ ⇾ a₂} :
        mapHom (idFun A) f ≃' f :=
      DefFun.byMapHomDef

      def byAppFunFunDef {A B : univ.{u} W} {F₁ F₂ : A ⟶ B} {η : F₁ ⇾ F₂} {a : A} :
        nat (mapHom (appFunFun A B) η) a ≃' nat η a :=
      nat.congrArg byIdFunDef a

      def byRevAppFunDef {A B : univ.{u} W} {a : A} {F₁ F₂ : A ⟶ B} {η : F₁ ⇾ F₂} :
        mapHom (revAppFun a B) η ≃' nat η a :=
      DefFun.byMapHomDef

      def byRevAppFunFunDef {A B : univ.{u} W} {a₁ a₂ : A} {f : a₁ ⇾ a₂} {F : A ⟶ B} :
        nat (mapHom (revAppFunFun A B) f) F ≃' mapHom F f :=
      DefFunFun.byFunFunDef

      def byCompFunDef {A B C : univ.{u} W} {F : A ⟶ B} {G : B ⟶ C} {a₁ a₂ : A} {f : a₁ ⇾ a₂} :
        mapHom (G • F) f ≃' mapHom G (mapHom F f) :=
      DefFun.byMapHomDef

      def byCompFunFunDef {A B C : univ.{u} W} {F : A ⟶ B} {G₁ G₂ : B ⟶ C} {ε : G₁ ⇾ G₂} {a : A} :
        nat (mapHom (compFunFun F C) ε) a ≃' nat ε (F a) :=
      DefFunFun.byFunFunDef

      def byCompFunFunFunDef {A B C : univ.{u} W} {F₁ F₂ : A ⟶ B} {η : F₁ ⇾ F₂} {G : B ⟶ C} {a : A} :
        nat (nat (mapHom (compFunFunFun A B C) η) G) a ≃' mapHom G (nat η a) :=
      DefFunFunFun.byFunFunFunDef

      def bySwapFunDef {A B C : univ.{u} W} {F : A ⟶ B ⟶ C} {b : B} {a₁ a₂ : A} {f : a₁ ⇾ a₂} :
        mapHom (swapFun F b) f ≃' nat (mapHom F f) b :=
      byRevAppFunDef • byCompFunDef (F := F) (G := revAppFun b C)

      def bySwapFunFunDef {A B C : univ.{u} W} {F : A ⟶ B ⟶ C} {b₁ b₂ : B} {g : b₁ ⇾ b₂} {a : A} :
        nat (mapHom (swapFunFun F) g) a ≃' mapHom (F a) g :=
      byRevAppFunFunDef •
      byCompFunFunDef •
      nat.congrArg (byCompFunDef (F := revAppFunFun B C) (G := compFunFun F C)) a

      def bySwapFunFunFunDef {A B C : univ.{u} W} {F₁ F₂ : A ⟶ B ⟶ C} {η : F₁ ⇾ F₂} {a : A} {b : B} :
        nat (nat (mapHom (swapFunFunFun A B C) η) b) a ≃' nat (nat η a) b :=
      byRevAppFunDef •
      byCompFunFunFunDef •
      nat.congrArg (byCompFunFunDef (F := revAppFunFun B C) •
                    nat.congrArg (byCompFunDef (F := compFunFunFun A (B ⟶ C) C)
                                               (G := compFunFun (revAppFunFun B C) (A ⟶ C))) b) a

      def byRevCompFunFunDef {A B C : univ.{u} W} {G : B ⟶ C} {F₁ F₂ : A ⟶ B} {η : F₁ ⇾ F₂} {a : A} :
        nat (mapHom (revCompFunFun A G) η) a ≃' mapHom G (nat η a) :=
      byCompFunFunFunDef •
      nat.congrArg (bySwapFunDef (F := compFunFunFun A B C)) a

      def byRevCompFunFunFunDef {A B C : univ.{u} W} {G₁ G₂ : B ⟶ C} {ε : G₁ ⇾ G₂} {F : A ⟶ B} {a : A} :
        nat (nat (mapHom (revCompFunFunFun A B C) ε) F) a ≃' nat ε (F a) :=
      byCompFunFunDef •
      nat.congrArg (bySwapFunFunDef (F := compFunFunFun A B C)) a

    end

    section

      variable [HasSubLinearFunOp W] [HasAffineCatFun W]

      def byConstFunDef {A B : univ.{u} W} {b : B} {a₁ a₂ : A} {f : a₁ ⇾ a₂} :
        mapHom (constFun A b) f ≃' idHom b :=
      DefFun.byMapHomDef

      def byConstFunFunDef {A B : univ.{u} W} {b₁ b₂ : B} {g : b₁ ⇾ b₂} {a : A} :
        nat (mapHom (constFunFun A B) g) a ≃' g :=
      DefFunFun.byFunFunDef

    end

    section

      variable [HasSubLinearFunOp W] [HasNonLinearFunOp W] [HasFullCatFun W]

      def byDupFunDef {A B : univ.{u} W} {F : A ⟶ A ⟶ B} {a₁ a₂ : A} {f : a₁ ⇾ a₂} :
        mapHom (dupFun F) f ≃' mapDupHom F f :=
      DefFun.byMapHomDef

      def byDupFunDef' {A B : univ.{u} W} {F : A ⟶ A ⟶ B} {a₁ a₂ : A} {f : a₁ ⇾ a₂} :
        mapHom (dupFun F) f ≃' mapDupHom' F f :=
      (mapDupHomEq F f)⁻¹ • byDupFunDef

      def byDupFunFunDef {A B : univ.{u} W} {F₁ F₂ : A ⟶ A ⟶ B} {η : F₁ ⇾ F₂} {a : A} :
        nat (mapHom (dupFunFun A B) η) a ≃' nat (nat η a) a :=
      DefFunFun.byFunFunDef

      def bySubstFunDef {A B C : univ.{u} W} {F : A ⟶ B} {G : A ⟶ B ⟶ C} {a₁ a₂ : A} {f : a₁ ⇾ a₂} :
        mapHom (substFun F G) f ≃' mapHom (G a₂) (mapHom F f) • nat (mapHom G f) (F a₁) :=
      congrArgTrans (byCompFunFunDef • nat.congrArg (byCompFunDef (F := G) (G := compFunFun F C)) a₁)
                    byCompFunDef •
      byDupFunDef (F := compFunFun F C • G)

      def bySubstFunDef' {A B C : univ.{u} W} {F : A ⟶ B} {G : A ⟶ B ⟶ C} {a₁ a₂ : A} {f : a₁ ⇾ a₂} :
        mapHom (substFun F G) f ≃' nat (mapHom G f) (F a₂) • mapHom (G a₁) (mapHom F f) :=
      congrArgTrans byCompFunDef
                    (byCompFunFunDef • nat.congrArg (byCompFunDef (F := G) (G := compFunFun F C)) a₂) •
      byDupFunDef' (F := compFunFun F C • G)

      def bySubstFunFunDef {A B C : univ.{u} W} {F : A ⟶ B} {G₁ G₂ : A ⟶ B ⟶ C} {ε : G₁ ⇾ G₂} {a : A} :
        nat (mapHom (substFunFun F C) ε) a ≃' nat (nat ε a) (F a) :=
      byCompFunFunDef (ε := nat ε a) •
      nat.congrArg (byRevCompFunFunDef (G := compFunFun F C)) a •
      byDupFunFunDef (η := mapHom (revCompFunFun A (compFunFun F C)) ε) •
      nat.congrArg (byCompFunDef (F := revCompFunFun A (compFunFun F C)) (G := dupFunFun A C)) a

      def bySubstFunFunFunDef {A B C : univ.{u} W} {F₁ F₂ : A ⟶ B} {η : F₁ ⇾ F₂} {G : A ⟶ B ⟶ C} {a : A} :
        nat (nat (mapHom (substFunFunFun A B C) η) G) a ≃' mapHom (G a) (nat η a) :=
      byCompFunFunFunDef (G := G a) •
      nat.congrArg (byRevCompFunFunFunDef (ε := mapHom (compFunFunFun A B C) η) •
                    nat.congrArg (nat.congrArg (byCompFunDef (F := compFunFunFun A B C)
                                                             (G := revCompFunFunFun A (B ⟶ C) (A ⟶ C))) G) a) a •
      byDupFunFunDef (η := nat (mapHom (revCompFunFunFun A (B ⟶ C) (A ⟶ C) • compFunFunFun A B C) η) G) •
      nat.congrArg (byRevCompFunFunDef (G := dupFunFun A C)
                                       (η := mapHom (revCompFunFunFun A (B ⟶ C) (A ⟶ C) •
                                                     compFunFunFun A B C) η) •
                    nat.congrArg (byCompFunDef (F := revCompFunFunFun A (B ⟶ C) (A ⟶ C) •
                                                     compFunFunFun A B C)
                                               (G := revCompFunFun (A ⟶ B ⟶ C) (dupFunFun A C))) G) a

    end

  end IsSortNatUniverse

end CategoryTheory
