import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.MetaRelations
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.FunctorExtensionality
import UniverseAbstractions.CategoryTheory.Meta
import UniverseAbstractions.Lemmas.DerivedFunctors
import UniverseAbstractions.Lemmas.DerivedFunctorExtensionality



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u u' v w w' iv iw



namespace MetaRelation

  open HasFunctors HasCongrArg HasCongrFun HasLinearFunOp HasSubLinearFunOp HasNonLinearFunOp HasFullFunOp
       HasTransFun HasSymmFun
       IsAssociative IsCategoricalPreorder IsGroupoidEquivalence

  variable {α : Sort u} {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasInternalFunctors V]

  section

    variable {R : MetaRelation α V}

    namespace HasSymmEq

      variable (hR₁ hR₂ : HasSymm R) (hRF₁ : HasSymmFun R (hR := hR₁)) (hRF₂ : HasSymmFun R (hR := hR₂))

      class HasSymmEqExt [h : HasSymmEq hR₁ hR₂] where
      (symmEqExt (a b : α) :
         symmFun R (hR := hR₁) (h := hRF₁) a b
         ≃{▻ λ f => h.symmEq f ◅}
         symmFun R (hR := hR₂) (h := hRF₂) a b)

      def HasSymmEqExt.translate {h₁ h₂ : HasSymmEq hR₁ hR₂} [HasSymmEqExt hR₁ hR₂ hRF₁ hRF₂ (h := h₁)] :
        HasSymmEqExt hR₁ hR₂ hRF₁ hRF₂ (h := h₂) :=
      { symmEqExt := symmEqExt (h := h₁) }

    end HasSymmEq

    namespace HasTransEq

      variable (hR₁ hR₂ : HasTrans R) (hRF₁ : HasTransFun R (hR := hR₁)) (hRF₂ : HasTransFun R (hR := hR₂))

      class HasTransEqExt [h : HasTransEq hR₁ hR₂] where
      (transEqExt {a b : α} (f : R a b) (c : α) :
         transFun R (hR := hR₁) (h := hRF₁) f c
         ≃{▻ λ g => transEq f g ◅}
         transFun R (hR := hR₂) (h := hRF₂) f c)
      (transEqExtExt (a b c : α) :
         transFunFun R (hR := hR₁) (h := hRF₁) a b c
         ≃{▻ λ f => transEqExt f c ◅}
         transFunFun R (hR := hR₂) (h := hRF₂) a b c)

      def HasTransEqExt.translate {h₁ h₂ : HasTransEq hR₁ hR₂} [HasTransEqExt hR₁ hR₂ hRF₁ hRF₂ (h := h₁)] :
        HasTransEqExt hR₁ hR₂ hRF₁ hRF₂ (h := h₂) :=
      { transEqExt    := transEqExt    (h := h₁),
        transEqExtExt := transEqExtExt (h := h₁) }

    end HasTransEq

  end

  variable (R : MetaRelation α V)

  namespace IsAssociative

    variable [HasLinearFunOp V] [HasTrans R] [HasTransFun R]

    class IsAssociativeExt [h : IsAssociative R] where
    (assocExt {a b c : α} (f : R a b) (g : R b c) (d : α) :
       transFun R f d • transFun R g d
       ≃{byDefDef ▻ λ h => assoc f g h ◅}
       transFun R (g • f) d)
    (assocExtExt {a b : α} (f : R a b) (c d : α) :
       revCompFunFun (R c d) (transFun R f d) • transFunFun R b c d
       ≃{byDefDef ▻ λ g => assocExt f g d ◅ byDefDef}
       transFunFun R a c d • transFun R f c)
    (assocExtExtExt (a b c d : α) :
       compFunFun (transFunFun R b c d) (R c d ⟶ R a d) •
       revCompFunFunFun (R c d) (R b d) (R a d) •
       transFunFun R a b d
       ≃{byDefDefDef • byArgDef ▻ λ f => assocExtExt f c d ◅ byDefDef}
       revCompFunFun (R b c) (transFunFun R a c d) • transFunFun R a b c)

    def IsAssociativeExt.translate {h₁ h₂ : IsAssociative R} [IsAssociativeExt R (h := h₁)] :
      IsAssociativeExt R (h := h₂) :=
    { assocExt       := assocExt       (h := h₁),
      assocExtExt    := assocExtExt    (h := h₁),
      assocExtExtExt := assocExtExtExt (h := h₁) }

  end IsAssociative

  namespace IsCategoricalPreorder

    variable [HasLinearFunOp V] [IsPreorder R] [HasTransFun R]

    class IsCategoricalPreorderExt [h : IsCategoricalPreorder R] extends
      IsAssociativeExt R where
    (rightIdExt (a b : α) : transFun    R (HasRefl.refl a) b ≃{▻ λ f => h.rightId f ◅} idFun (R a b))
    (leftIdExt  (a b : α) : revTransFun R a (HasRefl.refl b) ≃{▻ λ f => h.leftId  f ◅} idFun (R a b))

    def IsCategoricalPreorderExt.translate {h₁ h₂ : IsCategoricalPreorder R}
                                           [IsCategoricalPreorderExt R (h := h₁)] :
      IsCategoricalPreorderExt R (h := h₂) :=
    { toIsAssociativeExt := IsAssociativeExt.translate R (h₁ := h₁.toIsAssociative),
      rightIdExt := rightIdExt (h := h₁),
      leftIdExt  := leftIdExt  (h := h₁) }

  end IsCategoricalPreorder

  namespace IsGroupoidEquivalence

    variable [HasFullFunOp V] [IsEquivalence R] [HasTransFun R] [HasSymmFun R]

    class IsGroupoidEquivalenceExt [h : IsGroupoidEquivalence R] extends
      IsCategoricalPreorderExt R where
    (leftInvExt  (a b : α) : substFun (symmFun R a b) (transFunFun    R a b a)
                             ≃{byDefDef • byFunDef ▻ λ f => h.leftInv  f ◅}
                             constFun (R a b) (HasRefl.refl a))
    (rightInvExt (a b : α) : substFun (symmFun R a b) (revTransFunFun R b a b)
                             ≃{byDefDef • byFunDef ▻ λ f => h.rightInv f ◅}
                             constFun (R a b) (HasRefl.refl b))

    def IsGroupoidEquivalenceExt.translate {h₁ h₂ : IsGroupoidEquivalence R}
                                           [IsGroupoidEquivalenceExt R (h := h₁)] :
      IsGroupoidEquivalenceExt R (h := h₂) :=
    { toIsCategoricalPreorderExt := IsCategoricalPreorderExt.translate R
                                      (h₁ := h₁.toIsCategoricalPreorder),
      leftInvExt  := leftInvExt  (h := h₁),
      rightInvExt := rightInvExt (h := h₁) }

    variable [HasFullFunExt V] [IsGroupoidEquivalence R] [IsGroupoidEquivalenceExt R]

    def symmInvExt (a b : α) :
      symmFun R b a • symmFun R a b
      ≃{byDefDef ▻ λ f => symmInv f ◅}
      idFun (R a b) :=
    sorry

    def transInvExt {a b : α} (f : R a b) (c : α) :
      symmFun R a c • transFun R f c
      ≃{byDefDef ▻ λ g => transInv f g ◅ byDefDef}
      revTransFun R c f⁻¹ • symmFun R b c :=
    sorry

    def transInvExtExt (a b c : α) :
      revCompFunFun (R b c) (symmFun R a c) • transFunFun R a b c
      ≃{byDefDef ▻ λ f => transInvExt R f c ◅ byDefDefDef • byArgDef}
      compFunFun (symmFun R b c) (R c a) • revTransFunFun R c b a • symmFun R a b :=
    sorry

  end IsGroupoidEquivalence

  namespace opposite

    instance isAssociativeExt [HasLinearFunOp V] [HasLinearFunExt V] [HasTrans R] [IsAssociative R]
                              [HasTransFun R] [hAssocExt : IsAssociativeExt R] :
      IsAssociativeExt (opposite R) :=
    -- TODO: This essentially requires making `compAssocRightExt` more generic.
    { assocExt       := λ f g d   => sorry,
      assocExtExt    := λ f c d   => sorry,
      assocExtExtExt := λ a b c d => sorry }

    instance isCategoricalPreorderExt [HasLinearFunOp V] [HasLinearFunExt V] [IsPreorder R]
                                      [IsCategoricalPreorder R] [HasTransFun R]
                                      [hCatExt : IsCategoricalPreorderExt R] :
      IsCategoricalPreorderExt (opposite R) :=
    { rightIdExt := λ a b => hCatExt.leftIdExt  b a,
      leftIdExt  := λ a b => hCatExt.rightIdExt b a • revTransFunEq R a (HasRefl.refl b) }

    instance isGroupoidEquivalenceExt [HasFullFunOp V] [HasLinearFunExt V] [IsEquivalence R]
                                      [IsGroupoidEquivalence R] [HasSymmFun R]
                                      [HasTransFun R] [hGrpExt : IsGroupoidEquivalenceExt R] :
      IsGroupoidEquivalenceExt (opposite R) :=
    { leftInvExt  := λ a b => hGrpExt.rightInvExt b a,
      rightInvExt := λ a b => hGrpExt.leftInvExt  b a •
                              defCongrArg (defSubstFunFun (symmFun (opposite R) a b) (R b b))
                                          (revTransFunFunEq R b a b) }

  end opposite

  namespace lift

    variable {ω : Sort w} (l : ω → α)

    instance isAssociativeExt [HasLinearFunOp V] [HasTrans R] [IsAssociative R] [HasTransFun R]
                              [h : IsAssociativeExt R] :
      IsAssociativeExt (lift R l) :=
    { assocExt       := λ f g d   => h.assocExt f g (l d),
      assocExtExt    := λ f c d   => h.assocExtExt f (l c) (l d),
      assocExtExtExt := λ a b c d => h.assocExtExtExt (l a) (l b) (l c) (l d) }

    instance isCategoricalPreorderExt [HasLinearFunOp V] [IsPreorder R] [IsCategoricalPreorder R]
                                      [HasTransFun R] [h : IsCategoricalPreorderExt R] :
      IsCategoricalPreorderExt (lift R l) :=
    { rightIdExt := λ a b => h.rightIdExt (l a) (l b),
      leftIdExt  := λ a b => h.leftIdExt (l a) (l b) }

    instance isGroupoidEquivalenceExt [HasFullFunOp V] [IsEquivalence R]
                                      [IsGroupoidEquivalence R] [HasSymmFun R]
                                      [HasTransFun R] [h : IsGroupoidEquivalenceExt R] :
      IsGroupoidEquivalenceExt (lift R l) :=
    { leftInvExt  := λ a b => h.leftInvExt (l a) (l b),
      rightInvExt := λ a b => h.rightInvExt (l a) (l b) }

  end lift

end MetaRelation



namespace MetaFunctor

  open MetaRelation HasSymmFun HasTransFun IsCategoricalPreorder IsGroupoidEquivalence
       HasFunctors HasCongrArg HasLinearFunOp HasLinearFunExt HasSubLinearFunOp HasAffineFunOp HasAffineFunExt

  section

    variable {α : Sort u} {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasInternalFunctors V]
             {R S : MetaRelation α V} (F : MetaFunctor R S)

    namespace IsSymmFunctor

      variable [HasLinearFunOp V] [HasSymm R] [HasSymmFun R] [HasSymm S] [HasSymmFun S]

      class IsSymmFunctorExt [h : IsSymmFunctor F] where
      (symmEqExt (a b : α) :
         F.baseFun b a • symmFun R a b
         ≃{byArgDef ▻ λ f => symmEq f ◅ byDef}
         symmFun S a b • F.baseFun a b)

      def IsSymmFunctorExt.translate {h₁ h₂ : IsSymmFunctor F} [IsSymmFunctorExt F (h := h₁)] :
        IsSymmFunctorExt F (h := h₂) :=
      { symmEqExt := symmEqExt (h := h₁) }

    end IsSymmFunctor

    namespace IsTransFunctor

      variable [HasLinearFunOp V] [HasTrans R] [HasTransFun R] [HasTrans S] [HasTransFun S]

      class IsTransFunctorExt [h : IsTransFunctor F] where
      (transEqExt {a b : α} (f : R a b) (c : α) :
         F.baseFun a c • transFun R f c
         ≃{byArgDef ▻ λ g => transEq f g ◅ byDef}
         transFun S (F f) c • F.baseFun b c)
      (transEqExtExt (a b c : α) :
         revCompFunFun (R b c) (F.baseFun a c) • transFunFun R a b c
         ≃{byDefDef ▻ λ f => transEqExt f c ◅ byDefDef • byArgDef}
         compFunFun (F.baseFun b c) (S a c) • transFunFun S a b c • F.baseFun a b)

      def IsTransFunctorExt.translate {h₁ h₂ : IsTransFunctor F}
                                      [IsTransFunctorExt F (h := h₁)] :
        IsTransFunctorExt F (h := h₂) :=
      { transEqExt    := transEqExt    (h := h₁),
        transEqExtExt := transEqExtExt (h := h₁) }

    end IsTransFunctor

    namespace lift

      variable {ω : Sort w'} (l : ω → α)

      instance isSymmFunctorExt [HasLinearFunOp V] [HasSymm R] [HasSymmFun R] [HasSymm S] [HasSymmFun S]
                                [IsSymmFunctor F] [h : IsSymmFunctor.IsSymmFunctorExt F] :
        IsSymmFunctor.IsSymmFunctorExt (lift F l) :=
      { symmEqExt := λ a b => h.symmEqExt (l a) (l b) }

      instance isTransFunctorExt [HasLinearFunOp V] [HasTrans R] [HasTransFun R] [HasTrans S] [HasTransFun S]
                                 [IsTransFunctor F] [h : IsTransFunctor.IsTransFunctorExt F] :
        IsTransFunctor.IsTransFunctorExt (lift F l) :=
      { transEqExt    := λ f c   => h.transEqExt f (l c),
        transEqExtExt := λ a b c => h.transEqExtExt (l a) (l b) (l c) }

    end lift

  end

  namespace idFun

    variable {α : Sort u} {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasInternalFunctors V]
             [HasLinearFunOp V] (R : MetaRelation α V)

    instance isSymmFunctorExt [HasSymm R] [HasSymmFun R] [HasLinearFunExt V] :
      IsSymmFunctor.IsSymmFunctorExt (metaFunctor R) :=
    { symmEqExt := λ a b => (rightId (symmFun R a b))⁻¹ • leftId (symmFun R a b) }

    instance isTransFunctorExt [HasTrans R] [HasTransFun R] [HasLinearFunExt V] :
      IsTransFunctor.IsTransFunctorExt (metaFunctor R) :=
    { transEqExt    := λ {a b} f c => (rightId (transFun R f c) •
                                       defCongrArg (HasCompFunFun.defCompFunFun (idFun (R b c)) (R a c))
                                                   (defCongrArg (defTransFunFun a b c) byDef))⁻¹ •
                                      leftId (transFun R f c),
      transEqExtExt := λ a b c => (rightId (transFunFun R a b c) •
                                   leftId (transFunFun R a b c • idFun (R a b)) •
                                   defCongrArg (HasCompFunFun.defCompFunFun (transFunFun R a b c • idFun (R a b))
                                                                            (R b c ⟶ R a c))
                                               (rightIdExt (R b c) (R a c)))⁻¹ •
                                  (leftId (transFunFun R a b c) •
                                   defCongrArg (HasCompFunFun.defCompFunFun (transFunFun R a b c)
                                                                            (R b c ⟶ R a c))
                                               (leftIdExt (R b c) (R a c))) }

  end idFun

  namespace constFun

    instance (α : Sort u) {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasInternalFunctors V]
             [HasConstFun V V] {C : V} (c : C) :
      HasSymmFun (constRelation α c) :=
    { defSymmFun := λ _ _ => HasConstFun.defConstFun C c }

    instance (α : Sort u) {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasInternalFunctors V]
             [HasConstFun V V] {C : V} (c : C) :
      HasTransFun (constRelation α c) :=
    { defTransFun    := λ _ _   => HasConstFun.defConstFun C c,
      defTransFunFun := λ _ _ _ => HasConstFun.defConstFun C (HasConstFun.constFun C c) }

    variable {α : Sort u} {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasInternalFunctors V]
             (R : MetaRelation α V) {C : V} (c : C)

    instance isSymmFunctorExt [HasFullFunOp V] [HasAffineFunExt V] [HasSymm R] [HasSymmFun R] :
      IsSymmFunctor.IsSymmFunctorExt (metaFunctor R c) :=
    sorry
    --{ symmEqExt := λ a b => _ • (leftConst (constFun (R a b) (HasRefl.refl (R := S) c)) (HasRefl.refl c))⁻¹ • leftConst (symmFun R a b) (HasRefl.refl c) }

    instance isTransFunctorExt [HasAffineFunOp V] [HasAffineFunExt V] [HasTrans R] [HasTransFun R] :
      IsTransFunctor.IsTransFunctorExt (metaFunctor R c) :=
    sorry
    --{ transEqExt    := λ {a b} f d => (leftConst (constFun (R b d) c) c)⁻¹ • leftConst (transFun R f d) c,
    --  transEqExtExt := λ a b d => (defCongrArg (defConstFunFun (R a b) (R b d ⟶ C))
    --                                            (leftConst (constFun (R b d) c) c • byDef) •
    --                               rightConst (R a b) (constFun C c) (compFunFun (constFun (R b d) c) C) •
    --                               defCongrArg (defRevCompFunFun (R a b) (compFunFun (constFun (R b d) c) C))
    --                                           (leftConst (constFun (R a b) c) (constFun C c)))⁻¹ •
    --                              (leftConst (transFunFun R a b d) (constFun (R b d) c) •
    --                               defCongrArg (HasCompFunFun.defCompFunFun (transFunFun R a b d) (R b d ⟶ C))
    --                                           (leftConstFunExt (R b d) (R a d) c)) }

    -- TODO: We may need slightly different code for `PreFunctor.constFun`.

  end constFun

  namespace compFun

    variable {α : Sort u} {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasInternalFunctors V]
             [HasLinearFunOp V] [HasLinearFunExt V] {R S T : MetaRelation α V}
             (F : MetaFunctor R S) (G : MetaFunctor S T)

    instance isSymmFunctorExt [HasSymm R] [HasSymm S] [HasSymm T]
                              [HasSymmFun R] [HasSymmFun S] [HasSymmFun T]
                              [hF : IsSymmFunctor F] [hG : IsSymmFunctor G]
                              [hFExt : IsSymmFunctor.IsSymmFunctorExt F]
                              [hGExt : IsSymmFunctor.IsSymmFunctorExt G] :
      IsSymmFunctor.IsSymmFunctorExt (metaFunctor F G) :=
    { symmEqExt := λ a b => compAssoc (F.baseFun a b) (G.baseFun a b) (symmFun T a b) •
                            defCongrArg (HasCompFunFun.defCompFunFun (F.baseFun a b) (T b a)) (hGExt.symmEqExt a b) •
                            (compAssoc (F.baseFun a b) (symmFun S a b) (G.baseFun b a))⁻¹ •
                            defCongrArg (defRevCompFunFun (R a b) (G.baseFun b a)) (hFExt.symmEqExt a b) •
                            compAssoc (symmFun R a b) (F.baseFun b a) (G.baseFun b a) }

    instance isTransFunctorExt [HasTrans R] [HasTrans S] [HasTrans T]
                               [HasTransFun R] [HasTransFun S] [HasTransFun T]
                               [hF : IsTransFunctor F] [hG : IsTransFunctor G]
                               [hFExt : IsTransFunctor.IsTransFunctorExt F]
                               [hGExt : IsTransFunctor.IsTransFunctorExt G] :
      IsTransFunctor.IsTransFunctorExt (metaFunctor F G) :=
    { transEqExt    := λ {a b} f c => compAssoc (F.baseFun b c) (G.baseFun b c) (transFun T ((metaFunctor F G) f) c) •
                                      defCongrArg (HasCompFunFun.defCompFunFun (F.baseFun b c) (T a c))
                                                  (defCongrArg (HasCompFunFun.defCompFunFun (G.baseFun b c) (T a c))
                                                               (defCongrArg (defTransFunFun a b c)
                                                                            ((HasCompFun.defCompFun (F.baseFun a b) (G.baseFun a b)).eff f)⁻¹) •
                                                   hGExt.transEqExt (F f) c) •
                                      (compAssoc (F.baseFun b c) (transFun S (F f) c) (G.baseFun a c))⁻¹ •
                                      defCongrArg (defRevCompFunFun (R b c) (G.baseFun a c)) (hFExt.transEqExt f c) •
                                      compAssoc (transFun R f c) (F.baseFun a c) (G.baseFun a c),
      transEqExtExt := λ a b c => defCongrArg (defRevCompFunFun (R a b) (compFunFun (G.baseFun b c • F.baseFun b c) (T a c)))
                                              (compAssoc (F.baseFun a b) (G.baseFun a b) (transFunFun T a b c)) •
                                  defCongrArg (HasCompFunFun.defCompFunFun ((transFunFun T a b c • G.baseFun a b) • F.baseFun a b) (R b c ⟶ T a c))
                                              (compAssocExt (F.baseFun b c) (G.baseFun b c) (T a c)) •
                                  (compAssoc ((transFunFun T a b c • G.baseFun a b) • F.baseFun a b)
                                             (compFunFun (G.baseFun b c) (T a c))
                                             (compFunFun (F.baseFun b c) (T a c)))⁻¹ •
                                  defCongrArg (defRevCompFunFun (R a b) (compFunFun (F.baseFun b c) (T a c)))
                                              (compAssoc (F.baseFun a b)
                                                         (transFunFun T a b c • G.baseFun a b)
                                                         (compFunFun (G.baseFun b c) (T a c)) •
                                               defCongrArg (HasCompFunFun.defCompFunFun (F.baseFun a b) (S b c ⟶ T a c))
                                                           (hGExt.transEqExtExt a b c) •
                                               (compAssoc (F.baseFun a b)
                                                          (transFunFun S a b c)
                                                          (revCompFunFun (S b c) (G.baseFun a c)))⁻¹) •
                                  compAssoc (transFunFun S a b c • F.baseFun a b)
                                            (revCompFunFun (S b c) (G.baseFun a c))
                                            (compFunFun (F.baseFun b c) (T a c)) •
                                  defCongrArg (HasCompFunFun.defCompFunFun (transFunFun S a b c • F.baseFun a b) (R b c ⟶ T a c))
                                              (compAssocMidExt (F.baseFun b c) (G.baseFun a c))⁻¹ •
                                  (compAssoc (transFunFun S a b c • F.baseFun a b)
                                             (compFunFun (F.baseFun b c) (S a c))
                                             (revCompFunFun (R b c) (G.baseFun a c)))⁻¹ •
                                  defCongrArg (defRevCompFunFun (R a b) (revCompFunFun (R b c) (G.baseFun a c)))
                                              (hFExt.transEqExtExt a b c) •
                                  compAssoc (transFunFun R a b c)
                                            (revCompFunFun (R b c) (F.baseFun a c))
                                            (revCompFunFun (R b c) (G.baseFun a c)) •
                                  defCongrArg (HasCompFunFun.defCompFunFun (transFunFun R a b c) (R b c ⟶ T a c))
                                              (compAssocRightExt (R b c) (F.baseFun a c) (G.baseFun a c)) }

  end compFun

  namespace symmFun

    variable {α : Sort u} {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasInternalFunctors V]
             [HasFullFunOp V] (R : MetaRelation α V) [IsEquivalence R] [IsGroupoidEquivalence R]
             [HasSymmFun R] [HasTransFun R] [IsGroupoidEquivalenceExt R]

    instance isSymmFunctorExt : IsSymmFunctor.IsSymmFunctorExt (metaFunctor R) :=
    { symmEqExt := λ a b => HasRefl.refl (symmFun R b a • symmFun R a b) }

    instance isTransFunctorExt : IsTransFunctor.IsTransFunctorExt (metaFunctor R) :=
    { transEqExt    := λ {a b} f c => defCongrArg (HasCompFunFun.defCompFunFun (symmFun R b c) (R c a))
                                                  (defCongrArg (defRevTransFunFun R c b a) byDef⁻¹) •
                                      transInvExt R f c,
      transEqExtExt := λ a b c     => transInvExtExt R a b c }

  end symmFun

end MetaFunctor



namespace MetaQuantification

  open MetaRelation MetaFunctor HasTransFun IsAssociative IsCategoricalPreorder
       IsCategoricalPreorderExt IsGroupoidEquivalence
       HasFunctors HasCongrArg HasLinearFunOp

  namespace IsNatural

    variable {α : Sort u} {β : Sort u'} {W : Universe.{w}} [HasIdentity.{w, iw} W]
             [HasInternalFunctors W] {R : MetaRelation α W} {S : MetaRelation β W}

    class IsNaturalExt [HasLinearFunOp W] [HasTrans S] [HasTransFun S]
                       {φ ψ : α → β} (F : PreFunctor R S φ) (G : PreFunctor R S ψ)
                       (η : MetaQuantification S φ ψ) [h : IsNatural F G η] where
    (natExt (a b : α) :
       revTransFun S (φ a) (η b) • F.baseFun a b
       ≃{byDef ▻ λ f => h.nat f ◅ byDef}
       transFun S (η a) (ψ b) • G.baseFun a b)

    namespace IsNaturalExt

      instance refl [HasLinearFunOp W] [IsPreorder S] [IsCategoricalPreorder S]
                    [HasTransFun S] [IsCategoricalPreorderExt S]
                    {φ : α → β} (F : PreFunctor R S φ) :
        IsNaturalExt F F (MetaQuantification.refl S φ) :=
      ⟨λ a b => defCongrArg (HasCompFunFun.defCompFunFun (F.baseFun a b) (S (φ a) (φ b)))
                            ((rightIdExt (φ a) (φ b))⁻¹ • leftIdExt (φ a) (φ b))⟩

      instance symm [HasFullFunOp W] [IsEquivalence S] [IsGroupoidEquivalence S]
                    [HasTransFun S] [HasSymmFun S] [IsGroupoidEquivalenceExt S]
                    {φ ψ : α → β} {F : PreFunctor R S φ} {G : PreFunctor R S ψ}
                    (η : MetaQuantification S φ ψ) [IsNatural F G η] [hη : IsNaturalExt F G η] :
        IsNaturalExt G F (MetaQuantification.symm S η) :=
      ⟨λ a b => sorry⟩

      instance trans [HasLinearFunOp W] [HasTrans S] [IsAssociative S]
                     [HasTransFun S] [IsAssociativeExt S] {φ ψ χ : α → β}
                     {F : PreFunctor R S φ} {G : PreFunctor R S ψ} {H : PreFunctor R S χ}
                     (η : MetaQuantification S φ ψ) [IsNatural F G η] [hη : IsNaturalExt F G η]
                     (ε : MetaQuantification S ψ χ) [IsNatural G H ε] [hε : IsNaturalExt G H ε] :
        IsNaturalExt F H (MetaQuantification.trans S η ε) :=
      ⟨λ a b => sorry⟩

      def translate [HasLinearFunOp W] [HasTrans S] [HasTransFun S]
                    {φ ψ : α → β} (F : PreFunctor R S φ) (G : PreFunctor R S ψ)
                    (η : MetaQuantification S φ ψ) {h₁ h₂ : IsNatural F G η}
                    [IsNaturalExt F G η (h := h₁)] :
        IsNaturalExt F G η (h := h₂) :=
      { natExt := natExt (h := h₁) }

    end IsNaturalExt

  end IsNatural

end MetaQuantification
