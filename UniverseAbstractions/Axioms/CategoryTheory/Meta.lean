/-
Prerequisites for (higher) category theory, in the form of properties on `MetaRelation`, under the
condition that the target universe of the `MetaRelation` has instance equivalences. In particular,
transitivity can be strengthened to an associative operation, reflexivity and transitivity together
can give a `MetaRelation` the structure of a category, and symmetry can additionally strengthen
this to a groupoid.

In the main part of the category theory formalization, we do not work directly with `MetaRelation`
but use them implicitly as morphisms that are part of a category.
-/



import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.MetaRelations
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.FunctorExtensionality
import UniverseAbstractions.Lemmas.DerivedFunctors
import UniverseAbstractions.Lemmas.DerivedFunctorExtensionality



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u u' v w vw iv iw



namespace MetaRelation

  open HasFunctors HasCongrArg HasCongrFun HasLinearFunOp HasSubLinearFunOp HasFullFunOp
       HasTransFun HasSymmFun

  variable {α : Sort u} {V : Universe.{v}} [HasIdentity.{v, iv} V]
           (R : MetaRelation α V)

  class IsAssociative [HasTrans R] where
  (assoc {a b c d : α} (f : R a b) (g : R b c) (h : R c d) : (h • g) • f ≃ h • (g • f))

  namespace IsAssociative

    section

      variable [HasInternalFunctors V] [HasLinearFunOp V] [HasTrans R] [HasTransFun R]

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
    end

  end IsAssociative

  class IsCategoricalPreorder [IsPreorder R] extends IsAssociative R where
  (rightId {a b : α} (f : R a b) : f • HasRefl.refl a ≃ f)
  (leftId  {a b : α} (f : R a b) : HasRefl.refl b • f ≃ f)

  namespace IsCategoricalPreorder

    section

      variable [IsPreorder R] [IsCategoricalPreorder R]

      def idId (a : α) :
        HasRefl.refl (R := R) a • HasRefl.refl (R := R) a ≃ HasRefl.refl (R := R) a :=
      rightId (HasRefl.refl a)

      variable [HasInternalFunctors V] [HasTransFun R]

      def congrArgTransLeftId [HasCongrArg V V] {a b : α} (f : R a b) {g : R b b}
                              (hg : g ≃ HasRefl.refl (R := R) b) :
        g • f ≃ f :=
      leftId f • congrArgTransLeft R f hg

      def congrArgTransRightId [HasCongrFun V V] {a b : α} {f : R a a}
                               (hf : f ≃ HasRefl.refl (R := R) a) (g : R a b) :
        g • f ≃ g :=
      rightId g • congrArgTransRight R hf g

    end

    section

      variable [HasInternalFunctors V] [HasLinearFunOp V] [IsPreorder R] [HasTransFun R]

      class IsCategoricalPreorderExt [h : IsCategoricalPreorder R] extends
        IsAssociative.IsAssociativeExt R where
      (rightIdExt (a b : α) : transFun    R (HasRefl.refl a) b ≃{▻ λ f => h.rightId f ◅} idFun (R a b))
      (leftIdExt  (a b : α) : revTransFun R a (HasRefl.refl b) ≃{▻ λ f => h.leftId  f ◅} idFun (R a b))

      def IsCategoricalPreorderExt.translate {h₁ h₂ : IsCategoricalPreorder R}
                                             [IsCategoricalPreorderExt R (h := h₁)] :
        IsCategoricalPreorderExt R (h := h₂) :=
      { toIsAssociativeExt := IsAssociative.IsAssociativeExt.translate R (h₁ := h₁.toIsAssociative),
        rightIdExt := rightIdExt (h := h₁),
        leftIdExt  := leftIdExt  (h := h₁) }

    end

  end IsCategoricalPreorder

  def HalfInv [IsPreorder R] {a b : α} (f : R a b) (g : R b a) :=
  g • f ≃ HasRefl.refl (R := R) a

  namespace HalfInv

    open IsAssociative IsCategoricalPreorder

    variable [IsPreorder R] [IsCategoricalPreorder R]

    def refl (a : α) : HalfInv R (HasRefl.refl a) (HasRefl.refl a) := idId R a

    variable [HasInternalFunctors V] [HasLinearFunOp V] [HasTransFun R]

    def trans {a b c : α} {f₁ : R a b} {g₁ : R b a} (e₁ : HalfInv R f₁ g₁)
                          {f₂ : R b c} {g₂ : R c b} (e₂ : HalfInv R f₂ g₂) :
      HalfInv R (f₂ • f₁) (g₁ • g₂) :=
    e₁ •
    congrArgTransRight R (leftId f₁ •
                          congrArgTransLeft R f₁ e₂ •
                          (assoc f₁ f₂ g₂)⁻¹) g₁ •
    assoc (f₂ • f₁) g₂ g₁

  end HalfInv

  class IsInv [IsPreorder R] {a b : α} (f : R a b) (g : R b a) where
  (leftInv  : HalfInv R f g)
  (rightInv : HalfInv R g f)

  namespace IsInv

    variable [IsPreorder R] [IsCategoricalPreorder R]

    instance refl (a : α) : IsInv R (HasRefl.refl a) (HasRefl.refl a) :=
    { leftInv  := HalfInv.refl R a,
      rightInv := HalfInv.refl R a }

    instance symm {a b : α} (f : R a b) (g : R b a) [h : IsInv R f g] : IsInv R g f :=
    { leftInv  := h.rightInv,
      rightInv := h.leftInv }

    variable [HasInternalFunctors V] [HasLinearFunOp V] [HasTransFun R]

    instance trans {a b c : α} (f₁ : R a b) (g₁ : R b a) [h₁ : IsInv R f₁ g₁]
                               (f₂ : R b c) (g₂ : R c b) [h₂ : IsInv R f₂ g₂] :
      IsInv R (f₂ • f₁) (g₁ • g₂) :=
    { leftInv  := HalfInv.trans R h₁.leftInv  h₂.leftInv,
      rightInv := HalfInv.trans R h₂.rightInv h₁.rightInv }

  end IsInv

  class IsGroupoidEquivalence [IsEquivalence R] extends IsCategoricalPreorder R where
  (leftInv  {a b : α} (f : R a b) : HalfInv R f f⁻¹)
  (rightInv {a b : α} (f : R a b) : HalfInv R f⁻¹ f)

  namespace IsGroupoidEquivalence

    open IsAssociative IsCategoricalPreorder

    section

      variable [IsEquivalence R] [IsGroupoidEquivalence R]

      instance isInv {a b : α} (f : R a b) : IsInv R f f⁻¹ :=
      { leftInv  := leftInv  f,
        rightInv := rightInv f }

      variable [HasInternalFunctors V] [HasTransFun R]

      def cancelLeft [HasCongrArg V V] {a b c : α} (f : R a b) (g : R c b) :
        g • (g⁻¹ • f) ≃ f :=
      congrArgTransLeftId R f (rightInv g) • (assoc f g⁻¹ g)⁻¹

      def cancelLeftInv [HasCongrArg V V] {a b c : α} (f : R a b) (g : R b c) :
        g⁻¹ • (g • f) ≃ f :=
      congrArgTransLeftId R f (leftInv g) • (assoc f g g⁻¹)⁻¹

      def cancelRight [HasCongrFun V V] {a b c : α} (f : R b a) (g : R b c) :
        (g • f⁻¹) • f ≃ g :=
      congrArgTransRightId R (leftInv f) g • assoc f f⁻¹ g

      def cancelRightInv [HasCongrFun V V] {a b c : α} (f : R a b) (g : R b c) :
        (g • f) • f⁻¹ ≃ g :=
      congrArgTransRightId R (rightInv f) g • assoc f⁻¹ f g

      def invEq [HasCongrFun V V] {a b : α} (f : R a b) (g : R b a) [h : IsInv R f g] : f⁻¹ ≃ g :=
      cancelRightInv R f g • (leftId f⁻¹ • congrArgTransLeft R f⁻¹ h.leftInv)⁻¹

      def reflInv [HasCongrFun V V] (a : α) : (HasRefl.refl (R := R) a)⁻¹ ≃ HasRefl.refl (R := R) a :=
      invEq R (HasRefl.refl a) (HasRefl.refl a)

      def symmInv [HasCongrFun V V] {a b : α} (f : R a b) : (f⁻¹)⁻¹ ≃ f :=
      invEq R f⁻¹ f

      def transInv [HasLinearFunOp V] {a b c : α} (f : R a b) (g : R b c) : (g • f)⁻¹ ≃ f⁻¹ • g⁻¹ :=
      invEq R (g • f) (f⁻¹ • g⁻¹)

    end

    section

      variable [HasInternalFunctors V] [HasFullFunOp V] [IsEquivalence R]
               [HasTransFun R] [HasSymmFun R]

      class IsGroupoidEquivalenceExt [h : IsGroupoidEquivalence R] extends
        IsCategoricalPreorder.IsCategoricalPreorderExt R where
      (leftInvExt  (a b : α) : substFun (symmFun R a b) (transFunFun    R a b a)
                               ≃{byDefDef • byFunDef ▻ λ f => h.leftInv  f ◅}
                               constFun (R a b) (HasRefl.refl a))
      (rightInvExt (a b : α) : substFun (symmFun R a b) (revTransFunFun R b a b)
                               ≃{byDefDef • byFunDef ▻ λ f => h.rightInv f ◅}
                               constFun (R a b) (HasRefl.refl b))

      def IsGroupoidEquivalenceExt.translate {h₁ h₂ : IsGroupoidEquivalence R}
                                             [IsGroupoidEquivalenceExt R (h := h₁)] :
        IsGroupoidEquivalenceExt R (h := h₂) :=
      { toIsCategoricalPreorderExt := IsCategoricalPreorder.IsCategoricalPreorderExt.translate R
                                        (h₁ := h₁.toIsCategoricalPreorder),
        leftInvExt  := leftInvExt  (h := h₁),
        rightInvExt := rightInvExt (h := h₁) }

      variable [HasFullFunExt V] [IsGroupoidEquivalence R] [IsGroupoidEquivalenceExt R]

      def symmInvExt (a b : α) :
        symmFun R b a • symmFun R a b
        ≃{byDefDef ▻ λ f => symmInv R f ◅}
        idFun (R a b) :=
      sorry

      def transInvExt {a b : α} (f : R a b) (c : α) :
        symmFun R a c • transFun R f c
        ≃{byDefDef ▻ λ g => transInv R f g ◅ byDefDef}
        revTransFun R c f⁻¹ • symmFun R b c :=
      sorry

      def transInvExtExt (a b c : α) :
        revCompFunFun (R b c) (symmFun R a c) • transFunFun R a b c
        ≃{byDefDef ▻ λ f => transInvExt R f c ◅ byDefDefDef • byArgDef}
        compFunFun (symmFun R b c) (R c a) • revTransFunFun R c b a • symmFun R a b :=
      sorry

    end

  end IsGroupoidEquivalence

  namespace opposite

    open IsAssociative IsCategoricalPreorder IsGroupoidEquivalence

    variable {α : Sort u} {V : Universe.{v}} [HasIdentity.{v, iv} V] (R : MetaRelation α V)

    instance isAssociative [HasTrans R] [hAssoc : IsAssociative R] : IsAssociative (opposite R) :=
    { assoc := λ f g h => (hAssoc.assoc h g f)⁻¹ }

    instance isCategoricalPreorder [IsPreorder R] [hCat : IsCategoricalPreorder R] :
      IsCategoricalPreorder (opposite R) :=
    { rightId := hCat.leftId,
      leftId  := hCat.rightId }

    instance isGroupoidEquivalence [IsEquivalence R] [hGrp : IsGroupoidEquivalence R] :
      IsGroupoidEquivalence (opposite R) :=
    { leftInv  := hGrp.rightInv,
      rightInv := hGrp.leftInv }

    variable [HasInternalFunctors V]

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

    open IsAssociative IsCategoricalPreorder IsGroupoidEquivalence

    variable {α : Sort u} {V : Universe.{v}} [HasIdentity.{v, iv} V] (R : MetaRelation α V)
             {ω : Sort w} (l : ω → α)

    instance isAssociative [HasTrans R] [h : IsAssociative R] : IsAssociative (lift R l) :=
    { assoc := h.assoc }

    instance isCategoricalPreorder [IsPreorder R] [h : IsCategoricalPreorder R] :
      IsCategoricalPreorder (lift R l) :=
    { rightId := h.rightId,
      leftId  := h.leftId }

    instance isGroupoidEquivalence [IsEquivalence R] [h : IsGroupoidEquivalence R] :
      IsGroupoidEquivalence (lift R l) :=
    { leftInv  := h.leftInv,
      rightInv := h.rightInv }

    variable [HasInternalFunctors V]

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



class MetaFunctor {α : Sort u} {V : Universe.{v}} {W : Universe.{w}} {VW : Universe.{vw}}
                  [HasFunctors V W VW] (R : MetaRelation α V) (S : MetaRelation α W) :
  Sort (max 1 u vw) where
(baseFun (a b : α) : R a b ⟶ S a b)

namespace MetaFunctor

  open MetaRelation HasSymmFun HasTransFun HasFunctors HasCongrArg HasLinearFunOp HasLinearFunExt
       HasSubLinearFunOp HasAffineFunOp HasAffineFunExt

  section

    variable {α : Sort u} {V : Universe.{v}} {W : Universe.{w}} {VW : Universe.{vw}}
             [HasFunctors V W VW] {R : MetaRelation α V} {S : MetaRelation α W}

    instance coeFun : CoeFun (MetaFunctor R S) (λ _ => ∀ {a b}, R a b → S a b) :=
    ⟨λ F {a b} => apply (F.baseFun a b)⟩

    variable [HasIdentity.{w, iw} W] (F : MetaFunctor R S)

    class IsReflFunctor  [hR : HasRefl  R] [hS : HasRefl  S] where
    (reflEq  (a     : α)                         : F (hR.refl a) ≃ hS.refl a)

    class IsSymmFunctor  [hR : HasSymm  R] [hS : HasSymm  S] where
    (symmEq  {a b   : α} (f : R a b)             : F f⁻¹ ≃ (F f)⁻¹)

    class IsTransFunctor [hR : HasTrans R] [hS : HasTrans S] where
    (transEq {a b c : α} (f : R a b) (g : R b c) : F (g • f) ≃ F g • F f)

    class IsPreorderFunctor [IsPreorder R] [IsPreorder S] extends
      IsReflFunctor F, IsTransFunctor F

    class IsEquivalenceFunctor [IsEquivalence R] [IsEquivalence S] extends
      IsPreorderFunctor F, IsSymmFunctor F

  end

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

  end

  namespace idFun

    variable {α : Sort u} {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasInternalFunctors V]
             [HasLinearFunOp V] (R : MetaRelation α V)

    def metaFunctor : MetaFunctor R R := ⟨λ a b => idFun (R a b)⟩

    instance isReflFunctor [HasRefl R] : IsReflFunctor (metaFunctor R) :=
    ⟨λ _ => byDef⟩

    instance isSymmFunctor [HasSymm R] [HasSymmFun R] : IsSymmFunctor (metaFunctor R) :=
    ⟨λ _ => (congrArgSymm R byDef)⁻¹ • byDef⟩

    instance isSymmFunctorExt [HasSymm R] [HasSymmFun R] [HasLinearFunExt V] :
      IsSymmFunctor.IsSymmFunctorExt (metaFunctor R) :=
    { symmEqExt := λ a b => (rightId (symmFun R a b))⁻¹ • leftId (symmFun R a b) }

    instance isTransFunctor [HasTrans R] [HasTransFun R] : IsTransFunctor (metaFunctor R) :=
    ⟨λ _ _ => (congrArgTrans R byDef byDef)⁻¹ • byDef⟩

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

    instance isPreorderFunctor [IsPreorder R] [HasTransFun R] :
      IsPreorderFunctor (metaFunctor R) :=
    ⟨⟩

    instance isEquivalenceFunctor [IsEquivalence R] [HasSymmFun R] [HasTransFun R] :
      IsEquivalenceFunctor (metaFunctor R) :=
    ⟨⟩

  end idFun

  namespace constFun

    section

      variable (α : Sort u) {V : Universe.{v}} {C : V}

      def constRelation (c : C) : MetaRelation α V := unitRelation α C

      instance (c : C) : IsEquivalence (constRelation α c) := unitEquivalence α c

      variable [HasIdentity V] [HasInternalFunctors V] [HasAffineFunOp V] (c : C)

      instance hasSymmFun : HasSymmFun (constRelation α c) :=
      { defSymmFun := λ _ _ => HasConstFun.defConstFun C c }

      instance hasTransFun : HasTransFun (constRelation α c) :=
      { defTransFun    := λ _ _   => HasConstFun.defConstFun C c,
        defTransFunFun := λ _ _ _ => HasConstFun.defConstFun C (constFun C c), }

    end

    variable {α : Sort u} {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasInternalFunctors V]
             [HasAffineFunOp V] (R : MetaRelation α V) {C : V} (c : C)

    def metaFunctor : MetaFunctor R (constRelation α c) :=
    ⟨λ a b => constFun (R a b) c⟩

    instance isReflFunctor [HasRefl R] : IsReflFunctor (metaFunctor R c) :=
    ⟨λ _ => byDef⟩

    instance isSymmFunctor [HasSymm R] : IsSymmFunctor (metaFunctor R c) :=
    ⟨λ _ => (congrArgSymm (constRelation α c) byDef)⁻¹ • byDef⟩

    instance isSymmFunctorExt [HasSymm R] [HasSymmFun R] [HasAffineFunExt V] :
      IsSymmFunctor.IsSymmFunctorExt (metaFunctor R c) :=
    { symmEqExt := λ a b => (leftConst (constFun (R a b) c) c)⁻¹ • leftConst (symmFun R a b) c }

    instance isTransFunctor [HasTrans R] : IsTransFunctor (metaFunctor R c) :=
    ⟨λ _ _ => (congrArgTrans (constRelation α c) byDef byDef)⁻¹ • byDef⟩

    instance isTransFunctorExt [HasTrans R] [HasTransFun R] [HasAffineFunExt V] :
      IsTransFunctor.IsTransFunctorExt (metaFunctor R c) :=
    { transEqExt    := λ {a b} f d => (leftConst (constFun (R b d) c) c)⁻¹ • leftConst (transFun R f d) c,
      transEqExtExt := λ a b d => (defCongrArg (defConstFunFun (R a b) (R b d ⟶ C))
                                                (leftConst (constFun (R b d) c) c • byDef) •
                                   rightConst (R a b) (constFun C c) (compFunFun (constFun (R b d) c) C) •
                                   defCongrArg (defRevCompFunFun (R a b) (compFunFun (constFun (R b d) c) C))
                                               (leftConst (constFun (R a b) c) (constFun C c)))⁻¹ •
                                  (leftConst (transFunFun R a b d) (constFun (R b d) c) •
                                   defCongrArg (HasCompFunFun.defCompFunFun (transFunFun R a b d) (R b d ⟶ C))
                                               (leftConstFunExt (R b d) (R a d) c)) }

    instance isPreorderFunctor    [IsPreorder    R] : IsPreorderFunctor    (metaFunctor R c) := ⟨⟩
    instance isEquivalenceFunctor [IsEquivalence R] : IsEquivalenceFunctor (metaFunctor R c) := ⟨⟩

  end constFun

  namespace compFun

    variable {α : Sort u} {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasInternalFunctors V]
             [HasLinearFunOp V] {R S T : MetaRelation α V}
             (F : MetaFunctor R S) (G : MetaFunctor S T)

    def metaFunctor : MetaFunctor R T :=
    ⟨λ a b => G.baseFun a b • F.baseFun a b⟩

    instance isReflFunctor [HasRefl R] [HasRefl S] [HasRefl T]
                           [hF : IsReflFunctor F] [hG : IsReflFunctor G] :
      IsReflFunctor (metaFunctor F G) :=
    ⟨λ a => hG.reflEq a • HasCongrArg.congrArg (G.baseFun a a) (hF.reflEq a) • byDef⟩

    instance isSymmFunctor [HasSymm R] [HasSymm S] [HasSymm T] [HasSymmFun T]
                           [hF : IsSymmFunctor F] [hG : IsSymmFunctor G] :
      IsSymmFunctor (metaFunctor F G) :=
    ⟨λ {a b} e => (congrArgSymm T byDef)⁻¹ •
                  hG.symmEq (F e) •
                  HasCongrArg.congrArg (G.baseFun b a) (hF.symmEq e) •
                  byDef⟩

    instance isSymmFunctorExt [HasSymm R] [HasSymm S] [HasSymm T]
                              [HasSymmFun R] [HasSymmFun S] [HasSymmFun T]
                              [hF : IsSymmFunctor F] [hG : IsSymmFunctor G]
                              [hFExt : IsSymmFunctor.IsSymmFunctorExt F]
                              [hGExt : IsSymmFunctor.IsSymmFunctorExt G]
                              [HasLinearFunExt V] :
      IsSymmFunctor.IsSymmFunctorExt (metaFunctor F G) :=
    { symmEqExt := λ a b => compAssoc (F.baseFun a b) (G.baseFun a b) (symmFun T a b) •
                            defCongrArg (HasCompFunFun.defCompFunFun (F.baseFun a b) (T b a)) (hGExt.symmEqExt a b) •
                            (compAssoc (F.baseFun a b) (symmFun S a b) (G.baseFun b a))⁻¹ •
                            defCongrArg (defRevCompFunFun (R a b) (G.baseFun b a)) (hFExt.symmEqExt a b) •
                            compAssoc (symmFun R a b) (F.baseFun b a) (G.baseFun b a) }

    instance isTransFunctor [HasTrans R] [HasTrans S] [HasTrans T] [HasTransFun T]
                            [hF : IsTransFunctor F] [hG : IsTransFunctor G] :
      IsTransFunctor (metaFunctor F G) :=
    ⟨λ {a b c} e f => (congrArgTrans T byDef byDef)⁻¹ •
                      hG.transEq (F e) (F f) •
                      HasCongrArg.congrArg (G.baseFun a c) (hF.transEq e f) •
                      byDef⟩

    instance isTransFunctorExt [HasTrans R] [HasTrans S] [HasTrans T]
                               [HasTransFun R] [HasTransFun S] [HasTransFun T]
                               [hF : IsTransFunctor F] [hG : IsTransFunctor G]
                               [hFExt : IsTransFunctor.IsTransFunctorExt F]
                               [hGExt : IsTransFunctor.IsTransFunctorExt G] [HasLinearFunExt V] :
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

    instance isPreorderFunctor [IsPreorder R] [IsPreorder S] [IsPreorder T] [HasTransFun T]
                               [IsPreorderFunctor F] [IsPreorderFunctor G] :
      IsPreorderFunctor (metaFunctor F G) :=
    ⟨⟩

    instance isEquivalenceFunctor [IsEquivalence R] [IsEquivalence S] [IsEquivalence T]
                                  [HasSymmFun T] [HasTransFun T]
                                  [IsEquivalenceFunctor F] [IsEquivalenceFunctor G] :
      IsEquivalenceFunctor (metaFunctor F G) :=
    ⟨⟩

  end compFun

  namespace symmFun

    open IsGroupoidEquivalence

    variable {α : Sort u} {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasInternalFunctors V]
             (R : MetaRelation α V)

    def metaFunctor [HasSymm R] [HasSymmFun R] : MetaFunctor R (opposite R) := ⟨HasSymmFun.symmFun R⟩

    variable [HasFullFunOp V] [IsEquivalence R] [IsGroupoidEquivalence R]
             [HasSymmFun R] [HasTransFun R] [IsGroupoidEquivalenceExt R]

    instance isReflFunctor : IsReflFunctor (metaFunctor R) :=
    ⟨λ a => reflInv R a • byDef⟩

    instance isSymmFunctor : IsSymmFunctor (metaFunctor R) :=
    ⟨λ _ => (congrArgSymm R byDef)⁻¹ • byDef⟩

    instance isSymmFunctorExt : IsSymmFunctor.IsSymmFunctorExt (metaFunctor R) :=
    { symmEqExt := λ a b => HasRefl.refl (symmFun R b a • symmFun R a b) }

    instance isTransFunctor : IsTransFunctor (metaFunctor R) :=
    ⟨λ f g => (congrArgTrans R byDef byDef)⁻¹ • transInv R f g • byDef⟩

    instance isTransFunctorExt : IsTransFunctor.IsTransFunctorExt (metaFunctor R) :=
    { transEqExt    := λ {a b} f c => defCongrArg (HasCompFunFun.defCompFunFun (symmFun R b c) (R c a))
                                                  (defCongrArg (defRevTransFunFun R c b a)
                                                               byDef⁻¹) •
                                      transInvExt R f c,
      transEqExtExt := λ a b c     => transInvExtExt R a b c }

    instance isPreorderFunctor    : IsPreorderFunctor    (metaFunctor R) := ⟨⟩
    instance isEquivalenceFunctor : IsEquivalenceFunctor (metaFunctor R) := ⟨⟩

  end symmFun

  @[reducible] def PreFunctor {α : Sort u} {β : Sort u'} {V : Universe.{v}}
                              {W : Universe.{w}} {VW : Universe.{vw}} [HasFunctors V W VW]
                              (R : MetaRelation α V) (S : MetaRelation β W) (φ : α → β) :=
  MetaFunctor R (lift S φ)

end MetaFunctor



def MetaQuantification {α : Sort u} {β : Sort u'} {W : Universe.{w}} (S : MetaRelation β W)
                       (φ ψ : α → β) :=
∀ a, S (φ a) (ψ a)

namespace MetaQuantification

  open MetaRelation MetaFunctor HasTransFun IsAssociative IsCategoricalPreorder
       IsCategoricalPreorderExt IsGroupoidEquivalence
       HasFunctors HasCongrArg HasLinearFunOp

  section

    variable {α : Sort u} {β : Sort u'} {W : Universe.{w}} (S : MetaRelation β W)

    def refl [HasRefl S] (φ : α → β) : MetaQuantification S φ φ :=
    λ a => HasRefl.refl (φ a)

    def symm [HasSymm S] {φ ψ : α → β} (η : MetaQuantification S φ ψ) :
      MetaQuantification S ψ φ :=
    λ a => (η a)⁻¹

    def trans [HasTrans S] {φ ψ χ : α → β} (η : MetaQuantification S φ ψ)
                                           (ε : MetaQuantification S ψ χ) :
      MetaQuantification S φ χ :=
    λ a => ε a • η a

  end

  section

    variable {α : Sort u} {β : Sort u'} {V : Universe.{v}} {W : Universe.{w}}
             {VW : Universe.{vw}} [HasFunctors V W VW] [HasIdentity.{w, iw} W]
             {R : MetaRelation α V} {S : MetaRelation β W}

    class IsNatural {φ ψ : α → β} (F : PreFunctor R S φ) (G : PreFunctor R S ψ)
                    (η : MetaQuantification S φ ψ) [hTrans : HasTrans S] where
    (nat {a b : α} (f : R a b) : hTrans.trans (η a) (G f) ≃ hTrans.trans (F f) (η b))

    namespace IsNatural

      instance refl [IsPreorder S] [IsCategoricalPreorder S] {φ : α → β}
                    (F : PreFunctor R S φ) :
        IsNatural F F (MetaQuantification.refl S φ) :=
      ⟨λ f => (leftId (F f))⁻¹ • rightId (F f)⟩

      variable [HasInternalFunctors W] [HasCongrFun W W]

      instance symm [IsEquivalence S] [IsGroupoidEquivalence S] [HasTransFun S]
                    {φ ψ : α → β} {F : PreFunctor R S φ} {G : PreFunctor R S ψ}
                    (η : MetaQuantification S φ ψ) [hη : IsNatural F G η] :
        IsNatural G F (MetaQuantification.symm S η) :=
      ⟨λ {a b} f => cancelRightInv S (η a) ((η b)⁻¹ • G f) •
                    (cancelLeftInv S (F f • (η a)⁻¹) (η b) •
                     congrArgTransRight S (assoc (η a)⁻¹ (F f) (η b)) (η b)⁻¹ •
                     assoc (η a)⁻¹ (η b • F f) (η b)⁻¹ •
                     congrArgTransLeft S (η a)⁻¹ (congrArgTransRight S (hη.nat f) (η b)⁻¹ •
                                                  assoc (η a) (G f) (η b)⁻¹))⁻¹⟩

      instance trans [HasTrans S] [IsAssociative S] [HasTransFun S] {φ ψ χ : α → β}
                     {F : PreFunctor R S φ} {G : PreFunctor R S ψ} {H : PreFunctor R S χ}
                     (η : MetaQuantification S φ ψ) [hη : IsNatural F G η]
                     (ε : MetaQuantification S ψ χ) [hε : IsNatural G H ε] :
        IsNatural F H (MetaQuantification.trans S η ε) :=
      ⟨λ {a b} f => (assoc (R := S) (F f) (η b) (ε b))⁻¹ •
                    congrArgTransRight S (hη.nat f) (ε b) •
                    assoc (η a) (G f) (ε b) •
                    congrArgTransLeft S (η a) (hε.nat f) •
                    (assoc (η a) (ε a) (H f))⁻¹⟩

    end IsNatural

  end

  section

    namespace IsNatural

      variable {α : Sort u} {β : Sort u'} {W : Universe.{w}} [HasIdentity.{w, iw} W]
               [HasInternalFunctors W] {R : MetaRelation α W} {S : MetaRelation β W}

      class IsNaturalExt [HasLinearFunOp W] [HasTrans S] [HasTransFun S]
                         {φ ψ : α → β} (F : PreFunctor R S φ) (G : PreFunctor R S ψ)
                         (η : MetaQuantification S φ ψ) [h : IsNatural F G η] where
      (natExt (a b : α) :
         transFun S (η a) (ψ b) • G.baseFun a b
         ≃{byDef ▻ λ f => h.nat f ◅ byDef}
         revTransFun S (φ a) (η b) • F.baseFun a b)

      namespace IsNaturalExt

        instance refl [HasLinearFunOp W] [IsPreorder S] [IsCategoricalPreorder S]
                      [HasTransFun S] [IsCategoricalPreorderExt S]
                      {φ : α → β} (F : PreFunctor R S φ) :
          IsNaturalExt F F (MetaQuantification.refl S φ) :=
        ⟨λ a b => defCongrArg (HasCompFunFun.defCompFunFun (F.baseFun a b) (S (φ a) (φ b)))
                              ((leftIdExt (φ a) (φ b))⁻¹ • rightIdExt (φ a) (φ b))⟩

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

  end

end MetaQuantification
