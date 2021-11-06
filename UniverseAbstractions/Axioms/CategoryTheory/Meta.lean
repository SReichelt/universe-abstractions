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



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w vw iv iw



namespace MetaRelation

  open HasFunctors HasCongrArg HasCongrFun HasLinearFunOp HasSubLinearFunOp HasFullFunOp
       HasTransFun HasSymmFun

  variable {α : Sort u} {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasInternalFunctors V]
           (R : MetaRelation α V)

  class IsAssociative [HasTrans R] where
  (assoc {a b c d : α} (f : R a b) (g : R b c) (h : R c d) : (h • g) • f ≃ h • (g • f))

  namespace IsAssociative

    section

      variable [HasTrans R] [h : IsAssociative R]

      class IsAssociativeExt [HasLinearFunOp V] [HasTransFun R] where
      (assocExt {a b c : α} (f : R a b) (g : R b c) (d : α) :
         transFun R f d • transFun R g d
         ≃{byDef • byArgDef ▻ λ h => assoc f g h ◅}
         transFun R (g • f) d)
      (assocExtExt {a b : α} (f : R a b) (c d : α) :
         revCompFunFun (R c d) (transFun R f d) • transFunFun R b c d
         ≃{byDef • byArgDef ▻ λ g => assocExt f g d ◅ byDef • byArgDef}
         transFunFun R a c d • transFun R f c)
      (assocExtExtExt (a b c d : α) :
         compFunFun (transFunFun R b c d) (R c d ⟶ R a d) •
         revCompFunFunFun (R c d) (R b d) (R a d) •
         transFunFun R a b d
         ≃{byDef • byArgDef • byArgDef₂ • byArgDef ▻
           λ f => assocExtExt f c d
           ◅ byDef • byArgDef}
         revCompFunFun (R b c) (transFunFun R a c d) • transFunFun R a b c)

    end

    def IsAssociativeExt.translate [HasLinearFunOp V] [HasTrans R] [HasTransFun R]
                                   {h₁ h₂ : IsAssociative R} [IsAssociativeExt R (h := h₁)] :
      IsAssociativeExt R (h := h₂) :=
    { assocExt       := assocExt       (h := h₁),
      assocExtExt    := assocExtExt    (h := h₁),
      assocExtExtExt := assocExtExtExt (h := h₁) }

  end IsAssociative

  class IsCategoricalPreorder [IsPreorder R] extends IsAssociative R where
  (rightId {a b : α} (f : R a b) : f • HasRefl.refl a ≃ f)
  (leftId  {a b : α} (f : R a b) : HasRefl.refl b • f ≃ f)

  namespace IsCategoricalPreorder

    section

      variable [IsPreorder R] [h : IsCategoricalPreorder R]

      def idId (a : α) :
        HasRefl.refl (R := R) a • HasRefl.refl (R := R) a ≃ HasRefl.refl (R := R) a :=
      rightId (HasRefl.refl a)

      def congrArgTransLeftId [HasCongrArg V V] [HasTransFun R]
                              {a b : α} (f : R a b) {g : R b b} (hg : g ≃ HasRefl.refl (R := R) b) :
        g • f ≃ f :=
      leftId f • congrArgTransLeft R f hg

      def congrArgTransRightId [HasCongrFun V V] [HasTransFun R]
                               {a b : α} {f : R a a} (hf : f ≃ HasRefl.refl (R := R) a) (g : R a b) :
        g • f ≃ g :=
      rightId g • congrArgTransRight R hf g

      class IsCategoricalPreorderExt [HasLinearFunOp V] [IsPreorder R] [HasTransFun R]
                                     [h : IsCategoricalPreorder R] extends
        IsAssociative.IsAssociativeExt R where
      (rightIdExt (a b : α) : transFun    R (HasRefl.refl a) b ≃{▻ λ f => h.rightId f ◅} idFun (R a b))
      (leftIdExt  (a b : α) : revTransFun R a (HasRefl.refl b) ≃{▻ λ f => h.leftId  f ◅} idFun (R a b))

    end

    def IsCategoricalPreorderExt.translate [HasLinearFunOp V] [IsPreorder R] [HasTransFun R]
                                           {h₁ h₂ : IsCategoricalPreorder R}
                                           [IsCategoricalPreorderExt R (h := h₁)] :
      IsCategoricalPreorderExt R (h := h₂) :=
    { toIsAssociativeExt := IsAssociative.IsAssociativeExt.translate R (h₁ := h₁.toIsAssociative),
      rightIdExt := rightIdExt (h := h₁),
      leftIdExt  := leftIdExt  (h := h₁) }

  end IsCategoricalPreorder

  def HalfInv [IsPreorder R] {a b : α} (f : R a b) (g : R b a) := g • f ≃ HasRefl.refl (R := R) a

  namespace HalfInv

    open IsAssociative IsCategoricalPreorder

    variable [IsPreorder R] [IsCategoricalPreorder R]

    def refl (a : α) : HalfInv R (HasRefl.refl a) (HasRefl.refl a) := idId R a

    variable [HasTransFun R] [HasLinearFunOp V]

    def trans {a b c : α} {f₁ : R a b} {g₁ : R b a} (e₁ : HalfInv R f₁ g₁)
                          {f₂ : R b c} {g₂ : R c b} (e₂ : HalfInv R f₂ g₂) :
      HalfInv R (f₂ • f₁) (g₁ • g₂) :=
    e₁ •
    congrArgTransRight R (leftId f₁ •
                          congrArgTransLeft R f₁ e₂ •
                          (assoc f₁ f₂ g₂)⁻¹) g₁ •
    assoc (f₂ • f₁) g₂ g₁

  end HalfInv

  class IsPreGroupoidEquivalence [IsEquivalence R] extends IsCategoricalPreorder R where
  (leftInv  {a b : α} (f : R a b) : HalfInv R f f⁻¹)
  (rightInv {a b : α} (f : R a b) : HalfInv R f⁻¹ f)

  namespace IsPreGroupoidEquivalence

    open IsCategoricalPreorder

    section

      variable [IsEquivalence R] [h : IsPreGroupoidEquivalence R]

      def cancelLeft [HasCongrArg V V] [HasTransFun R]
                     {a b c : α} (f : R a b) (g : R c b) : g • (g⁻¹ • f) ≃ f :=
      congrArgTransLeftId R f (h.rightInv g) • (h.assoc f g⁻¹ g)⁻¹

      def cancelLeftInv [HasCongrArg V V] [HasTransFun R]
                        {a b c : α} (f : R a b) (g : R b c) : g⁻¹ • (g • f) ≃ f :=
      congrArgTransLeftId R f (h.leftInv g) • (h.assoc f g g⁻¹)⁻¹

      def cancelRight [HasCongrFun V V] [HasTransFun R]
                      {a b c : α} (f : R b a) (g : R b c) : (g • f⁻¹) • f ≃ g :=
      congrArgTransRightId R (h.leftInv f) g • h.assoc f f⁻¹ g

      def cancelRightInv [HasCongrFun V V] [HasTransFun R]
                         {a b c : α} (f : R a b) (g : R b c) : (g • f) • f⁻¹ ≃ g :=
      congrArgTransRightId R (h.rightInv f) g • h.assoc f⁻¹ f g

      class IsPreGroupoidEquivalenceExt [HasFullFunOp V] [HasTransFun R] [HasSymmFun R] extends
        IsCategoricalPreorder.IsCategoricalPreorderExt R where
      (leftInvExt  (a b : α) : substFun (symmFun R a b) (transFunFun    R a b a)
                               ≃{byDef • byArgDef • byFunDef ▻ λ f => h.leftInv  f ◅}
                               constFun (R a b) (HasRefl.refl a))
      (rightInvExt (a b : α) : substFun (symmFun R a b) (revTransFunFun R b a b)
                               ≃{byDef • byArgDef • byFunDef ▻ λ f => h.rightInv f ◅}
                               constFun (R a b) (HasRefl.refl b))

    end

    def IsPreGroupoidEquivalenceExt.translate [HasFullFunOp V] [IsEquivalence R] [HasTransFun R]
                                              [HasSymmFun R] {h₁ h₂ : IsPreGroupoidEquivalence R}
                                              [IsPreGroupoidEquivalenceExt R (h := h₁)] :
      IsPreGroupoidEquivalenceExt R (h := h₂) :=
    { toIsCategoricalPreorderExt := IsCategoricalPreorder.IsCategoricalPreorderExt.translate R
                                      (h₁ := h₁.toIsCategoricalPreorder),
      leftInvExt  := leftInvExt  (h := h₁),
      rightInvExt := rightInvExt (h := h₁) }

  end IsPreGroupoidEquivalence

  -- These axioms are, of course, derivable (in the presence of `HasTransFun`), but we prefer to
  -- include them explicitly because they hold definitionally for `IsoDesc`.
  class IsGroupoidEquivalence [IsEquivalence R] extends IsPreGroupoidEquivalence R where
  (reflInv  (a     : α)                         : (HasRefl.refl (R := R) a)⁻¹ ≃ HasRefl.refl (R := R) a)
  (symmInv  {a b   : α} (f : R a b)             : (f⁻¹)⁻¹ ≃ f)
  (transInv {a b c : α} (f : R a b) (g : R b c) : (g • f)⁻¹ ≃ f⁻¹ • g⁻¹)

  namespace IsGroupoidEquivalence

    open IsCategoricalPreorder IsPreGroupoidEquivalence

    def fromIsPreGroupoidEquivalence [HasCongrFun V V] [IsEquivalence R] [h : IsPreGroupoidEquivalence R]
                                     [HasTransFun R] :
      IsGroupoidEquivalence R :=
    { reflInv  := λ a   => h.leftInv (HasRefl.refl a) •
                           (h.rightId (HasRefl.refl a)⁻¹)⁻¹,
      symmInv  := λ f   => congrArgTransLeftId R f (h.leftInv f⁻¹) •
                           (cancelRight R f (f⁻¹)⁻¹)⁻¹,
      transInv := λ f g => congrArgTransLeft R g⁻¹ (congrArgTransLeftId R f⁻¹ (h.leftInv (g • f) •
                                                                               h.assoc f g (g • f)⁻¹) •
                                                    (cancelRightInv R f ((g • f)⁻¹ • g))⁻¹) •
                           (cancelRightInv R g (g • f)⁻¹)⁻¹ }

    section

      variable [IsEquivalence R] [h : IsGroupoidEquivalence R]

      class IsGroupoidEquivalenceExt [HasFullFunOp V] [HasTransFun R] [HasSymmFun R] extends
        IsPreGroupoidEquivalence.IsPreGroupoidEquivalenceExt R where
      (symmInvExt  (a b : α) :
         symmFun R b a • symmFun R a b
         ≃{byDef • byArgDef ▻ λ f => h.symmInv f ◅}
         idFun (R a b))
      (transInvExt {a b : α} (f : R a b) (c : α) :
         symmFun R a c • transFun R f c
         ≃{byDef • byArgDef ▻ λ g => h.transInv f g ◅ byDef • byArgDef}
         revTransFun R c f⁻¹ • symmFun R b c)
      (transInvExtExt (a b c : α) :
         revCompFunFun (R b c) (symmFun R a c) • transFunFun R a b c
         ≃{byDef • byArgDef ▻ λ f => transInvExt f c ◅ byDef • byArgDef • byArgDef₂ • byArgDef}
         compFunFun (symmFun R b c) (R c a) • revTransFunFun R c b a • symmFun R a b)

      -- TODO: We should probably have `fromIsPreGroupoidEquivalenceExt` in addition to
      -- `fromIsPreGroupoidEquivalence` above.

    end

    def IsGroupoidEquivalenceExt.translate [HasFullFunOp V] [IsEquivalence R] [HasTransFun R]
                                           [HasSymmFun R] {h₁ h₂ : IsGroupoidEquivalence R}
                                           [IsGroupoidEquivalenceExt R (h := h₁)] :
      IsGroupoidEquivalenceExt R (h := h₂) :=
    { toIsPreGroupoidEquivalenceExt := IsPreGroupoidEquivalence.IsPreGroupoidEquivalenceExt.translate R
                                         (h₁ := h₁.toIsPreGroupoidEquivalence),
      symmInvExt     := symmInvExt     (h := h₁),
      transInvExt    := transInvExt    (h := h₁),
      transInvExtExt := transInvExtExt (h := h₁) }

  end IsGroupoidEquivalence

end MetaRelation



class MetaFunctor {α : Sort u} {V : Universe.{v}} {W : Universe.{w}} {VW : Universe.{vw}}
                  [HasFunctors V W VW] (R : MetaRelation α V) (S : MetaRelation α W) :
  Sort (max 1 u vw) where
(baseFun (a b : α) : R a b ⟶ S a b)

namespace MetaFunctor

  open MetaRelation HasSymmFun HasTransFun HasFunctors HasCongrArg HasLinearFunOp HasLinearFunExt

  section

    variable {α : Sort u} {V : Universe.{v}} {W : Universe.{w}} {VW : Universe.{vw}}
             [HasIdentity.{w, iw} W] [HasFunctors V W VW]
             {R : MetaRelation α V} {S : MetaRelation α W}

    instance coeFun : CoeFun (MetaFunctor R S) (λ _ => ∀ {a b}, R a b → S a b) :=
    ⟨λ F {a b} => apply (F.baseFun a b)⟩

    variable (F : MetaFunctor R S)

    class IsReflFunctor  [HasRefl  R] [HasRefl  S] where
    (reflEq  (a     : α)                         : F (HasRefl.refl a) ≃ HasRefl.refl (R := S) a)

    class IsSymmFunctor  [HasSymm  R] [HasSymm  S] where
    (symmEq  {a b   : α} (f : R a b)             : F f⁻¹ ≃ (F f)⁻¹)

    class IsTransFunctor [HasTrans R] [HasTrans S] where
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

      class IsSymmFunctorExt [HasLinearFunOp V] [HasSymm R] [HasSymmFun R] [HasSymm S]
                             [HasSymmFun S] [h : IsSymmFunctor F] where
      (symmEqExt (a b : α) :
         F.baseFun b a • symmFun R a b
         ≃{byArgDef ▻ λ f => symmEq f ◅ byDef}
         symmFun S a b • F.baseFun a b)

      def IsSymmFunctorExt.translate [HasLinearFunOp V] [HasSymm R] [HasSymmFun R]
                                     [HasSymm S] [HasSymmFun S] {h₁ h₂ : IsSymmFunctor F}
                                     [IsSymmFunctorExt F (h := h₁)] :
        IsSymmFunctorExt F (h := h₂) :=
      { symmEqExt := symmEqExt (h := h₁) }

    end IsSymmFunctor

    namespace IsTransFunctor

      class IsTransFunctorExt [HasLinearFunOp V] [HasTrans R] [HasTransFun R] [HasTrans S]
                              [HasTransFun S] [h : IsTransFunctor F] where
      (transEqExt {a b : α} (f : R a b) (c : α) :
         F.baseFun a c • transFun R f c
         ≃{byArgDef ▻ λ g => transEq f g ◅ byDef}
         transFun S (F f) c • F.baseFun b c)
      (transEqExtExt (a b c : α) :
         revCompFunFun (R b c) (F.baseFun a c) • transFunFun R a b c
         ≃{byDef • byArgDef ▻ λ f => transEqExt f c ◅ byDef • byArgDef • byArgDef}
         compFunFun (F.baseFun b c) (S a c) • transFunFun S a b c • F.baseFun a b)

      def IsTransFunctorExt.translate [HasLinearFunOp V] [HasTrans R] [HasTransFun R]
                                      [HasTrans S] [HasTransFun S] {h₁ h₂ : IsTransFunctor F}
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

    instance isReflFunctor [HasRefl R] : IsReflFunctor  (metaFunctor R) :=
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
                                       defCongrArg (defCompFunFun (idFun (R b c)) (R a c))
                                                   (defCongrArg (defTransFunFun a b c) byDef))⁻¹ •
                                      leftId (transFun R f c),
      transEqExtExt := λ a b c => (rightId (transFunFun R a b c) •
                                   leftId (transFunFun R a b c • idFun (R a b)) •
                                   defCongrArg (defCompFunFun (transFunFun R a b c • idFun (R a b))
                                                              ((R b c) ⟶ (R a c)))
                                               (rightIdExt (R b c) (R a c)))⁻¹ •
                                  (leftId (transFunFun R a b c) •
                                   defCongrArg (defCompFunFun (transFunFun R a b c)
                                                              ((R b c) ⟶ (R a c)))
                                               (leftIdExt (R b c) (R a c))) }

    instance isPreorderFunctor [IsPreorder R] [HasTransFun R] :
      IsPreorderFunctor (metaFunctor R) :=
    ⟨⟩

    instance isEquivalenceFunctor [IsEquivalence R] [HasSymmFun R] [HasTransFun R] :
      IsEquivalenceFunctor (metaFunctor R) :=
    ⟨⟩

  end idFun

  -- TODO: comp, const

  @[reducible] def PreFunctor {α : Sort u} {β : Sort v} {W : Universe.{w}}
                              [HasIdentity.{w, iw} W] [HasInternalFunctors W]
                              (R : MetaRelation α W) (S : MetaRelation β W) (φ : α → β) :=
  MetaFunctor R (lift S φ)

end MetaFunctor
