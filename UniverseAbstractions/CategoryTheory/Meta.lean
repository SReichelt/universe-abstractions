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
import UniverseAbstractions.Axioms.Universe.Equivalences
import UniverseAbstractions.Lemmas.DerivedFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u u' u'' v w w' vv vw wv v_v v_w iv iw ivw



namespace MetaRelation

  open HasFunctors HasCongrArg HasCongrFun HasLinearFunOp HasTransFun HasSymmFun

  variable {α : Sort u} {V : Universe.{v}} [HasIdentity.{v, iv} V]

  section

    variable {R : MetaRelation α V}

    class HasReflEq  (hR₁ hR₂ : HasRefl  R) where
    (reflEq  (a     : α)                         : hR₁.refl a ≃ hR₂.refl a)

    class HasSymmEq  (hR₁ hR₂ : HasSymm  R) where
    (symmEq  {a b   : α} (f : R a b)             : hR₁.symm f ≃ hR₂.symm f)

    class HasTransEq (hR₁ hR₂ : HasTrans R) where
    (transEq {a b c : α} (f : R a b) (g : R b c) : hR₁.trans f g ≃ hR₂.trans f g)

    class IsPreorderEq (hR₁ hR₂ : IsPreorder R) extends
      HasReflEq hR₁.toHasRefl hR₂.toHasRefl, HasTransEq hR₁.toHasTrans hR₂.toHasTrans

    class IsEquivalenceEq (hR₁ hR₂ : IsEquivalence R) extends
      IsPreorderEq hR₁.toIsPreorder hR₂.toIsPreorder, HasSymmEq hR₁.toHasSymm hR₂.toHasSymm

  end

  section

    variable (R : MetaRelation α V)

    instance HasReflEq.refl  [hR : HasRefl  R] : HasReflEq  hR hR := ⟨λ a   => HasRefl.refl (hR.refl a)⟩
    instance HasSymmEq.refl  [hR : HasSymm  R] : HasSymmEq  hR hR := ⟨λ f   => HasRefl.refl f⁻¹⟩
    instance HasTransEq.refl [hR : HasTrans R] : HasTransEq hR hR := ⟨λ f g => HasRefl.refl (g • f)⟩

    instance IsPreorderEq.refl    [hR : IsPreorder    R] : IsPreorderEq    hR hR := ⟨⟩
    instance IsEquivalenceEq.refl [hR : IsEquivalence R] : IsEquivalenceEq hR hR := ⟨⟩

  end

  class IsAssociative (R : MetaRelation α V) [HasTrans R] where
  (assoc {a b c d : α} (f : R a b) (g : R b c) (h : R c d) : (h • g) • f ≃ h • (g • f))

  namespace IsAssociative

    variable {R : MetaRelation α V} [HasTrans R] [IsAssociative R]

    def assoc₄ {a b c d e : α} (f : R a b) (g : R b c) (h : R c d) (i : R d e) :
      ((i • h) • g) • f ≃ i • (h • (g • f)) :=
    assoc (g • f) h i • assoc f g (i • h)

  end IsAssociative

  class IsCategoricalPreorder (R : MetaRelation α V) [IsPreorder R] extends IsAssociative R where
  (rightId {a b : α} (f : R a b) : f • HasRefl.refl a ≃ f)
  (leftId  {a b : α} (f : R a b) : HasRefl.refl b • f ≃ f)

  namespace IsCategoricalPreorder

    variable {R : MetaRelation α V} [IsPreorder R] [IsCategoricalPreorder R]

    def idId (a : α) :
      HasRefl.refl (R := R) a • HasRefl.refl (R := R) a ≃ HasRefl.refl (R := R) a :=
    rightId (HasRefl.refl a)

    variable [HasInternalFunctors V] [HasTransFun R]

    def cancelLeftId [HasCongrArg V V] {a b : α} (f : R a b) {e : R b b}
                     (he : e ≃ HasRefl.refl (R := R) b) :
      e • f ≃ f :=
    leftId f • congrArgTransLeft f he

    def cancelRightId [HasCongrFun V V] {a b : α} {e : R a a}
                      (he : e ≃ HasRefl.refl (R := R) a) (f : R a b) :
      f • e ≃ f :=
    rightId f • congrArgTransRight he f

  end IsCategoricalPreorder

  def HalfInv {R : MetaRelation α V} [IsPreorder R] {a b : α} (f : R a b) (g : R b a) :=
  g • f ≃ HasRefl.refl (R := R) a

  namespace HalfInv

    open IsAssociative IsCategoricalPreorder

    variable {R : MetaRelation α V} [IsPreorder R] [IsCategoricalPreorder R]

    def refl (a : α) : HalfInv (R := R) (HasRefl.refl a) (HasRefl.refl a) := idId a

    variable [HasInternalFunctors V] [HasCongrFun V V] [HasTransFun R]

    def trans {a b c : α} {f₁ : R a b} {g₁ : R b a} (e₁ : HalfInv f₁ g₁)
                          {f₂ : R b c} {g₂ : R c b} (e₂ : HalfInv f₂ g₂) :
      HalfInv (f₂ • f₁) (g₁ • g₂) :=
    e₁ •
    congrArgTransRight (leftId f₁ • congrArgTransLeft f₁ e₂ • (assoc f₁ f₂ g₂)⁻¹) g₁ •
    assoc (f₂ • f₁) g₂ g₁

    def unique {a b : α} {f : R a b} {g₁ g₂ : R b a} (h₁ : HalfInv f g₁) (h₂ : HalfInv g₂ f) :
      g₂ ≃ g₁ :=
    cancelRightId h₂ g₁ •
    assoc g₂ f g₁ •
    (cancelLeftId g₂ h₁)⁻¹

    def congrArgLeft {a b : α} {f : R a b} {g₁ g₂ : R b a} (hg : g₁ ≃ g₂) (h : HalfInv f g₂) :
      HalfInv f g₁ :=
    h • congrArgTransLeft f hg

    def congrArgRight {a b : α} {f₁ f₂ : R a b} (hf : f₁ ≃ f₂) {g : R b a} (h : HalfInv f₂ g) :
      HalfInv f₁ g :=
    h • congrArgTransRight hf g

  end HalfInv

  class IsInv {R : MetaRelation α V} [IsPreorder R] {a b : α} (f : R a b) (g : R b a) where
  (leftInv  : HalfInv f g)
  (rightInv : HalfInv g f)

  namespace IsInv

    open IsAssociative IsCategoricalPreorder

    variable {R : MetaRelation α V} [IsPreorder R] [IsCategoricalPreorder R]

    instance refl (a : α) : IsInv (R := R) (HasRefl.refl a) (HasRefl.refl a) :=
    { leftInv  := HalfInv.refl a,
      rightInv := HalfInv.refl a }

    instance symm {a b : α} (f : R a b) (g : R b a) [h : IsInv f g] : IsInv g f :=
    { leftInv  := h.rightInv,
      rightInv := h.leftInv }

    variable [HasInternalFunctors V] [HasCongrFun V V] [HasTransFun R]

    instance trans {a b c : α} (f₁ : R a b) (g₁ : R b a) [h₁ : IsInv f₁ g₁]
                               (f₂ : R b c) (g₂ : R c b) [h₂ : IsInv f₂ g₂] :
      IsInv (f₂ • f₁) (g₁ • g₂) :=
    { leftInv  := HalfInv.trans h₁.leftInv  h₂.leftInv,
      rightInv := HalfInv.trans h₂.rightInv h₁.rightInv }

    def unique {a b : α} (f : R a b) (g₁ g₂ : R b a) [h₁ : IsInv f g₁] [h₂ : IsInv f g₂] :
      g₂ ≃ g₁ :=
    HalfInv.unique h₁.leftInv h₂.rightInv

    def congrArgLeft {a b : α} (f : R a b) {g₁ g₂ : R b a} (hg : g₁ ≃ g₂) [h : IsInv f g₂] :
      IsInv f g₁ :=
    { leftInv  := HalfInv.congrArgLeft  hg h.leftInv,
      rightInv := HalfInv.congrArgRight hg h.rightInv }

    def congrArgRight {a b : α} {f₁ f₂ : R a b} (hf : f₁ ≃ f₂) (g : R b a) [h : IsInv f₂ g] :
      IsInv f₁ g :=
    { leftInv  := HalfInv.congrArgRight hf h.leftInv,
      rightInv := HalfInv.congrArgLeft  hf h.rightInv }

  end IsInv

  class IsGroupoidEquivalence (R : MetaRelation α V) [IsEquivalence R] extends
    IsCategoricalPreorder R where
  (leftInv  {a b : α} (f : R a b) : HalfInv f f⁻¹)
  (rightInv {a b : α} (f : R a b) : HalfInv f⁻¹ f)

  namespace IsGroupoidEquivalence

    open IsAssociative IsCategoricalPreorder

    variable {R : MetaRelation α V} [IsEquivalence R] [IsGroupoidEquivalence R]

    instance isInv {a b : α} (f : R a b) : IsInv f f⁻¹ :=
    { leftInv  := leftInv  f,
      rightInv := rightInv f }

    variable [HasInternalFunctors V] [HasTransFun R]

    def invEq [HasCongrFun V V] {a b : α} (f : R a b) (g : R b a) [h : IsInv f g] : f⁻¹ ≃ g :=
    IsInv.unique f g f⁻¹

    def reflInv [HasCongrFun V V] (a : α) : (HasRefl.refl (R := R) a)⁻¹ ≃ HasRefl.refl (R := R) a :=
    invEq (HasRefl.refl a) (HasRefl.refl a)

    def symmInv [HasCongrFun V V] {a b : α} (f : R a b) : (f⁻¹)⁻¹ ≃ f :=
    invEq f⁻¹ f

    def transInv [HasLinearFunOp V] {a b c : α} (f : R a b) (g : R b c) : (g • f)⁻¹ ≃ f⁻¹ • g⁻¹ :=
    invEq (g • f) (f⁻¹ • g⁻¹)

    def cancelLeft [HasCongrArg V V] {a b c : α} (f : R a b) (g : R c b) :
      g • (g⁻¹ • f) ≃ f :=
    cancelLeftId f (rightInv g) • (assoc f g⁻¹ g)⁻¹

    def cancelLeftInv [HasCongrArg V V] {a b c : α} (f : R a b) (g : R b c) :
      g⁻¹ • (g • f) ≃ f :=
    cancelLeftId f (leftInv g) • (assoc f g g⁻¹)⁻¹

    def cancelRight [HasCongrFun V V] {a b c : α} (f : R b a) (g : R b c) :
      (g • f⁻¹) • f ≃ g :=
    cancelRightId (leftInv f) g • assoc f f⁻¹ g

    def cancelRightInv [HasCongrFun V V] {a b c : α} (f : R a b) (g : R b c) :
      (g • f) • f⁻¹ ≃ g :=
    cancelRightId (rightInv f) g • assoc f⁻¹ f g

  end IsGroupoidEquivalence

  namespace opposite

    variable (R : MetaRelation α V)

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

  end opposite

  namespace lift

    variable (R : MetaRelation α V) {ω : Sort w} (l : ω → α)

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

  end lift

end MetaRelation

namespace MetaRelation.emptyRelation

  variable (V : Universe.{v}) {VV : Universe.{vv}} [HasIdentity.{v, iv} V] [HasFunctors V V VV]

  instance isAssociative : IsAssociative (emptyRelation V) :=
  { assoc := λ {e _ _ _} _ _ _ => PEmpty.elim e }

  instance isCategoricalPreorder : IsCategoricalPreorder (emptyRelation V) :=
  { rightId := λ {e _} _ => PEmpty.elim e,
    leftId  := λ {e _} _ => PEmpty.elim e }

  instance isGroupoidEquivalence : IsGroupoidEquivalence (emptyRelation V) :=
  { leftInv  := λ {e _} _ => PEmpty.elim e,
    rightInv := λ {e _} _ => PEmpty.elim e }

end MetaRelation.emptyRelation



structure MetaFunctor {α : Sort u} {V : Universe.{v}} {W : Universe.{w}} {VW : Universe.{vw}}
                      [HasFunctors V W VW] (R : MetaRelation α V) (S : MetaRelation α W) :
  Sort (max 1 u vw) where
(baseFun (a b : α) : R a b ⟶ S a b)

namespace MetaFunctor

  open MetaRelation HasSymmFun HasTransFun HasFunctors HasCongrArg HasLinearFunOp
       HasSubLinearFunOp HasAffineFunOp

  section

    variable {α : Sort u} {V : Universe.{v}} {W : Universe.{w}} {VW : Universe.{vw}}
             [HasFunctors V W VW] {R : MetaRelation α V} {S : MetaRelation α W}

    instance coeFun : CoeFun (MetaFunctor R S) (λ _ => ∀ {a b}, R a b → S a b) :=
    ⟨λ F {a b} => apply (F.baseFun a b)⟩

    variable [HasIdentity.{w, iw} W]

    def fromDefFun {f : ∀ a b, R a b → S a b} (F : ∀ a b, R a b ⟶{f a b} S a b) :
      MetaFunctor R S :=
    ⟨λ a b => F a b⟩

    variable (F : MetaFunctor R S)

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

    def mapHalfInv [HasIdentity V] [HasCongrArg V W] [IsPreorder R] [IsPreorder S]
                   [hF : IsPreorderFunctor F] {a b : α} {f : R a b} {g : R b a}
                   (hfg : HalfInv f g) :
      HalfInv (F f) (F g) :=
    hF.reflEq a •
    HasCongrArg.congrArg (F.baseFun a a) hfg •
    (hF.transEq f g)⁻¹

    def lift {ω : Sort w'} (l : ω → α) : MetaFunctor (lift R l) (lift S l) :=
    ⟨λ a b => F.baseFun (l a) (l b)⟩

    namespace lift

      variable {ω : Sort w'} (l : ω → α)

      instance isReflFunctor [HasRefl R] [HasRefl S] [h : IsReflFunctor F] :
        IsReflFunctor (lift F l) :=
      ⟨λ a => h.reflEq (l a)⟩

      instance isSymmFunctor [HasSymm R] [HasSymm S] [h : IsSymmFunctor F] :
        IsSymmFunctor (lift F l) :=
      ⟨h.symmEq⟩

      instance isTransFunctor [HasTrans R] [HasTrans S] [h : IsTransFunctor F] :
        IsTransFunctor (lift F l) :=
      ⟨h.transEq⟩

      instance isPreorderFunctor [IsPreorder R] [IsPreorder S] [h : IsPreorderFunctor F] :
        IsPreorderFunctor (lift F l) :=
      ⟨⟩

      instance isEquivalenceFunctor [IsEquivalence R] [IsEquivalence S] [IsEquivalenceFunctor F] :
        IsEquivalenceFunctor (lift F l) :=
      ⟨⟩

    end lift

  end

  namespace idFun

    variable {α : Sort u} {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasInternalFunctors V]
             [HasIdFun V] (R : MetaRelation α V)

    def metaFunctor : MetaFunctor R R := ⟨λ a b => HasIdFun.idFun (R a b)⟩

    instance isReflFunctor [HasRefl R] : IsReflFunctor (metaFunctor R) :=
    ⟨λ _ => byDef⟩

    instance isSymmFunctor [HasSymm R] [HasSymmFun R] : IsSymmFunctor (metaFunctor R) :=
    ⟨λ _ => (congrArgSymm byDef)⁻¹ • byDef⟩

    variable [HasCongrFun V V]

    instance isTransFunctor [HasTrans R] [HasTransFun R] :
      IsTransFunctor (metaFunctor R) :=
    ⟨λ _ _ => (congrArgTrans byDef byDef)⁻¹ • byDef⟩

    instance isPreorderFunctor [IsPreorder R] [HasTransFun R] :
      IsPreorderFunctor (metaFunctor R) :=
    ⟨⟩

    instance isEquivalenceFunctor [IsEquivalence R] [HasSymmFun R] [HasTransFun R] :
      IsEquivalenceFunctor (metaFunctor R) :=
    ⟨⟩

  end idFun

  namespace constFun

    @[reducible] def constRelation (α : Sort u) {V : Universe.{v}} {C : V} (c : C) :
      MetaRelation α V :=
    unitRelation α C

    instance (α : Sort u) {V : Universe.{v}} {C : V} (c : C) : IsEquivalence (constRelation α c) :=
    unitEquivalence α c

    variable {α : Sort u} {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasInternalFunctors V]
             [HasConstFun V V] (R : MetaRelation α V) {C : V} (c : C)

    def metaFunctor : MetaFunctor R (constRelation α c) :=
    ⟨λ a b => HasConstFun.constFun (R a b) c⟩

    instance isReflFunctor  [HasRefl  R] : IsReflFunctor  (metaFunctor R c) := ⟨λ _   => byDef⟩
    instance isSymmFunctor  [HasSymm  R] : IsSymmFunctor  (metaFunctor R c) := ⟨λ _   => byDef⟩
    instance isTransFunctor [HasTrans R] : IsTransFunctor (metaFunctor R c) := ⟨λ _ _ => byDef⟩

    instance isPreorderFunctor    [IsPreorder    R] : IsPreorderFunctor    (metaFunctor R c) := ⟨⟩
    instance isEquivalenceFunctor [IsEquivalence R] : IsEquivalenceFunctor (metaFunctor R c) := ⟨⟩

  end constFun

  namespace compFun

    variable {α : Sort u} {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasInternalFunctors V]
             [HasCompFun V V V] {R S T : MetaRelation α V} (F : MetaFunctor R S) (G : MetaFunctor S T)

    def metaFunctor : MetaFunctor R T :=
    ⟨λ a b => G.baseFun a b ⊙ F.baseFun a b⟩

    instance isReflFunctor [HasRefl R] [HasRefl S] [HasRefl T]
                           [hF : IsReflFunctor F] [hG : IsReflFunctor G] :
      IsReflFunctor (metaFunctor F G) :=
    ⟨λ a => hG.reflEq a • HasCongrArg.congrArg (G.baseFun a a) (hF.reflEq a) • byDef⟩

    instance isSymmFunctor [HasSymm R] [HasSymm S] [HasSymm T] [HasSymmFun T]
                           [hF : IsSymmFunctor F] [hG : IsSymmFunctor G] :
      IsSymmFunctor (metaFunctor F G) :=
    ⟨λ {a b} e => (congrArgSymm byDef)⁻¹ •
                  hG.symmEq (F e) •
                  HasCongrArg.congrArg (G.baseFun b a) (hF.symmEq e) •
                  byDef⟩

    variable [HasCongrFun V V]

    instance isTransFunctor [HasTrans R] [HasTrans S] [HasTrans T] [HasTransFun T]
                            [hF : IsTransFunctor F] [hG : IsTransFunctor G] :
      IsTransFunctor (metaFunctor F G) :=
    ⟨λ {a b c} e f => (congrArgTrans byDef byDef)⁻¹ •
                      hG.transEq (F e) (F f) •
                      HasCongrArg.congrArg (G.baseFun a c) (hF.transEq e f) •
                      byDef⟩

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

    variable [HasLinearFunOp V] [IsEquivalence R] [IsGroupoidEquivalence R]
             [HasSymmFun R] [HasTransFun R]

    instance isReflFunctor : IsReflFunctor (metaFunctor R) :=
    ⟨λ a => reflInv a • byDef⟩

    instance isSymmFunctor : IsSymmFunctor (metaFunctor R) :=
    ⟨λ _ => (congrArgSymm byDef)⁻¹ • byDef⟩

    instance isTransFunctor : IsTransFunctor (metaFunctor R) :=
    ⟨λ f g => (congrArgTrans byDef byDef)⁻¹ • transInv f g • byDef⟩

    instance isPreorderFunctor    : IsPreorderFunctor    (metaFunctor R) := ⟨⟩
    instance isEquivalenceFunctor : IsEquivalenceFunctor (metaFunctor R) := ⟨⟩

  end symmFun

  @[reducible] def PreFunctor {α : Sort u} {β : Sort u'} {V : Universe.{v}}
                              {W : Universe.{w}} {VW : Universe.{vw}} [HasFunctors V W VW]
                              (R : MetaRelation α V) (S : MetaRelation β W) (φ : α → β) :=
  MetaFunctor R (MetaRelation.lift S φ)

  namespace PreFunctor

    namespace idFun

      variable {α : Sort u} {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasInternalFunctors V]
               [HasIdFun V] (R : MetaRelation α V)

      @[reducible] def preFunctor : PreFunctor R R id := idFun.metaFunctor R

      instance isReflFunctor [HasRefl R] : IsReflFunctor (preFunctor R) := inferInstance
      instance isSymmFunctor [HasSymm R] [HasSymmFun R] : IsSymmFunctor (preFunctor R) := inferInstance
      variable [HasCongrFun V V]
      instance isTransFunctor [HasTrans R] [HasTransFun R] : IsTransFunctor (preFunctor R) := inferInstance
      instance isPreorderFunctor [IsPreorder R] [HasTransFun R] : IsPreorderFunctor (preFunctor R) := inferInstance
      instance isEquivalenceFunctor [IsEquivalence R] [HasSymmFun R] [HasTransFun R] : IsEquivalenceFunctor (preFunctor R) := inferInstance

    end idFun

    namespace constFun

      variable {α : Sort u} {β : Sort u'} {V : Universe.{v}} [HasIdentity.{v, iv} V]
               [HasInternalFunctors V] [HasConstFun V V]
               (R : MetaRelation α V) (S : MetaRelation β V) (c : β)

      def preFunctor [HasRefl S] : PreFunctor R S (Function.const α c) :=
      constFun.metaFunctor R (HasRefl.refl c)

      instance isReflFunctor [HasRefl R] [HasRefl S] : IsReflFunctor (preFunctor R S c) :=
      MetaFunctor.constFun.isReflFunctor R (HasRefl.refl c)

      variable [HasCongrFun V V]

      instance isSymmFunctor [HasSymm R] [IsEquivalence S] [IsGroupoidEquivalence S] [HasSymmFun S] [HasTransFun S] :
        IsSymmFunctor (preFunctor R S c) :=
      ⟨λ _ => (IsGroupoidEquivalence.reflInv c • congrArgSymm byDef)⁻¹ • byDef⟩

      instance isTransFunctor [HasTrans R] [IsPreorder S] [IsCategoricalPreorder S] [HasTransFun S] :
        IsTransFunctor (preFunctor R S c) :=
      ⟨λ _ _ => (IsCategoricalPreorder.leftId (HasRefl.refl c) •
                 congrArgTrans byDef byDef)⁻¹ •
                byDef⟩

      instance isPreorderFunctor [IsPreorder R] [IsPreorder S] [IsCategoricalPreorder S] [HasTransFun S] :
        IsPreorderFunctor (preFunctor R S c) :=
      ⟨⟩

      instance isEquivalenceFunctor [IsEquivalence R] [IsEquivalence S] [IsGroupoidEquivalence S] [HasSymmFun S] [HasTransFun S] :
        IsEquivalenceFunctor (preFunctor R S c) :=
      ⟨⟩

    end constFun

    namespace compFun

      variable {α : Sort u} {β : Sort u'} {γ : Sort u''} {V : Universe.{v}} [HasIdentity.{v, iv} V]
               [HasInternalFunctors V] [HasCompFun V V V]
               {R : MetaRelation α V} {S : MetaRelation β V} {T : MetaRelation γ V}
               {φ : α → β} {ψ : β → γ} (F : PreFunctor R S φ) (G : PreFunctor S T ψ)

      @[reducible] def preFunctor : PreFunctor R T (ψ ∘ φ) :=
      compFun.metaFunctor F (MetaFunctor.lift G φ)

      instance [HasRefl  S] [HasRefl  T] [IsReflFunctor  G] : IsReflFunctor  (MetaFunctor.lift G φ) := inferInstance
      instance [HasSymm  S] [HasSymm  T] [IsSymmFunctor  G] : IsSymmFunctor  (MetaFunctor.lift G φ) := inferInstance
      instance [HasTrans S] [HasTrans T] [IsTransFunctor G] : IsTransFunctor (MetaFunctor.lift G φ) := inferInstance
      instance [IsPreorder    S] [IsPreorder    T] [IsPreorderFunctor    G] : IsPreorderFunctor    (MetaFunctor.lift G φ) := inferInstance
      instance [IsEquivalence S] [IsEquivalence T] [IsEquivalenceFunctor G] : IsEquivalenceFunctor (MetaFunctor.lift G φ) := inferInstance

      instance isReflFunctor [HasRefl R] [HasRefl S] [HasRefl T] [IsReflFunctor F] [IsReflFunctor G] : IsReflFunctor (preFunctor F G) := inferInstance
      instance isSymmFunctor [HasSymm R] [HasSymm S] [HasSymm T] [HasSymmFun T] [IsSymmFunctor F] [IsSymmFunctor G] : IsSymmFunctor (preFunctor F G) := inferInstance
      variable [HasCongrFun V V]
      instance isTransFunctor [HasTrans R] [HasTrans S] [HasTrans T] [HasTransFun T] [IsTransFunctor F] [IsTransFunctor G] : IsTransFunctor (preFunctor F G) := inferInstance
      instance isPreorderFunctor [IsPreorder R] [IsPreorder S] [IsPreorder T] [HasTransFun T] [IsPreorderFunctor F] [IsPreorderFunctor G] : IsPreorderFunctor (preFunctor F G) := inferInstance
      instance isEquivalenceFunctor [IsEquivalence R] [IsEquivalence S] [IsEquivalence T] [HasSymmFun T] [HasTransFun T] [IsEquivalenceFunctor F] [IsEquivalenceFunctor G] : IsEquivalenceFunctor (preFunctor F G) := inferInstance

    end compFun

  end PreFunctor

end MetaFunctor



structure MetaEquivalence {α : Sort u} {V : Universe.{v}} {W : Universe.{w}}
                          {VW : Universe.{vw}} {WV : Universe.{wv}} {V_W : Universe.{v_w}}
                          [HasIdentity V] [HasIdentity W] [HasFunctors V W VW] [HasFunctors W V WV]
                          [HasEquivalences V W V_W] (R : MetaRelation α V) (S : MetaRelation α W) :
  Sort (max 1 u vw wv v_w) where
(baseEquiv (a b : α) : R a b ⟷ S a b)

namespace MetaEquivalence

  open MetaRelation MetaFunctor HasSymmFun HasTransFun

  section

    variable {α : Sort u} {V : Universe.{v}} {W : Universe.{w}}
             {VW : Universe.{vw}} {WV : Universe.{wv}} {V_W : Universe.{v_w}}
             [HasIdentity V] [HasIdentity W] [HasFunctors V W VW] [HasFunctors W V WV]
             [HasEquivalences V W V_W] {R : MetaRelation α V} {S : MetaRelation α W}
             (E : MetaEquivalence R S)

    def toMetaFunctor  : MetaFunctor R S := ⟨λ a b => HasEquivalences.toFun  (E.baseEquiv a b)⟩
    def invMetaFunctor : MetaFunctor S R := ⟨λ a b => HasEquivalences.invFun (E.baseEquiv a b)⟩

  end

  section

    variable {α : Sort u} {V : Universe.{v}} {V_V : Universe.{v_v}} [HasIdentity V]
             [HasInternalFunctors V] [HasCongrFun V V] [HasEquivalences V V V_V]
             {R S : MetaRelation α V} (E : MetaEquivalence R S)

    instance toInvReflFunctor [HasRefl R] [HasRefl S] [h : IsReflFunctor (toMetaFunctor E)] :
      IsReflFunctor (invMetaFunctor E) :=
    ⟨λ a => (HasEquivalences.toInv (h.reflEq a))⁻¹⟩

    instance toInvSymmFunctor [HasSymm R] [HasSymm S] [HasSymmFun S][h : IsSymmFunctor (toMetaFunctor E)] :
      IsSymmFunctor (invMetaFunctor E) :=
    ⟨λ {a b} f => (HasEquivalences.toInv (congrArgSymm (HasEquivalences.rightInv (E.baseEquiv a b) f) •
                                          h.symmEq ((invMetaFunctor E) f)))⁻¹⟩

    instance toInvTransFunctor [HasTrans R] [HasTrans S] [HasTransFun S] [h : IsTransFunctor (toMetaFunctor E)] :
      IsTransFunctor (invMetaFunctor E) :=
    ⟨λ {a b c} f g => (HasEquivalences.toInv (congrArgTrans (HasEquivalences.rightInv (E.baseEquiv a b) f)
                                                            (HasEquivalences.rightInv (E.baseEquiv b c) g) •
                                              h.transEq ((invMetaFunctor E) f) ((invMetaFunctor E) g)))⁻¹⟩

    instance toInvPreorderFunctor [IsPreorder R] [IsPreorder S] [HasTransFun S]
                                  [h : IsPreorderFunctor (toMetaFunctor E)] :
      IsPreorderFunctor (invMetaFunctor E) :=
    ⟨⟩

    instance toInvEquivalenceFunctor [IsEquivalence R] [IsEquivalence S] [HasSymmFun S] [HasTransFun S]
                                     [h : IsEquivalenceFunctor (toMetaFunctor E)] :
      IsEquivalenceFunctor (invMetaFunctor E) :=
    ⟨⟩

  end

end MetaEquivalence



def MetaQuantification {α : Sort u} {β : Sort u'} {W : Universe.{w}} (S : MetaRelation β W)
                       (φ ψ : α → β) :=
∀ a, S (φ a) (ψ a)

namespace MetaQuantification

  open MetaRelation MetaFunctor HasTransFun IsAssociative IsCategoricalPreorder
       IsGroupoidEquivalence HasFunctors HasCongrArg HasLinearFunOp

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
    (nat {a b : α} (f : R a b) : hTrans.trans (F f) (η b) ≃ hTrans.trans (η a) (G f))

    namespace IsNatural

      def fromEq [IsPreorder S] [IsCategoricalPreorder S] {φ : α → β}
                 (F G : PreFunctor R S φ) (hEq : ∀ {a b : α} (f : R a b), F f ≃ G f) :
        IsNatural F G (MetaQuantification.refl S φ) :=
      ⟨λ {a b} f => (rightId (G f))⁻¹ • hEq f • leftId (F f)⟩

      instance refl [IsPreorder S] [IsCategoricalPreorder S] {φ : α → β} (F : PreFunctor R S φ) :
        IsNatural F F (MetaQuantification.refl S φ) :=
      ⟨λ f => (rightId (F f))⁻¹ • leftId (F f)⟩

      variable [HasInternalFunctors W] [HasCongrFun W W]

      instance symm [IsEquivalence S] [IsGroupoidEquivalence S] [HasTransFun S]
                    {φ ψ : α → β} {F : PreFunctor R S φ} {G : PreFunctor R S ψ}
                    (η : MetaQuantification S φ ψ) [hη : IsNatural F G η] :
        IsNatural G F (MetaQuantification.symm S η) :=
      ⟨λ {a b} f => cancelLeftInv (F f • (η a)⁻¹) (η b) •
                    congrArgTransRight (assoc (η a)⁻¹ (F f) (η b)) (η b)⁻¹ •
                    assoc (η a)⁻¹ (η b • F f) (η b)⁻¹ •
                    congrArgTransLeft (η a)⁻¹ (congrArgTransRight (hη.nat f)⁻¹ (η b)⁻¹ •
                                               assoc (η a) (G f) (η b)⁻¹) •
                    (cancelRightInv (η a) ((η b)⁻¹ • G f))⁻¹⟩

      instance trans [HasTrans S] [IsAssociative S] [HasTransFun S] {φ ψ χ : α → β}
                     {F : PreFunctor R S φ} {G : PreFunctor R S ψ} {H : PreFunctor R S χ}
                     (η : MetaQuantification S φ ψ) (ε : MetaQuantification S ψ χ)
                     [hη : IsNatural F G η] [hε : IsNatural G H ε] :
        IsNatural F H (MetaQuantification.trans S η ε) :=
      ⟨λ {a b} f => assoc (η a) (ε a) (H f) •
                    congrArgTransLeft (η a) (hε.nat f) •
                    (assoc (η a) (G f) (ε b))⁻¹ •
                    congrArgTransRight (hη.nat f) (ε b) •
                    assoc (R := S) (F f) (η b) (ε b)⟩

    end IsNatural

  end

end MetaQuantification
