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
import UniverseAbstractions.Lemmas.DerivedFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u u' v w w' vw iv iw



namespace MetaRelation

  open HasFunctors HasCongrArg HasCongrFun HasLinearFunOp HasTransFun HasSymmFun

  variable {α : Sort u} {V : Universe.{v}} [HasIdentity.{v, iv} V]
           (R : MetaRelation α V)

  class IsAssociative [HasTrans R] where
  (assoc {a b c d : α} (f : R a b) (g : R b c) (h : R c d) : (h • g) • f ≃ h • (g • f))

  class IsCategoricalPreorder [IsPreorder R] extends IsAssociative R where
  (rightId {a b : α} (f : R a b) : f • HasRefl.refl a ≃ f)
  (leftId  {a b : α} (f : R a b) : HasRefl.refl b • f ≃ f)

  namespace IsCategoricalPreorder

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

  end IsCategoricalPreorder

  def HalfInv [IsPreorder R] {a b : α} (f : R a b) (g : R b a) :=
  g • f ≃ HasRefl.refl (R := R) a

  namespace HalfInv

    open IsAssociative IsCategoricalPreorder

    variable [IsPreorder R] [IsCategoricalPreorder R]

    def refl (a : α) : HalfInv R (HasRefl.refl a) (HasRefl.refl a) := idId R a

    variable [HasInternalFunctors V] [HasCongrFun V V] [HasTransFun R]

    def trans {a b c : α} {f₁ : R a b} {g₁ : R b a} (e₁ : HalfInv R f₁ g₁)
                          {f₂ : R b c} {g₂ : R c b} (e₂ : HalfInv R f₂ g₂) :
      HalfInv R (f₂ • f₁) (g₁ • g₂) :=
    e₁ •
    congrArgTransRight R (leftId f₁ • congrArgTransLeft R f₁ e₂ • (assoc f₁ f₂ g₂)⁻¹) g₁ •
    assoc (f₂ • f₁) g₂ g₁

    def unique {a b : α} {f : R a b} {g₁ g₂ : R b a} (h₁ : HalfInv R f g₁) (h₂ : HalfInv R g₂ f) :
      g₂ ≃ g₁ :=
    congrArgTransRightId R h₂ g₁ •
    assoc g₂ f g₁ •
    (congrArgTransLeftId R g₂ h₁)⁻¹

    def congrArgLeft {a b : α} {f : R a b} {g₁ g₂ : R b a} (hg : g₁ ≃ g₂) (h : HalfInv R f g₂) :
      HalfInv R f g₁ :=
    h • congrArgTransLeft R f hg

    def congrArgRight {a b : α} {f₁ f₂ : R a b} (hf : f₁ ≃ f₂) {g : R b a} (h : HalfInv R f₂ g) :
      HalfInv R f₁ g :=
    h • congrArgTransRight R hf g

  end HalfInv

  class IsInv [IsPreorder R] {a b : α} (f : R a b) (g : R b a) where
  (leftInv  : HalfInv R f g)
  (rightInv : HalfInv R g f)

  namespace IsInv

    open IsAssociative IsCategoricalPreorder

    variable [IsPreorder R] [IsCategoricalPreorder R]

    instance refl (a : α) : IsInv R (HasRefl.refl a) (HasRefl.refl a) :=
    { leftInv  := HalfInv.refl R a,
      rightInv := HalfInv.refl R a }

    instance symm {a b : α} (f : R a b) (g : R b a) [h : IsInv R f g] : IsInv R g f :=
    { leftInv  := h.rightInv,
      rightInv := h.leftInv }

    variable [HasInternalFunctors V] [HasCongrFun V V] [HasTransFun R]

    instance trans {a b c : α} (f₁ : R a b) (g₁ : R b a) [h₁ : IsInv R f₁ g₁]
                               (f₂ : R b c) (g₂ : R c b) [h₂ : IsInv R f₂ g₂] :
      IsInv R (f₂ • f₁) (g₁ • g₂) :=
    { leftInv  := HalfInv.trans R h₁.leftInv  h₂.leftInv,
      rightInv := HalfInv.trans R h₂.rightInv h₁.rightInv }

    def unique {a b : α} (f : R a b) (g₁ g₂ : R b a) [h₁ : IsInv R f g₁] [h₂ : IsInv R f g₂] :
      g₂ ≃ g₁ :=
    HalfInv.unique R h₁.leftInv h₂.rightInv

    def congrArgLeft {a b : α} (f : R a b) {g₁ g₂ : R b a} (hg : g₁ ≃ g₂) [h : IsInv R f g₂] :
      IsInv R f g₁ :=
    { leftInv  := HalfInv.congrArgLeft  R hg h.leftInv,
      rightInv := HalfInv.congrArgRight R hg h.rightInv }

    def congrArgRight {a b : α} {f₁ f₂ : R a b} (hf : f₁ ≃ f₂) (g : R b a) [h : IsInv R f₂ g] :
      IsInv R f₁ g :=
    { leftInv  := HalfInv.congrArgRight R hf h.leftInv,
      rightInv := HalfInv.congrArgLeft  R hf h.rightInv }

  end IsInv

  class IsGroupoidEquivalence [IsEquivalence R] extends IsCategoricalPreorder R where
  (leftInv  {a b : α} (f : R a b) : HalfInv R f f⁻¹)
  (rightInv {a b : α} (f : R a b) : HalfInv R f⁻¹ f)

  namespace IsGroupoidEquivalence

    open IsAssociative IsCategoricalPreorder

    variable [IsEquivalence R] [IsGroupoidEquivalence R]

    instance isInv {a b : α} (f : R a b) : IsInv R f f⁻¹ :=
    { leftInv  := leftInv  f,
      rightInv := rightInv f }

    variable [HasInternalFunctors V] [HasTransFun R]

    def invEq [HasCongrFun V V] {a b : α} (f : R a b) (g : R b a) [h : IsInv R f g] : f⁻¹ ≃ g :=
    IsInv.unique R f g f⁻¹

    def reflInv [HasCongrFun V V] (a : α) : (HasRefl.refl (R := R) a)⁻¹ ≃ HasRefl.refl (R := R) a :=
    invEq R (HasRefl.refl a) (HasRefl.refl a)

    def symmInv [HasCongrFun V V] {a b : α} (f : R a b) : (f⁻¹)⁻¹ ≃ f :=
    invEq R f⁻¹ f

    def transInv [HasLinearFunOp V] {a b c : α} (f : R a b) (g : R b c) : (g • f)⁻¹ ≃ f⁻¹ • g⁻¹ :=
    invEq R (g • f) (f⁻¹ • g⁻¹)

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

  end IsGroupoidEquivalence

  namespace opposite

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

    variable {ω : Sort w} (l : ω → α)

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
             [HasLinearFunOp V] (R : MetaRelation α V)

    def metaFunctor : MetaFunctor R R := ⟨λ a b => idFun (R a b)⟩

    instance isReflFunctor [HasRefl R] : IsReflFunctor (metaFunctor R) :=
    ⟨λ _ => byDef⟩

    instance isSymmFunctor [HasSymm R] [HasSymmFun R] : IsSymmFunctor (metaFunctor R) :=
    ⟨λ _ => (congrArgSymm R byDef)⁻¹ • byDef⟩

    instance isTransFunctor [HasTrans R] [HasTransFun R] : IsTransFunctor (metaFunctor R) :=
    ⟨λ _ _ => (congrArgTrans R byDef byDef)⁻¹ • byDef⟩

    instance isPreorderFunctor [IsPreorder R] [HasTransFun R] :
      IsPreorderFunctor (metaFunctor R) :=
    ⟨⟩

    instance isEquivalenceFunctor [IsEquivalence R] [HasSymmFun R] [HasTransFun R] :
      IsEquivalenceFunctor (metaFunctor R) :=
    ⟨⟩

  end idFun

  namespace constFun

    @[reducible] def constRelation {α : Sort u} {β : Sort u'} {V : Universe.{v}}
                                   (S : MetaRelation β V) (c : β) :
      MetaRelation α V :=
    MetaRelation.lift S (Function.const α c)

    theorem constRelation.isConst {α : Sort u} {β : Sort u'} {V : Universe.{v}}
                                  (S : MetaRelation β V) (c : β) :
      constRelation S c = unitRelation α (S c c) :=
    rfl

    variable {α : Sort u} {β : Sort u'} {V : Universe.{v}} [HasIdentity.{v, iv} V]
             [HasInternalFunctors V] [HasAffineFunOp V]
             (R : MetaRelation α V) (S : MetaRelation β V) (c : β)

    def metaFunctor [HasRefl S] : MetaFunctor R (constRelation S c) :=
    ⟨λ a b => constFun (R a b) (HasRefl.refl c)⟩

    instance isReflFunctor [HasRefl R] [HasRefl S] :
      IsReflFunctor (metaFunctor R S c) :=
    ⟨λ _ => byDef⟩

    instance isSymmFunctor [HasSymm R] [IsEquivalence S]
                           [IsGroupoidEquivalence S] [HasSymmFun S] [HasTransFun S] :
      IsSymmFunctor (metaFunctor R S c) :=
    ⟨λ _ => (IsGroupoidEquivalence.reflInv S c • congrArgSymm (constRelation S c) byDef)⁻¹ • byDef⟩

    instance isTransFunctor [HasTrans R] [IsPreorder S]
                            [IsCategoricalPreorder S] [HasTransFun S] :
      IsTransFunctor (metaFunctor R S c) :=
    ⟨λ _ _ => (IsCategoricalPreorder.leftId (HasRefl.refl c) •
               congrArgTrans (constRelation S c) byDef byDef)⁻¹ •
              byDef⟩

    instance isPreorderFunctor [IsPreorder R] [IsPreorder S]
                               [IsCategoricalPreorder S] [HasTransFun S] :
      IsPreorderFunctor (metaFunctor R S c) :=
    ⟨⟩

    instance isEquivalenceFunctor [IsEquivalence R] [IsEquivalence S]
                                  [IsGroupoidEquivalence S] [HasSymmFun S] [HasTransFun S] :
      IsEquivalenceFunctor (metaFunctor R S c) :=
    ⟨⟩

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

    instance isTransFunctor [HasTrans R] [HasTrans S] [HasTrans T] [HasTransFun T]
                            [hF : IsTransFunctor F] [hG : IsTransFunctor G] :
      IsTransFunctor (metaFunctor F G) :=
    ⟨λ {a b c} e f => (congrArgTrans T byDef byDef)⁻¹ •
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
    ⟨λ a => reflInv R a • byDef⟩

    instance isSymmFunctor : IsSymmFunctor (metaFunctor R) :=
    ⟨λ _ => (congrArgSymm R byDef)⁻¹ • byDef⟩

    instance isTransFunctor : IsTransFunctor (metaFunctor R) :=
    ⟨λ f g => (congrArgTrans R byDef byDef)⁻¹ • transInv R f g • byDef⟩

    instance isPreorderFunctor    : IsPreorderFunctor    (metaFunctor R) := ⟨⟩
    instance isEquivalenceFunctor : IsEquivalenceFunctor (metaFunctor R) := ⟨⟩

  end symmFun

  @[reducible] def PreFunctor {α : Sort u} {β : Sort u'} {V : Universe.{v}}
                              {W : Universe.{w}} {VW : Universe.{vw}} [HasFunctors V W VW]
                              (R : MetaRelation α V) (S : MetaRelation β W) (φ : α → β) :=
  MetaFunctor R (MetaRelation.lift S φ)

end MetaFunctor



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
                     (η : MetaQuantification S φ ψ) (ε : MetaQuantification S ψ χ)
                     [hη : IsNatural F G η] [hε : IsNatural G H ε] :
        IsNatural F H (MetaQuantification.trans S η ε) :=
      ⟨λ {a b} f => (assoc (R := S) (F f) (η b) (ε b))⁻¹ •
                    congrArgTransRight S (hη.nat f) (ε b) •
                    assoc (η a) (G f) (ε b) •
                    congrArgTransLeft S (η a) (hε.nat f) •
                    (assoc (η a) (ε a) (H f))⁻¹⟩

    end IsNatural

  end

end MetaQuantification
