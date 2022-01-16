import UniverseAbstractions.Axioms.CategoryTheory.Basic
import UniverseAbstractions.Meta.Tactics.Functoriality



set_option autoBoundImplicitLocal false
set_option synthInstance.maxHeartbeats 2000
--set_option pp.universes true

universe u u' u'' v w ww iw



-- Here, we define three typeclasses `IsFunUniverse`, `IsNatUniverse`, and `IsIsoUniverse`,
-- that a universe of morphisms should satisfy. They let us obtain certain category-theoretic
-- structure that depends on the specific morphism universe, e.g. it may require additional
-- coherence conditions for higher categories.
--
-- In particular,
-- * `IsFunUniverse` defines a condition for functoriality, which must imply the conditions
--   defined by `IsCategoryFunctor` and also `IsGroupoidFunctor` for isomorphisms, with
--   coherence conditions.
-- * `IsNatUniverse` defines an analogous condition for naturality.
-- * `IsIsoUniverse` (in `Isomorphisms.lean`) defines a second meta-relation `Iso` for
--   categories, in addition to `Hom`. `Iso` is required to form a groupoid and to imply `Hom`.
--   Moreover, there are coherence conditions that ensure the correct behavior of isomorphisms
--   regarding functors and natural transformations.

namespace CategoryTheory

  open MetaRelation MetaFunctor MetaQuantification HasTransFun HasSymmFun
       IsAssociative IsCategoricalPreorder IsGroupoidEquivalence IsSymmFunctor IsTransFunctor
       IsCategory
       HasFunctors HasCongrArg HasCongrFun HasLinearFunOp

  class HasFunProp {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                   (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β] where
  (Fun : MetaProperty (α → β) W)
  [isCategoryFunctor {φ : α → β} (F : Fun φ) : IsCategoryFunctor φ]

  namespace HasFunProp

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]

    structure Functor (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
                      [h : HasFunProp α β] : Sort (max 1 u v w) where
    {φ : α → β}
    (F : h.Fun φ)

    namespace Functor

      infixr:20 " ⮕ " => CategoryTheory.HasFunProp.Functor

      variable {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
               [h : HasFunProp α β] (F : α ⮕ β)

      instance isCategoryFunctor : IsCategoryFunctor F.φ := h.isCategoryFunctor F.F

      @[reducible] def mapHom {a b : α} (f : a ⇾ b) : F.φ a ⇾ F.φ b :=
      (IsMorphismFunctor.preFunctor F.φ) f

      def reflEq (a : α) : mapHom F (idHom a) ≃ idHom (F.φ a) :=
      IsReflFunctor.reflEq (F := IsMorphismFunctor.preFunctor F.φ) a

      def transEq {a b c : α} (f : a ⇾ b) (g : b ⇾ c) :
        mapHom F (g • f) ≃ mapHom F g • mapHom F f :=
      IsTransFunctor.transEq (F := IsMorphismFunctor.preFunctor F.φ) f g

    end Functor

    structure DefFun {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
                     [h : HasFunProp α β] (φ : α → β) [hφ : IsCategoryFunctor φ] where
    (F            : h.Fun φ)
    (eq (a b : α) : (h.isCategoryFunctor F).F.baseFun a b ≃ hφ.F.baseFun a b)

    namespace DefFun

      variable {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
               [h : HasFunProp α β] {φ : α → β} [hφ : IsCategoryFunctor φ]

      @[reducible] def toFunctor (F : DefFun φ) : α ⮕ β := ⟨F.F⟩

      def byMapHomDef {F : DefFun φ} {a b : α} {f : a ⇾ b} {g : φ a ⇾ φ b} (h : hφ.F f ≃ g) :
        Functor.mapHom (toFunctor F) f ≃ g :=
      h • HasCongrFun.congrFun (F.eq a b) f

    end DefFun

    class HasTrivialFunctorialityCondition (α : Sort u) (β : Sort v)
                                           [hα : IsCategory W α] [hβ : IsCategory W β]
                                           [h : HasFunProp α β] where
    (functor (φ : α → β) [hφ : IsCategoryFunctor φ] : DefFun φ)

    namespace HasTrivialFunctorialityCondition

      variable {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
               [HasFunProp α β] [h : HasTrivialFunctorialityCondition α β]
      
      def defFun {φ : α → β} [hφ : IsCategoryFunctor φ] : DefFun φ := h.functor φ

    end HasTrivialFunctorialityCondition

    class HasIdFun (α : Sort u) [hα : IsCategory W α] [hFunαα : HasFunProp α α] where 
    (defIdFun : DefFun (@id α))

    namespace HasIdFun

      instance trivial (α : Sort u) [IsCategory W α] [HasFunProp α α]
                       [HasTrivialFunctorialityCondition α α] :
        HasIdFun α :=
      ⟨HasTrivialFunctorialityCondition.defFun⟩

    end HasIdFun

    class HasConstFun [HasSubLinearFunOp W] (α : Sort u) (β : Sort v) [hα : IsCategory W α]
                      [hβ : IsCategory W β] [hFunαβ : HasFunProp α β] where
    (defConstFun (b : β) : DefFun (Function.const α b))

    namespace HasConstFun

      instance trivial [HasSubLinearFunOp W] (α : Sort u) (β : Sort v) [IsCategory W α]
                       [IsCategory W β] [HasFunProp α β] [HasTrivialFunctorialityCondition α β] :
        HasConstFun α β :=
      ⟨λ _ => HasTrivialFunctorialityCondition.defFun⟩

    end HasConstFun

    class HasCompFun (α : Sort u) (β : Sort u') (γ : Sort u'') [hα : IsCategory W α]
                     [hβ : IsCategory W β] [hγ : IsCategory W γ] [hFunαβ : HasFunProp α β]
                     [hFunβγ : HasFunProp β γ] [hFunαγ : HasFunProp α γ] where
    (defCompFun (F : α ⮕ β) (G : β ⮕ γ) : DefFun (G.φ ∘ F.φ))

    namespace HasCompFun

      instance trivial (α : Sort u) (β : Sort u') (γ : Sort u'') [IsCategory W α] [IsCategory W β]
                       [IsCategory W γ] [HasFunProp α β] [HasFunProp β γ] [HasFunProp α γ]
                       [HasTrivialFunctorialityCondition α γ] :
        HasCompFun α β γ :=
      ⟨λ _ _ => HasTrivialFunctorialityCondition.defFun⟩

    end HasCompFun

  end HasFunProp

  class IsFunUniverse (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw} W] where
  [hasFun (α β : Sort (max 1 u w)) [IsCategory W α] [IsCategory W β] : HasFunProp α β]

  namespace IsFunUniverse

    open HasFunProp

    section

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W] [h : IsFunUniverse.{u} W]

      instance (α β : Sort (max 1 u w)) [IsCategory W α] [IsCategory W β] : HasFunProp α β :=
      h.hasFun α β

    end

    class HasLinearFunctors (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw} W]
                            [hFunUniv : IsFunUniverse.{u} W] where
    [hasIdFun (α : Sort (max 1 u w)) [IsCategory W α] : HasIdFun α]
    [hasCompFun (α β γ : Sort (max 1 u w)) [IsCategory W α] [IsCategory W β] [IsCategory W γ] :
       HasCompFun α β γ]

    namespace HasLinearFunctors

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W] [IsFunUniverse.{u} W]
               [h : HasLinearFunctors W]

      instance (α : Sort (max 1 u w)) [IsCategory W α] : HasIdFun α := h.hasIdFun α

      instance (α β γ : Sort (max 1 u w)) [IsCategory W α] [IsCategory W β] [IsCategory W γ] :
        HasCompFun α β γ :=
      h.hasCompFun α β γ

      def idFun (α : Sort (max 1 u w)) [IsCategory W α] : α ⮕ α :=
      DefFun.toFunctor (h.hasIdFun α).defIdFun

      def compFun {α β γ : Sort (max 1 u w)} [IsCategory W α] [IsCategory W β] [IsCategory W γ]
                  (F : α ⮕ β) (G : β ⮕ γ) :
        α ⮕ γ :=
      DefFun.toFunctor ((h.hasCompFun α β γ).defCompFun F G)

    end HasLinearFunctors

    class HasAffineFunctors (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw} W]
                            [hFunUniv : IsFunUniverse.{u} W]
                            [HasSubLinearFunOp W] extends
      HasLinearFunctors W where
    [hasConstFun (α β : Sort (max 1 u w)) [IsCategory W α] [IsCategory W β] : HasConstFun α β]

    namespace HasAffineFunctors

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W] [IsFunUniverse.{u} W]
               [HasSubLinearFunOp W] [h : HasAffineFunctors W]

      instance (α β : Sort (max 1 u w)) [IsCategory W α] [IsCategory W β] : HasConstFun α β :=
      h.hasConstFun α β

      def constFun (α : Sort (max 1 u w)) {β : Sort (max 1 u w)} [IsCategory W α] [IsCategory W β] (b : β) :
        α ⮕ β :=
      DefFun.toFunctor ((h.hasConstFun α β).defConstFun b)

    end HasAffineFunctors

  end IsFunUniverse



  structure NatDesc {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                    {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
                    [hFunProp : HasFunProp α β] (F G : α ⮕ β) :
    Sort (max 1 u w iw) where
  (nat   : MetaQuantification hβ.Hom F.φ G.φ)
  [isNat : IsNaturalTransformation nat]

  namespace NatDesc

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
             {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
             [hFunProp : HasFunProp α β]
             {F G : α ⮕ β} (η : NatDesc F G)

    instance : IsNaturalTransformation η.nat := η.isNat

  end NatDesc

  class HasNatRel {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                  (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
                  [hFunProp : HasFunProp α β] where
  (Nat : MetaRelation (α ⮕ β) W)
  (desc {F G : α ⮕ β} (η : Nat F G) : NatDesc F G)
  (defNatFun (F G : α ⮕ β) (a : α) :
     Nat F G ⟶{λ η => (desc η).nat a} (F.φ a ⇾ G.φ a))

  namespace HasNatRel

    open HasFunctors HasFunProp HasFunProp.Functor

    section

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
               {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
               [hFunProp : HasFunProp α β] [h : HasNatRel α β]

      @[reducible] def nat {F G : α ⮕ β} (η : h.Nat F G) (a : α) : F.φ a ⇾ G.φ a :=
      (h.desc η).nat a

      @[reducible] def natFun (F G : α ⮕ β) (a : α) : h.Nat F G ⟶ (F.φ a ⇾ G.φ a) :=
      h.defNatFun F G a

      instance {F G : α ⮕ β} (η : h.Nat F G) (a : α) : IsFunApp (h.Nat F G) (nat η a) :=
      { F := natFun F G a,
        a := η,
        e := byDef }

      def natCongrArg {F G : α ⮕ β} {η₁ η₂ : h.Nat F G} (e : η₁ ≃ η₂) (a : α) :
        nat η₁ a ≃ nat η₂ a :=
      defCongrArg (defNatFun F G a) e

      def naturality {F G : α ⮕ β} (η : h.Nat F G) {a b : α} (f : a ⇾ b) :
        mapHom G f • nat η a ≃ nat η b • mapHom F f :=
      (h.desc η).isNat.nat f

      structure DefNat {F G : α ⮕ β} (desc : NatDesc F G) where
      (η             : h.Nat F G)
      (natEq (a : α) : nat η a ≃ desc.nat a)

      def byNatDef {F G : α ⮕ β} {desc : NatDesc F G} {η : DefNat desc} (a : α) :
        nat η.η a ≃ desc.nat a :=
      η.natEq a

      def NatEquiv {F G : α ⮕ β} (η₁ η₂ : h.Nat F G)
                   (hNat : ∀ a, nat η₁ a ≃ nat η₂ a) :=
      η₁ ≃ η₂

      def DefNatEquiv {F G : α ⮕ β} {desc₁ desc₂ : NatDesc F G} (η₁ : DefNat desc₁)
                      (η₂ : DefNat desc₂) (hNat : ∀ a, desc₁.nat a ≃ desc₂.nat a) :=
      NatEquiv η₁.η η₂.η (λ a => (byNatDef a)⁻¹ • hNat a • byNatDef a)

    end

    class HasTrivialNaturalityCondition {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                                        (α : Sort u) (β : Sort v)
                                        [hα : IsCategory W α] [hβ : IsCategory W β]
                                        [hFunProp : HasFunProp α β] [h : HasNatRel α β] where
    (nat {F G : α ⮕ β} (desc : NatDesc F G) : DefNat desc)

    namespace HasTrivialNaturalityCondition

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
               {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
               [HasFunProp α β] [HasNatRel α β] [h : HasTrivialNaturalityCondition α β]

      def defNat {F G : α ⮕ β} {desc : NatDesc F G} : DefNat desc := h.nat desc

    end HasTrivialNaturalityCondition

    class HasTrivialNatEquiv {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                             (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
                             [hFunProp : HasFunProp α β] [h : HasNatRel α β] where
    (equiv {F G : α ⮕ β} (η₁ η₂ : h.Nat F G) (hNat : ∀ a, nat η₁ a ≃ nat η₂ a) :
       NatEquiv η₁ η₂ hNat)

    namespace HasTrivialNatEquiv

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
               {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
               [HasFunProp α β] [hNatRel : HasNatRel α β] [h : HasTrivialNatEquiv α β]

      def natEquiv {F G : α ⮕ β} {η₁ η₂ : hNatRel.Nat F G} {hNat : ∀ a, nat η₁ a ≃ nat η₂ a} :
        NatEquiv η₁ η₂ hNat :=
      h.equiv η₁ η₂ hNat

    end HasTrivialNatEquiv

  end HasNatRel

  class HasNatOp {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                 (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
                 [hFunProp : HasFunProp α β] extends
    HasNatRel α β where
  (defRefl (F : α ⮕ β) :
     HasNatRel.DefNat ⟨MetaQuantification.refl hβ.Hom F.φ⟩)
  (defTrans {F G H : α ⮕ β} (η : Nat F G) (ε : Nat G H) :
     HasNatRel.DefNat ⟨MetaQuantification.trans hβ.Hom (desc η).nat (desc ε).nat⟩)

  namespace HasNatOp

    open HasNatRel

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]

    section

      variable (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
               [HasFunProp α β]

      instance trivial [HasNatRel α β] [HasTrivialNaturalityCondition α β] : HasNatOp α β :=
      { defRefl  := λ _   => HasTrivialNaturalityCondition.defNat,
        defTrans := λ _ _ => HasTrivialNaturalityCondition.defNat }

      variable [h : HasNatOp α β]

      instance natIsPreorder : IsPreorder h.Nat :=
      { refl  := λ F   => (h.defRefl F).η,
        trans := λ η ε => (h.defTrans η ε).η }

    end

    section

      variable {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
               [HasFunProp α β] [h : HasNatOp α β]

      def natReflEq (F : α ⮕ β) (a : α) :
        nat (HasRefl.refl F) a ≃ idHom (F.φ a) :=
      byNatDef a

      def natTransEq {F G H : α ⮕ β} (η : Nat F G) (ε : Nat G H) (a : α) :
        nat (ε • η) a ≃ nat ε a • nat η a :=
      byNatDef a

      def natAssoc {F G H I : α ⮕ β} (η : Nat F G) (ε : Nat G H) (θ : Nat H I) (a : α) :
        nat ((θ • ε) • η) a ≃ nat (θ • (ε • η)) a :=
      (congrArgTransRight hβ.Hom (natTransEq η ε a) (nat θ a) •
       natTransEq (ε • η) θ a)⁻¹ •
      assoc (nat η a) (nat ε a) (nat θ a) •
      (congrArgTransLeft hβ.Hom (nat η a) (natTransEq ε θ a) •
       natTransEq η (θ • ε) a)

      def natRightId {F G : α ⮕ β} (η : Nat F G) (a : α) :
        nat (η • HasRefl.refl F) a ≃ nat η a :=
      rightId (nat η a) •
      congrArgTransRight hβ.Hom (natReflEq F a) (nat η a) •
      natTransEq (HasRefl.refl F) η a

      def natLeftId {F G : α ⮕ β} (η : Nat F G) (a : α) :
        nat (HasRefl.refl G • η) a ≃ nat η a :=
      leftId (nat η a) •
      congrArgTransLeft hβ.Hom (nat η a) (natReflEq G a) •
      natTransEq η (HasRefl.refl G) a

    end

  end HasNatOp

  class HasNatOpEquiv {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                      (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
                      [hFunProp : HasFunProp α β] extends
    HasNatOp α β where
  (assoc {F G H I : α ⮕ β} (η : Nat F G) (ε : Nat G H) (θ : Nat H I) :
     HasNatRel.NatEquiv ((θ • ε) • η) (θ • (ε • η)) (HasNatOp.natAssoc η ε θ))
  (rightId {F G : α ⮕ β} (η : Nat F G) :
     HasNatRel.NatEquiv (η • HasRefl.refl F) η (HasNatOp.natRightId η))
  (leftId {F G : α ⮕ β} (η : Nat F G) :
     HasNatRel.NatEquiv (HasRefl.refl G • η) η (HasNatOp.natLeftId η))

  namespace HasNatOpEquiv

    open HasNatRel

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
             (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β] [HasFunProp α β]

    instance trivial [HasNatOp α β] [HasTrivialNatEquiv α β] : HasNatOpEquiv α β :=
    { assoc   := λ _ _ _ => HasTrivialNatEquiv.natEquiv,
      rightId := λ _     => HasTrivialNatEquiv.natEquiv,
      leftId  := λ _     => HasTrivialNatEquiv.natEquiv }

    variable [h : HasNatOpEquiv α β]

    instance natIsCategoricalPreorder : IsCategoricalPreorder h.Nat :=
    { assoc   := h.assoc,
      leftId  := h.leftId,
      rightId := h.rightId }

  end HasNatOpEquiv

  class HasNaturality {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                      (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
                      [hFunProp : HasFunProp α β] extends
    HasNatOpEquiv α β where
  [natHasTransFun : HasTransFun Nat]

  namespace HasNaturality

    open HasFunProp HasFunProp.Functor HasNatRel HasNatOp

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]

    section

      variable (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
               [HasFunProp α β] [h : HasNaturality α β]

      instance : IsPreorder            h.Nat := h.natIsPreorder
      instance : HasTransFun           h.Nat := h.natHasTransFun
      instance : IsCategoricalPreorder h.Nat := h.natIsCategoricalPreorder

      instance funHasMorphisms : HasMorphisms W (α ⮕ β) := ⟨h.Nat⟩

      instance funIsCategory : IsCategory.{max 1 u v w} W (α ⮕ β) :=
      { homIsPreorder            := HasNatOp.natIsPreorder α β,
        homHasTransFun           := h.natHasTransFun,
        homIsCategoricalPreorder := h.natIsCategoricalPreorder }

    end

    section

      variable {α : Sort u} {β : Sort u'} {γ : Sort u''}
               [hα : IsCategory W α] [hβ : IsCategory W β] [hγ : IsCategory W γ]
               [hFunβγ : HasFunProp β γ] [hNatβγ : HasNaturality β γ]
               {φ : α → β → γ} [hφ : ∀ a, IsCategoryFunctor (φ a)]

      structure FunFunDesc (F : ∀ a, HasFunProp.DefFun (φ a)) where
      (natDesc {a₁ a₂ : α} : (a₁ ⇾ a₂) → NatDesc (DefFun.toFunctor (F a₁)) (DefFun.toFunctor (F a₂)))
      (natDescReflEq (a : α) (b : β) : (natDesc (idHom a)).nat b ≃ idHom (φ a b))
      (natDescTransEq {a₁ a₂ a₃ : α} (f : a₁ ⇾ a₂) (g : a₂ ⇾ a₃) (b : β) :
         (natDesc (g • f)).nat b ≃ (natDesc g).nat b • (natDesc f).nat b)

      structure DefFunFunBase {F : ∀ a, HasFunProp.DefFun (φ a)} (desc : FunFunDesc F) where
      (defNat {a₁ a₂ : α} (f : a₁ ⇾ a₂) : DefNat (desc.natDesc f))
      (defNatFun (a₁ a₂ : α) :
         (a₁ ⇾ a₂) ⟶{λ f => (defNat f).η} (DefFun.toFunctor (F a₁) ⇾ DefFun.toFunctor (F a₂)))
      (natReflEq (a : α) :
         DefNatEquiv (defNat (idHom a)) (HasNatOp.defRefl (DefFun.toFunctor (F a)))
                     (desc.natDescReflEq a))
      (natTransEq {a₁ a₂ a₃ : α} (f : a₁ ⇾ a₂) (g : a₂ ⇾ a₃) :
         DefNatEquiv (defNat (g • f)) (HasNatOp.defTrans (defNat f).η (defNat g).η)
                     (λ b => (congrArgTrans hγ.Hom (byNatDef b) (byNatDef b))⁻¹ • desc.natDescTransEq f g b))

      namespace DefFunFunBase

        variable {F : ∀ a, HasFunProp.DefFun (φ a)} {desc : FunFunDesc F} (G : DefFunFunBase desc)

        @[reducible] def natFun (a₁ a₂ : α) :
          (a₁ ⇾ a₂) ⟶ (DefFun.toFunctor (F a₁) ⇾ DefFun.toFunctor (F a₂)) :=
        G.defNatFun a₁ a₂

        instance isCategoryFunctor : IsCategoryFunctor (λ a => DefFun.toFunctor (F a)) :=
        { F         := ⟨natFun G⟩,
          hPreorder := { reflEq  := λ a   => G.natReflEq a • byDef,
                         transEq := λ f g => (congrArgTrans hNatβγ.Nat byDef byDef)⁻¹ •
                                             G.natTransEq f g •
                                             byDef } }

      end DefFunFunBase

      structure DefFunFun [hFunαβγ : HasFunProp α (β ⮕ γ)] {F : ∀ a, HasFunProp.DefFun (φ a)}
                          (desc : FunFunDesc F) extends
        DefFunFunBase desc where
      (defFunFun : DefFun (λ a => DefFun.toFunctor (F a))
                          (hφ := DefFunFunBase.isCategoryFunctor toDefFunFunBase))

      namespace DefFunFun

        variable [HasFunProp α (β ⮕ γ)] {F : ∀ a, HasFunProp.DefFun (φ a)} {desc : FunFunDesc F}

        def toFunctor (F : DefFunFun desc) : α ⮕ β ⮕ γ :=
        DefFun.toFunctor F.defFunFun (hφ := DefFunFunBase.isCategoryFunctor F.toDefFunFunBase)

      end DefFunFun

    end

    section

      variable {α : Sort u} (a : α) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
               [HasFunProp α β] [h : HasNaturality α β]

      def revApp (F : α ⮕ β) : β := F.φ a

      instance revAppIsFun : IsCategoryFunctor (revApp a β) :=
      { F         := ⟨λ F₁ F₂ => natFun F₁ F₂ a⟩,
        hPreorder := { reflEq  := λ F   => natReflEq F a • byDef,
                       transEq := λ η ε => (congrArgTrans hβ.Hom byDef byDef)⁻¹ •
                                           natTransEq η ε a •
                                           byDef } }

    end

    class HasRevAppFun (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
                       [hFunαβ : HasFunProp α β] [hNatαβ : HasNaturality α β]
                       [hFunαββ : HasFunProp (α ⮕ β) β] where
    (defRevAppFun (a : α) : HasFunProp.DefFun (revApp a β))

    namespace HasRevAppFun

      variable (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
               [HasFunProp α β] [HasNaturality α β] [HasFunProp (α ⮕ β) β]
               [h : HasRevAppFun α β]

      def revAppFun (a : α) : (α ⮕ β) ⮕ β := DefFun.toFunctor (h.defRevAppFun a)

      def mapRevNat {a₁ a₂ : α} (f : a₁ ⇾ a₂) :
        MetaQuantification hβ.Hom (revAppFun α β a₁).φ (revAppFun α β a₂).φ :=
      λ F => mapHom F f

      instance mapRevNat.isNat {a₁ a₂ : α} (f : a₁ ⇾ a₂) :
        IsNaturalTransformation (mapRevNat α β f) :=
      { nat := λ {F₁ F₂} η => (naturality η f •
                               congrArgTransRight hβ.Hom
                                                  (DefFun.byMapHomDef (hφ := revAppIsFun a₁ β) byDef)
                                                  (mapHom F₂ f))⁻¹ •
                              congrArgTransLeft hβ.Hom
                                                (mapHom F₁ f)
                                                (DefFun.byMapHomDef (hφ := revAppIsFun a₂ β) byDef) }

      def revAppNatDesc {a₁ a₂ : α} (f : a₁ ⇾ a₂) :
        NatDesc (revAppFun α β a₁) (revAppFun α β a₂) :=
      { nat   := mapRevNat       α β f,
        isNat := mapRevNat.isNat α β f }

      def revAppFunFunDesc : FunFunDesc h.defRevAppFun :=
      { natDesc        := revAppNatDesc α β,
        natDescReflEq  := λ a   F => Functor.reflEq  F a,
        natDescTransEq := λ f g F => Functor.transEq F f g }

    end HasRevAppFun

    class HasRevAppFunFun (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
                          [hFunαβ : HasFunProp α β] [hNatαβ : HasNaturality α β]
                          [hFunαββ : HasFunProp (α ⮕ β) β] [hNatαββ : HasNaturality (α ⮕ β) β]
                          [hFunααββ : HasFunProp α ((α ⮕ β) ⮕ β)] extends
      HasRevAppFun α β where
    (defRevAppFunFun : DefFunFun (HasRevAppFun.revAppFunFunDesc α β))

    namespace HasRevAppFunFun

      variable (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
               [HasFunProp α β] [h₁ : HasNaturality α β] [HasFunProp (α ⮕ β) β]
               [h₂ : HasNaturality (α ⮕ β) β] [HasFunProp α ((α ⮕ β) ⮕ β)]
               [h : HasRevAppFunFun α β]

      def revAppFunFun : α ⮕ (α ⮕ β) ⮕ β := DefFunFun.toFunctor h.defRevAppFunFun

    end HasRevAppFunFun

    section

      variable [HasNonLinearFunOp W] {α : Sort u} {β : Sort v}
               [hα : IsCategory W α] [hβ : IsCategory W β] [HasFunProp α β] [h : HasNaturality α β]
               [HasFunProp α (α ⮕ β)] (F : α ⮕ α ⮕ β)

      def dup (a : α) : β := (F.φ a).φ a

      @[reducible] def mapDupHom {a₁ a₂ : α} (f : a₁ ⇾ a₂) : dup F a₁ ⇾ dup F a₂ :=
      mapHom (F.φ a₂) f • nat (mapHom F f) a₁

      @[reducible] def mapDupHom' {a₁ a₂ : α} (f : a₁ ⇾ a₂) : dup F a₁ ⇾ dup F a₂ :=
      nat (mapHom F f) a₂ • mapHom (F.φ a₁) f

      def mapDupHomEq {a₁ a₂ : α} (f : a₁ ⇾ a₂) : mapDupHom F f ≃ mapDupHom' F f :=
      naturality (mapHom F f) f

      def mapDupHomFun (a₁ a₂ : α) : (a₁ ⇾ a₂) ⟶ (dup F a₁ ⇾ dup F a₂) :=
      Λ f => mapDupHom F f

      def mapDupHomFunDef {a₁ a₂ : α} (f : a₁ ⇾ a₂) : (mapDupHomFun F a₁ a₂) f ≃ mapDupHom F f :=
      byDef

      instance dupIsFun : IsCategoryFunctor (dup F) :=
      { F         := ⟨mapDupHomFun F⟩,
        hPreorder := { reflEq  := λ a =>
                                  idId hβ.Hom (dup F a) •
                                  congrArgTrans hβ.Hom (natReflEq (F.φ a) a •
                                                        natCongrArg (Functor.reflEq F a) a)
                                                       (Functor.reflEq (F.φ a) a) •
                                  mapDupHomFunDef F (idHom a),
                       transEq := λ {a₁ a₂ a₃} f g =>
                                  (congrArgTrans hβ.Hom (mapDupHomFunDef F f) (mapDupHomFunDef F g))⁻¹ •
                                  assoc (nat (mapHom F f) a₁) (mapHom (F.φ a₂) f) (mapDupHom F g) •
                                  defCongrArg (defTransFun (nat (mapHom F f) a₁) (dup F a₃))
                                              ((assoc (mapHom (F.φ a₂) f)
                                                      (nat (mapHom F g) a₂)
                                                      (mapHom (F.φ a₃) g))⁻¹ •
                                               defCongrArg (defRevTransFun hβ.Hom ((F.φ a₂).φ a₁)
                                                                                  (mapHom (F.φ a₃) g))
                                                           (naturality (mapHom F g) f) •
                                               assoc (nat (mapHom F g) a₁)
                                                     (mapHom (F.φ a₃) f)
                                                     (mapHom (F.φ a₃) g)) •
                                  (assoc (nat (mapHom F f) a₁) (nat (mapHom F g) a₁)
                                         (mapHom (F.φ a₃) g • mapHom (F.φ a₃) f))⁻¹ •
                                  congrArgTrans hβ.Hom (natTransEq (mapHom F f) (mapHom F g) a₁ •
                                                        natCongrArg (Functor.transEq F f g) a₁)
                                                       (Functor.transEq (F.φ a₃) f g) •
                                  mapDupHomFunDef F (g • f) } }

    end

    section

      variable [HasSubLinearFunOp W] (α : Sort u) (β : Sort v)
               [hα : IsCategory W α] [hβ : IsCategory W β] [HasFunProp α β] [h : HasConstFun α β]

      def constFun (b : β) : α ⮕ β := DefFun.toFunctor (h.defConstFun b)

      def mapConstNat {b₁ b₂ : β} (g : b₁ ⇾ b₂) :
        MetaQuantification hβ.Hom (constFun α β b₁).φ (constFun α β b₂).φ :=
      λ _ => g

      instance mapConstNat.isNat {b₁ b₂ : β} (g : b₁ ⇾ b₂) :
        IsNaturalTransformation (mapConstNat α β g) :=
      { nat := λ _ => (rightId g •
                       congrArgTransRight hβ.Hom (DefFun.byMapHomDef (hφ := IsCategoryFunctor.constFun α b₁) byDef) g)⁻¹ •
                      (leftId g •
                       congrArgTransLeft hβ.Hom g (DefFun.byMapHomDef (hφ := IsCategoryFunctor.constFun α b₂) byDef)) }

      def constNatDesc {b₁ b₂ : β} (g : b₁ ⇾ b₂) :
        NatDesc (constFun α β b₁) (constFun α β b₂) :=
      { nat   := mapConstNat       α β g,
        isNat := mapConstNat.isNat α β g }

      def constFunFunDesc : FunFunDesc h.defConstFun :=
      { natDesc        := constNatDesc α β,
        natDescReflEq  := λ b   _ => HasInstanceEquivalences.refl (idHom b),
        natDescTransEq := λ f g _ => HasInstanceEquivalences.refl (g • f) }

    end

    class HasConstFunFun [HasSubLinearFunOp W] (α : Sort u) (β : Sort v)
                         [hα : IsCategory W α] [hβ : IsCategory W β] [hFunαβ : HasFunProp α β]
                         [hNatαβ : HasNaturality α β] [hFunβαβ : HasFunProp β (α ⮕ β)]
                         [h : HasConstFun α β] where
    (defConstFunFun : DefFunFun (constFunFunDesc α β))

    namespace HasConstFunFun

      variable [HasSubLinearFunOp W] (α : Sort u) (β : Sort v) [hα : IsCategory W α]
               [hβ : IsCategory W β] [HasFunProp α β] [HasNaturality α β] [HasFunProp β (α ⮕ β)]
               [HasConstFun α β] [h : HasConstFunFun α β]

      def constFunFun : β ⮕ (α ⮕ β) := DefFunFun.toFunctor h.defConstFunFun

    end HasConstFunFun

    class HasDupFun [HasNonLinearFunOp W] (α : Sort u) (β : Sort v)
                    [hα : IsCategory W α] [hβ : IsCategory W β] [hFunαβ : HasFunProp α β]
                    [hNatαβ : HasNaturality α β] [hFunααβ : HasFunProp α (α ⮕ β)] where
    (defDupFun (F : α ⮕ α ⮕ β) : HasFunProp.DefFun (dup F))

    namespace HasDupFun

      variable [HasNonLinearFunOp W] (α : Sort u) (β : Sort v)
               [hα : IsCategory W α] [hβ : IsCategory W β] [HasFunProp α β]
               [HasNaturality α β] [HasFunProp α (α ⮕ β)] [h : HasDupFun α β]

      def dupFun (F : α ⮕ α ⮕ β) : α ⮕ β := DefFun.toFunctor (h.defDupFun F)

      variable [HasNaturality α (α ⮕ β)]

      def mapDupNat {F₁ F₂ : α ⮕ α ⮕ β} (η : F₁ ⇾ F₂) :
        MetaQuantification hβ.Hom (dupFun α β F₁).φ (dupFun α β F₂).φ :=
      λ a => nat (nat η a) a

      instance mapDupNat.isNat {F₁ F₂ : α ⮕ α ⮕ β} (η : F₁ ⇾ F₂) :
        IsNaturalTransformation (mapDupNat α β η) :=
      { nat := λ {a₁ a₂} f =>
               congrArgTransRight hβ.Hom (DefFun.byMapHomDef (hφ := dupIsFun F₁) (mapDupHomFunDef F₁ f))⁻¹
                                         (mapDupNat α β η a₂) •
               assoc (nat (mapHom F₁ f) a₁) (mapHom (F₁.φ a₂) f) (mapDupNat α β η a₂) •
               congrArgTransLeft hβ.Hom (nat (mapHom F₁ f) a₁)
                                        (naturality (nat η a₂) f) •
               (assoc (nat (mapHom F₁ f) a₁) (nat (nat η a₂) a₁) (mapHom (F₂.φ a₂) f))⁻¹ •
               congrArgTransRight hβ.Hom (natTransEq (mapHom F₁ f) (nat η a₂) a₁ •
                                          natCongrArg (naturality η f) a₁ •
                                          (natTransEq (nat η a₁) (mapHom F₂ f) a₁)⁻¹)
                                         (mapHom (F₂.φ a₂) f) •
               assoc (mapDupNat α β η a₁) (nat (mapHom F₂ f) a₁) (mapHom (F₂.φ a₂) f) •
               congrArgTransLeft hβ.Hom (mapDupNat α β η a₁)
                                        (DefFun.byMapHomDef (hφ := dupIsFun F₂) (mapDupHomFunDef F₂ f)) }

      def dupNatDesc {F₁ F₂ : α ⮕ α ⮕ β} (η : F₁ ⇾ F₂) :
        NatDesc (dupFun α β F₁) (dupFun α β F₂) :=
      { nat   := mapDupNat       α β η,
        isNat := mapDupNat.isNat α β η }

      def dupFunFunDesc : FunFunDesc h.defDupFun :=
      { natDesc        := dupNatDesc α β,
        natDescReflEq  := λ F   a => natReflEq (F.φ a) a •
                                     natCongrArg (natReflEq F a) a,
        natDescTransEq := λ η ε a => natTransEq (nat η a) (nat ε a) a •
                                     natCongrArg (natTransEq η ε a) a }

    end HasDupFun

    class HasDupFunFun [HasNonLinearFunOp W] (α : Sort u) (β : Sort v)
                       [hα : IsCategory W α] [hβ : IsCategory W β] [hFunαβ : HasFunProp α β]
                       [hNatαβ : HasNaturality α β] [hFunααβ : HasFunProp α (α ⮕ β)]
                       [hNatααβ : HasNaturality α (α ⮕ β)]
                       [hFunααβαβ : HasFunProp (α ⮕ α ⮕ β) (α ⮕ β)] extends
      HasDupFun α β where
    (defDupFunFun : DefFunFun (HasDupFun.dupFunFunDesc α β))

    namespace HasDupFunFun

      variable [HasNonLinearFunOp W] (α : Sort u) (β : Sort v) [hα : IsCategory W α]
               [hβ : IsCategory W β] [HasFunProp α β] [HasNaturality α β] [HasFunProp α (α ⮕ β)]
               [HasNaturality α (α ⮕ β)] [HasFunProp (α ⮕ α ⮕ β) (α ⮕ β)] [h : HasDupFunFun α β]

      def dupFunFun : (α ⮕ α ⮕ β) ⮕ (α ⮕ β) := DefFunFun.toFunctor h.defDupFunFun

    end HasDupFunFun

  end HasNaturality

  class IsNatUniverse (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw} W]
                      [hFunUniv : IsFunUniverse.{u} W] where
  [hasNat (α β : Sort (max 1 u w)) [hα : IsCategory W α] [hβ : IsCategory W β] :
     HasNaturality α β]

  namespace IsNatUniverse

    open HasFunProp

    section

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
               [IsFunUniverse.{u} W] [h : IsNatUniverse.{u} W]

      instance (α β : Sort (max 1 u w)) [hα : IsCategory W α] [hβ : IsCategory W β] :
        HasNaturality α β :=
      h.hasNat α β

    end

    class HasLinearFunctors (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw} W]
                            [hFunUniv : IsFunUniverse.{u} W]
                            [hFunLin : IsFunUniverse.HasLinearFunctors W]
                            [hNatUniv : IsNatUniverse.{u} W] where
    [hasRevAppFunFun (α β : Sort max 1 u w) [hα : IsCategory W α] [hβ : IsCategory W β] :
       HasNaturality.HasRevAppFunFun α β]

    namespace HasLinearFunctors

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
               [IsFunUniverse.{u} W] [IsFunUniverse.HasLinearFunctors W] [IsNatUniverse.{u} W]
               [h : HasLinearFunctors W]

      instance (α β : Sort (max 1 u w)) [hα : IsCategory W α] [hβ : IsCategory W β] :
        HasNaturality.HasRevAppFunFun α β :=
      h.hasRevAppFunFun α β

      def revAppFun {α : Sort (max 1 u w)} (a : α) (β : Sort (max 1 u w))
                    [hα : IsCategory W α] [hβ : IsCategory W β] :
        (α ⮕ β) ⮕ β :=
      HasNaturality.HasRevAppFun.revAppFun α β a

      def revAppFunFun (α β : Sort max 1 u w) [hα : IsCategory W α] [hβ : IsCategory W β] :
        α ⮕ (α ⮕ β) ⮕ β :=
      HasNaturality.HasRevAppFunFun.revAppFunFun α β

    end HasLinearFunctors

    class HasAffineFunctors (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw} W]
                            [HasSubLinearFunOp W] [hFunUniv : IsFunUniverse.{u} W]
                            [hFunAff : IsFunUniverse.HasAffineFunctors W]
                            [hNatUniv : IsNatUniverse.{u} W] extends
      HasLinearFunctors W where
    [hasConstFunFun (α β : Sort max 1 u w) [hα : IsCategory W α] [hβ : IsCategory W β] :
       HasNaturality.HasConstFunFun α β]

    namespace HasAffineFunctors

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W] [HasSubLinearFunOp W]
               [IsFunUniverse.{u} W] [IsFunUniverse.HasAffineFunctors W] [IsNatUniverse.{u} W]
               [h : HasAffineFunctors W]

      instance (α β : Sort (max 1 u w)) [hα : IsCategory W α] [hβ : IsCategory W β] :
        HasNaturality.HasConstFunFun α β :=
      h.hasConstFunFun α β

      def constFunFun (α β : Sort max 1 u w) [hα : IsCategory W α] [hβ : IsCategory W β] :
        β ⮕ (α ⮕ β) :=
      HasNaturality.HasConstFunFun.constFunFun α β

    end HasAffineFunctors

    class HasFullFunctors (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw} W]
                          [HasSubLinearFunOp W] [HasNonLinearFunOp W]
                          [hFunUniv : IsFunUniverse.{u} W]
                          [hFunAff : IsFunUniverse.HasAffineFunctors W]
                          [hNatUniv : IsNatUniverse.{u} W] extends
      HasAffineFunctors W where
    [hasDupFunFun (α β : Sort max 1 u w) [hα : IsCategory W α] [hβ : IsCategory W β] :
       HasNaturality.HasDupFunFun α β]

    namespace HasFullFunctors

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W] [HasSubLinearFunOp W]
               [HasNonLinearFunOp W] [IsFunUniverse.{u} W] [IsFunUniverse.HasAffineFunctors W]
               [IsNatUniverse.{u} W] [h : HasFullFunctors W]

      instance (α β : Sort (max 1 u w)) [hα : IsCategory W α] [hβ : IsCategory W β] :
        HasNaturality.HasDupFunFun α β :=
      h.hasDupFunFun α β

      def dupFun {α β : Sort max 1 u w} [hα : IsCategory W α] [hβ : IsCategory W β] (F : α ⮕ α ⮕ β) :
        α ⮕ β :=
      HasNaturality.HasDupFun.dupFun α β F

      def dupFunFun (α β : Sort max 1 u w) [hα : IsCategory W α] [hβ : IsCategory W β] :
        (α ⮕ α ⮕ β) ⮕ (α ⮕ β) :=
      HasNaturality.HasDupFunFun.dupFunFun α β

    end HasFullFunctors

  end IsNatUniverse

end CategoryTheory
