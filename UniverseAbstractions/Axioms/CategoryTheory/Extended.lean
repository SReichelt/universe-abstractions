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

      variable {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
               [h : HasFunProp α β] (F : Functor α β)

      instance isCategoryFunctor : IsCategoryFunctor F.φ := h.isCategoryFunctor F.F

      def mapHom {a b : α} (f : a ⇾ b) : F.φ a ⇾ F.φ b :=
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

      @[reducible] def toFunctor (F : DefFun φ) : Functor α β := ⟨F.F⟩

      def byDef {F : DefFun φ} {a b : α} {f : a ⇾ b} {g : φ a ⇾ φ b} (h : hφ.F f ≃ g) :
        (Functor.isCategoryFunctor (toFunctor F)).F f ≃ g :=
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

  end HasFunProp

  class IsFunUniverse (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw} W] where
  [hasFun (α β : Sort (max 1 u w)) [IsCategory W α] [IsCategory W β] : HasFunProp α β]

  namespace IsFunUniverse

    open HasFunProp

    section

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
               [h : IsFunUniverse.{u} W]

      instance (α β : Sort (max 1 u w)) [IsCategory W α] [IsCategory W β] : HasFunProp α β :=
      h.hasFun α β

    end

    class HasLinearFunctors (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw} W]
                            [hFunUniv : IsFunUniverse.{u} W] where
    (defIdFun (α : Sort (max 1 u w)) [IsCategory W α] : HasFunProp.DefFun (@id α))
    (defCompFun {α β γ : Sort (max 1 u w)} [IsCategory W α] [IsCategory W β] [IsCategory W γ]
                (F : HasFunProp.Functor α β) (G : HasFunProp.Functor β γ) :
       HasFunProp.DefFun (G.φ ∘ F.φ))

    namespace HasLinearFunctors

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W] [IsFunUniverse.{u} W]
               [h : HasLinearFunctors W]

      def idFun (α : Sort (max 1 u w)) [IsCategory W α] : Functor α α := DefFun.toFunctor (h.defIdFun α)

      def compFun {α β γ : Sort (max 1 u w)} [IsCategory W α] [IsCategory W β] [IsCategory W γ]
                  (F : Functor α β) (G : Functor β γ) :
        Functor α γ :=
      DefFun.toFunctor (h.defCompFun F G)

    end HasLinearFunctors

    class HasAffineFunctors (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw} W]
                            [hFunUniv : IsFunUniverse.{u} W]
                            [HasSubLinearFunOp W] extends
      HasLinearFunctors W where
    (defConstFun (α : Sort (max 1 u w)) {β : Sort (max 1 u w)} [IsCategory W α] [IsCategory W β] (b : β) :
       HasFunProp.DefFun (Function.const α b))

    namespace HasAffineFunctors

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W] [IsFunUniverse.{u} W]
               [HasSubLinearFunOp W] [h : HasAffineFunctors W]

      def constFun (α : Sort (max 1 u w)) {β : Sort (max 1 u w)} [IsCategory W α] [IsCategory W β] (b : β) :
        Functor α β :=
      DefFun.toFunctor (h.defConstFun α b)

    end HasAffineFunctors

  end IsFunUniverse



  structure NatDesc {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                    {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
                    [hFunProp : HasFunProp α β] (F G : HasFunProp.Functor α β) :
    Sort (max 1 u w iw) where
  (nat   : MetaQuantification hβ.Hom F.φ G.φ)
  [isNat : IsNaturalTransformation nat]

  namespace NatDesc

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
             {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
             [hFunProp : HasFunProp α β]
             {F G : HasFunProp.Functor α β} (η : NatDesc F G)

    instance : IsNaturalTransformation η.nat := η.isNat

  end NatDesc

  class HasNatRel {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                  (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
                  [hFunProp : HasFunProp α β] where
  (Nat : MetaRelation (HasFunProp.Functor α β) W)
  (desc {F G : HasFunProp.Functor α β} (η : Nat F G) : NatDesc F G)
  (defNatFun (F G : HasFunProp.Functor α β) (a : α) :
     Nat F G ⟶{λ η => (desc η).nat a} (F.φ a ⇾ G.φ a))

  namespace HasNatRel

    open HasFunctors HasFunProp HasFunProp.Functor

    section

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
               {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
               [hFunProp : HasFunProp α β] [h : HasNatRel α β]

      @[reducible] def nat {F G : Functor α β} (η : h.Nat F G) (a : α) : F.φ a ⇾ G.φ a :=
      (h.desc η).nat a

      @[reducible] def natFun (F G : Functor α β) (a : α) : h.Nat F G ⟶ (F.φ a ⇾ G.φ a) :=
      h.defNatFun F G a

      instance {F G : Functor α β} (η : h.Nat F G) (a : α) : IsFunApp (h.Nat F G) (nat η a) :=
      { F := natFun F G a,
        a := η,
        e := byDef }

      def natCongrArg {F G : Functor α β} {η₁ η₂ : h.Nat F G} (e : η₁ ≃ η₂) (a : α) :
        nat η₁ a ≃ nat η₂ a :=
      defCongrArg (defNatFun F G a) e

      def naturality {F G : Functor α β} (η : h.Nat F G) {a b : α} (f : a ⇾ b) :
        mapHom G f • nat η a ≃ nat η b • mapHom F f :=
      (h.desc η).isNat.nat f

      structure DefNat {F G : Functor α β} (desc : NatDesc F G) where
      (η             : h.Nat F G)
      (natEq (a : α) : nat η a ≃ desc.nat a)

      def byNatDef {F G : Functor α β} {desc : NatDesc F G} {η : DefNat desc} (a : α) :
        nat η.η a ≃ desc.nat a :=
      η.natEq a

      def NatEquiv {F G : Functor α β} (η₁ η₂ : h.Nat F G)
                   (hNat : ∀ a, nat η₁ a ≃ nat η₂ a) :=
      η₁ ≃ η₂

    end

    class HasTrivialNaturalityCondition {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                                        (α : Sort u) (β : Sort v)
                                        [hα : IsCategory W α] [hβ : IsCategory W β]
                                        [hFunProp : HasFunProp α β] [h : HasNatRel α β] where
    (nat {F G : Functor α β} (desc : NatDesc F G) : DefNat desc)

    namespace HasTrivialNaturalityCondition

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
               {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
               [HasFunProp α β] [HasNatRel α β] [h : HasTrivialNaturalityCondition α β]

      def defNat {F G : Functor α β} {desc : NatDesc F G} : DefNat desc := h.nat desc

    end HasTrivialNaturalityCondition

    class HasTrivialNatEquiv {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                             (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
                             [hFunProp : HasFunProp α β] [h : HasNatRel α β] where
    (equiv {F G : Functor α β} (η₁ η₂ : h.Nat F G) (hNat : ∀ a, nat η₁ a ≃ nat η₂ a) :
       NatEquiv η₁ η₂ hNat)

    namespace HasTrivialNatEquiv

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
               {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
               [HasFunProp α β] [hNatRel : HasNatRel α β] [h : HasTrivialNatEquiv α β]

      def natEquiv {F G : Functor α β} {η₁ η₂ : hNatRel.Nat F G} {hNat : ∀ a, nat η₁ a ≃ nat η₂ a} :
        NatEquiv η₁ η₂ hNat :=
      h.equiv η₁ η₂ hNat

    end HasTrivialNatEquiv

  end HasNatRel

  class HasNatOp {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                 (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
                 [hFunProp : HasFunProp α β] extends
    HasNatRel α β where
  (defRefl (F : HasFunProp.Functor α β) :
     HasNatRel.DefNat ⟨MetaQuantification.refl hβ.Hom F.φ⟩)
  (defTrans {F G H : HasFunProp.Functor α β} (η : Nat F G) (ε : Nat G H) :
     HasNatRel.DefNat ⟨MetaQuantification.trans hβ.Hom (desc η).nat (desc ε).nat⟩)

  namespace HasNatOp

    open HasNatRel

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]

    section

      variable (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
               [HasFunProp α β]

      instance [HasNatRel α β] [h : HasTrivialNaturalityCondition α β] : HasNatOp α β :=
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

      def natReflEq (F : HasFunProp.Functor α β) (a : α) :
        nat (HasRefl.refl F) a ≃ idHom (F.φ a) :=
      byNatDef a

      def natTransEq {F G H : HasFunProp.Functor α β} (η : Nat F G) (ε : Nat G H) (a : α) :
        nat (ε • η) a ≃ nat ε a • nat η a :=
      byNatDef a

      def natAssoc {F G H I : HasFunProp.Functor α β} (η : Nat F G) (ε : Nat G H) (θ : Nat H I)
                   (a : α) :
        nat ((θ • ε) • η) a ≃ nat (θ • (ε • η)) a :=
      (congrArgTransRight hβ.Hom (natTransEq η ε a) (nat θ a) •
       natTransEq (ε • η) θ a)⁻¹ •
      assoc (nat η a) (nat ε a) (nat θ a) •
      (congrArgTransLeft hβ.Hom (nat η a) (natTransEq ε θ a) •
       natTransEq η (θ • ε) a)

      def natRightId {F G : HasFunProp.Functor α β} (η : Nat F G) (a : α) :
        nat (η • HasRefl.refl F) a ≃ nat η a :=
      rightId (nat η a) •
      congrArgTransRight hβ.Hom (natReflEq F a) (nat η a) •
      natTransEq (HasRefl.refl F) η a

      def natLeftId {F G : HasFunProp.Functor α β} (η : Nat F G) (a : α) :
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
  (assoc {F G H I : HasFunProp.Functor α β} (η : Nat F G) (ε : Nat G H) (θ : Nat H I) :
     HasNatRel.NatEquiv ((θ • ε) • η) (θ • (ε • η)) (HasNatOp.natAssoc η ε θ))
  (rightId {F G : HasFunProp.Functor α β} (η : Nat F G) :
     HasNatRel.NatEquiv (η • HasRefl.refl F) η (HasNatOp.natRightId η))
  (leftId {F G : HasFunProp.Functor α β} (η : Nat F G) :
     HasNatRel.NatEquiv (HasRefl.refl G • η) η (HasNatOp.natLeftId η))

  namespace HasNatOpEquiv

    open HasNatRel

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
             (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β] [HasFunProp α β]

    instance [HasNatOp α β] [h : HasTrivialNatEquiv α β] : HasNatOpEquiv α β :=
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

      instance funHasMorphisms : HasMorphisms W (Functor α β) := ⟨h.Nat⟩

      instance funIsCategory : IsCategory.{max 1 u v w} W (Functor α β) :=
      { homIsPreorder            := HasNatOp.natIsPreorder α β,
        homHasTransFun           := h.natHasTransFun,
        homIsCategoricalPreorder := h.natIsCategoricalPreorder }

    end

    section

      variable {α : Sort u} (a : α) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
               [HasFunProp α β] [h : HasNaturality α β]

      def revApp (F : Functor α β) : β := F.φ a

      def revAppPreFun : PreFunctor h.Nat hβ.Hom (revApp a β) :=
      ⟨λ F₁ F₂ => natFun F₁ F₂ a⟩

      instance revAppPreFunIsPreorderFunctor : IsPreorderFunctor (revAppPreFun a β) :=
      { reflEq  := λ F   => natReflEq F a • byDef,
        transEq := λ η ε => (HasTransFun.congrArgTrans hβ.Hom byDef byDef)⁻¹ • natTransEq η ε a • byDef }

      instance revAppIsFun : IsCategoryFunctor (revApp a β) :=
      { F         := revAppPreFun a β,
        hPreorder := revAppPreFunIsPreorderFunctor a β }

    end

    class HasRevAppFun (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
                       [hFunProp₁ : HasFunProp α β] [h : HasNaturality α β]
                       [hFunProp₂ : HasFunProp (Functor α β) β] where
    (defRevAppFun (a : α) : HasFunProp.DefFun (revApp a β))

    namespace HasRevAppFun

      variable (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
               [HasFunProp α β] [h₁ : HasNaturality α β] [HasFunProp (Functor α β) β]
               [h₂ : HasNaturality (Functor α β) β] [h : HasRevAppFun α β]

      def revAppFun (a : α) : Functor (Functor α β) β :=
      DefFun.toFunctor (h.defRevAppFun a)

    end HasRevAppFun

    section

      variable (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
               [HasFunProp α β] [h₁ : HasNaturality α β] [HasFunProp (Functor α β) β]
               [h₂ : HasNaturality (Functor α β) β] [HasFunProp α (Functor (Functor α β) β)]
               [hApp : HasRevAppFun α β]

      def mapRevNat {a₁ a₂ : α} (f : a₁ ⇾ a₂) :
        MetaQuantification hβ.Hom (HasRevAppFun.revAppFun α β a₁).φ (HasRevAppFun.revAppFun α β a₂).φ :=
      λ F => mapHom F f

      instance mapRevNat.isNat {a₁ a₂ : α} (f : a₁ ⇾ a₂) : IsNaturalTransformation (mapRevNat α β f) :=
      { nat := λ {F₁ F₂} η => (naturality η f •
                                HasTransFun.congrArgTransRight hβ.Hom
                                                               (DefFun.byDef (hφ := revAppIsFun a₁ β) byDef)
                                                               (mapHom F₂ f))⁻¹ •
                               HasTransFun.congrArgTransLeft hβ.Hom
                                                             (mapHom F₁ f)
                                                             (DefFun.byDef (hφ := revAppIsFun a₂ β) byDef) }

      def revAppCongrArgDesc {a₁ a₂ : α} (f : a₁ ⇾ a₂) :
        NatDesc (HasRevAppFun.revAppFun α β a₁) (HasRevAppFun.revAppFun α β a₂) :=
      { nat   := mapRevNat       α β f,
        isNat := mapRevNat.isNat α β f }

      variable (defRevAppCongrArg : ∀ {a₁ a₂ : α} (f : a₁ ⇾ a₂), DefNat (revAppCongrArgDesc α β f))

      def revAppCongrArg {a₁ a₂ : α} (f : a₁ ⇾ a₂) :
        HasRevAppFun.revAppFun α β a₁ ⇾ HasRevAppFun.revAppFun α β a₂ :=
      (defRevAppCongrArg f).η

      def RevAppEquivReflType (a : α) :=
      NatEquiv (revAppCongrArg α β defRevAppCongrArg (idHom a))
               (idHom (HasRevAppFun.revAppFun α β a))
               (λ F => (byNatDef F)⁻¹ • Functor.reflEq F a • byNatDef F)

      def RevAppEquivTransType {a₁ a₂ a₃ : α} (f : a₁ ⇾ a₂) (g : a₂ ⇾ a₃) :=
      NatEquiv (revAppCongrArg α β defRevAppCongrArg (g • f))
               (revAppCongrArg α β defRevAppCongrArg g • revAppCongrArg α β defRevAppCongrArg f)
               (λ F => (HasTransFun.congrArgTrans hβ.Hom (byNatDef F) (byNatDef F) • byNatDef F)⁻¹ •
                       Functor.transEq F f g •
                       byNatDef F)

      variable (defRevAppCongrArgFun : ∀ a₁ a₂ : α, (a₁ ⇾ a₂) ⟶{λ f => revAppCongrArg α β defRevAppCongrArg f} (HasRevAppFun.revAppFun α β a₁ ⇾ HasRevAppFun.revAppFun α β a₂))

      @[reducible] def revAppCongrArgFun (a₁ a₂ : α) :
        (a₁ ⇾ a₂) ⟶ (HasRevAppFun.revAppFun α β a₁ ⇾ HasRevAppFun.revAppFun α β a₂) :=
      defRevAppCongrArgFun a₁ a₂

      variable (revAppEquivRefl : ∀ a : α, RevAppEquivReflType α β defRevAppCongrArg a)
               (revAppEquivTrans : ∀ {a₁ a₂ a₃ : α} (f : a₁ ⇾ a₂) (g : a₂ ⇾ a₃), RevAppEquivTransType α β defRevAppCongrArg f g)

      instance revAppFunIsFun : IsCategoryFunctor (λ a : α => HasRevAppFun.revAppFun α β a) :=
      { F         := ⟨revAppCongrArgFun α β defRevAppCongrArg defRevAppCongrArgFun⟩,
        hPreorder := { reflEq  := λ a   => revAppEquivRefl a • byDef,
                       transEq := λ f g => HasTransFun.congrArgTrans h₂.Nat byDef⁻¹ byDef⁻¹ •
                                           revAppEquivTrans f g •
                                           byDef } }

      def DefRevAppFunFunType :=
      HasFunProp.DefFun (HasRevAppFun.revAppFun α β)
        (hφ := revAppFunIsFun α β defRevAppCongrArg defRevAppCongrArgFun revAppEquivRefl revAppEquivTrans)

      def revAppFunFun (defRevAppFunFun : DefRevAppFunFunType α β defRevAppCongrArg defRevAppCongrArgFun
                                                                  revAppEquivRefl revAppEquivTrans) :
        Functor α (Functor (Functor α β) β) :=
      DefFun.toFunctor defRevAppFunFun
        (hφ := revAppFunIsFun α β defRevAppCongrArg defRevAppCongrArgFun revAppEquivRefl revAppEquivTrans)

    end

    class HasRevAppFunFun (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
                          [hFunProp₁ : HasFunProp α β] [h₁ : HasNaturality α β]
                          [hFunProp₂ : HasFunProp (Functor α β) β] [h₂ : HasNaturality (Functor α β) β]
                          [hFunProp₃ : HasFunProp α (Functor (Functor α β) β)] extends
      HasRevAppFun α β where
    (defRevAppCongrArg {a₁ a₂ : α} (f : a₁ ⇾ a₂) : DefNat (revAppCongrArgDesc α β f))
    (defRevAppCongrArgFun (a₁ a₂ : α) :
       (a₁ ⇾ a₂)
       ⟶{λ f => revAppCongrArg α β defRevAppCongrArg f}
       (HasRevAppFun.revAppFun α β a₁ ⇾ HasRevAppFun.revAppFun α β a₂))
    (revAppEquivRefl (a : α) : RevAppEquivReflType α β defRevAppCongrArg a)
    (revAppEquivTrans {a₁ a₂ a₃ : α} (f : a₁ ⇾ a₂) (g : a₂ ⇾ a₃) :
       RevAppEquivTransType α β defRevAppCongrArg f g)
    (defRevAppFunFun : DefRevAppFunFunType α β defRevAppCongrArg defRevAppCongrArgFun
                                               revAppEquivRefl revAppEquivTrans)

    namespace HasRevAppFunFun

      variable (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
               [HasFunProp α β] [h₁ : HasNaturality α β] [HasFunProp (Functor α β) β]
               [h₂ : HasNaturality (Functor α β) β] [HasFunProp α (Functor (Functor α β) β)]
               [h : HasRevAppFunFun α β]

      def revAppFunFun : Functor α (Functor (Functor α β) β) :=
      HasNaturality.revAppFunFun α β h.defRevAppCongrArg h.defRevAppCongrArgFun
                                     h.revAppEquivRefl h.revAppEquivTrans h.defRevAppFunFun

    end HasRevAppFunFun

    section

      variable [HasSubstFun W W W] {α : Sort u} {β : Sort v}
               [hα : IsCategory W α] [hβ : IsCategory W β] [HasFunProp α β] [h : HasNaturality α β]
               [HasFunProp α (Functor α β)] (F : Functor α (Functor α β))

      def dup (a : α) : β := (F.φ a).φ a

      @[reducible] def mapDupHom {a₁ a₂ : α} (f : a₁ ⇾ a₂) : dup F a₁ ⇾ dup F a₂ :=
      mapHom (F.φ a₂) f • nat (mapHom F f) a₁

      @[reducible] def mapDupHom' {a₁ a₂ : α} (f : a₁ ⇾ a₂) : dup F a₁ ⇾ dup F a₂ :=
      nat (mapHom F f) a₂ • mapHom (F.φ a₁) f

      def mapDupHomEq {a₁ a₂ : α} (f : a₁ ⇾ a₂) : mapDupHom F f ≃ mapDupHom' F f :=
      naturality (mapHom F f) f

      def mapDupHomFun (a₁ a₂ : α) : (a₁ ⇾ a₂) ⟶ (dup F a₁ ⇾ dup F a₂) :=
      Λ f => mapDupHom F f

      def dupPreFun : PreFunctor hα.Hom hβ.Hom (dup F) :=
      ⟨mapDupHomFun F⟩

      def dupReflEq (a : α) : (mapDupHomFun F a a) (idHom a) ≃ idHom (dup F a) :=
      idId hβ.Hom (dup F a) •
      congrArgTrans hβ.Hom (natReflEq (F.φ a) a • natCongrArg (Functor.reflEq F a) a)
                           (Functor.reflEq (F.φ a) a) •
      byDef

      def dupTransEq {a₁ a₂ a₃ : α} (f : a₁ ⇾ a₂) (g : a₂ ⇾ a₃) :
        (mapDupHomFun F a₁ a₃) (g • f) ≃ (mapDupHomFun F a₂ a₃) g • (mapDupHomFun F a₁ a₂) f :=
      (congrArgTrans hβ.Hom byDef byDef)⁻¹ •
      assoc (nat (mapHom F f) a₁) (mapHom (F.φ a₂) f) (mapDupHom F g) •
      defCongrArg (defTransFun (nat (mapHom F f) a₁) (dup F a₃))
                  ((assoc (mapHom (F.φ a₂) f) (nat (mapHom F g) a₂) (mapHom (F.φ a₃) g))⁻¹ •
                   defCongrArg (defRevTransFun hβ.Hom ((F.φ a₂).φ a₁) (mapHom (F.φ a₃) g))
                               (naturality (mapHom F g) f) •
                   assoc (nat (mapHom F g) a₁) (mapHom (F.φ a₃) f) (mapHom (F.φ a₃) g)) •
      (assoc (nat (mapHom F f) a₁) (nat (mapHom F g) a₁) (mapHom (F.φ a₃) g • mapHom (F.φ a₃) f))⁻¹ •
      congrArgTrans hβ.Hom (natTransEq (mapHom F f) (mapHom F g) a₁ •
                            natCongrArg (Functor.transEq F f g) a₁)
                           (Functor.transEq (F.φ a₃) f g) •
      byDef

      instance dupPreFunIsPreorderFunctor : IsPreorderFunctor (dupPreFun F) :=
      { reflEq  := dupReflEq  F,
        transEq := dupTransEq F }

      instance dupIsFun : IsCategoryFunctor (dup F) :=
      { F         := dupPreFun F,
        hPreorder := dupPreFunIsPreorderFunctor F }

    end

    class HasDupFun [HasSubstFun W W W] (α : Sort u) (β : Sort v)
                    [hα : IsCategory W α] [hβ : IsCategory W β] [hFunProp₁ : HasFunProp α β]
                    [h : HasNaturality α β] [hFunProp₂ : HasFunProp α (Functor α β)] where
    (defDupFun (F : Functor α (Functor α β)) : HasFunProp.DefFun (dup F))

    namespace HasDupFun

      variable [HasSubstFun W W W] (α : Sort u) (β : Sort v)
               [hα : IsCategory W α] [hβ : IsCategory W β] [HasFunProp α β]
               [HasNaturality α β] [HasFunProp α (Functor α β)] [h : HasDupFun α β]

      def dupFun (F : Functor α (Functor α β)) : Functor α β :=
      DefFun.toFunctor (h.defDupFun F)

    end HasDupFun

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
                            [hFunUniv : IsFunUniverse.{u} W] [hNatUniv : IsNatUniverse.{u} W] where
    [hasRevAppFunFun (α β : Sort max 1 u w) [hα : IsCategory W α] [hβ : IsCategory W β] :
       HasNaturality.HasRevAppFunFun α β]

    namespace HasLinearFunctors

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
               [IsFunUniverse.{u} W] [IsNatUniverse.{u} W] [h : HasLinearFunctors W]

      instance (α β : Sort (max 1 u w)) [hα : IsCategory W α] [hβ : IsCategory W β] :
        HasNaturality.HasRevAppFunFun α β :=
      h.hasRevAppFunFun α β

      def revAppFun {α : Sort (max 1 u w)} (a : α) (β : Sort (max 1 u w))
                    [hα : IsCategory W α] [hβ : IsCategory W β] :
        Functor (Functor α β) β :=
      HasNaturality.HasRevAppFun.revAppFun α β a

      def revAppFunFun (α β : Sort max 1 u w) [hα : IsCategory W α] [hβ : IsCategory W β] :
        Functor α (Functor (Functor α β) β) :=
      HasNaturality.HasRevAppFunFun.revAppFunFun α β

    end HasLinearFunctors

  end IsNatUniverse

end CategoryTheory
