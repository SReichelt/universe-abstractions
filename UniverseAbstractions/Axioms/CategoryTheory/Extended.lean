import UniverseAbstractions.Axioms.CategoryTheory.Basic



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
       HasFunctors HasCongrArg HasCongrFun HasLinearFunOp HasNonLinearFunOp

  structure FunDesc {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                    {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
                    (φ : α → β) where
  (F  : PreFunctor hα.Hom hβ.Hom φ)
  [hF : IsCategoryFunctor ⟨F⟩]

  namespace FunDesc

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
             {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β] {φ : α → β}

    @[reducible] def morFun (F : FunDesc φ) : MorphismFunctor α β := ⟨F.F⟩

    instance (F : FunDesc φ) : IsCategoryFunctor (morFun F) := F.hF

    instance (F : FunDesc φ) : IsReflFunctor  F.F := F.hF.toIsReflFunctor
    instance (F : FunDesc φ) : IsTransFunctor F.F := F.hF.toIsTransFunctor

    def FunDescEq (F G : FunDesc φ) := ∀ a b, F.F.baseFun a b ≃ G.F.baseFun a b

  end FunDesc

  class HasFunProp {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                   (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β] where
  (Fun : MetaProperty (α → β) W)
  (desc {φ : α → β} : Fun φ → FunDesc φ)

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

      def desc : FunDesc F.φ := h.desc F.F
      @[reducible] def preFun : PreFunctor hα.Hom hβ.Hom F.φ := (desc F).F
      @[reducible] def morFun : MorphismFunctor α β := ⟨preFun F⟩

      @[reducible] def mapHom {a b : α} (f : a ⇾ b) : F.φ a ⇾ F.φ b :=
      (preFun F) f

      def reflEq (a : α) : mapHom F (idHom a) ≃ idHom (F.φ a) :=
      IsReflFunctor.reflEq (F := preFun F) a

      def transEq {a b c : α} (f : a ⇾ b) (g : b ⇾ c) :
        mapHom F (g • f) ≃ mapHom F g • mapHom F f :=
      IsTransFunctor.transEq (F := preFun F) f g

      def mapHomCongrArg {a b : α} {f₁ f₂ : a ⇾ b} (e : f₁ ≃ f₂) :
        mapHom F f₁ ≃ mapHom F f₂ :=
      HasCongrArg.congrArg ((preFun F).baseFun a b) e

    end Functor

    structure DefFun {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
                     [h : HasFunProp α β] {φ : α → β} (desc : FunDesc φ) where
    (F  : h.Fun φ)
    (eq : FunDesc.FunDescEq (h.desc F) desc)

    namespace DefFun

      variable {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
               [h : HasFunProp α β] {φ : α → β} {desc : FunDesc φ}

      @[reducible] def toFunctor (F : DefFun desc) : α ⮕ β := ⟨F.F⟩

      def byMapHomDef {F : DefFun desc} {a b : α} {f : a ⇾ b} {g : φ a ⇾ φ b} (h : desc.F f ≃ g) :
        Functor.mapHom (toFunctor F) f ≃ g :=
      h • HasCongrFun.congrFun (F.eq a b) f

    end DefFun

    @[reducible] def DefFun' {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
                             [h : HasFunProp α β] (F : MorphismFunctor α β)
                             [hF : IsCategoryFunctor F] :=
    DefFun ⟨F.F⟩

    namespace DefFun'

      variable {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
               [h : HasFunProp α β] {F : MorphismFunctor α β} [hF : IsCategoryFunctor F]

      @[reducible] def toFunctor (F' : DefFun' F) : α ⮕ β := DefFun.toFunctor F'

      def byMapHomDef {F' : DefFun' F} {a b : α} {f : a ⇾ b} {g : F.φ a ⇾ F.φ b} (h : F.F f ≃ g) :
        Functor.mapHom (toFunctor F') f ≃ g :=
      DefFun.byMapHomDef h

    end DefFun'

    class HasTrivialFunctorialityCondition (α : Sort u) (β : Sort v)
                                           [hα : IsCategory W α] [hβ : IsCategory W β]
                                           [h : HasFunProp α β] where
    (functor {φ : α → β} (desc : FunDesc φ) : DefFun desc)

    namespace HasTrivialFunctorialityCondition

      variable {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
               [HasFunProp α β] [h : HasTrivialFunctorialityCondition α β]
      
      def defFun {φ : α → β} {desc : FunDesc φ} : DefFun desc := h.functor desc

    end HasTrivialFunctorialityCondition

    class HasIdFun (α : Sort u) [hα : IsCategory W α] [hFunαα : HasFunProp α α] where 
    (defIdFun : DefFun' (MorphismFunctor.idFun α))

    namespace HasIdFun

      instance trivial (α : Sort u) [IsCategory W α] [HasFunProp α α]
                       [HasTrivialFunctorialityCondition α α] :
        HasIdFun α :=
      ⟨HasTrivialFunctorialityCondition.defFun⟩

    end HasIdFun

    class HasConstFun [HasSubLinearFunOp W] (α : Sort u) (β : Sort v) [hα : IsCategory W α]
                      [hβ : IsCategory W β] [hFunαβ : HasFunProp α β] where
    (defConstFun (b : β) : DefFun' (MorphismFunctor.constFun α b))

    namespace HasConstFun

      instance trivial [HasSubLinearFunOp W] (α : Sort u) (β : Sort v) [IsCategory W α]
                       [IsCategory W β] [HasFunProp α β] [HasTrivialFunctorialityCondition α β] :
        HasConstFun α β :=
      ⟨λ _ => HasTrivialFunctorialityCondition.defFun⟩

    end HasConstFun

    class HasCompFun (α : Sort u) (β : Sort u') (γ : Sort u'') [hα : IsCategory W α]
                     [hβ : IsCategory W β] [hγ : IsCategory W γ] [hFunαβ : HasFunProp α β]
                     [hFunβγ : HasFunProp β γ] [hFunαγ : HasFunProp α γ] where
    (defCompFun (F : α ⮕ β) (G : β ⮕ γ) :
       DefFun' (MorphismFunctor.compFun (Functor.morFun F) (Functor.morFun G)))

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
  (η     : Quantification (HasFunProp.Functor.morFun F) (HasFunProp.Functor.morFun G))
  [isNat : IsNaturalTransformation η]

  namespace NatDesc

    open HasFunProp.Functor

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
             {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
             [hFunProp : HasFunProp α β]

    def strict {φ : α → β} (F G : hFunProp.Fun φ)
               (hEq : ∀ {a b : α} (f : a ⇾ b), mapHom ⟨F⟩ f ≃ mapHom ⟨G⟩ f) :
      NatDesc ⟨F⟩ ⟨G⟩ :=
    { η     := λ a => idHom (φ a),
      isNat := IsNaturalTransformation.fromEq hEq }

    variable {F G : α ⮕ β} (η : NatDesc F G)

    instance : IsNaturalTransformation η.η := η.isNat

  end NatDesc

  class HasNatRel {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                  (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
                  [hFunProp : HasFunProp α β] where
  (Nat : MetaRelation (α ⮕ β) W)
  (desc {F G : α ⮕ β} (η : Nat F G) : NatDesc F G)
  (defNatFun (F G : α ⮕ β) (a : α) :
     Nat F G ⟶{λ η => (desc η).η a} (F.φ a ⇾ G.φ a))

  namespace HasNatRel

    open HasFunctors HasFunProp HasFunProp.Functor

    section

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
               {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
               [hFunProp : HasFunProp α β] [h : HasNatRel α β]

      @[reducible] def nat {F G : α ⮕ β} (η : h.Nat F G) (a : α) : F.φ a ⇾ G.φ a :=
      (h.desc η).η a

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
        nat η b • mapHom F f ≃ mapHom G f • nat η a :=
      (h.desc η).isNat.nat f

      structure DefNat {F G : α ⮕ β} (desc : NatDesc F G) where
      (η             : h.Nat F G)
      (natEq (a : α) : nat η a ≃ desc.η a)

      def byNatDef {F G : α ⮕ β} {desc : NatDesc F G} {η : DefNat desc} (a : α) :
        nat η.η a ≃ desc.η a :=
      η.natEq a

      def NatEquiv {F G : α ⮕ β} (η₁ η₂ : h.Nat F G)
                   (hNat : ∀ a, nat η₁ a ≃ nat η₂ a) :=
      η₁ ≃ η₂

      def DefNatEquiv {F G : α ⮕ β} {desc₁ desc₂ : NatDesc F G} (η₁ : DefNat desc₁)
                      (η₂ : DefNat desc₂) (hNat : ∀ a, desc₁.η a ≃ desc₂.η a) :=
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
  (defRefl (F : α ⮕ β) : HasNatRel.DefNat { η     := Quantification.refl (HasFunProp.Functor.morFun F),
                                            isNat := IsNaturalTransformation.refl (HasFunProp.Functor.morFun F)})
  (defTrans {F G H : α ⮕ β} (η : Nat F G) (ε : Nat G H) :
     HasNatRel.DefNat ⟨Quantification.trans (desc η).η (desc ε).η⟩)

  namespace HasNatOp

    open HasFunProp HasFunProp.Functor HasNatRel

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
               [hFunProp : HasFunProp α β] [h : HasNatOp α β]

      def natReflEq (F : α ⮕ β) (a : α) :
        nat (HasRefl.refl F) a ≃ idHom (F.φ a) :=
      byNatDef a

      def natTransEq {F G H : α ⮕ β} (η : h.Nat F G) (ε : h.Nat G H) (a : α) :
        nat (ε • η) a ≃ nat ε a • nat η a :=
      byNatDef a

      def natAssoc {F G H I : α ⮕ β} (η : h.Nat F G) (ε : h.Nat G H) (θ : h.Nat H I) (a : α) :
        nat ((θ • ε) • η) a ≃ nat (θ • (ε • η)) a :=
      (congrArgTransRight hβ.Hom (natTransEq η ε a) (nat θ a) •
       natTransEq (ε • η) θ a)⁻¹ •
      assoc (nat η a) (nat ε a) (nat θ a) •
      (congrArgTransLeft hβ.Hom (nat η a) (natTransEq ε θ a) •
       natTransEq η (θ • ε) a)

      def natRightId {F G : α ⮕ β} (η : h.Nat F G) (a : α) :
        nat (η • HasRefl.refl F) a ≃ nat η a :=
      cancelRightId hβ.Hom (natReflEq F a) (nat η a) •
      natTransEq (HasRefl.refl F) η a

      def natLeftId {F G : α ⮕ β} (η : h.Nat F G) (a : α) :
        nat (HasRefl.refl G • η) a ≃ nat η a :=
      cancelLeftId hβ.Hom (nat η a) (natReflEq G a) •
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

      instance : HasTransFun h.Nat := h.natHasTransFun

      instance funHasMorphisms : HasMorphisms W (α ⮕ β) := ⟨h.Nat⟩

      instance funIsCategory : IsCategory.{max 1 u v w} W (α ⮕ β) :=
      { homIsPreorder            := HasNatOp.natIsPreorder α β,
        homHasTransFun           := h.natHasTransFun,
        homIsCategoricalPreorder := HasNatOpEquiv.natIsCategoricalPreorder α β }

    end

    section

      variable {α : Sort u} {β : Sort u'} {γ : Sort u''}
               [hα : IsCategory W α] [hβ : IsCategory W β] [hγ : IsCategory W γ]
               [hFunβγ : HasFunProp β γ] [hNatβγ : HasNaturality β γ]
               {φ : α → β → γ} {Φ : ∀ a, FunDesc (φ a)}

      structure FunFunDesc (F : ∀ a, HasFunProp.DefFun (Φ a)) where
      (natDesc {a₁ a₂ : α} : (a₁ ⇾ a₂) → NatDesc (DefFun.toFunctor (F a₁)) (DefFun.toFunctor (F a₂)))
      (natDescReflEq (a : α) (b : β) : (natDesc (idHom a)).η b ≃ idHom (φ a b))
      (natDescTransEq {a₁ a₂ a₃ : α} (f : a₁ ⇾ a₂) (g : a₂ ⇾ a₃) (b : β) :
         (natDesc (g • f)).η b ≃ (natDesc g).η b • (natDesc f).η b)

      structure DefFunFunBase {F : ∀ a, HasFunProp.DefFun (Φ a)} (desc : FunFunDesc F) where
      (defNat {a₁ a₂ : α} (f : a₁ ⇾ a₂) : DefNat (desc.natDesc f))
      (defNatFun (a₁ a₂ : α) :
         (a₁ ⇾ a₂) ⟶{λ f => (defNat f).η} (DefFun.toFunctor (F a₁) ⇾ DefFun.toFunctor (F a₂)))
      (natReflEq (a : α) :
         DefNatEquiv (defNat (idHom a)) (HasNatOp.defRefl (DefFun.toFunctor (F a)))
                     (desc.natDescReflEq a))
      (natTransEq {a₁ a₂ a₃ : α} (f : a₁ ⇾ a₂) (g : a₂ ⇾ a₃) :
         DefNatEquiv (defNat (g • f)) (HasNatOp.defTrans (defNat f).η (defNat g).η)
                     (λ b => (congrArgTrans hγ.Hom (byNatDef b) (byNatDef b))⁻¹ •
                             desc.natDescTransEq f g b))

      namespace DefFunFunBase

        variable {F : ∀ a, HasFunProp.DefFun (Φ a)} {desc : FunFunDesc F} (G : DefFunFunBase desc)

        @[reducible] def natFun (a₁ a₂ : α) :
          (a₁ ⇾ a₂) ⟶ (DefFun.toFunctor (F a₁) ⇾ DefFun.toFunctor (F a₂)) :=
        G.defNatFun a₁ a₂

        instance : IsCategoryFunctor ⟨⟨natFun G⟩⟩ :=
        { reflEq  := λ a   => G.natReflEq a • byDef,
          transEq := λ f g => (congrArgTrans hNatβγ.Nat byDef byDef)⁻¹ •
                              G.natTransEq f g •
                              byDef }

        def funDesc : FunDesc (λ a => DefFun.toFunctor (F a)) := ⟨⟨natFun G⟩⟩

      end DefFunFunBase

      structure DefFunFun [hFunαβγ : HasFunProp α (β ⮕ γ)] {F : ∀ a, HasFunProp.DefFun (Φ a)}
                          (desc : FunFunDesc F) extends
        DefFunFunBase desc where
      (defFunFun : DefFun (DefFunFunBase.funDesc toDefFunFunBase))

      namespace DefFunFun

        variable [HasFunProp α (β ⮕ γ)] {F : ∀ a, HasFunProp.DefFun (Φ a)} {desc : FunFunDesc F}

        def fromTrivialFunctoriality [h : HasTrivialFunctorialityCondition α (β ⮕ γ)]
                                     (base : DefFunFunBase desc) :
          DefFunFun desc :=
        { toDefFunFunBase := base,
          defFunFun       := HasTrivialFunctorialityCondition.defFun }

        def toFunctor (F : DefFunFun desc) : α ⮕ β ⮕ γ := DefFun.toFunctor F.defFunFun

      end DefFunFun

    end

    section

      variable {α : Sort u} (a : α) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
               [HasFunProp α β] [h : HasNaturality α β]

      def revApp (F : α ⮕ β) : β := F.φ a

      instance : IsCategoryFunctor { φ := revApp a β,
                                     F := ⟨λ F₁ F₂ => natFun F₁ F₂ a⟩ } :=
      { reflEq  := λ F   => natReflEq F a • byDef,
        transEq := λ η ε => (congrArgTrans hβ.Hom byDef byDef)⁻¹ •
                            natTransEq η ε a •
                            byDef }


      def revAppFunDesc : FunDesc (revApp a β) := ⟨⟨λ F₁ F₂ => natFun F₁ F₂ a⟩⟩

    end

    class HasRevAppFun (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
                       [hFunαβ : HasFunProp α β] [hNatαβ : HasNaturality α β]
                       [hFunαββ : HasFunProp (α ⮕ β) β] where
    (defRevAppFun (a : α) : HasFunProp.DefFun (revAppFunDesc a β))

    namespace HasRevAppFun

      variable (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
               [HasFunProp α β] [HasNaturality α β] [HasFunProp (α ⮕ β) β]
               [h : HasRevAppFun α β]

      def revAppFun (a : α) : (α ⮕ β) ⮕ β := DefFun.toFunctor (h.defRevAppFun a)

      def mapRevNat {a₁ a₂ : α} (f : a₁ ⇾ a₂) :
        Quantification (morFun (revAppFun α β a₁)) (morFun (revAppFun α β a₂)) :=
      λ F => mapHom F f

      instance mapRevNat.isNat {a₁ a₂ : α} (f : a₁ ⇾ a₂) :
        IsNaturalTransformation (mapRevNat α β f) :=
      { nat := λ {F₁ F₂} η => (naturality η f •
                               congrArgTransLeft hβ.Hom
                                                 (mapHom F₁ f)
                                                 (DefFun.byMapHomDef (desc := revAppFunDesc a₂ β) byDef))⁻¹ •
                              congrArgTransRight hβ.Hom
                                                 (DefFun.byMapHomDef (desc := revAppFunDesc a₁ β) byDef)
                                                 (mapHom F₂ f)}

      def revAppNatDesc {a₁ a₂ : α} (f : a₁ ⇾ a₂) :
        NatDesc (revAppFun α β a₁) (revAppFun α β a₂) :=
      { η     := mapRevNat       α β f,
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

      variable (α : Sort u) (β : Sort u') (γ : Sort u'')
               [hα : IsCategory W α] [hβ : IsCategory W β] [hγ : IsCategory W γ]
               [HasFunProp α β] [HasFunProp β γ] [HasFunProp α γ] [h : HasCompFun α β γ]

      def compFun (F : α ⮕ β) (G : β ⮕ γ) : α ⮕ γ := DefFun.toFunctor (h.defCompFun F G)

      section

        variable [HasNaturality β γ] (F : α ⮕ β)

        def mapCompNat {G₁ G₂ : β ⮕ γ} (η : G₁ ⇾ G₂) :
          Quantification (morFun (compFun α β γ F G₁)) (morFun (compFun α β γ F G₂)) :=
        λ a => nat η (F.φ a)

        instance mapCompNat.isNat {G₁ G₂ : β ⮕ γ} (η : G₁ ⇾ G₂) :
          IsNaturalTransformation (mapCompNat α β γ F η) :=
        { nat := λ {a₁ a₂} f =>
                 (congrArgTransLeft hγ.Hom (mapCompNat α β γ F η a₁)
                                           (DefFun'.byMapHomDef (F := MorphismFunctor.compFun (morFun F) (morFun G₂)) byDef))⁻¹ •
                 naturality η (mapHom F f) •
                 congrArgTransRight hγ.Hom (DefFun'.byMapHomDef (F := MorphismFunctor.compFun (morFun F) (morFun G₁)) byDef)
                                           (mapCompNat α β γ F η a₂) }

        def compNatDesc {G₁ G₂ : β ⮕ γ} (η : G₁ ⇾ G₂) :
          NatDesc (compFun α β γ F G₁) (compFun α β γ F G₂) :=
        { η     := mapCompNat       α β γ F η,
          isNat := mapCompNat.isNat α β γ F η }

        def compFunFunDesc : FunFunDesc (h.defCompFun F) :=
        { natDesc        := compNatDesc α β γ F,
          natDescReflEq  := λ G   a => natReflEq  G   (F.φ a),
          natDescTransEq := λ η ε a => natTransEq η ε (F.φ a) }

      end

      section

        variable [HasNaturality α β] (G : β ⮕ γ)

        def mapRevCompNat {F₁ F₂ : α ⮕ β} (η : F₁ ⇾ F₂) :
          Quantification (morFun (compFun α β γ F₁ G)) (morFun (compFun α β γ F₂ G)) :=
        λ a => mapHom G (nat η a)

        instance mapRevCompNat.isNat {F₁ F₂ : α ⮕ β} (η : F₁ ⇾ F₂) :
          IsNaturalTransformation (mapRevCompNat α β γ G η) :=
        { nat := λ {a₁ a₂} f =>
                 (congrArgTransLeft hγ.Hom (mapRevCompNat α β γ G η a₁)
                                           (DefFun'.byMapHomDef (F := MorphismFunctor.compFun (morFun F₂) (morFun G)) byDef))⁻¹ •
                 Functor.transEq G (nat η a₁) (mapHom F₂ f) •
                 mapHomCongrArg G (naturality η f) •
                 (Functor.transEq G (mapHom F₁ f) (nat η a₂))⁻¹ •
                 congrArgTransRight hγ.Hom (DefFun'.byMapHomDef (F := MorphismFunctor.compFun (morFun F₁) (morFun G)) byDef)
                                           (mapRevCompNat α β γ G η a₂) }

        def revCompNatDesc {F₁ F₂ : α ⮕ β} (η : F₁ ⇾ F₂) :
          NatDesc (compFun α β γ F₁ G) (compFun α β γ F₂ G) :=
        { η     := mapRevCompNat       α β γ G η,
          isNat := mapRevCompNat.isNat α β γ G η }

        def revCompFunFunDesc : FunFunDesc (λ F => h.defCompFun F G) :=
        { natDesc        := revCompNatDesc α β γ G,
          natDescReflEq  := λ F   a => Functor.reflEq G (F.φ a) • mapHomCongrArg G (natReflEq F a),
          natDescTransEq := λ η ε a => Functor.transEq G (nat η a) (nat ε a) •
                                       mapHomCongrArg G (natTransEq η ε a) }

      end

    end

    class HasCompFunFun (α : Sort u) (β : Sort u') (γ : Sort u'') [hα : IsCategory W α]
                        [hβ : IsCategory W β] [hγ : IsCategory W γ] [hFunαβ : HasFunProp α β]
                        [hFunβγ : HasFunProp β γ] [hFunαγ : HasFunProp α γ]
                        [hNatαβ : HasNaturality α β] [hNatβγ : HasNaturality β γ]
                        [hNatαγ : HasNaturality α γ] [hFunβγαγ : HasFunProp (β ⮕ γ) (α ⮕ γ)]
                        [hFunαβαγ : HasFunProp (α ⮕ β) (α ⮕ γ)] [h : HasCompFun α β γ] where
    (defCompFunFun    (F : α ⮕ β) : DefFunFun (compFunFunDesc    α β γ F))
    (defRevCompFunFun (G : β ⮕ γ) : DefFunFun (revCompFunFunDesc α β γ G))
    (compNatEq {F₁ F₂ : α ⮕ β} {G₁ G₂ : β ⮕ γ} (η : F₁ ⇾ F₂) (ε : G₁ ⇾ G₂) :
       NatEquiv (((defCompFunFun F₂).defNat ε).η • ((defRevCompFunFun G₁).defNat η).η)
                (((defRevCompFunFun G₂).defNat η).η • ((defCompFunFun F₁).defNat ε).η)
                (λ a => (congrArgTrans hγ.Hom (byNatDef a) (byNatDef a) •
                         natTransEq ((defCompFunFun F₁).defNat ε).η ((defRevCompFunFun G₂).defNat η).η a)⁻¹ •
                        naturality ε (nat η a) •
                        (congrArgTrans hγ.Hom (byNatDef a) (byNatDef a) •
                         natTransEq ((defRevCompFunFun G₁).defNat η).η ((defCompFunFun F₂).defNat ε).η a)))

    namespace HasCompFunFun

      variable (α : Sort u) (β : Sort u') (γ : Sort u'') [hα : IsCategory W α]
               [hβ : IsCategory W β] [hγ : IsCategory W γ] [HasFunProp α β] [HasFunProp β γ]
               [HasFunProp α γ] [HasNaturality α β] [HasNaturality β γ] [hNatαγ : HasNaturality α γ]
               [HasFunProp (β ⮕ γ) (α ⮕ γ)] [HasFunProp (α ⮕ β) (α ⮕ γ)]
               [hCompFun : HasCompFun α β γ] [h : HasCompFunFun α β γ]

      def compFunFun    (F : α ⮕ β) : (β ⮕ γ) ⮕ (α ⮕ γ) := DefFunFun.toFunctor (h.defCompFunFun    F)
      def revCompFunFun (G : β ⮕ γ) : (α ⮕ β) ⮕ (α ⮕ γ) := DefFunFun.toFunctor (h.defRevCompFunFun G)

      def mapCompFunNat {F₁ F₂ : α ⮕ β} (η : F₁ ⇾ F₂) :
        Quantification (morFun (compFunFun α β γ F₁)) (morFun (compFunFun α β γ F₂)) :=
      λ G => mapHom (revCompFunFun α β γ G) η

      instance mapCompFunNat.isNat {F₁ F₂ : α ⮕ β} (η : F₁ ⇾ F₂) :
        IsNaturalTransformation (mapCompFunNat α β γ η) :=
      { nat := λ {G₁ G₂} ε =>
               (congrArgTrans hNatαγ.Nat (DefFun.byMapHomDef (desc := DefFunFunBase.funDesc (h.defRevCompFunFun G₁).toDefFunFunBase) byDef)
                                         (DefFun.byMapHomDef (desc := DefFunFunBase.funDesc (h.defCompFunFun F₂).toDefFunFunBase) byDef))⁻¹ •
               (h.compNatEq η ε)⁻¹ •
               congrArgTrans hNatαγ.Nat (DefFun.byMapHomDef (desc := DefFunFunBase.funDesc (h.defCompFunFun F₁).toDefFunFunBase) byDef)
                                        (DefFun.byMapHomDef (desc := DefFunFunBase.funDesc (h.defRevCompFunFun G₂).toDefFunFunBase) byDef) }

      def compFunNatDesc {F₁ F₂ : α ⮕ β} (η : F₁ ⇾ F₂) :
        NatDesc (compFunFun α β γ F₁) (compFunFun α β γ F₂) :=
      { η     := mapCompFunNat       α β γ η,
        isNat := mapCompFunNat.isNat α β γ η }

      def compFunFunFunDesc : FunFunDesc (λ F : α ⮕ β => (h.defCompFunFun F).defFunFun) :=
      { natDesc        := compFunNatDesc α β γ,
        natDescReflEq  := λ F   G => Functor.reflEq  (revCompFunFun α β γ G) F,
        natDescTransEq := λ η ε G => Functor.transEq (revCompFunFun α β γ G) η ε }

    end HasCompFunFun

    class HasCompFunFunFun (α : Sort u) (β : Sort u') (γ : Sort u'') [hα : IsCategory W α]
                           [hβ : IsCategory W β] [hγ : IsCategory W γ] [hFunαβ : HasFunProp α β]
                           [hFunβγ : HasFunProp β γ] [hFunαγ : HasFunProp α γ]
                           [hNatαβ : HasNaturality α β] [hNatβγ : HasNaturality β γ]
                           [hNatαγ : HasNaturality α γ] [hFunβγαγ : HasFunProp (β ⮕ γ) (α ⮕ γ)]
                           [hFunαβαγ : HasFunProp (α ⮕ β) (α ⮕ γ)]
                           [hNatβγαγ : HasNaturality (β ⮕ γ) (α ⮕ γ)]
                           [hFunαββγαγ : HasFunProp (α ⮕ β) ((β ⮕ γ) ⮕ (α ⮕ γ))]
                           [h : HasCompFun α β γ] extends
      HasCompFunFun α β γ where
    (defCompFunFunFun : DefFunFun (HasCompFunFun.compFunFunFunDesc α β γ))

    namespace HasCompFunFunFun

      variable (α : Sort u) (β : Sort u') (γ : Sort u'') [hα : IsCategory W α]
               [hβ : IsCategory W β] [hγ : IsCategory W γ] [HasFunProp α β] [HasFunProp β γ]
               [HasFunProp α γ] [HasNaturality α β] [HasNaturality β γ] [HasNaturality α γ]
               [HasFunProp (β ⮕ γ) (α ⮕ γ)] [HasFunProp (α ⮕ β) (α ⮕ γ)]
               [HasNaturality (β ⮕ γ) (α ⮕ γ)] [HasFunProp (α ⮕ β) ((β ⮕ γ) ⮕ (α ⮕ γ))]
               [HasCompFun α β γ] [h : HasCompFunFunFun α β γ]

      def compFunFunFun : (α ⮕ β) ⮕ (β ⮕ γ) ⮕ (α ⮕ γ) := DefFunFun.toFunctor h.defCompFunFunFun

    end HasCompFunFunFun

    section

      variable [HasSubLinearFunOp W] (α : Sort u) (β : Sort v)
               [hα : IsCategory W α] [hβ : IsCategory W β] [HasFunProp α β] [h : HasConstFun α β]

      def constFun (b : β) : α ⮕ β := DefFun.toFunctor (h.defConstFun b)

      def mapConstNat {b₁ b₂ : β} (g : b₁ ⇾ b₂) :
        Quantification (morFun (constFun α β b₁)) (morFun (constFun α β b₂)) :=
      λ _ => g

      instance mapConstNat.isNat {b₁ b₂ : β} (g : b₁ ⇾ b₂) :
        IsNaturalTransformation (mapConstNat α β g) :=
      { nat := λ _ => (leftId g •
                       congrArgTransLeft hβ.Hom g (DefFun'.byMapHomDef (F := MorphismFunctor.constFun α b₂) byDef))⁻¹ •
                      (rightId g •
                       congrArgTransRight hβ.Hom (DefFun'.byMapHomDef (F := MorphismFunctor.constFun α b₁) byDef) g) }

      def constNatDesc {b₁ b₂ : β} (g : b₁ ⇾ b₂) :
        NatDesc (constFun α β b₁) (constFun α β b₂) :=
      { η     := mapConstNat       α β g,
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

    section

      variable [HasNonLinearFunOp W] {α : Sort u} {β : Sort v}
               [hα : IsCategory W α] [hβ : IsCategory W β] [HasFunProp α β] [h : HasNaturality α β]
               [HasFunProp α (α ⮕ β)] (F : α ⮕ α ⮕ β)

      @[reducible] def dup (a : α) : β := (F.φ a).φ a

      @[reducible] def mapDupHom {a₁ a₂ : α} (f : a₁ ⇾ a₂) : dup F a₁ ⇾ dup F a₂ :=
      mapHom (F.φ a₂) f • nat (mapHom F f) a₁

      @[reducible] def mapDupHom' {a₁ a₂ : α} (f : a₁ ⇾ a₂) : dup F a₁ ⇾ dup F a₂ :=
      nat (mapHom F f) a₂ • mapHom (F.φ a₁) f

      def mapDupHomEq {a₁ a₂ : α} (f : a₁ ⇾ a₂) : mapDupHom' F f ≃ mapDupHom F f :=
      naturality (mapHom F f) f

      def mapDupHomArg (a₁ a₂ : α) :
        (a₁ ⇾ a₂) ⟶ ((F.φ a₂).φ a₁ ⇾ dup F a₂) ⟶ (dup F a₁ ⇾ dup F a₂) :=
      transFunFun hβ.Hom (dup F a₁) ((F.φ a₂).φ a₁) (dup F a₂) •
      natFun (F.φ a₁) (F.φ a₂) a₁ •
      (preFun F).baseFun a₁ a₂

      def mapDupHomFun (a₁ a₂ : α) : (a₁ ⇾ a₂) ⟶ (dup F a₁ ⇾ dup F a₂) :=
      substFun ((preFun (F.φ a₂)).baseFun a₁ a₂) (mapDupHomArg F a₁ a₂)

      def mapDupHomArgDef {a₁ a₂ : α} (f : a₁ ⇾ a₂) :
        (mapDupHomArg F a₁ a₂) f ≃ transFun hβ.Hom (nat (mapHom F f) a₁) (dup F a₂) :=
      byDefDef • byArgDef • byDef

      def mapDupHomFunDef {a₁ a₂ : α} (f : a₁ ⇾ a₂) : (mapDupHomFun F a₁ a₂) f ≃ mapDupHom F f :=
      byDef • congrFun (mapDupHomArgDef F f) (mapHom (F.φ a₂) f) • byDef

      instance : IsCategoryFunctor ⟨⟨mapDupHomFun F⟩⟩ :=
      { reflEq  := λ a =>
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
                                            (naturality (mapHom F g) f)⁻¹ •
                                assoc (nat (mapHom F g) a₁)
                                      (mapHom (F.φ a₃) f)
                                      (mapHom (F.φ a₃) g)) •
                   (assoc (nat (mapHom F f) a₁) (nat (mapHom F g) a₁)
                          (mapHom (F.φ a₃) g • mapHom (F.φ a₃) f))⁻¹ •
                   congrArgTrans hβ.Hom (natTransEq (mapHom F f) (mapHom F g) a₁ •
                                         natCongrArg (Functor.transEq F f g) a₁)
                                        (Functor.transEq (F.φ a₃) f g) •
                   mapDupHomFunDef F (g • f) }

      def dupFunDesc : FunDesc (dup F) := ⟨⟨mapDupHomFun F⟩⟩

    end

    class HasDupFun [HasNonLinearFunOp W] (α : Sort u) (β : Sort v)
                    [hα : IsCategory W α] [hβ : IsCategory W β] [hFunαβ : HasFunProp α β]
                    [hNatαβ : HasNaturality α β] [hFunααβ : HasFunProp α (α ⮕ β)] where
    (defDupFun (F : α ⮕ α ⮕ β) : HasFunProp.DefFun (dupFunDesc F))

    namespace HasDupFun

      variable [HasNonLinearFunOp W] (α : Sort u) (β : Sort v)
               [hα : IsCategory W α] [hβ : IsCategory W β] [HasFunProp α β]
               [HasNaturality α β] [HasFunProp α (α ⮕ β)] [h : HasDupFun α β]

      def dupFun (F : α ⮕ α ⮕ β) : α ⮕ β := DefFun.toFunctor (h.defDupFun F)

      variable [HasNaturality α (α ⮕ β)]

      def mapDupNat {F₁ F₂ : α ⮕ α ⮕ β} (η : F₁ ⇾ F₂) :
        Quantification (morFun (dupFun α β F₁)) (morFun (dupFun α β F₂)) :=
      λ a => nat (nat η a) a

      instance mapDupNat.isNat {F₁ F₂ : α ⮕ α ⮕ β} (η : F₁ ⇾ F₂) :
        IsNaturalTransformation (mapDupNat α β η) :=
      { nat := λ {a₁ a₂} f =>
               congrArgTransLeft hβ.Hom (mapDupNat α β η a₁)
                                        (DefFun.byMapHomDef (desc := dupFunDesc F₂) (mapDupHomFunDef F₂ f))⁻¹ •
               (assoc (mapDupNat α β η a₁) (nat (mapHom F₂ f) a₁) (mapHom (F₂.φ a₂) f))⁻¹ •
               congrArgTransRight hβ.Hom (natTransEq (nat η a₁) (mapHom F₂ f) a₁ •
                                          natCongrArg (naturality η f) a₁ •
                                          (natTransEq (mapHom F₁ f) (nat η a₂) a₁)⁻¹)
                                         (mapHom (F₂.φ a₂) f) •
               assoc (nat (mapHom F₁ f) a₁) (nat (nat η a₂) a₁) (mapHom (F₂.φ a₂) f) •
               congrArgTransLeft hβ.Hom (nat (mapHom F₁ f) a₁)
                                        (naturality (nat η a₂) f) •
               (assoc (nat (mapHom F₁ f) a₁) (mapHom (F₁.φ a₂) f) (mapDupNat α β η a₂))⁻¹ •
               congrArgTransRight hβ.Hom (DefFun.byMapHomDef (desc := dupFunDesc F₁) (mapDupHomFunDef F₁ f))
                                         (mapDupNat α β η a₂) }

      def dupNatDesc {F₁ F₂ : α ⮕ α ⮕ β} (η : F₁ ⇾ F₂) :
        NatDesc (dupFun α β F₁) (dupFun α β F₂) :=
      { η     := mapDupNat       α β η,
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
    [hasCompFunFunFun (α β γ : Sort max 1 u w) [hα : IsCategory W α] [hβ : IsCategory W β]
                      [hγ : IsCategory W γ] :
       HasNaturality.HasCompFunFunFun α β γ]

    namespace HasLinearFunctors

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
               [IsFunUniverse.{u} W] [IsFunUniverse.HasLinearFunctors W] [IsNatUniverse.{u} W]
               [h : HasLinearFunctors W]

      instance (α β : Sort (max 1 u w)) [hα : IsCategory W α] [hβ : IsCategory W β] :
        HasNaturality.HasRevAppFunFun α β :=
      h.hasRevAppFunFun α β

      instance (α β γ : Sort max 1 u w) [hα : IsCategory W α] [hβ : IsCategory W β]
               [hγ : IsCategory W γ] :
        HasNaturality.HasCompFunFunFun α β γ :=
      h.hasCompFunFunFun α β γ

      def revAppFun {α : Sort (max 1 u w)} (a : α) (β : Sort (max 1 u w))
                    [hα : IsCategory W α] [hβ : IsCategory W β] :
        (α ⮕ β) ⮕ β :=
      HasNaturality.HasRevAppFun.revAppFun α β a

      def revAppFunFun (α β : Sort max 1 u w) [hα : IsCategory W α] [hβ : IsCategory W β] :
        α ⮕ (α ⮕ β) ⮕ β :=
      HasNaturality.HasRevAppFunFun.revAppFunFun α β

      def compFunFun {α β : Sort (max 1 u w)} [hα : IsCategory W α] [hβ : IsCategory W β]
                     (F : α ⮕ β) (γ : Sort max 1 u w) [hγ : IsCategory W γ] :
        (β ⮕ γ) ⮕ (α ⮕ γ) :=
      HasNaturality.HasCompFunFun.compFunFun α β γ F

      def revCompFunFun (α : Sort (max 1 u w)) {β γ : Sort (max 1 u w)} [hα : IsCategory W α]
                        [hβ : IsCategory W β] [hγ : IsCategory W γ] (G : β ⮕ γ) :
        (α ⮕ β) ⮕ (α ⮕ γ) :=
      HasNaturality.HasCompFunFun.revCompFunFun α β γ G

      def compFunFunFun (α β γ : Sort max 1 u w) [hα : IsCategory W α] [hβ : IsCategory W β]
                        [hγ : IsCategory W γ] :
        (α ⮕ β) ⮕ (β ⮕ γ) ⮕ (α ⮕ γ) :=
      HasNaturality.HasCompFunFunFun.compFunFunFun α β γ

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
