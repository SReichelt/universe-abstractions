import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.MetaProperties
import UniverseAbstractions.Axioms.MetaRelations
import UniverseAbstractions.Axioms.CategoryTheory.Meta
import UniverseAbstractions.Axioms.CategoryTheory.Basic



set_option autoBoundImplicitLocal false
set_option synthInstance.maxHeartbeats 1000
--set_option pp.universes true

universe u u' u'' v w iv iw



-- Here, we define three typeclasses `IsIsoUniverse`, `IsFunUniverse`, and  `IsNatUniverse`,
-- that a universe of morphisms should satisfy. They let us obtain certain category-theoretic
-- structure that depends on the specific morphism universe, e.g. it may require additional
-- coherence conditions for higher categories.
--
-- In particular,
-- * `IsIsoUniverse` defines a second meta-relation `Iso` for categories, in addition to `Hom`.
--   `Iso` is required to form a groupoid and to imply `Hom`.
-- * `IsFunUniverse` defines a condition for functoriality, which must imply the conditions
--   defined by `IsCategoryFunctor` and also `IsGroupoidFunctor` for isomorphisms, with
--   coherence conditions.
-- * `IsNatUniverse` defines an analogous condition for naturality.

namespace CategoryTheory

  open MetaRelation MetaFunctor MetaQuantification HasTransFun HasSymmFun IsAssociative
       IsCategoricalPreorder IsGroupoidEquivalence IsCategory IsSymmFunctor IsTransFunctor
       HasFunctors HasCongrArg HasLinearFunOp

  namespace IsCategory

    class IsIsoRel {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasLinearFunctors V]
                   {α : Sort u} [hCat : IsCategory V α] (Iso : MetaRelation α V) where
    [isoIsEquivalence                     : IsEquivalence Iso]
    [isoInv {a b : α} (e : Iso a b)       : IsInv Iso e e⁻¹]
    [isoHasSymmFun                        : HasSymmFun Iso]
    [isoHasTransFun                       : HasTransFun Iso]
    (toHomMetaFunctor                     : MetaFunctor Iso hCat.Hom)
    [toHomIsPreorderFunctor               : IsPreorderFunctor toHomMetaFunctor]
    (toHomInj {a b : α} {e₁ e₂ : Iso a b} : toHomMetaFunctor e₁ ≃ toHomMetaFunctor e₂ → e₁ ≃ e₂)

    namespace IsIsoRel

      variable {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasLinearFunctors V]
               {α : Sort u} [hCat : IsCategory V α] (Iso : MetaRelation α V) [h : IsIsoRel Iso]

      instance : IsEquivalence Iso := h.isoIsEquivalence
      instance : HasSymmFun    Iso := h.isoHasSymmFun
      instance : HasTransFun   Iso := h.isoHasTransFun

      instance : IsPreorderFunctor h.toHomMetaFunctor := h.toHomIsPreorderFunctor

    end IsIsoRel

    class HasIsoRel {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasLinearFunctors V]
                    (α : Sort u) [hCat : IsCategory V α] where
    (Iso      : MetaRelation α V)
    [isIsoRel : IsIsoRel Iso]

    namespace HasIsoRel

      open IsIsoRel

      infix:20 " ⇿ " => CategoryTheory.IsCategory.HasIsoRel.Iso

      def isoMorphisms {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasLinearFunctors V]
                       (α : Sort u) [hCat : IsCategory V α] [h : HasIsoRel α] :
        HasMorphisms V α :=
      { Hom := h.Iso }

      section

        variable {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasLinearFunctors V] {α : Sort u}
                 [hCat : IsCategory V α] [h : HasIsoRel α]

        instance : IsIsoRel h.Iso := h.isIsoRel

        def idIso (a : α) : a ⇿ a := HasRefl.refl a

        def toHom  {a b : α} (e : a ⇿ b) : a ⇾ b := toHomMetaFunctor e
        def invHom {a b : α} (e : a ⇿ b) : b ⇾ a := toHom e⁻¹

        def isoAssoc {a b c d : α} (e : a ⇿ b) (f : b ⇿ c) (g : c ⇿ d) :
          (g • f) • e ≃ g • (f • e) :=
        toHomInj ((congrArgTransRight hCat.Hom (toHomIsPreorderFunctor.transEq e f) (toHom g) •
                   toHomIsPreorderFunctor.transEq (f • e) g)⁻¹ •
                  assoc (toHom e) (toHom f) (toHom g) •
                  (congrArgTransLeft hCat.Hom (toHom e) (toHomIsPreorderFunctor.transEq f g) •
                   toHomIsPreorderFunctor.transEq e (g • f)))

        def isoRightId {a b : α} (e : a ⇿ b) : e • idIso a ≃ e :=
        toHomInj (rightId (toHom e) •
                  (congrArgTransRight hCat.Hom (toHomIsPreorderFunctor.reflEq a) (toHom e) •
                   toHomIsPreorderFunctor.transEq (idIso a) e))

        def isoLeftId {a b : α} (e : a ⇿ b) : idIso b • e ≃ e :=
        toHomInj (leftId (toHom e) •
                  (congrArgTransLeft hCat.Hom (toHom e) (toHomIsPreorderFunctor.reflEq b) •
                   toHomIsPreorderFunctor.transEq e (idIso b)))

        def isoLeftInv  {a b : α} (e : a ⇿ b) : e⁻¹ • e ≃ idIso a := (isoInv e).leftInv
        def isoRightInv {a b : α} (e : a ⇿ b) : e • e⁻¹ ≃ idIso b := (isoInv e).rightInv

        instance isoIsGroupoidEquivalence : IsGroupoidEquivalence h.Iso :=
        { assoc    := isoAssoc,
          rightId  := isoRightId,
          leftId   := isoLeftId,
          leftInv  := isoLeftInv,
          rightInv := isoRightInv }

      end

      class HasIsoRelExt {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasStandardFunctors V]
                         (α : Sort u) [IsCategory V α] [hIso : HasIsoRel α] where
      [toHomIsTransFunctorExt      : IsTransFunctor.IsTransFunctorExt hIso.isIsoRel.toHomMetaFunctor]
      [isoIsGroupoidEquivalenceExt : IsGroupoidEquivalenceExt hIso.Iso]

      namespace HasIsoRelExt

        variable {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasStandardFunctors V] (α : Sort u)
                 [IsCategory V α] [hIso : HasIsoRel α] [h : HasIsoRelExt α]

        instance : IsTransFunctor.IsTransFunctorExt hIso.isIsoRel.toHomMetaFunctor := h.toHomIsTransFunctorExt

        instance : IsGroupoidEquivalenceExt hIso.Iso := h.isoIsGroupoidEquivalenceExt

      end HasIsoRelExt

    end HasIsoRel

    class HasIsomorphisms {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasStandardFunctors V]
                          (α : Sort u) [IsCategory V α] where
    [hasIsoRel    : HasIsoRel              α]
    [hasIsoRelExt : HasIsoRel.HasIsoRelExt α]

    namespace HasIsomorphisms

      variable {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasStandardFunctors V]
               (α : Sort u) [IsCategory V α] [h : HasIsomorphisms α]

      instance : HasIsoRel              α := h.hasIsoRel
      instance : HasIsoRel.HasIsoRelExt α := h.hasIsoRelExt

      def isoGroupoid : IsGroupoid V α :=
      { toHasMorphisms              := HasIsoRel.isoMorphisms α,
        homIsEquivalence            := h.hasIsoRel.isIsoRel.isoIsEquivalence,
        homHasSymmFun               := h.hasIsoRel.isIsoRel.isoHasSymmFun,
        homHasTransFun              := h.hasIsoRel.isIsoRel.isoHasTransFun,
        homIsGroupoidEquivalence    := HasIsoRel.isoIsGroupoidEquivalence,
        homIsGroupoidEquivalenceExt := h.hasIsoRelExt.isoIsGroupoidEquivalenceExt }

    end HasIsomorphisms

  end IsCategory



  namespace IsGroupoid

    open HasIsoRel

    variable {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasStandardFunctors V] (α : Sort u)
             [hGrp : IsGroupoid V α]

    instance isIsoRel : IsIsoRel hGrp.Hom :=
    { isoIsEquivalence       := hGrp.homIsEquivalence,
      isoInv                 := isInv hGrp.Hom,
      isoHasSymmFun          := hGrp.homHasSymmFun,
      isoHasTransFun         := hGrp.homHasTransFun,
      toHomMetaFunctor       := idFun.metaFunctor hGrp.Hom,
      toHomIsPreorderFunctor := idFun.isPreorderFunctor hGrp.Hom,
      toHomInj               := λ h => byDef • h • byDef⁻¹ }

    instance hasIsoRel : HasIsoRel α := ⟨hGrp.Hom⟩

    instance hasIsoRelExt : HasIsoRelExt α :=
    { toHomIsTransFunctorExt      := idFun.isTransFunctorExt hGrp.Hom,
      isoIsGroupoidEquivalenceExt := IsGroupoidEquivalenceExt.translate hGrp.Hom }

    instance hasIsomorphisms : HasIsomorphisms α := ⟨⟩

  end IsGroupoid



  class IsIsoUniverse (V : Universe.{v}) [HasIdentity.{v, iv} V] [HasStandardFunctors V] where
  [hasIsomorphisms    (α : Sort u) [IsCategory V α] : HasIsomorphisms α]

  namespace IsIsoUniverse

    variable {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasStandardFunctors V]
             [h : IsIsoUniverse V]

    instance (α : Sort u) [IsCategory V α] : HasIsomorphisms α := h.hasIsomorphisms α

  end IsIsoUniverse



  class IsIsoFunctor {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]
                     {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
                     [hαIso : HasIsomorphisms α] [hβIso : HasIsomorphisms β]
                     (φ : α → β) extends
    IsGroupoidFunctor φ (hα := HasIsomorphisms.isoGroupoid α)
                        (hβ := HasIsomorphisms.isoGroupoid β)

  namespace IsIsoFunctor

    variable {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]

    section

      variable {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
               [hαIso : HasIsomorphisms α] [hβIso : HasIsomorphisms β]
               (φ : α → β) [h : IsIsoFunctor φ]

      def isMorphismFunctor : IsMorphismFunctor φ (hα := HasIsoRel.isoMorphisms α)
                                                  (hβ := HasIsoRel.isoMorphisms β) :=
      h.toIsMorphismFunctor (hα := HasIsomorphisms.isoGroupoid α)
                            (hβ := HasIsomorphisms.isoGroupoid β)

      def preFunctor : PreFunctor hαIso.hasIsoRel.Iso hβIso.hasIsoRel.Iso φ :=
      (isMorphismFunctor φ).F (hα := HasIsoRel.isoMorphisms α) (hβ := HasIsoRel.isoMorphisms β)

    end

    instance idFun (α : Sort u) [hα : IsCategory W α] [HasIsomorphisms α] :
      IsIsoFunctor (@id α) :=
    { toIsGroupoidFunctor := IsGroupoidFunctor.idFun α (hα := HasIsomorphisms.isoGroupoid α) }

    instance constFun (α : Sort u) {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
                      [HasIsomorphisms α] [HasIsomorphisms β] (b : β) :
      IsIsoFunctor (Function.const α b) :=
    { toIsGroupoidFunctor := IsGroupoidFunctor.constFun α b (hα := HasIsomorphisms.isoGroupoid α)
                                                            (hβ := HasIsomorphisms.isoGroupoid β) }

    instance compFun {α : Sort u} {β : Sort u'} {γ : Sort u''}
                     [hα : IsCategory W α] [hβ : IsCategory W β] [hγ : IsCategory W γ]
                     [HasIsomorphisms α] [HasIsomorphisms β] [HasIsomorphisms γ]
                     (φ : α → β) (ψ : β → γ)
                     [hφ : IsIsoFunctor φ] [hψ : IsIsoFunctor ψ] :
      IsIsoFunctor (ψ ∘ φ) :=
    { toIsGroupoidFunctor := IsGroupoidFunctor.compFun φ ψ (hα := HasIsomorphisms.isoGroupoid α)
                                                           (hβ := HasIsomorphisms.isoGroupoid β)
                                                           (hγ := HasIsomorphisms.isoGroupoid γ) }

  end IsIsoFunctor

  class IsHomIsoFun {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]
                    {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
                    [hαIso : HasIsomorphisms α] [hβIso : HasIsomorphisms β] (φ : α → β) where
  [isHomFun : IsCategoryFunctor φ]
  [isIsoFun : IsIsoFunctor      φ] 
  (isoFunEq {a b : α} (e : a ⇿ b) :
     hβIso.hasIsoRel.isIsoRel.toHomMetaFunctor ((IsIsoFunctor.preFunctor φ) e) ≃
     isHomFun.F (hαIso.hasIsoRel.isIsoRel.toHomMetaFunctor e))
  (isoFunEqExt (a b : α) :
     hβIso.hasIsoRel.isIsoRel.toHomMetaFunctor.baseFun (φ a) (φ b) • (IsIsoFunctor.preFunctor φ).baseFun a b
     ≃{▻ λ e => isoFunEq e ◅}
     isHomFun.F.baseFun a b • hαIso.hasIsoRel.isIsoRel.toHomMetaFunctor.baseFun a b)

  namespace IsHomIsoFun

    variable {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]
             {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
             [HasIsomorphisms α] [HasIsomorphisms β] (φ : α → β) [h : IsHomIsoFun φ]

    instance : IsCategoryFunctor φ := h.isHomFun
    instance : IsIsoFunctor      φ := h.isIsoFun

  end IsHomIsoFun

  class HasFunctorialityProperty {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]
                                 (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
                                 [hαIso : HasIsomorphisms α] [hβIso : HasIsomorphisms β] where
  (Fun : FunctorialityProperty α β W)
  [isHomIsoFun {φ : α → β} : Fun φ → IsHomIsoFun φ]

  namespace HasFunctorialityProperty

    variable {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]

    def Functor (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
                [HasIsomorphisms α] [HasIsomorphisms β]
                [h : HasFunctorialityProperty α β] :=
    BundledFunctor h.Fun

    namespace Functor

      variable {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
               [HasIsomorphisms α] [HasIsomorphisms β]
               [h : HasFunctorialityProperty α β] (F : Functor α β)

      instance : IsHomIsoFun F.f := h.isHomIsoFun F.isFun

    end Functor

    variable {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
             [HasIsomorphisms α] [HasIsomorphisms β]
             [h : HasFunctorialityProperty α β]

    instance {φ : α → β} (isFun : h.Fun φ) : IsHomIsoFun φ := h.isHomIsoFun isFun

    structure DefFun (φ : α → β) [isHomFun : IsCategoryFunctor φ] [isIsoFun : IsIsoFunctor φ] where
    (isFun : h.Fun φ)
    (homFunEq {a b : α} (f : a ⇾ b) : (h.isHomIsoFun isFun).isHomFun.F f ≃ isHomFun.F f)
    (homFunEqExt (a b : α) :
       (h.isHomIsoFun isFun).isHomFun.F.baseFun a b ≃{λ f => homFunEq f} isHomFun.F.baseFun a b)
    (isoFunEq {a b : α} (e : a ⇿ b) :
       (IsIsoFunctor.preFunctor φ (h := (h.isHomIsoFun isFun).isIsoFun)) e ≃
       (IsIsoFunctor.preFunctor φ (h := isIsoFun)) e)
    (isoFunEqExt (a b : α) :
       (IsIsoFunctor.preFunctor φ (h := (h.isHomIsoFun isFun).isIsoFun)).baseFun a b
       ≃{λ e => isoFunEq e}
       (IsIsoFunctor.preFunctor φ (h := isIsoFun)).baseFun a b)

    namespace DefFun

      def toFunctor {φ : α → β} [IsCategoryFunctor φ] [IsIsoFunctor φ] (F : DefFun φ) :
        Functor α β :=
      ⟨F.isFun⟩

    end DefFun

  end HasFunctorialityProperty

  class IsFunUniverse (W : Universe.{w}) [HasIdentity.{w, iw} W] [HasStandardFunctors W]
                      [hIsoUniv : IsIsoUniverse W] where
  [hasFunProp (α β : Sort u) [IsCategory W α] [IsCategory W β] : HasFunctorialityProperty α β]
  (defIdFun (α : Sort u) [IsCategory W α] : HasFunctorialityProperty.DefFun (@id α))
  (defConstFun (α : Sort u) {β : Sort u} [IsCategory W α] [IsCategory W β] (b : β) :
     HasFunctorialityProperty.DefFun (Function.const α b))
  (defCompFun {α β γ : Sort u} [IsCategory W α] [IsCategory W β] [IsCategory W γ]
              (F : HasFunctorialityProperty.Functor α β) (G : HasFunctorialityProperty.Functor β γ) :
     HasFunctorialityProperty.DefFun (G.f ∘ F.f))

  namespace IsFunUniverse

    open HasFunctorialityProperty

    variable {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W] [IsIsoUniverse W]
             [h : IsFunUniverse W]

    instance (α β : Sort u) [IsCategory W α] [IsCategory W β] : HasFunctorialityProperty α β :=
    h.hasFunProp α β

    def idFun (α : Sort u) [IsCategory W α] : Functor α α := DefFun.toFunctor (h.defIdFun α)

    def constFun (α : Sort u) {β : Sort u} [IsCategory W α] [IsCategory W β] (b : β) :
      Functor α β :=
    DefFun.toFunctor (h.defConstFun α b)

    def compFun {α β γ : Sort u} [IsCategory W α] [IsCategory W β] [IsCategory W γ]
                (F : Functor α β) (G : Functor β γ) :
      Functor α γ :=
    DefFun.toFunctor (h.defCompFun F G)

  end IsFunUniverse



  structure NatDesc {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]
                    {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
                    [hαIso : HasIsomorphisms α] [hβIso : HasIsomorphisms β]
                    (φ ψ : α → β) [IsMorphismFunctor φ] [IsMorphismFunctor ψ] where
  (η     : MetaQuantification hβ.Hom φ ψ)
  [isNat : IsNaturalTransformation η]

  class HasNaturalityRelation {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]
                              [hIsoUniv : IsIsoUniverse W] [hFunUniv : IsFunUniverse W]
                              (α β : Sort u) [hα : IsCategory W α] [hβ : IsCategory W β] where
  (Nat : NaturalityRelation (hFunUniv.hasFunProp α β).Fun)
  (desc {F G : HasFunctorialityProperty.Functor α β} (η : Nat F G) : NatDesc F.f G.f)
  -- TODO: Incorporate naturality proofs, as with `IsExtensional`.
  [natIsPreorder               : IsPreorder                                     Nat]
  [natHasTransFun              : HasTransFun                                    Nat]
  [natIsCategoricalPreorder    : IsCategoricalPreorder                          Nat]
  [natIsCategoricalPreorderExt : IsCategoricalPreorder.IsCategoricalPreorderExt Nat]

  namespace HasNaturalityRelation

    variable {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]
             [IsIsoUniverse W] [IsFunUniverse W]

    variable (α β : Sort u) [hα : IsCategory W α] [hβ : IsCategory W β]
             [h : HasNaturalityRelation α β]

    instance funHasMorphisms : HasMorphisms W (HasFunctorialityProperty.Functor α β) := ⟨h.Nat⟩

    instance funIsCategory : IsCategory W (HasFunctorialityProperty.Functor α β) :=
    { homIsPreorder               := h.natIsPreorder,
      homHasTransFun              := h.natHasTransFun,
      homIsCategoricalPreorder    := h.natIsCategoricalPreorder,
      homIsCategoricalPreorderExt := h.natIsCategoricalPreorderExt }

  end HasNaturalityRelation

  class IsNatUniverse (W : Universe.{w}) [HasIdentity.{w, iw} W] [HasStandardFunctors W]
                      [hIsoUniv : IsIsoUniverse W] [hFunUniv : IsFunUniverse W] where
  [hasNaturalityRelation (α β : Sort u) [hα : IsCategory W α] [hβ : IsCategory W β] :
     HasNaturalityRelation α β]

  namespace IsNatUniverse

    variable (W : Universe.{w}) [HasIdentity.{w, iw} W] [HasStandardFunctors W]
             [hIsoUniv : IsIsoUniverse W] [hFunUniv : IsFunUniverse W] [h : IsNatUniverse W]

    instance (α β : Sort u) [hα : IsCategory W α] [hβ : IsCategory W β] :
      HasNaturalityRelation α β :=
    h.hasNaturalityRelation α β

  end IsNatUniverse

end CategoryTheory
