import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.MetaRelations
import UniverseAbstractions.Axioms.MetaProperties
import UniverseAbstractions.Axioms.CategoryTheory.Meta
import UniverseAbstractions.Axioms.CategoryTheory.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w iv iw



-- TODO: Adapt

-- We define a category to be a precategory that is additionally enriched with isomorphisms.
-- Like morphisms, they are also in `M`, and they need to map injectively to `IsoDesc` but may be
-- subject to further conditions beyond `IsoDesc`.
--
-- In other words, a category has an embedded groupoid that may be smaller than the "potential"
-- isomorphisms given by `IsoDesc`, in fact it only needs to contain `refl`. Therefore, one might
-- wonder what the point of `IsCategory` is, compared to either `IsPreCategory` for the entire
-- category or `IsGroupoid` for its isomorphisms. The answer is that it provides exactly the
-- right amount of information to build a universe of categories that has good properties:
-- * `IsPreCategory` lacks a good notion of identity, as the additional constraints beyond
--   `IsoDesc` may be required to define it (and also because `IsoDesc.univ` depends on `α`).
-- * `IsGroupoid` works (and of course `IsCategory` can be trivially derived from `IsGroupoid`),
--   but we do not want to restrict ourselves to isomorphisms completely.
--
-- So this combined definition is essentially just a convenient way of working with both a
-- category and its embedded groupoid at the same time, so everything can be stated once in full
-- generality.
--
-- The definition is split into several parts because some parts are trivial in simple
-- categories, and to reduce redundancies in nontrivial parts. In particular, the groupoid laws
-- of isomorphisms follow from injectivity and functoriality of `isoDesc`; however the
-- extensionality of these laws needs to be specified separately. (Note that instead of mapping
-- to `IsoDesc`, we could also just map to `Hom`, but then only the category laws would follow
-- in this way, and the other laws would need to be added explicitly -- which is essentially the
-- same as mapping to `IsoDesc`.)

namespace CategoryTheory

  open MetaRelation MetaFunctor MetaQuantification HasTransFun HasSymmFun IsAssociative
       IsCategoricalPreorder IsGroupoidEquivalence IsCategory IsSymmFunctor IsTransFunctor
       HasFunctors HasCongrArg HasLinearFunOp

  namespace IsCategory

    -- TODO: Unbundle (`IsIsoRel`)

    class HasIsomorphisms {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasLinearFunctors V]
                          (α : Sort u) [hCat : IsCategory V α] where
    (Iso                                  : MetaRelation α V)
    [isoIsEquivalence                     : IsEquivalence Iso]
    [isoInv {a b : α} (e : Iso a b)       : IsInv Iso e e⁻¹]
    [isoHasSymmFun                        : HasSymmFun Iso]
    [isoHasTransFun                       : HasTransFun Iso]
    (toHomMetaFunctor                     : MetaFunctor Iso hCat.Hom)
    [toHomIsPreorderFunctor               : IsPreorderFunctor toHomMetaFunctor]
    (toHomInj {a b : α} {e₁ e₂ : Iso a b} : toHomMetaFunctor e₁ ≃ toHomMetaFunctor e₂ → e₁ ≃ e₂)

    namespace HasIsomorphisms

      infix:20 " ⇿ " => CategoryTheory.IsCategory.HasIsomorphisms.Iso

      def isoMorphisms {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasLinearFunctors V]
                       (α : Sort u) [hCat : IsCategory V α] [h : HasIsomorphisms α] :
        HasMorphisms V α :=
      { Hom := h.Iso }

      section

        variable {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasLinearFunctors V] {α : Sort u}
                 [hCat : IsCategory V α] [h : HasIsomorphisms α]

        instance : IsEquivalence h.Iso := h.isoIsEquivalence
        instance : HasSymmFun    h.Iso := h.isoHasSymmFun
        instance : HasTransFun   h.Iso := h.isoHasTransFun

        instance : IsPreorderFunctor h.toHomMetaFunctor := h.toHomIsPreorderFunctor

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

        def isoLeftInv  {a b : α} (e : a ⇿ b) : e⁻¹ • e ≃ idIso a := (h.isoInv e).leftInv
        def isoRightInv {a b : α} (e : a ⇿ b) : e • e⁻¹ ≃ idIso b := (h.isoInv e).rightInv

        instance isoIsGroupoidEquivalence : IsGroupoidEquivalence h.Iso :=
        { assoc    := isoAssoc,
          rightId  := isoRightId,
          leftId   := isoLeftId,
          leftInv  := isoLeftInv,
          rightInv := isoRightInv }

      end

      class HasIsomorphismsExt {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasStandardFunctors V]
                               (α : Sort u) [IsCategory V α] [hIso : HasIsomorphisms α] where
      [toHomIsTransFunctorExt      : IsTransFunctor.IsTransFunctorExt hIso.toHomMetaFunctor]
      [isoIsGroupoidEquivalenceExt : IsGroupoidEquivalenceExt hIso.Iso]

      namespace HasIsomorphismsExt

        variable {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasStandardFunctors V] (α : Sort u)
                 [IsCategory V α] [hIso : HasIsomorphisms α] [h : HasIsomorphismsExt α]

        instance : IsTransFunctor.IsTransFunctorExt hIso.toHomMetaFunctor := h.toHomIsTransFunctorExt

        instance : IsGroupoidEquivalenceExt hIso.Iso := h.isoIsGroupoidEquivalenceExt

        def isoGroupoid : IsGroupoid V α :=
        { toHasMorphisms              := isoMorphisms α,
          homIsEquivalence            := hIso.isoIsEquivalence,
          homHasSymmFun               := hIso.isoHasSymmFun,
          homHasTransFun              := hIso.isoHasTransFun,
          homIsGroupoidEquivalence    := isoIsGroupoidEquivalence,
          homIsGroupoidEquivalenceExt := h.isoIsGroupoidEquivalenceExt }

      end HasIsomorphismsExt

    end HasIsomorphisms

  end IsCategory



  namespace IsGroupoid

    open HasIsomorphisms

    variable {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasStandardFunctors V] (α : Sort u)
             [hGrp : IsGroupoid V α]

    instance hasIsomorphisms : HasIsomorphisms α :=
    { Iso                    := hGrp.Hom,
      isoIsEquivalence       := hGrp.homIsEquivalence,
      isoInv                 := isInv hGrp.Hom,
      isoHasSymmFun          := hGrp.homHasSymmFun,
      isoHasTransFun         := hGrp.homHasTransFun,
      toHomMetaFunctor       := idFun.metaFunctor hGrp.Hom,
      toHomIsPreorderFunctor := idFun.isPreorderFunctor hGrp.Hom,
      toHomInj               := λ h => byDef • h • byDef⁻¹ }

    instance hasIsomorphismsExt : HasIsomorphismsExt α :=
    { toHomIsTransFunctorExt      := idFun.isTransFunctorExt hGrp.Hom,
      isoIsGroupoidEquivalenceExt := IsGroupoidEquivalenceExt.translate hGrp.Hom }

  end IsGroupoid



  class IsIsoUniverse (V : Universe.{v}) [HasIdentity.{v, iv} V] [HasLinearFunctors V] where
  [hasIsomorphisms (α : Sort u) [IsCategory V α] : HasIsomorphisms α]

  namespace IsIsoUniverse

    section

      variable {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasLinearFunctors V]
               [h : IsIsoUniverse V]

      instance (α : Sort u) [IsCategory V α] : HasIsomorphisms α := h.hasIsomorphisms α

    end

    class IsIsoExtUniverse (V : Universe.{v}) [HasIdentity.{v, iv} V] [HasStandardFunctors V]
                           [hIsoUniv : IsIsoUniverse V] where
    [hasIsomorphismsExt (α : Sort u) [IsCategory V α] :
       HasIsomorphisms.HasIsomorphismsExt α (hIso := hIsoUniv.hasIsomorphisms α)]

    namespace IsIsoExtUniverse

      open HasIsomorphisms

      variable {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasStandardFunctors V]
               [IsIsoUniverse V] [h : IsIsoExtUniverse V]

      instance (α : Sort u) [IsCategory V α] : HasIsomorphismsExt α := h.hasIsomorphismsExt α

    end IsIsoExtUniverse

  end IsIsoUniverse



  structure BundledFunctor {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasInternalFunctors W]
                           {α : Sort u} {β : Sort v} (Fun : MetaProperty (α → β) W) where
  {φ : α → β}
  (F : Fun φ)

  class IsFunProp {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasInternalFunctors W]
                  {α : Sort u} {β : Sort v} (R : MetaRelation α W) (S : MetaRelation β W)
                  (Fun : MetaProperty (α → β) W) where
  (preFunctor (F : BundledFunctor Fun) : PreFunctor R S F.φ)

  namespace HasMorphisms

    class HasMorphismFunctors {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasInternalFunctors W]
                              (α : Sort u) (β : Sort v)
                              [hα : HasMorphisms W α] [hβ : HasMorphisms W β] where
    (Fun       : MetaProperty (α → β) W)
    [isFunProp : IsFunProp hα.Hom hβ.Hom Fun]

    namespace HasMorphismFunctors

      variable {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasInternalFunctors W]
               {α : Sort u} {β : Sort v} [hα : HasMorphisms W α] [hβ : HasMorphisms W β]
               [h : HasMorphismFunctors α β]

      instance isMorphismFunctor (F : BundledFunctor h.Fun) : IsMorphismFunctor F.φ :=
      { F := h.isFunProp.preFunctor F }

    end HasMorphismFunctors

  end HasMorphisms

  namespace IsSemicategory

    open HasMorphisms

    class HasSemicategoryFunctors {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasLinearFunctors W]
                                  (α : Sort u) (β : Sort v)
                                  [hα : IsSemicategory W α] [hβ : IsSemicategory W β] extends
      HasMorphismFunctors α β where
    [isTransFunctor    (F : BundledFunctor Fun) : IsTransFunctor    (isFunProp.preFunctor F)]
    [isTransFunctorExt (F : BundledFunctor Fun) : IsTransFunctorExt (isFunProp.preFunctor F)]

    namespace HasSemicategoryFunctors

      variable {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasLinearFunctors W]
               {α : Sort u} {β : Sort v} [hα : IsSemicategory W α] [hβ : IsSemicategory W β]
               [h : HasSemicategoryFunctors α β]

      instance isSemicategoryFunctor (F : BundledFunctor h.Fun) : IsSemicategoryFunctor F.φ :=
      { hTrans    := h.isTransFunctor    F,
        hTransExt := h.isTransFunctorExt F }

    end HasSemicategoryFunctors

  end IsSemicategory

  namespace IsCategory

    open HasMorphisms HasIsomorphisms HasIsomorphismsExt

    class HasCategoryFunctors {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasLinearFunctors W]
                              (α : Sort u) (β : Sort v)
                              [hα : IsCategory W α] [hβ : IsCategory W β] extends
      HasMorphismFunctors α β where
    [isPreorderFunctor (F : BundledFunctor Fun) : IsPreorderFunctor (isFunProp.preFunctor F)]
    [isTransFunctorExt (F : BundledFunctor Fun) : IsTransFunctorExt (isFunProp.preFunctor F)]

    namespace HasCategoryFunctors

      variable {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasLinearFunctors W]
               {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
               [h : HasCategoryFunctors α β]

      instance isCategoryFunctor (F : BundledFunctor h.Fun) : IsCategoryFunctor F.φ :=
      { hPreorder := h.isPreorderFunctor F,
        hTransExt := h.isTransFunctorExt F }

    end HasCategoryFunctors

    class HasIsoFunEq {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]
                      (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
                      [hαIso : HasIsomorphisms α] [hβIso : HasIsomorphisms β]
                      [hαIsoExt : HasIsomorphismsExt α] [hβIsoExt : HasIsomorphismsExt β]
                      [hCatFun : HasCategoryFunctors α β] where
    [isIsoFunProp : IsFunProp hαIso.Iso hβIso.Iso hCatFun.Fun]
    [isEquivalenceFunctor (F : BundledFunctor hCatFun.Fun) : IsEquivalenceFunctor (isIsoFunProp.preFunctor F)]
    [isSymmFunctorExt     (F : BundledFunctor hCatFun.Fun) : IsSymmFunctorExt     (isIsoFunProp.preFunctor F)]
    [isTransFunctorExt    (F : BundledFunctor hCatFun.Fun) : IsTransFunctorExt    (isIsoFunProp.preFunctor F)]
    (isoFunEq (F : BundledFunctor hCatFun.Fun) {a b : α} (e : a ⇿ b) :
       hβIso.toHomMetaFunctor ((isIsoFunProp.preFunctor F) e) ≃ (hCatFun.isFunProp.preFunctor F) (hαIso.toHomMetaFunctor e))
    (isoFunEqExt (F : BundledFunctor hCatFun.Fun) (a b : α) :
       hβIso.toHomMetaFunctor.baseFun (F.φ a) (F.φ b) • (isIsoFunProp.preFunctor F).baseFun a b
       ≃{▻ λ e => isoFunEq F e ◅}
       (hCatFun.isFunProp.preFunctor F).baseFun a b • hαIso.toHomMetaFunctor.baseFun a b)

  end IsCategory

  namespace IsGroupoid

    open HasMorphisms HasIsomorphisms HasIsomorphismsExt

    class HasGroupoidFunctors {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]
                              (α : Sort u) (β : Sort v)
                              [hα : IsGroupoid W α] [hβ : IsGroupoid W β] extends
      HasMorphismFunctors α β where
    [isEquivalenceFunctor (F : BundledFunctor Fun) : IsEquivalenceFunctor (isFunProp.preFunctor F)]
    [isSymmFunctorExt     (F : BundledFunctor Fun) : IsSymmFunctorExt     (isFunProp.preFunctor F)]
    [isTransFunctorExt    (F : BundledFunctor Fun) : IsTransFunctorExt    (isFunProp.preFunctor F)]

    namespace HasGroupoidFunctors

      variable {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]
               {α : Sort u} {β : Sort v} [hα : IsGroupoid W α] [hβ : IsGroupoid W β]
               [h : HasGroupoidFunctors α β]

      instance isGroupoidFunctor (F : BundledFunctor h.Fun) : IsGroupoidFunctor F.φ :=
      { hEquivalence := h.isEquivalenceFunctor F,
        hSymmExt     := h.isSymmFunctorExt     F,
        hTransExt    := h.isTransFunctorExt    F }

    end HasGroupoidFunctors

  end IsGroupoid

  -- TODO: It is a bit unclear whether having all of these different instances is the correct way to go.
  -- But it seems impossible to merge them because the correct functor type differs.
  -- Do we need coherence conditions instead?

  class IsFunUniverse (W : Universe.{w}) [HasIdentity.{w, iw} W] [HasStandardFunctors W] where
  [hasMorphismFunctors     (α : Sort u) (β : Sort v) [HasMorphisms   W α] [HasMorphisms   W β] :
     HasMorphisms.HasMorphismFunctors       α β]
  [hasSemicategoryFunctors (α : Sort u) (β : Sort v) [IsSemicategory W α] [IsSemicategory W β] :
     IsSemicategory.HasSemicategoryFunctors α β]
  [hasCategoryFunctors     (α : Sort u) (β : Sort v) [IsCategory     W α] [IsCategory     W β] :
     IsCategory.HasCategoryFunctors         α β]
  [hasGroupoidFunctors     (α : Sort u) (β : Sort v) [IsGroupoid     W α] [IsGroupoid     W β] :
     IsGroupoid.HasGroupoidFunctors         α β]

  namespace IsFunUniverse

    variable (W : Universe.{w}) [HasIdentity.{w, iw} W] [HasStandardFunctors W]
             [h : IsFunUniverse W]

    instance (α : Sort u) (β : Sort v) [HasMorphisms   W α] [HasMorphisms   W β] :
      HasMorphisms.HasMorphismFunctors       α β :=
    h.hasMorphismFunctors     α β

    instance (α : Sort u) (β : Sort v) [IsSemicategory W α] [IsSemicategory W β] :
      IsSemicategory.HasSemicategoryFunctors α β :=
    h.hasSemicategoryFunctors α β

    instance (α : Sort u) (β : Sort v) [IsCategory     W α] [IsCategory     W β] :
      IsCategory.HasCategoryFunctors         α β :=
    h.hasCategoryFunctors     α β

    instance (α : Sort u) (β : Sort v) [IsGroupoid     W α] [IsGroupoid     W β] :
      IsGroupoid.HasGroupoidFunctors         α β :=
    h.hasGroupoidFunctors     α β

  end IsFunUniverse

  class IsIsoFunUniverse (W : Universe.{w}) [HasIdentity.{w, iw} W] [HasStandardFunctors W]
                         [hIsoUniv : IsIsoUniverse W]
                         [hIsoExtUniv : IsIsoUniverse.IsIsoExtUniverse W]
                         [hFunUniv : IsFunUniverse W] where
  [hasIsoFunEq (α β : Sort u) [IsCategory W α] [IsCategory W β] :
     HasIsoFunEq α β (hαIso := hIsoUniv.hasIsomorphisms α) (hβIso := hIsoUniv.hasIsomorphisms β)
                     (hCatFun := hFunUniv.hasCategoryFunctors α β)]

  namespace IsIsoFunUniverse

    open IsIsoUniverse

    variable {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]
             [hIsoUniv : IsIsoUniverse W] [IsIsoExtUniverse W] [hFunUniv : IsFunUniverse W]
             [h : IsIsoFunUniverse W]

    instance (α β : Sort u) [IsCategory W α] [IsCategory W β] :
      HasIsoFunEq α β (hαIso := hIsoUniv.hasIsomorphisms α) (hβIso := hIsoUniv.hasIsomorphisms β)
                      (hCatFun := hFunUniv.hasCategoryFunctors α β) :=
    h.hasIsoFunEq α β

  end IsIsoFunUniverse



  structure BundledQuantification {W : Universe.{w}} [HasIdentity.{w, iw} W]
                                  [HasInternalFunctors W] {α : Sort u} {β : Sort v}
                                  {Fun : MetaProperty (α → β) W}
                                  (Nat : MetaRelation (BundledFunctor Fun) W) where
  {F G : BundledFunctor Fun}
  (η   : Nat F G)

  class IsNatRel {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasInternalFunctors W]
                 {α : Sort u} {β : Sort v} (S : MetaRelation β W)
                 {Fun : MetaProperty (α → β) W} (Nat : MetaRelation (BundledFunctor Fun) W) where
  (metaQuantification (η : BundledQuantification Nat) : MetaQuantification S η.F.φ η.G.φ)

  namespace HasMorphisms

    class HasNaturalTransformations {W : Universe.{w}} [HasIdentity.{w, iw} W]
                                    [HasInternalFunctors W] (α : Sort u) (β : Sort v)
                                    [hα : HasMorphisms W α] [hβ : HasMorphisms W β]
                                    [hFun : HasMorphismFunctors α β] [HasTrans hβ.Hom] where
    (Nat      : MetaRelation (BundledFunctor hFun.Fun) W)
    [isNatRel : IsNatRel hβ.Hom Nat]
    [isNatural (η : BundledQuantification Nat) :
       IsNatural (hFun.isFunProp.preFunctor η.F) (hFun.isFunProp.preFunctor η.G)
                 (isNatRel.metaQuantification η)]

  end HasMorphisms

end CategoryTheory
