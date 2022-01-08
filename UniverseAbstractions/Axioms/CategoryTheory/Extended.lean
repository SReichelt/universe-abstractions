import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.MetaProperties
import UniverseAbstractions.Axioms.MetaRelations
import UniverseAbstractions.Axioms.CategoryTheory.Meta
import UniverseAbstractions.Axioms.CategoryTheory.Basic



set_option autoBoundImplicitLocal false
set_option maxHeartbeats 100000
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

    structure IsoDesc {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasLinearFunctors V]
                      {α : Sort u} [hCat : IsCategory V α] (a b : α) :
      Sort (max 1 u v iv) where
    (toHom  : a ⇾ b)
    (invHom : b ⇾ a)
    [isInv  : IsInv hCat.Hom toHom invHom]

    namespace IsoDesc

      variable {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasLinearFunctors V]
               {α : Sort u} [hCat : IsCategory V α]

      instance {a b : α} (e : IsoDesc a b) : IsInv hCat.Hom e.toHom e.invHom := e.isInv

      def refl (a : α) : IsoDesc a a :=
      ⟨idHom a, idHom a⟩

      def symm {a b : α} (e : IsoDesc a b) : IsoDesc b a :=
      ⟨e.invHom, e.toHom⟩

      def trans {a b c : α} (e : IsoDesc a b) (f : IsoDesc b c) : IsoDesc a c :=
      ⟨f.toHom • e.toHom, e.invHom • f.invHom⟩

      def toInvEquiv {a b : α} {e₁ e₂ : IsoDesc a b} (h : e₁.toHom ≃ e₂.toHom) :
        e₁.invHom ≃ e₂.invHom :=
      (HalfInv.unique hCat.Hom e₁.isInv.leftInv (HalfInv.congrArgLeft hCat.Hom h e₂.isInv.rightInv))⁻¹

    end IsoDesc

    class HasIsoRel {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasLinearFunctors V]
                    (α : Sort u) [hCat : IsCategory V α] where
    (Iso                                  : MetaRelation α V)
    [isoIsEquivalence                     : IsEquivalence Iso]
    [isoInv {a b : α} (e : Iso a b)       : IsInv Iso e e⁻¹]
    [isoHasSymmFun                        : HasSymmFun Iso]
    [isoHasTransFun                       : HasTransFun Iso]
    (desc {a b : α} (e : Iso a b)         : IsoDesc a b)
    (defToHomFun (a b : α)                : Iso a b ⟶{λ e => (desc e).toHom} (a ⇾ b))
    [toHomIsPreorderFunctor               : IsPreorderFunctor (MetaFunctor.fromDefFun defToHomFun)]
    (toHomInj {a b : α} {e₁ e₂ : Iso a b} : (desc e₁).toHom ≃ (desc e₂).toHom → e₁ ≃ e₂)

    namespace HasIsoRel

      infix:20 " ⇿ " => CategoryTheory.IsCategory.HasIsoRel.Iso

      section

        variable {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasLinearFunctors V] (α : Sort u)
                 [hCat : IsCategory V α] [h : HasIsoRel α]

        instance : IsEquivalence h.Iso := h.isoIsEquivalence
        instance : HasSymmFun    h.Iso := h.isoHasSymmFun
        instance : HasTransFun   h.Iso := h.isoHasTransFun

        def toHomMetaFunctor : MetaFunctor h.Iso hCat.Hom := MetaFunctor.fromDefFun h.defToHomFun

        instance : IsPreorderFunctor (toHomMetaFunctor α) := h.toHomIsPreorderFunctor

        def isoMorphisms : HasMorphisms V α := ⟨h.Iso⟩

      end

      section

        variable {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasLinearFunctors V] {α : Sort u}
                 [hCat : IsCategory V α] [h : HasIsoRel α]

        @[reducible] def idIso (a : α) : a ⇿ a := HasRefl.refl a

        @[reducible] def toHom  {a b : α} (e : a ⇿ b) : a ⇾ b := (h.desc e).toHom
        @[reducible] def invHom {a b : α} (e : a ⇿ b) : b ⇾ a := (h.desc e).invHom

        def toHomEq {a b : α} {e₁ e₂ : a ⇿ b} (he : e₁ ≃ e₂) : toHom e₁ ≃ toHom e₂ :=
        defCongrArg (h.defToHomFun a b) he

        def toHomReflEq (a : α) : toHom (idIso a) ≃ idHom a :=
        h.toHomIsPreorderFunctor.reflEq a • byDef⁻¹

        def toHomTransEq {a b c : α} (e : a ⇿ b) (f : b ⇿ c) : toHom (f • e) ≃ toHom f • toHom e :=
        congrArgTrans hCat.Hom byDef byDef • h.toHomIsPreorderFunctor.transEq e f • byDef⁻¹

        def isoAssoc {a b c d : α} (e : a ⇿ b) (f : b ⇿ c) (g : c ⇿ d) :
          (g • f) • e ≃ g • (f • e) :=
        toHomInj ((congrArgTransRight hCat.Hom (toHomTransEq e f) (toHom g) •
                   toHomTransEq (f • e) g)⁻¹ •
                  assoc (toHom e) (toHom f) (toHom g) •
                  (congrArgTransLeft hCat.Hom (toHom e) (toHomTransEq f g) •
                   toHomTransEq e (g • f)))

        def isoRightId {a b : α} (e : a ⇿ b) : e • idIso a ≃ e :=
        toHomInj (rightId (toHom e) •
                  (congrArgTransRight hCat.Hom (toHomReflEq a) (toHom e) •
                   toHomTransEq (idIso a) e))

        def isoLeftId {a b : α} (e : a ⇿ b) : idIso b • e ≃ e :=
        toHomInj (leftId (toHom e) •
                  (congrArgTransLeft hCat.Hom (toHom e) (toHomReflEq b) •
                   toHomTransEq e (idIso b)))

        def isoLeftInv  {a b : α} (e : a ⇿ b) : e⁻¹ • e ≃ idIso a := (h.isoInv e).leftInv
        def isoRightInv {a b : α} (e : a ⇿ b) : e • e⁻¹ ≃ idIso b := (h.isoInv e).rightInv

        def toHomHalfInv {a b : α} {e : a ⇿ b} {f : b ⇿ a} (hef : HalfInv h.Iso e f) :
          HalfInv hCat.Hom (toHom e) (toHom f) :=
        toHomReflEq a • toHomEq hef • (toHomTransEq e f)⁻¹

        instance toHomInv {a b : α} (e : a ⇿ b) : IsInv hCat.Hom (toHom e) (toHom e⁻¹) :=
        { leftInv  := toHomHalfInv (isoLeftInv  e),
          rightInv := toHomHalfInv (isoRightInv e) }

        def invHomEq {a b : α} (e : a ⇿ b) : invHom e ≃ toHom e⁻¹ :=
        IsInv.unique hCat.Hom (toHom e) (toHom e⁻¹) (invHom e)

        instance isoIsGroupoidEquivalence : IsGroupoidEquivalence h.Iso :=
        { assoc    := isoAssoc,
          rightId  := isoRightId,
          leftId   := isoLeftId,
          leftInv  := isoLeftInv,
          rightInv := isoRightInv }

      end

      class HasIsoRelExt {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasStandardFunctors V]
                         (α : Sort u) [IsCategory V α] [hIso : HasIsoRel α] where
      [toHomIsTransFunctorExt      : IsTransFunctor.IsTransFunctorExt hIso.toHomMetaFunctor]
      [isoIsGroupoidEquivalenceExt : IsGroupoidEquivalenceExt hIso.Iso]

      namespace HasIsoRelExt

        variable {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasStandardFunctors V] (α : Sort u)
                 [IsCategory V α] [hIso : HasIsoRel α] [h : HasIsoRelExt α]

        instance : IsTransFunctor.IsTransFunctorExt hIso.toHomMetaFunctor := h.toHomIsTransFunctorExt

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
        homIsEquivalence            := h.hasIsoRel.isoIsEquivalence,
        homHasSymmFun               := h.hasIsoRel.isoHasSymmFun,
        homHasTransFun              := h.hasIsoRel.isoHasTransFun,
        homIsGroupoidEquivalence    := HasIsoRel.isoIsGroupoidEquivalence,
        homIsGroupoidEquivalenceExt := h.hasIsoRelExt.isoIsGroupoidEquivalenceExt }

    end HasIsomorphisms

  end IsCategory



  namespace IsGroupoid

    open HasIsoRel

    variable {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasStandardFunctors V] (α : Sort u)
             [hGrp : IsGroupoid V α]

    def isoDesc {a b : α} (e : a ⇾ b) : IsoDesc a b := ⟨e, e⁻¹⟩

    instance hasIsoRel : HasIsoRel α :=
    { Iso                    := hGrp.Hom,
      isoIsEquivalence       := hGrp.homIsEquivalence,
      isoInv                 := isInv hGrp.Hom,
      isoHasSymmFun          := hGrp.homHasSymmFun,
      isoHasTransFun         := hGrp.homHasTransFun,
      desc                   := isoDesc α,
      defToHomFun            := λ a b => HasIdFun.defIdFun (a ⇾ b),
      toHomIsPreorderFunctor := idFun.isPreorderFunctor hGrp.Hom,
      toHomInj               := id }

    instance hasIsoRelExt : HasIsoRelExt α :=
    { toHomIsTransFunctorExt      := idFun.isTransFunctorExt hGrp.Hom,
      isoIsGroupoidEquivalenceExt := IsGroupoidEquivalenceExt.translate hGrp.Hom }

    instance hasIsomorphisms : HasIsomorphisms α := ⟨⟩

  end IsGroupoid



  class IsIsoUniverse (V : Universe.{v}) [HasIdentity.{v, iv} V] [HasStandardFunctors V] where
  [hasIsomorphisms (α : Sort (max 1 u v iv)) [IsCategory V α] : HasIsomorphisms α]

  namespace IsIsoUniverse

    variable {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasStandardFunctors V]
             [h : IsIsoUniverse.{u} V]

    instance (α : Sort (max 1 u v iv)) [IsCategory V α] : HasIsomorphisms α := h.hasIsomorphisms α

  end IsIsoUniverse



  class IsIsoFunctor {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]
                     {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
                     [hαIso : HasIsomorphisms α] [hβIso : HasIsomorphisms β]
                     (φ : α → β) [hφ : IsCategoryFunctor φ] extends
    IsGroupoidFunctor φ (hα := HasIsomorphisms.isoGroupoid α)
                        (hβ := HasIsomorphisms.isoGroupoid β) where
  (homIsoCongr {a b : α} (e : a ⇿ b) : HasIsoRel.toHom (F e) ≃ hφ.F (HasIsoRel.toHom e))
  (homIsoCongrExt (a b : α) :
     (HasIsoRel.toHomMetaFunctor β).baseFun (φ a) (φ b) • F.baseFun a b
     ≃{byDef ▻ λ e => homIsoCongr e ◅ byArgDef}
     hφ.F.baseFun a b • (HasIsoRel.toHomMetaFunctor α).baseFun a b)

  namespace IsIsoFunctor

    variable {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]

    section

      variable {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
               [hαIso : HasIsomorphisms α] [hβIso : HasIsomorphisms β]
               (φ : α → β) [IsCategoryFunctor φ] [h : IsIsoFunctor φ]

      def isMorphismFunctor : IsMorphismFunctor φ (hα := HasIsoRel.isoMorphisms α)
                                                  (hβ := HasIsoRel.isoMorphisms β) :=
      h.toIsMorphismFunctor (hα := HasIsomorphisms.isoGroupoid α)
                            (hβ := HasIsomorphisms.isoGroupoid β)

      def preFunctor : PreFunctor hαIso.hasIsoRel.Iso hβIso.hasIsoRel.Iso φ :=
      (isMorphismFunctor φ).F (hα := HasIsoRel.isoMorphisms α) (hβ := HasIsoRel.isoMorphisms β)

    end

  end IsIsoFunctor

  class HasFunctorialityProperty {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]
                                 (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β] where
  (IsFun (φ : α → β) [hφ : IsCategoryFunctor φ] : HasIdentity.univ W)

  namespace HasFunctorialityProperty

    variable {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]

    structure Functor (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
                      [h : HasFunctorialityProperty α β] : Sort (max 1 u v w iw) where
    {φ     : α → β}
    [hφ    : IsCategoryFunctor φ]
    (isFun : h.IsFun φ)

    namespace Functor

      variable {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
               [h : HasFunctorialityProperty α β] (F : Functor α β)

      instance : IsCategoryFunctor F.φ := F.hφ

    end Functor

  end HasFunctorialityProperty

  class HasIsoFunctoriality {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]
                            (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
                            [hαIso : HasIsomorphisms α] [hβIso : HasIsomorphisms β] extends
    HasFunctorialityProperty α β where
  [isIsoFun (F : HasFunctorialityProperty.Functor α β) : IsIsoFunctor F.φ]

  namespace HasIsoFunctoriality

    variable {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]
             (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
             [hαIso : HasIsomorphisms α] [hβIso : HasIsomorphisms β] [h : HasIsoFunctoriality α β]

    instance (F : HasFunctorialityProperty.Functor α β) : IsIsoFunctor F.φ := h.isIsoFun F

  end HasIsoFunctoriality

  class IsFunUniverse (W : Universe.{w}) [HasIdentity.{w, iw} W] [HasStandardFunctors W]
                      [hIsoUniv : IsIsoUniverse.{u} W] where
  [hasFunProp (α β : Sort (max 1 u w iw)) [IsCategory W α] [IsCategory W β] : HasIsoFunctoriality α β]
  (idIsFun (α : Sort (max 1 u w iw)) [IsCategory W α] : (hasFunProp α α).IsFun id)
  (constIsFun (α : Sort (max 1 u w iw)) {β : Sort (max 1 u w iw)} [IsCategory W α] [IsCategory W β] (b : β) :
     (hasFunProp α β).IsFun (Function.const α b))
  (compIsFun {α β γ : Sort (max 1 u w iw)} [IsCategory W α] [IsCategory W β] [IsCategory W γ]
             (F : HasFunctorialityProperty.Functor α β) (G : HasFunctorialityProperty.Functor β γ) :
     (hasFunProp α γ).IsFun (G.φ ∘ F.φ))

  namespace IsFunUniverse

    open HasFunctorialityProperty

    variable {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W] [IsIsoUniverse.{u} W]
             [h : IsFunUniverse.{u} W]

    instance (α β : Sort (max 1 u w iw)) [IsCategory W α] [IsCategory W β] : HasIsoFunctoriality α β :=
    h.hasFunProp α β

    def idFun (α : Sort (max 1 u w iw)) [IsCategory W α] : Functor α α := ⟨h.idIsFun α⟩

    def constFun (α : Sort (max 1 u w iw)) {β : Sort (max 1 u w iw)} [IsCategory W α] [IsCategory W β] (b : β) :
      Functor α β :=
    ⟨h.constIsFun α b⟩

    def compFun {α β γ : Sort (max 1 u w iw)} [IsCategory W α] [IsCategory W β] [IsCategory W γ]
                (F : Functor α β) (G : Functor β γ) :
      Functor α γ :=
    ⟨h.compIsFun F G⟩

  end IsFunUniverse



  structure NatDesc {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]
                    {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
                    (φ ψ : α → β) [IsMorphismFunctor φ] [IsMorphismFunctor ψ] where
  (nat   : MetaQuantification hβ.Hom φ ψ)
  [isNat : IsNaturalTransformation nat]

  namespace NatDesc

    variable {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]
             {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
             {φ ψ : α → β} [IsMorphismFunctor φ] [IsMorphismFunctor ψ] (η : NatDesc φ ψ)

    instance : IsNaturalTransformation η.nat := η.isNat

  end NatDesc

  class HasNaturalityRelation {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]
                              [hIsoUniv : IsIsoUniverse.{u} W] [hFunUniv : IsFunUniverse.{u} W]
                              (α β : Sort (max 1 u w iw)) [hα : IsCategory W α] [hβ : IsCategory W β] where
  (Nat : MetaRelation (HasFunctorialityProperty.Functor α β) W)
  (desc {F G : HasFunctorialityProperty.Functor α β} (η : Nat F G) : NatDesc F.φ G.φ)
  (defNatFun (F G : HasFunctorialityProperty.Functor α β) (a : α) :
     Nat F G ⟶{λ η => (desc η).nat a} hβ.Hom (F.φ a) (G.φ a))

  namespace HasNaturalityRelation

    open HasFunctors HasFunctorialityProperty

    variable {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]
             [hIsoUniv : IsIsoUniverse.{u} W] [hFunUniv : IsFunUniverse.{u} W]
             {α β : Sort (max 1 u w iw)} [hα : IsCategory W α] [hβ : IsCategory W β]
             [h : HasNaturalityRelation.{u} α β]

    @[reducible] def natFun (F G : Functor α β) (a : α) :
      h.Nat F G ⟶ hβ.Hom (F.φ a) (G.φ a) :=
    defNatFun F G a

    instance {F G : Functor α β} (η : h.Nat F G) (a : α) :
      IsFunApp (h.Nat F G) ((desc η).nat a) :=
    { F := natFun F G a,
      a := η,
      e := byDef }

    def FunNatDesc (F G : Functor α β) := NatDesc F.φ G.φ

    structure DefNat {F G : Functor α β} (desc : FunNatDesc F G) where
    (η             : h.Nat F G)
    (natEq (a : α) : (h.desc η).nat a ≃ desc.nat a)

    def byNatDef {F G : Functor α β} {desc : FunNatDesc F G} {η : DefNat desc} (a : α) :
      (h.desc η.η).nat a ≃ desc.nat a :=
    η.natEq a

    def NatEquiv {F G : Functor α β} (η ε : h.Nat F G)
                 (h : ∀ a, (h.desc η).nat a ≃ (h.desc ε).nat a) :=
    η ≃ ε

  end HasNaturalityRelation

  class HasNatOp {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]
                 [hIsoUniv : IsIsoUniverse.{u} W] [hFunUniv : IsFunUniverse.{u} W]
                 (α β : Sort (max 1 u w iw)) [hα : IsCategory W α] [hβ : IsCategory W β] extends
    HasNaturalityRelation.{u} α β where
  (defRefl (F : HasFunctorialityProperty.Functor α β) :
     HasNaturalityRelation.DefNat ⟨MetaQuantification.refl hβ.Hom F.φ⟩)
  (defTrans {F G H : HasFunctorialityProperty.Functor α β} (η : Nat F G) (ε : Nat G H) :
     HasNaturalityRelation.DefNat ⟨MetaQuantification.trans hβ.Hom (desc η).nat (desc ε).nat⟩)

  namespace HasNatOp

    variable {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]
             [hIsoUniv : IsIsoUniverse.{u} W] [hFunUniv : IsFunUniverse.{u} W]
             {α β : Sort (max 1 u w iw)} [hα : IsCategory W α] [hβ : IsCategory W β]
             [h : HasNatOp.{u} α β]

    def refl (F : HasFunctorialityProperty.Functor α β) : h.Nat F F := (h.defRefl F).η

    def trans {F G H : HasFunctorialityProperty.Functor α β} (η : h.Nat F G) (ε : h.Nat G H) :
      h.Nat F H :=
    (h.defTrans η ε).η

    instance natIsPreorder : IsPreorder h.Nat :=
    { refl  := refl,
      trans := trans }

  end HasNatOp

  class HasNaturality {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]
                      [hIsoUniv : IsIsoUniverse.{u} W] [hFunUniv : IsFunUniverse.{u} W]
                      (α β : Sort (max 1 u w iw)) [hα : IsCategory W α] [hβ : IsCategory W β] extends
    HasNatOp.{u} α β where
  [natHasTransFun              : HasTransFun                                    Nat]
  [natIsCategoricalPreorder    : IsCategoricalPreorder                          Nat]
  [natIsCategoricalPreorderExt : IsCategoricalPreorder.IsCategoricalPreorderExt Nat]

  namespace HasNaturality

    open HasFunctorialityProperty HasNaturalityRelation

    variable {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]
             [hIsoUniv : IsIsoUniverse.{u} W] [hFunUniv : IsFunUniverse.{u} W]

    section

      variable (α β : Sort (max 1 u w iw)) [hα : IsCategory W α] [hβ : IsCategory W β]
               [h : HasNaturality.{u} α β]

      instance : IsPreorder                                     h.Nat := h.natIsPreorder
      instance : HasTransFun                                    h.Nat := h.natHasTransFun
      instance : IsCategoricalPreorder                          h.Nat := h.natIsCategoricalPreorder
      instance : IsCategoricalPreorder.IsCategoricalPreorderExt h.Nat := h.natIsCategoricalPreorderExt

      instance funHasMorphisms : HasMorphisms W (Functor α β) := ⟨h.Nat⟩

      instance funIsCategory : IsCategory.{max 1 u w iw} W (Functor α β) :=
      { homIsPreorder               := HasNatOp.natIsPreorder,
        homHasTransFun              := h.natHasTransFun,
        homIsCategoricalPreorder    := h.natIsCategoricalPreorder,
        homIsCategoricalPreorderExt := h.natIsCategoricalPreorderExt }

    end

    section

      variable {α : Sort (max 1 u w iw)} (a : α) (β : Sort (max 1 u w iw))
               [hα : IsCategory W α] [hβ : IsCategory W β] [h : HasNaturality.{u} α β]

      def revApp (F : Functor α β) : β := F.φ a

      def revAppPreFun : PreFunctor h.Nat hβ.Hom (revApp a β) :=
      ⟨λ F₁ F₂ => natFun F₁ F₂ a⟩

      instance revAppPreFunIsReflFunctor : IsReflFunctor (revAppPreFun.{u} a β) := ⟨λ F => byNatDef a • byDef⟩

      instance revAppPreFunIsTransFunctor : IsTransFunctor (revAppPreFun.{u} a β) :=
      ⟨λ η ε => (HasTransFun.congrArgTrans hβ.Hom byDef byDef)⁻¹ • byNatDef a • byDef⟩

      instance revAppPreFunIsPreorderFunctor : IsPreorderFunctor (revAppPreFun.{u} a β) := ⟨⟩

      instance revAppPreFunIsTransFunctorExt : IsTransFunctorExt (revAppPreFun.{u} a β) :=
      { transEqExt    := λ η F₃ => sorry,
        transEqExtExt := λ F₁ F₂ F₃ => sorry }

      instance : IsCategoryFunctor (revApp.{u} a β) :=
      { F         := revAppPreFun.{u} a β,
        hPreorder := revAppPreFunIsPreorderFunctor a β,
        hTransExt := revAppPreFunIsTransFunctorExt a β }

      def RevAppFunType := (hFunUniv.hasFunProp (Functor α β) β).IsFun (revApp.{u} a β)

      def revAppFun (revAppIsFun : RevAppFunType.{u} a β) : Functor (Functor α β) β :=
      { isFun := revAppIsFun }

    end

    section

      variable (α β : Sort max 1 u w iw) [hα : IsCategory W α] [hβ : IsCategory W β]
               [h₁ : HasNaturality.{u} α β] [h₂ : HasNaturality.{u, w, iw} (Functor α β) β]
               (revAppIsFun : ∀ a : α, RevAppFunType.{u} a β)

      def revAppCongrArgDesc {a₁ a₂ : α} (f : a₁ ⇾ a₂) :
        FunNatDesc (revAppFun.{u} a₁ β (revAppIsFun a₁)) (revAppFun.{u} a₂ β (revAppIsFun a₂)) :=
      { nat   := λ F => IsMorphismFunctor.F (φ := F.φ) f,
        isNat := { isNatural    := ⟨λ {F₁ F₂} η =>
                                    ((h₁.desc η).isNat.isNatural.nat f •
                                     HasTransFun.congrArgTransRight hβ.Hom byDef (IsMorphismFunctor.F (φ := F₂.φ) f))⁻¹ •
                                    HasTransFun.congrArgTransLeft hβ.Hom (IsMorphismFunctor.F (φ := F₁.φ) f) byDef⟩,
                   isNaturalExt := sorry } }

      variable (defRevAppCongrArg : ∀ {a₁ a₂ : α} (f : a₁ ⇾ a₂), DefNat (revAppCongrArgDesc α β revAppIsFun f))

      def revAppCongrArg {a₁ a₂ : α} (f : a₁ ⇾ a₂) :
        revAppFun.{u} a₁ β (revAppIsFun a₁) ⇾ revAppFun.{u} a₂ β (revAppIsFun a₂) :=
      (defRevAppCongrArg f).η

      def RevAppEquivReflType (a : α) :=
      NatEquiv (revAppCongrArg.{u} α β revAppIsFun defRevAppCongrArg (idHom a))
               (idHom (revAppFun.{u} a β (revAppIsFun a)))
               (λ F => (byNatDef F)⁻¹ •
                       IsReflFunctor.reflEq (F := IsMorphismFunctor.F (φ := F.φ)) a •
                       byNatDef F)

      def RevAppEquivTransType {a₁ a₂ a₃ : α} (f : a₁ ⇾ a₂) (g : a₂ ⇾ a₃) :=
      NatEquiv (revAppCongrArg.{u} α β revAppIsFun defRevAppCongrArg (g • f))
               (revAppCongrArg.{u} α β revAppIsFun defRevAppCongrArg g • revAppCongrArg α β revAppIsFun defRevAppCongrArg f)
               (λ F => (HasTransFun.congrArgTrans hβ.Hom (byNatDef F) (byNatDef F) •
                        byNatDef F)⁻¹ •
                       IsTransFunctor.transEq (F := IsMorphismFunctor.F (φ := F.φ)) f g •
                       byNatDef F)

      variable (defRevAppCongrArgFun : ∀ a₁ a₂ : α, (a₁ ⇾ a₂) ⟶{λ f => revAppCongrArg α β revAppIsFun defRevAppCongrArg f} (revAppFun.{u} a₁ β (revAppIsFun a₁) ⇾ revAppFun.{u} a₂ β (revAppIsFun a₂)))

      @[reducible] def revAppCongrArgFun (a₁ a₂ : α) :
        (a₁ ⇾ a₂) ⟶ (revAppFun.{u} a₁ β (revAppIsFun a₁) ⇾ revAppFun.{u} a₂ β (revAppIsFun a₂)) :=
      defRevAppCongrArgFun a₁ a₂

      variable (revAppEquivRefl : ∀ a : α, RevAppEquivReflType α β revAppIsFun defRevAppCongrArg a)
               (revAppEquivTrans : ∀ {a₁ a₂ a₃ : α} (f : a₁ ⇾ a₂) (g : a₂ ⇾ a₃), RevAppEquivTransType α β revAppIsFun defRevAppCongrArg f g)

      instance revAppFunIsCategoryFunctor : IsCategoryFunctor (λ a : α => revAppFun.{u} a β (revAppIsFun a)) :=
      { F         := ⟨revAppCongrArgFun.{u} α β revAppIsFun defRevAppCongrArg defRevAppCongrArgFun⟩,
        hPreorder := { reflEq  := λ a   => revAppEquivRefl a • byDef,
                       transEq := λ f g => HasTransFun.congrArgTrans h₂.Nat byDef⁻¹ byDef⁻¹ •
                                           revAppEquivTrans f g •
                                           byDef },
        hTransExt := sorry }

      def RevAppFunFunType :=
      (hFunUniv.hasFunProp α (Functor (Functor α β) β)).IsFun (λ a : α => revAppFun.{u} a β (revAppIsFun a))
        (hφ := revAppFunIsCategoryFunctor.{u} α β revAppIsFun defRevAppCongrArg defRevAppCongrArgFun
                                              revAppEquivRefl revAppEquivTrans)

      def revAppFunFun (revAppFunIsFun : RevAppFunFunType.{u} α β revAppIsFun defRevAppCongrArg defRevAppCongrArgFun
                                                              revAppEquivRefl revAppEquivTrans) :
        Functor α (Functor (Functor α β) β) :=
      { isFun := revAppFunIsFun }

    end

    class HasRevAppFun (α β : Sort max 1 u w iw) [hα : IsCategory W α] [hβ : IsCategory W β]
                       [h₁ : HasNaturality.{u} α β]
                       [h₂ : HasNaturality.{u, w, iw} (Functor α β) β] where
    (revAppIsFun (a : α) : RevAppFunType.{u} a β)
    (defRevAppCongrArg {a₁ a₂ : α} (f : a₁ ⇾ a₂) : DefNat (revAppCongrArgDesc α β revAppIsFun f))
    (defRevAppCongrArgFun (a₁ a₂ : α) :
       (a₁ ⇾ a₂)
       ⟶{λ f => revAppCongrArg α β revAppIsFun defRevAppCongrArg f}
       (revAppFun.{u} a₁ β (revAppIsFun a₁) ⇾ revAppFun.{u} a₂ β (revAppIsFun a₂)))
    (revAppEquivRefl (a : α) : RevAppEquivReflType α β revAppIsFun defRevAppCongrArg a)
    (revAppEquivTrans {a₁ a₂ a₃ : α} (f : a₁ ⇾ a₂) (g : a₂ ⇾ a₃) :
       RevAppEquivTransType α β revAppIsFun defRevAppCongrArg f g)
    (revAppFunIsFun : RevAppFunFunType.{u} α β revAppIsFun defRevAppCongrArg defRevAppCongrArgFun
                                           revAppEquivRefl revAppEquivTrans)

  end HasNaturality

  class IsNatUniverse (W : Universe.{w}) [HasIdentity.{w, iw} W] [HasStandardFunctors W]
                      [hIsoUniv : IsIsoUniverse.{u} W] [hFunUniv : IsFunUniverse.{u} W] where
  [hasNatRel (α β : Sort (max 1 u w iw)) [hα : IsCategory W α] [hβ : IsCategory W β] :
     HasNaturality.{u} α β]
  [hasRevAppFun (α β : Sort max 1 u w iw) [hα : IsCategory W α] [hβ : IsCategory W β] :
     HasNaturality.HasRevAppFun.{u} α β]

  namespace IsNatUniverse

    open HasFunctorialityProperty

    variable {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]
             [hIsoUniv : IsIsoUniverse.{u} W] [hFunUniv : IsFunUniverse.{u} W]
             [h : IsNatUniverse.{u} W]

    instance (α β : Sort (max 1 u w iw)) [hα : IsCategory W α] [hβ : IsCategory W β] :
      HasNaturality.{u} α β :=
    h.hasNatRel α β

    def revAppFun {α : Sort (max 1 u w iw)} (a : α) (β : Sort (max 1 u w iw))
                  [hα : IsCategory W α] [hβ : IsCategory W β] :
      Functor (Functor α β) β :=
    { isFun := (h.hasRevAppFun α β).revAppIsFun a }

    def revAppFunFun (α β : Sort max 1 u w iw) [hα : IsCategory W α] [hβ : IsCategory W β] :
      Functor α (Functor (Functor α β) β) :=
    { isFun := (h.hasRevAppFun α β).revAppFunIsFun }

  end IsNatUniverse

end CategoryTheory
