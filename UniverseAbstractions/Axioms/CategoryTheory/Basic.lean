/-
A version of higher category that works for universes, i.e. every universe with functors (more
specifically, with full functor operations and extensionality) and equivalences is a category
according to this definition.
-/



import UniverseAbstractions.Axioms.CategoryTheory.Meta
import UniverseAbstractions.Axioms.Universe.FunctorExtensionality
import UniverseAbstractions.Lemmas.DerivedFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v iv



namespace CategoryTheory

  open MetaRelation MetaFunctor HasTransFun HasSymmFun IsAssociative IsCategoricalPreorder
       IsPreGroupoidEquivalence IsGroupoidEquivalence HasFunctors HasCongrArg HasLinearFunOp

  structure HomUniverse where
  (V                   : Universe.{v})
  [hasIdentity         : HasIdentity.{v, iv} V]
  [hasInternalFunctors : HasInternalFunctors V]
  [hasLinearFunOp      : HasLinearFunOp      V]
  [hasLinearFunExt     : HasLinearFunExt     V]

  namespace HomUniverse

    variable (M : HomUniverse)

    def homEqUniv : Universe := M.hasIdentity.IU

    instance : HasIdentity         M.V := M.hasIdentity
    instance : HasInternalFunctors M.V := M.hasInternalFunctors
    instance : HasLinearFunOp      M.V := M.hasLinearFunOp
    instance : HasLinearFunExt     M.V := M.hasLinearFunExt

  end HomUniverse

  structure IsoUniverse extends HomUniverse where
  [hasSubLinearFunOp : HasSubLinearFunOp V]
  [hasNonLinearFunOp : HasNonLinearFunOp V]

  namespace IsoUniverse

    variable (M : IsoUniverse)

    instance : HasSubLinearFunOp M.V := M.hasSubLinearFunOp
    instance : HasNonLinearFunOp M.V := M.hasNonLinearFunOp

    instance : HasAffineFunOp M.V := ⟨⟩
    instance : HasFullFunOp   M.V := ⟨⟩

  end IsoUniverse

  structure IsoIndex (α : Sort u) : Type (max u v) where
  (a b : α)

  class IsSemigroupoid (M : outParam HomUniverse.{v, iv}) (α : Sort u) :
    Sort (max u (v + 1) iv) where
  (Hom                 : MetaRelation α M.V)
  [homHasTrans         : HasTrans         Hom]
  [homHasTransFun      : HasTransFun      Hom]
  [homIsAssociative    : IsAssociative    Hom]
  [homIsAssociativeExt : IsAssociativeExt Hom]

  namespace IsSemigroupoid

    infix:20 " ⇾ " => CategoryTheory.IsSemigroupoid.Hom

    variable {M : HomUniverse.{v, iv}} {α : Sort u} [h : IsSemigroupoid M α]

    instance : HasTrans         h.Hom := h.homHasTrans
    instance : HasTransFun      h.Hom := h.homHasTransFun
    instance : IsAssociative    h.Hom := h.homIsAssociative
    instance : IsAssociativeExt h.Hom := h.homIsAssociativeExt

  end IsSemigroupoid

  class IsPreCategory (M : outParam HomUniverse.{v, iv}) (α : Sort u) :
    Sort (max u (v + 1) iv) where
  (Hom                         : MetaRelation α M.V)
  [homIsPreorder               : IsPreorder               Hom]
  [homHasTransFun              : HasTransFun              Hom]
  [homIsCategoricalPreorder    : IsCategoricalPreorder    Hom]
  [homIsCategoricalPreorderExt : IsCategoricalPreorderExt Hom]

  namespace IsPreCategory

    open IsAssociative IsCategoricalPreorder HasFunctors HasCongrArg

    variable {M : HomUniverse.{v, iv}} {α : Sort u} [h : IsPreCategory.{u, v, iv} M α]

    instance : IsPreorder               h.Hom := h.homIsPreorder
    instance : HasTransFun              h.Hom := h.homHasTransFun
    instance : IsCategoricalPreorder    h.Hom := h.homIsCategoricalPreorder
    instance : IsCategoricalPreorderExt h.Hom := h.homIsCategoricalPreorderExt

    instance isSemigroupoid : IsSemigroupoid M α := ⟨h.Hom⟩

    instance : IsPreorder               (IsSemigroupoid.Hom (α := α)) := h.homIsPreorder
    instance : HasTransFun              (IsSemigroupoid.Hom (α := α)) := h.homHasTransFun
    instance : IsCategoricalPreorder    (IsSemigroupoid.Hom (α := α)) := h.homIsCategoricalPreorder
    instance : IsCategoricalPreorderExt (IsSemigroupoid.Hom (α := α)) := h.homIsCategoricalPreorderExt

    def idHom (a : α) : a ⇾ a := HasRefl.refl a

    -- A "descriptor" of a potential isomorphism. In a 1-category, each `IsoDesc` is really an
    -- isomorphism, but in higher categories, there may be additional conditions encoded in
    -- `HasIsomorphisms.Iso`.

    structure IsoDesc (a b : α) : Sort (max 1 u v iv) where
    (toHom    : a ⇾ b)
    (invHom   : b ⇾ a)
    (leftInv  : HalfInv Hom toHom invHom)
    (rightInv : HalfInv Hom invHom toHom)

    namespace IsoDesc

      -- We define a custom universe for isomorphism descriptors so that we can attach
      -- instance equivalences to them and show that `IsoDesc` satisfies
      -- `IsGroupoidEquivalence` with respect to those instance equivalences.

      instance hasInstances : HasInstances (IsoIndex.{u, max 1 v iv} α) :=
      ⟨λ i => IsoDesc i.a i.b⟩

      def univ : Universe.{max 1 u v iv} := ⟨IsoIndex.{u, max 1 v iv} α⟩

      @[reducible] def rel : MetaRelation α (univ (α := α)) := IsoIndex.mk

      infix:20 " ⇽⇾ " => CategoryTheory.IsPreCategory.IsoDesc.rel

      def refl (a : α) : a ⇽⇾ a :=
      ⟨idHom a, idHom a, HalfInv.refl Hom a, HalfInv.refl Hom a⟩

      def symm {a b : α} (e : a ⇽⇾ b) : b ⇽⇾ a :=
      ⟨e.invHom, e.toHom, e.rightInv, e.leftInv⟩

      def trans {a b c : α} (e : a ⇽⇾ b) (f : b ⇽⇾ c) : a ⇽⇾ c :=
      ⟨f.toHom • e.toHom, e.invHom • f.invHom,
       HalfInv.trans Hom e.leftInv f.leftInv, HalfInv.trans Hom f.rightInv e.rightInv⟩

      instance isEquivalence : IsEquivalence (rel (α := α)) :=
      { refl  := refl,
        symm  := symm,
        trans := trans }

      -- When checking whether two isomorphism descriptors are equivalent, checking one direction
      -- is sufficient; see `Equiv.toInvEquiv`.
      def Equiv {a b : α} (e₁ e₂ : IsoDesc a b) := e₁.toHom ≃ e₂.toHom

      namespace Equiv

        def toInvEquiv {a b : α} {e₁ e₂ : IsoDesc a b} (h : e₁.toHom ≃ e₂.toHom) :
          e₂.invHom ≃ e₁.invHom :=
        rightId e₁.invHom •
        congrArgTransRight Hom (e₂.rightInv • congrArgTransLeft Hom e₂.invHom h) e₁.invHom •
        assoc e₂.invHom e₁.toHom e₁.invHom •
        congrArgTransLeft Hom e₂.invHom (e₁.leftInv)⁻¹ •
        (leftId e₂.invHom)⁻¹

        instance hasEquivalenceRelation (a b : α) :
          HasEquivalenceRelation (a ⇽⇾ b) (HomUniverse.homEqUniv M) :=
        ⟨lift (HasInstanceEquivalences.Rel (a ⇾ b)) IsoDesc.toHom⟩

        instance hasInstanceEquivalences :
          HasInstanceEquivalences (univ (α := α)) (HomUniverse.homEqUniv M) :=
        ⟨λ i => hasEquivalenceRelation i.a i.b⟩

        def invEquiv {a b : α} {e₁ e₂ : a ⇽⇾ b} (he : e₁ ≃ e₂) :
          e₂⁻¹ ≃ e₁⁻¹ :=
        toInvEquiv he

        def rightCompEquiv {a b c : α} (e : a ⇽⇾ b)
                                       {f₁ f₂ : b ⇽⇾ c} (hf : f₁ ≃ f₂) :
          f₁ • e ≃ f₂ • e :=
        congrArgTransLeft Hom e.toHom hf

        def leftCompEquiv {a b c : α} {e₁ e₂ : a ⇽⇾ b} (he : e₁ ≃ e₂)
                                      (f : b ⇽⇾ c) :
          f • e₁ ≃ f • e₂ :=
        congrArgTransRight Hom he f.toHom

        def compEquiv {a b c : α} {e₁ e₂ : a ⇽⇾ b} (he : e₁ ≃ e₂)
                                  {f₁ f₂ : b ⇽⇾ c} (hf : f₁ ≃ f₂) :
          f₁ • e₁ ≃ f₂ • e₂ :=
        congrArgTrans Hom he hf

      end Equiv

      instance isGroupoidEquivalence : IsGroupoidEquivalence (rel (α := α)) :=
      { assoc    := λ e f g => assoc e.toHom f.toHom g.toHom,
        rightId  := λ e     => rightId e.toHom,
        leftId   := λ e     => leftId e.toHom,
        leftInv  := λ e     => e.leftInv,
        rightInv := λ e     => e.rightInv,
        reflInv  := λ a     => HasInstanceEquivalences.refl (idHom a),
        symmInv  := λ e     => HasInstanceEquivalences.refl e,
        transInv := λ f g   => HasInstanceEquivalences.refl (f⁻¹ • g⁻¹) }

    end IsoDesc

  end IsPreCategory

  class IsGroupoid (M : outParam IsoUniverse.{v, iv}) (α : Sort u) :
    Sort (max u (v + 1) iv) where
  (Iso                         : MetaRelation α M.V)
  [isoIsEquivalence            : IsEquivalence            Iso]
  [isoHasTransFun              : HasTransFun              Iso]
  [isoHasSymmFun               : HasSymmFun               Iso]
  [isoIsGroupoidEquivalence    : IsGroupoidEquivalence    Iso]
  [isoIsGroupoidEquivalenceExt : IsGroupoidEquivalenceExt Iso]

  namespace IsGroupoid

    open IsPreCategory

    variable {M : IsoUniverse.{v, iv}} {α : Sort u} [h : IsGroupoid M α]

    instance : IsEquivalence            h.Iso := h.isoIsEquivalence
    instance : HasTransFun              h.Iso := h.isoHasTransFun
    instance : HasSymmFun               h.Iso := h.isoHasSymmFun
    instance : IsGroupoidEquivalence    h.Iso := h.isoIsGroupoidEquivalence
    instance : IsGroupoidEquivalenceExt h.Iso := h.isoIsGroupoidEquivalenceExt

    instance isPreCategory : IsPreCategory M.toHomUniverse α := ⟨h.Iso⟩

    instance : IsEquivalence            (IsPreCategory.Hom (α := α)) := h.isoIsEquivalence
    instance : HasSymmFun               (IsPreCategory.Hom (α := α)) := h.isoHasSymmFun
    instance : IsGroupoidEquivalence    (IsPreCategory.Hom (α := α)) := h.isoIsGroupoidEquivalence
    instance : IsGroupoidEquivalenceExt (IsPreCategory.Hom (α := α)) := h.isoIsGroupoidEquivalenceExt

    instance : IsEquivalence            (IsSemigroupoid.Hom (α := α)) := h.isoIsEquivalence
    instance : HasSymmFun               (IsSemigroupoid.Hom (α := α)) := h.isoHasSymmFun
    instance : IsGroupoidEquivalence    (IsSemigroupoid.Hom (α := α)) := h.isoIsGroupoidEquivalence
    instance : IsGroupoidEquivalenceExt (IsSemigroupoid.Hom (α := α)) := h.isoIsGroupoidEquivalenceExt

    def isoDesc {a b : α} (e : a ⇾ b) : a ⇽⇾ b := ⟨e, e⁻¹, leftInv e, rightInv e⟩

    def isoDescReflEq (a : α) :
      isoDesc (idHom a) ≃ IsoDesc.refl a :=
    HasEquivalenceRelation.refl (idHom a)

    def isoDescSymmEq {a b : α} (e : a ⇾ b) :
      isoDesc e⁻¹ ≃ (isoDesc e)⁻¹ :=
    HasEquivalenceRelation.refl e⁻¹

    def isoDescTransEq {a b c : α} (e : a ⇾ b) (f : b ⇾ c) :
      isoDesc (f • e) ≃ isoDesc f • isoDesc e :=
    HasEquivalenceRelation.refl (f • e)

  end IsGroupoid



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

  open IsPreCategory

  class HasIsomorphisms {M : HomUniverse.{v, iv}} (α : Sort u) [IsPreCategory M α] where
  (Iso                                    : MetaRelation α M.V)
  [isoEquivalence                         : IsEquivalence Iso]
  (isoDesc {a b : α}                      : Iso a b → (a ⇽⇾ b))
  (isoDescInj {a b : α} {e₁ e₂ : Iso a b} : isoDesc e₁ ≃ isoDesc e₂ → e₁ ≃ e₂)

  namespace HasIsomorphisms

    open IsoDesc.Equiv

    infix:20 " ⇿ " => CategoryTheory.HasIsomorphisms.Iso

    section

      variable {M : HomUniverse.{v, iv}} {α : Sort u} [IsPreCategory M α]
               [h : HasIsomorphisms α]

      instance isoIsEquivalence : IsEquivalence h.Iso := h.isoEquivalence

      def idIso (a : α) : a ⇿ a := HasRefl.refl a

      def toHom  {a b : α} (e : a ⇿ b) : a ⇾ b := (isoDesc e).toHom
      def invHom {a b : α} (e : a ⇿ b) : b ⇾ a := (isoDesc e).invHom

    end

    class HasIsoDescEq {M : HomUniverse.{v, iv}} (α : Sort u) [IsPreCategory M α]
                       [HasIsomorphisms α] where
    (isoDescReflEq  (a     : α)                         :
       isoDesc (idIso a) ≃ IsoDesc.refl a)
    (isoDescSymmEq  {a b   : α} (e : a ⇿ b)             :
       isoDesc e⁻¹       ≃ (isoDesc e)⁻¹)
    (isoDescTransEq {a b c : α} (e : a ⇿ b) (f : b ⇿ c) :
       isoDesc (f • e)   ≃ isoDesc f • isoDesc e)

    namespace HasIsoDescEq

      variable {M : HomUniverse.{v, iv}} {α : Sort u} [IsPreCategory M α]
               [hIso : HasIsomorphisms α] [h : HasIsoDescEq α]

      def isoAssoc {a b c d : α} (e : a ⇿ b) (f : b ⇿ c) (g : c ⇿ d) :
        (g • f) • e ≃ g • (f • e) :=
      isoDescInj ((leftCompEquiv (isoDescTransEq e f) (isoDesc g) •
                   isoDescTransEq (f • e) g)⁻¹ •
                  assoc (isoDesc e) (isoDesc f) (isoDesc g) •
                  (rightCompEquiv (isoDesc e) (isoDescTransEq f g) •
                   isoDescTransEq e (g • f)))

      def isoRightId {a b : α} (e : a ⇿ b) : e • idIso a ≃ e :=
      isoDescInj (rightId (isoDesc e) •
                  (leftCompEquiv (isoDescReflEq a) (isoDesc e) •
                   isoDescTransEq (idIso a) e))

      def isoLeftId {a b : α} (e : a ⇿ b) : idIso b • e ≃ e :=
      isoDescInj (leftId (isoDesc e) •
                  (rightCompEquiv (isoDesc e) (isoDescReflEq b) •
                   isoDescTransEq e (idIso b)))

      def isoLeftInv {a b : α} (e : a ⇿ b) : e⁻¹ • e ≃ idIso a :=
      isoDescInj ((isoDescReflEq a)⁻¹ •
                  leftInv (isoDesc e) •
                  (rightCompEquiv (isoDesc e) (isoDescSymmEq e) •
                   isoDescTransEq e e⁻¹))

      def isoRightInv {a b : α} (e : a ⇿ b) : e • e⁻¹ ≃ idIso b :=
      isoDescInj ((isoDescReflEq b)⁻¹ •
                  rightInv (isoDesc e) •
                  (leftCompEquiv (isoDescSymmEq e) (isoDesc e) •
                   isoDescTransEq e⁻¹ e))

      def isoReflInv (a : α) : (idIso a)⁻¹ ≃ idIso a :=
      isoDescInj ((invEquiv (isoDescReflEq a) •
                   isoDescReflEq a)⁻¹ •
                  isoDescSymmEq (idIso a))

      def isoSymmInv {a b : α} (e : a ⇿ b) : (e⁻¹)⁻¹ ≃ e :=
      isoDescInj ((invEquiv (isoDescSymmEq e))⁻¹ •
                  isoDescSymmEq e⁻¹)

      def isoTransInv {a b c : α} (e : a ⇿ b) (f : b ⇿ c) : (f • e)⁻¹ ≃ e⁻¹ • f⁻¹ :=
      isoDescInj ((invEquiv (isoDescTransEq e f) •
                   compEquiv (isoDescSymmEq f) (isoDescSymmEq e) •
                   isoDescTransEq f⁻¹ e⁻¹)⁻¹ •
                  isoDescSymmEq (f • e))

      instance isoIsGroupoidEquivalence : IsGroupoidEquivalence hIso.Iso :=
      { assoc    := isoAssoc,
        rightId  := isoRightId,
        leftId   := isoLeftId,
        leftInv  := isoLeftInv,
        rightInv := isoRightInv,
        reflInv  := isoReflInv,
        symmInv  := isoSymmInv,
        transInv := isoTransInv }

    end HasIsoDescEq

    class HasIsoToHomFun {M : HomUniverse.{v, iv}} (α : Sort u) [IsPreCategory M α]
                         [hIso : HasIsomorphisms α] where
    [isoSymmFun            : HasSymmFun  hIso.Iso]
    [isoTransFun           : HasTransFun hIso.Iso]
    (defToHomFun (a b : α) : (a ⇿ b) ⟶{λ e => toHom e} (a ⇾ b))

    namespace HasIsoToHomFun

      open HasFunctors HasIsoDescEq

      section

        variable {M : HomUniverse.{v, iv}} {α : Sort u} [hPreCat : IsPreCategory M α]
                 [hIso : HasIsomorphisms α] [h : HasIsoToHomFun α]

        instance isoHasSymmFun  : HasSymmFun  hIso.Iso := h.isoSymmFun
        instance isoHasTransFun : HasTransFun hIso.Iso := h.isoTransFun

        @[reducible] def toHomFun (a b : α) : (a ⇿ b) ⟶ (a ⇾ b) := defToHomFun a b

        variable [HasIsoDescEq α]

        def defInvHomFun (a b : α) : (a ⇿ b) ⟶{λ e => invHom e} (b ⇾ a) :=
        toDefFun' (toHomFun b a • symmFun hIso.Iso a b)
                  (λ e => isoDescSymmEq e • byDef • byArgDef • byDef)

        @[reducible] def invHomFun (a b : α) : (a ⇿ b) ⟶ (b ⇾ a) :=
        defInvHomFun a b

      end

      section

        variable {M : HomUniverse.{v, iv}} (α : Sort u) [hPreCat : IsPreCategory M α]
                 [hIso : HasIsomorphisms α] [HasIsoToHomFun α] [HasIsoDescEq α]

        def toHomMetaFunctor : MetaFunctor hIso.Iso hPreCat.Hom := ⟨toHomFun⟩

        instance toHomIsPreorderFunctor : IsPreorderFunctor (toHomMetaFunctor α) :=
        { reflEq  := λ a   => isoDescReflEq a • byDef,
          transEq := λ e f => (congrArgTrans Hom byDef byDef)⁻¹ • isoDescTransEq e f • byDef }

      end

      section

        open HasIsoDescEq HasTransFun HasIsoToHomFun

        class HasIsoToHomFunExt {M : IsoUniverse.{v, iv}} (α : Sort u)
                                [IsPreCategory M.toHomUniverse α] [hIso : HasIsomorphisms α]
                                [HasIsoDescEq α] [HasIsoToHomFun α] where
        [toHomFunExt    : IsTransFunctor.IsTransFunctorExt (toHomMetaFunctor (α := α))]
        [isoGroupoidExt : IsGroupoidEquivalence.IsGroupoidEquivalenceExt hIso.Iso]

        namespace HasIsoToHomFunExt

          variable {M : IsoUniverse.{v, iv}} {α : Sort u} [IsPreCategory M.toHomUniverse α]
                   [hIso : HasIsomorphisms α] [HasIsoDescEq α] [HasIsoToHomFun α]
                   [h : HasIsoToHomFunExt α]

          instance isoHasGroupoidExt : IsGroupoidEquivalence.IsGroupoidEquivalenceExt hIso.Iso :=
          isoGroupoidExt

        end HasIsoToHomFunExt

      end

    end HasIsoToHomFun

  end HasIsomorphisms

  open HasIsomorphisms HasIsoToHomFun

  class IsCategory (M : outParam IsoUniverse.{v, iv}) (α : Sort u) extends
    IsPreCategory M.toHomUniverse α,
    HasIsomorphisms α, HasIsoDescEq α, HasIsoToHomFun α, HasIsoToHomFunExt α :
    Sort (max u (v + 1) iv)

  namespace IsCategory

    def isoGroupoid {M : IsoUniverse.{v, iv}} (α : Sort u) [h : IsCategory M α] :
      IsGroupoid M α :=
    ⟨h.Iso⟩

  end IsCategory

  namespace IsGroupoid

    variable {M : IsoUniverse.{v, iv}} (α : Sort u) [h : IsGroupoid M α]

    instance hasIsomorphisms : HasIsomorphisms α :=
    { Iso            := h.Iso,
      isoEquivalence := h.isoIsEquivalence,
      isoDesc        := isoDesc,
      isoDescInj     := id }

    instance hasIsoToHomFun : HasIsoToHomFun α :=
    { isoSymmFun  := h.isoHasSymmFun,
      isoTransFun := h.isoHasTransFun,
      defToHomFun := λ a b => defIdFun (a ⇿ b) }

    instance hasIsoDescEq : HasIsoDescEq α :=
    { isoDescReflEq  := isoDescReflEq,
      isoDescSymmEq  := isoDescSymmEq,
      isoDescTransEq := isoDescTransEq }

    instance toHomIsPreorderFunctor : IsPreorderFunctor (toHomMetaFunctor α) :=
    idFun.isPreorderFunctor h.Iso

    instance toHomIsTransFunctorExt : IsTransFunctor.IsTransFunctorExt (toHomMetaFunctor α) :=
    idFun.isTransFunctorExt h.Iso

    instance hasIsoToHomFunExt : HasIsoToHomFunExt α :=
    { toHomFunExt    := IsTransFunctor.IsTransFunctorExt.translate (toHomMetaFunctor α),
      isoGroupoidExt := IsGroupoidEquivalenceExt.translate h.Iso }

    instance isCategory : IsCategory M α := ⟨⟩

  end IsGroupoid

end CategoryTheory
