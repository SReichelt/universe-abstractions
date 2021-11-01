/-
A version of higher category that works for universes, i.e. every universe with functors (more
specifically, with full functor operations and extensionality) and equivalences is a category
according to this definition.

The definitions extend reflexivity, symmetry, and transitivity defined on `MetaRelation`, by
specifying that instances of `R a b` have well-behaved instance equivalences.
-/



import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Relations
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Lemmas.DerivedFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v iv



namespace MetaRelation

  open HasFunctors HasCongrArg HasCongrFun HasLinearFunOp HasSubLinearFunOp HasFullFunOp
       HasTransFun HasSymmFun

  structure IsoIndex (α : Sort u) : Type (max u v) where
  (a b : α)

  variable {α : Sort u} {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasInternalFunctors V]
           (R : MetaRelation α V)



  class IsAssociative [HasTrans R] where
  (assoc {a b c d : α} (f : R a b) (g : R b c) (h : R c d) : (h • g) • f ≃ h • (g • f))

  class IsAssociative.IsAssociativeExt [HasTrans R] [IsAssociative R] [HasTransFun R]
                                       [HasLinearFunOp V] where
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

  class IsCategoricalPreorder [IsPreorder R] extends IsAssociative R where
  (rightId {a b : α} (f : R a b) : f • HasRefl.refl a ≃ f)
  (leftId  {a b : α} (f : R a b) : HasRefl.refl b • f ≃ f)

  class IsCategoricalPreorder.IsCategoricalPreorderExt [IsPreorder R] [IsCategoricalPreorder R]
                                                       [HasTransFun R] [HasLinearFunOp V] extends
    IsAssociative.IsAssociativeExt R where
  (rightIdExt (a b : α) : transFun    R (HasRefl.refl a) b ≃{▻ λ f => rightId f ◅} idFun (R a b))
  (leftIdExt  (a b : α) : revTransFun R a (HasRefl.refl b) ≃{▻ λ f => leftId  f ◅} idFun (R a b))

  def HalfInv [IsPreorder R] {a b : α} (f : R a b) (g : R b a) := g • f ≃ HasRefl.refl (R := R) a

  namespace HalfInv

    open IsAssociative IsCategoricalPreorder

    variable [IsPreorder R] [IsCategoricalPreorder R]

    def refl (a : α) : HalfInv R (HasRefl.refl a) (HasRefl.refl a) :=
    rightId (HasRefl.refl a)

    variable [HasTransFun R] [HasLinearFunOp V]

    def trans {a b c : α} {f₁ : R a b} {g₁ : R b a} (e₁ : HalfInv R f₁ g₁)
                          {f₂ : R b c} {g₂ : R c b} (e₂ : HalfInv R f₂ g₂) :
      HalfInv R (f₂ • f₁) (g₁ • g₂) :=
    e₁ •
    defCongrArg (defRevTransFun R a g₁) (leftId f₁ •
                                         defCongrArg (defTransFun f₁ b) e₂ •
                                         (assoc f₁ f₂ g₂)⁻¹) •
    assoc (f₂ • f₁) g₂ g₁

  end HalfInv

  -- Although the last three equivalences can be derived from the first two, we redundantly assert
  -- them as axioms to reduce the complexity of terms. In particular, they hold definitionally for
  -- `IsoDesc`.
  class IsGroupoidEquivalence [IsEquivalence R] extends IsCategoricalPreorder R where
  (leftInv  {a b   : α} (f : R a b)             : HalfInv R f f⁻¹)
  (rightInv {a b   : α} (f : R a b)             : HalfInv R f⁻¹ f)
  (reflInv  (a     : α)                         : (HasRefl.refl (R := R) a)⁻¹ ≃ HasRefl.refl (R := R) a)
  (symmInv  {a b   : α} (f : R a b)             : (f⁻¹)⁻¹ ≃ f)
  (transInv {a b c : α} (f : R a b) (g : R b c) : (g • f)⁻¹ ≃ f⁻¹ • g⁻¹)

  class IsGroupoidEquivalence.IsGroupoidEquivalenceExt [IsEquivalence R] [IsGroupoidEquivalence R]
                                                       [HasTransFun R] [HasSymmFun R]
                                                       [HasFullFunOp V] extends
    IsCategoricalPreorder.IsCategoricalPreorderExt R where
  (leftInvExt  (a b : α) : substFun (symmFun R a b) (transFunFun    R a b a)
                           ≃{byDef • byArgDef • byFunDef ▻ λ f => leftInv  f ◅}
                           constFun (R a b) (HasRefl.refl a))
  (rightInvExt (a b : α) : substFun (symmFun R a b) (revTransFunFun R b a b)
                           ≃{byDef • byArgDef • byFunDef ▻ λ f => rightInv f ◅}
                           constFun (R a b) (HasRefl.refl b))
  (symmInvExt  (a b : α) : symmFun R b a • symmFun R a b
                           ≃{byDef • byArgDef ▻ λ f => symmInv f ◅}
                           idFun (R a b))
  (transInvExt {a b : α} (f : R a b) (c : α) :
     symmFun R a c • transFun R f c
     ≃{byDef • byArgDef ▻ λ g => transInv f g ◅ byDef • byArgDef}
     revTransFun R c f⁻¹ • symmFun R b c)
  (transInvExtExt (a b c : α) :
     revCompFunFun (R b c) (symmFun R a c) • transFunFun R a b c
     ≃{byDef • byArgDef ▻ λ f => transInvExt f c ◅ byDef • byArgDef • byArgDef₂ • byArgDef}
     compFunFun (symmFun R b c) (R c a) • revTransFunFun R c b a • symmFun R a b)



  class IsSemigroupoid [HasLinearFunOp V] extends
    HasTrans R, IsAssociative R,
    HasTransFun R, IsAssociative.IsAssociativeExt R

  class IsPreCategory [HasLinearFunOp V] extends
    IsPreorder R, IsCategoricalPreorder R,
    HasTransFun R, IsCategoricalPreorder.IsCategoricalPreorderExt R

  namespace IsPreCategory

    open IsAssociative IsCategoricalPreorder

    variable [HasLinearFunOp V] [IsPreCategory R]

    instance isSemigroupoid : IsSemigroupoid R := ⟨⟩

    -- A "descriptor" of a potential isomorphism. In a 1-category, each `IsoDesc` is really an
    -- isomorphism, but in higher categories, there may be additional conditions encoded in
    -- `HasIsomorphisms.Iso`.

    structure IsoDesc (a b : α) : Sort (max 1 u v iv) where
    (f        : R a b)
    (g        : R b a)
    (leftInv  : HalfInv R f g)
    (rightInv : HalfInv R g f)

    namespace IsoDesc

      -- We define a custom universe for isomorphism descriptors so that we can attach
      -- instance equivalences to them and show that `IsoDesc` satisfies
      -- `IsGroupoidEquivalence` with respect to those instance equivalences.

      instance hasInstances : HasInstances (IsoIndex.{u, max 1 v iv} α) :=
      ⟨λ i => IsoDesc R i.a i.b⟩

      def univ : Universe.{max 1 u v iv} := ⟨IsoIndex.{u, max 1 v iv} α⟩

      @[reducible] def rel : MetaRelation α (univ R) := IsoIndex.mk

      def refl (a : α) : (rel R) a a :=
      ⟨HasRefl.refl a, HasRefl.refl a, HalfInv.refl R a, HalfInv.refl R a⟩

      def symm {a b : α} (e : (rel R) a b) : (rel R) b a :=
      ⟨e.g, e.f, e.rightInv, e.leftInv⟩

      def trans {a b c : α} (e : (rel R) a b) (f : (rel R) b c) : (rel R) a c :=
      ⟨f.f • e.f, e.g • f.g,
       HalfInv.trans R e.leftInv f.leftInv, HalfInv.trans R f.rightInv e.rightInv⟩

      instance isEquivalence : IsEquivalence (rel R) :=
      { refl  := refl  R,
        symm  := symm  R,
        trans := trans R }

      -- When checking whether two isomorphism descriptors are equivalent, checking one direction
      -- is sufficient; see `Equiv.invEquiv`.
      def Equiv {a b : α} (e₁ e₂ : IsoDesc R a b) := e₁.f ≃ e₂.f

      namespace Equiv

        def invEquiv {a b : α} {e₁ e₂ : IsoDesc R a b} (h : e₁.f ≃ e₂.f) : e₂.g ≃ e₁.g :=
        rightId e₁.g •
        defCongrArg (defRevTransFun R b e₁.g) (e₂.rightInv •
                                               defCongrArg (defTransFun e₂.g b) h) •
        assoc e₂.g e₁.f e₁.g •
        defCongrArg (defTransFun e₂.g a) (e₁.leftInv)⁻¹ •
        (leftId e₂.g)⁻¹

        def rightCompEquiv {a b c : α} (e : IsoDesc R a b)
                                       {f₁ f₂ : IsoDesc R b c} (hf : f₁.f ≃ f₂.f) :
          f₁.f • e.f ≃ f₂.f • e.f :=
        defCongrArg (defTransFun e.f c) hf

        def leftCompEquiv {a b c : α} {e₁ e₂ : IsoDesc R a b} (he : e₁.f ≃ e₂.f)
                                      (f : IsoDesc R b c) :
          f.f • e₁.f ≃ f.f • e₂.f :=
        defCongrArg (defRevTransFun R a f.f) he

        def compEquiv {a b c : α} {e₁ e₂ : IsoDesc R a b} (he : e₁.f ≃ e₂.f)
                                  {f₁ f₂ : IsoDesc R b c} (hf : f₁.f ≃ f₂.f) :
          f₁.f • e₁.f ≃ f₂.f • e₂.f :=
        leftCompEquiv R he f₂ • rightCompEquiv R e₁ hf

        instance hasEquivalenceRelation (a b : α) :
          HasEquivalenceRelation ((rel R) a b) (HasIdentity.univ V) :=
        ⟨lift (HasInstanceEquivalences.Rel (R a b)) IsoDesc.f⟩

        instance hasInstanceEquivalences :
          HasInstanceEquivalences (univ R) (HasIdentity.univ V) :=
        ⟨λ i => hasEquivalenceRelation R i.a i.b⟩

        def symmEquiv {a b : α} {e₁ e₂ : (rel R) a b} (he : e₁ ≃ e₂) :
          e₂⁻¹ ≃ e₁⁻¹ :=
        invEquiv R he

        def rightTransEquiv {a b c : α} (e : (rel R) a b)
                                        {f₁ f₂ : (rel R) b c} (hf : f₁ ≃ f₂) :
          f₁ • e ≃ f₂ • e :=
        rightCompEquiv R e hf

        def leftTransEquiv {a b c : α} {e₁ e₂ : (rel R) a b} (he : e₁ ≃ e₂)
                                       (f : (rel R) b c) :
          f • e₁ ≃ f • e₂ :=
        leftCompEquiv R he f

        def transEquiv {a b c : α} {e₁ e₂ : (rel R) a b} (he : e₁ ≃ e₂)
                                   {f₁ f₂ : (rel R) b c} (hf : f₁ ≃ f₂) :
          f₁ • e₁ ≃ f₂ • e₂ :=
        compEquiv R he hf

      end Equiv

      instance isGroupoidEquivalence : IsGroupoidEquivalence (rel R) :=
      { assoc    := λ e f g => assoc e.f f.f g.f,
        rightId  := λ e     => rightId e.f,
        leftId   := λ e     => leftId e.f,
        leftInv  := λ e     => e.leftInv,
        rightInv := λ e     => e.rightInv,
        reflInv  := λ a     => HasInstanceEquivalences.refl (HasRefl.refl (R := R) a),
        symmInv  := λ e     => HasInstanceEquivalences.refl e,
        transInv := λ f g   => HasInstanceEquivalences.refl (f⁻¹ • g⁻¹) }

    end IsoDesc

  end IsPreCategory

  class IsGroupoid [HasFullFunOp V] extends
    IsEquivalence R, IsGroupoidEquivalence R,
    HasTransFun R, HasSymmFun R, IsGroupoidEquivalence.IsGroupoidEquivalenceExt R

  namespace IsGroupoid

    open IsPreCategory IsGroupoidEquivalence

    variable [HasFullFunOp V] [IsGroupoid R]

    instance isPreCategory : IsPreCategory R := ⟨⟩

    def isoDesc {a b : α} (f : R a b) : IsoDesc R a b :=
    ⟨f, f⁻¹, leftInv f, rightInv f⟩

  end IsGroupoid



  -- We define a category to be a precategory that is additionally enriched with isomorphisms.
  -- Like morphisms, they are also in `V`, and they need to map to `IsoDesc` but may be subject to
  -- further conditions beyond `IsoDesc`.
  -- The definition is split into several parts because some parts are trivial in simple
  -- categories, and to reduce redundancies in nontrivial parts. In particular, the groupoid laws
  -- of isomorphisms follow from injectivity and functoriality of `isoDesc`; however the
  -- extensionality of these laws needs to be specified separately.

  class HasIsomorphisms [HasLinearFunOp V] [IsPreCategory R] where
  (Iso                                    : MetaRelation α V)
  [isoEquivalence                         : IsEquivalence Iso]
  (isoDesc {a b : α}                      : Iso a b → (IsPreCategory.IsoDesc.rel R) a b)
  (isoDescInj {a b : α} {e₁ e₂ : Iso a b} : isoDesc e₁ ≃ isoDesc e₂ → e₁ ≃ e₂)

  namespace HasIsomorphisms

    open HasFunctors IsAssociative IsCategoricalPreorder IsGroupoidEquivalence IsPreCategory IsoDesc.Equiv

    section

      variable [HasLinearFunOp V] [IsPreCategory R] [h : HasIsomorphisms R]

      instance isoIsEquivalence : IsEquivalence h.Iso := h.isoEquivalence

      class HasIsoDescEq where
      (isoDescReflEq  (a     : α)                         :
         isoDesc (HasRefl.refl (R := Iso R) a) ≃ IsoDesc.refl R a)
      (isoDescSymmEq  {a b   : α} (e : Iso R a b)             :
         isoDesc e⁻¹                           ≃ (isoDesc e)⁻¹)
      (isoDescTransEq {a b c : α} (e : Iso R a b) (f : Iso R b c) :
         isoDesc (f • e)                       ≃ isoDesc f • isoDesc e)

      namespace HasIsoDescEq

        variable [HasIsoDescEq R]

        def isoAssoc {a b c d : α} (e : Iso R a b) (f : Iso R b c) (g : Iso R c d) :
          (g • f) • e ≃ g • (f • e) :=
        isoDescInj ((leftTransEquiv R (isoDescTransEq e f) (isoDesc g) •
                     isoDescTransEq (f • e) g)⁻¹ •
                    assoc (isoDesc e) (isoDesc f) (isoDesc g) •
                    (rightTransEquiv R (isoDesc e) (isoDescTransEq f g) •
                     isoDescTransEq e (g • f)))

        def isoRightId {a b : α} (e : Iso R a b) : e • HasRefl.refl a ≃ e :=
        isoDescInj (rightId (isoDesc e) •
                    (leftTransEquiv R (isoDescReflEq a) (isoDesc e) •
                     isoDescTransEq (HasRefl.refl a) e))

        def isoLeftId {a b : α} (e : Iso R a b) : HasRefl.refl b • e ≃ e :=
        isoDescInj (leftId (isoDesc e) •
                    (rightTransEquiv R (isoDesc e) (isoDescReflEq b) •
                     isoDescTransEq e (HasRefl.refl b)))

        def isoLeftInv {a b : α} (e : Iso R a b) : e⁻¹ • e ≃ HasRefl.refl (R := Iso R) a :=
        isoDescInj ((isoDescReflEq a)⁻¹ •
                    leftInv (isoDesc e) •
                    (rightTransEquiv R (isoDesc e) (isoDescSymmEq e) •
                     isoDescTransEq e e⁻¹))

        def isoRightInv {a b : α} (e : Iso R a b) : e • e⁻¹ ≃ HasRefl.refl (R := Iso R) b :=
        isoDescInj ((isoDescReflEq b)⁻¹ •
                    rightInv (isoDesc e) •
                    (leftTransEquiv R (isoDescSymmEq e) (isoDesc e) •
                     isoDescTransEq e⁻¹ e))

        def isoReflInv (a : α) : (HasRefl.refl (R := Iso R) a)⁻¹ ≃ HasRefl.refl (R := Iso R) a :=
        isoDescInj ((symmEquiv R (isoDescReflEq a) •
                     isoDescReflEq a)⁻¹ •
                    isoDescSymmEq (HasRefl.refl a))

        def isoSymmInv {a b : α} (e : Iso R a b) : (e⁻¹)⁻¹ ≃ e :=
        isoDescInj ((symmEquiv R (isoDescSymmEq e))⁻¹ •
                    isoDescSymmEq e⁻¹)

        def isoTransInv {a b c : α} (e : Iso R a b) (f : Iso R b c) : (f • e)⁻¹ ≃ e⁻¹ • f⁻¹ :=
        isoDescInj ((symmEquiv R (isoDescTransEq e f) •
                     transEquiv R (isoDescSymmEq f) (isoDescSymmEq e) •
                     isoDescTransEq f⁻¹ e⁻¹)⁻¹ •
                    isoDescSymmEq (f • e))

        instance isoIsGroupoidEquivalence : IsGroupoidEquivalence h.Iso :=
        { assoc    := isoAssoc    R,
          rightId  := isoRightId  R,
          leftId   := isoLeftId   R,
          leftInv  := isoLeftInv  R,
          rightInv := isoRightInv R,
          reflInv  := isoReflInv  R,
          symmInv  := isoSymmInv  R,
          transInv := isoTransInv R }

      end HasIsoDescEq

      class HasIsoElimFun where
      [isoSymmFun              : HasSymmFun  h.Iso]
      [isoTransFun             : HasTransFun h.Iso]
      (defIsoElimFun (a b : α) : Iso R a b ⟶{λ e => (isoDesc e).f} R a b)

      namespace HasIsoElimFun

        variable [HasIsoElimFun R]

        instance isoHasSymmFun  : HasSymmFun  h.Iso := isoSymmFun
        instance isoHasTransFun : HasTransFun h.Iso := isoTransFun

        @[reducible] def isoElimFun (a b : α) : Iso R a b ⟶ R a b := fromDefFun (defIsoElimFun a b)

      end HasIsoElimFun

    end

    section

      open HasIsoDescEq HasTransFun HasIsoElimFun

      variable [HasFullFunOp V] [IsPreCategory R] [h : HasIsomorphisms R]
               [HasIsoDescEq R] [HasIsoElimFun R]

      -- Note: There is no `isoSymmEqExt` because `IsoDesc.symm` is not functorial in the way
      -- `IsoDesc.trans` is: Functoriality of `IsoDesc.trans` really refers specifically to
      -- `IsoDesc.f`, whereas we do not say anything about `IsoDesc.g`.
      class HasIsoDescEq.HasIsoDescEqExt where
      (isoDescTransEqExt {a b : α} (e : Iso R a b) (c : α) :
         isoElimFun R a c • transFun h.Iso e c
         ≃{byDef • byArgDef ▻ λ f => isoDescTransEq e f ◅ byDef • byArgDef}
         transFun R (isoDesc e).f c • isoElimFun R b c)
      (isoDescTransEqExtExt (a b c : α) :
         revCompFunFun (Iso R b c) (isoElimFun R a c) • transFunFun h.Iso a b c
         ≃{byDef • byArgDef ▻ λ e => isoDescTransEqExt e c ◅ byDef • byArgDef • byArgDef₂ • byArgDef}
         compFunFun (isoElimFun R b c) (R a c) • transFunFun R a b c • isoElimFun R a b)
      [isoGroupoidExt : IsGroupoidEquivalence.IsGroupoidEquivalenceExt h.Iso]

      namespace HasIsoDescEq.HasIsoDescEqExt

        variable [HasIsoDescEqExt R]

        instance isoHasGroupoidExt : IsGroupoidEquivalence.IsGroupoidEquivalenceExt h.Iso :=
        isoGroupoidExt

        instance isoIsGroupoid : IsGroupoid h.Iso := ⟨⟩

      end HasIsoDescEq.HasIsoDescEqExt

    end

  end HasIsomorphisms

  class IsCategory [HasFullFunOp V] extends
    IsPreCategory R, HasIsomorphisms R, HasIsomorphisms.HasIsoDescEq R,
    HasIsomorphisms.HasIsoElimFun R, HasIsomorphisms.HasIsoDescEq.HasIsoDescEqExt R

end MetaRelation
