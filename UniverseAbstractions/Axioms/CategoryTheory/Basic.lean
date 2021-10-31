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
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Lemmas.DerivedFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v iv



namespace MetaRelation

  open HasFunctors HasCongrArg HasCongrFun HasLinearFunOp HasSubLinearFunOp HasFullFunOp
       HasTransFun HasSymmFun

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

  class IsSemigroupoid [HasLinearFunOp V] extends
    HasTrans R, IsAssociative R,
    HasTransFun R, IsAssociative.IsAssociativeExt R

  class IsCategoricalPreorder [IsPreorder R] extends IsAssociative R where
  (rightId {a b : α} (f : R a b) : f • HasRefl.refl a ≃ f)
  (leftId  {a b : α} (f : R a b) : HasRefl.refl b • f ≃ f)

  class IsCategoricalPreorder.IsCategoricalPreorderExt [IsPreorder R] [IsCategoricalPreorder R]
                                                       [HasTransFun R] [HasLinearFunOp V] extends
    IsAssociative.IsAssociativeExt R where
  (rightIdExt (a b : α) : transFun    R (HasRefl.refl a) b ≃{▻ λ f => rightId f ◅} idFun (R a b))
  (leftIdExt  (a b : α) : revTransFun R a (HasRefl.refl b) ≃{▻ λ f => leftId  f ◅} idFun (R a b))

  class IsPreCategory [HasLinearFunOp V] extends
    IsPreorder R, IsCategoricalPreorder R,
    HasTransFun R, IsCategoricalPreorder.IsCategoricalPreorderExt R

  def HalfInv [IsPreorder R] {a b : α} (f : R a b) (g : R b a) := g • f ≃ HasRefl.refl (R := R) a

  namespace HalfInv

    open IsAssociative IsCategoricalPreorder

    variable [HasLinearFunOp V] [IsPreCategory R]

    def refl (a : α) : HalfInv R (HasRefl.refl a) (HasRefl.refl a) :=
    rightId (HasRefl.refl a)

    def trans {a b c : α} {f₁ : R a b} {g₁ : R b a} (e₁ : HalfInv R f₁ g₁)
                          {f₂ : R b c} {g₂ : R c b} (e₂ : HalfInv R f₂ g₂) :
      HalfInv R (f₂ • f₁) (g₁ • g₂) :=
    e₁ •
    defCongrArg (defRevTransFun R a g₁) (leftId f₁ •
                                         defCongrArg (defTransFun f₁ b) e₂ •
                                         (assoc f₁ f₂ g₂)⁻¹) •
    assoc (f₂ • f₁) g₂ g₁

  end HalfInv

  namespace IsPreCategory

    variable [HasLinearFunOp V] [IsPreCategory R]

    instance isSemigroupoid : IsSemigroupoid R := ⟨⟩

    -- A "descriptor" of a potential isomorphism. In a 1-category, each `IsoDesc` is really an
    -- isomorphism, but in higher categories, there may be additional conditions encoded in
    -- `HasIsomorphisms.Iso`.

    structure IsoDesc (a b : α) where
    (f        : R a b)
    (g        : R b a)
    (leftInv  : HalfInv R f g)
    (rightInv : HalfInv R g f)

    namespace IsoDesc

      def refl (a : α) : IsoDesc R a a :=
      ⟨HasRefl.refl a, HasRefl.refl a, HalfInv.refl R a, HalfInv.refl R a⟩

      def symm {a b : α} (e : IsoDesc R a b) : IsoDesc R b a :=
      ⟨e.g, e.f, e.rightInv, e.leftInv⟩

      def trans {a b c : α} (e : IsoDesc R a b) (f : IsoDesc R b c) : IsoDesc R a c :=
      ⟨f.f • e.f, e.g • f.g,
       HalfInv.trans R e.leftInv f.leftInv, HalfInv.trans R f.rightInv e.rightInv⟩

      @[reducible] def rel : MetaRelation α sort := IsoDesc R

      instance isEquivalence : IsEquivalence (rel R) :=
      { refl  := refl  R,
        symm  := symm  R,
        trans := trans R }

      -- When checking whether two isomorphism descriptors are equivalent, checking one direction
      -- is sufficient; see `Equiv.invEquiv`.
      def Equiv {a b : α} (e₁ e₂ : IsoDesc R a b) := e₁.f ≃ e₂.f

      namespace Equiv

        open IsAssociative IsCategoricalPreorder

        def invEquiv {a b : α} {e₁ e₂ : IsoDesc R a b} (h : e₁.f ≃ e₂.f) : e₂.g ≃ e₁.g :=
        rightId e₁.g •
        defCongrArg (defRevTransFun R b e₁.g) (e₂.rightInv •
                                               defCongrArg (defTransFun e₂.g b) h) •
        assoc e₂.g e₁.f e₁.g •
        defCongrArg (defTransFun e₂.g a) (e₁.leftInv)⁻¹ •
        (leftId e₂.g)⁻¹

        def compEquiv {a b c : α} {e₁ e₂ : IsoDesc R a b} (he : e₁.f ≃ e₂.f)
                                  {f₁ f₂ : IsoDesc R b c} (hf : f₁.f ≃ f₂.f) :
          f₁.f • e₁.f ≃ f₂.f • e₂.f :=
        defCongrArg (defRevTransFun R a f₂.f) he •
        defCongrArg (defTransFun e₁.f c) hf

        -- Enable writing `Equiv e₁ e₂` as `e₁ ≃ e₂`.
        instance hasEquivalenceRelation (a b : α) :
          HasEquivalenceRelation (IsoDesc R a b) (HasIdentity.univ V) :=
        ⟨lift (HasInstanceEquivalences.Rel (R a b)) IsoDesc.f⟩

        def symmEquiv {a b : α} {e₁ e₂ : IsoDesc R a b} (he : e₁ ≃ e₂) :
          symm R e₂ ≃ symm R e₁ :=
        invEquiv R he

        def transEquiv {a b c : α} {e₁ e₂ : IsoDesc R a b} (he : e₁ ≃ e₂)
                                   {f₁ f₂ : IsoDesc R b c} (hf : f₁ ≃ f₂) :
          trans R e₁ f₁ ≃ trans R e₂ f₂ :=
        compEquiv R he hf

      end Equiv

    end IsoDesc

  end IsPreCategory

  class IsGroupoidEquivalence [IsEquivalence R] extends IsCategoricalPreorder R where
  (leftInv  {a b : α} (f : R a b) : HalfInv R f f⁻¹)
  (rightInv {a b : α} (f : R a b) : HalfInv R f⁻¹ f)

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
  -- The definition is split into three parts because some parts are often trivial.

  class HasIsomorphisms [HasFullFunOp V] [IsPreCategory R] where
  (Iso                     : MetaRelation α V)
  [isoGroupoid             : IsGroupoid Iso]
  (isoDesc       {a b : α} : Iso a b → IsPreCategory.IsoDesc R a b)
  (defIsoElimFun (a b : α) : Iso a b ⟶{λ e => (isoDesc e).f} R a b)

  namespace HasIsomorphisms

    open HasFunctors IsPreCategory

    variable [HasFullFunOp V] [IsPreCategory R] [h : HasIsomorphisms R]

    -- Enable writing `Iso R a b` as `a ≃ b`.
    instance isoIsGroupoid : IsGroupoid h.Iso := h.isoGroupoid
    instance hasEquivalenceRelation : HasEquivalenceRelation α V := ⟨h.Iso⟩

    @[reducible] def isoElimFun (a b : α) : a ≃ b ⟶ R a b := fromDefFun (h.defIsoElimFun a b)

    class HasIsoEq where
    (isoReflEq  (a     : α)                         :
       isoDesc (HasEquivalenceRelation.refl a) ≃ IsoDesc.refl  R a)
    (isoSymmEq  {a b   : α} (e : a ≃ b)             :
       isoDesc e⁻¹                             ≃ IsoDesc.symm  R (isoDesc e))
    (isoTransEq {a b c : α} (e : a ≃ b) (f : b ≃ c) :
       isoDesc (f • e)                         ≃ IsoDesc.trans R (isoDesc e) (isoDesc f))

    -- Note: There is no `isoSymmEqExt` because `IsoDesc.symm` is not functorial in the way
    -- `IsoDesc.trans` is.
    class HasIsoEq.HasIsoEqExt [HasIsoEq R] where
    (isoTransEqExt {a b : α} (e : a ≃ b) (c : α) :
       isoElimFun R a c • transFun h.Iso e c
       ≃{byDef • byArgDef ▻ λ f => isoTransEq e f ◅ byDef • byArgDef}
       transFun R (isoDesc e).f c • isoElimFun R b c)
    (isoTransEqExtExt (a b c : α) :
       revCompFunFun (b ≃ c) (isoElimFun R a c) • transFunFun h.Iso a b c
       ≃{byDef • byArgDef ▻ λ e => isoTransEqExt e c ◅ byDef • byArgDef • byArgDef₂ • byArgDef}
       compFunFun (isoElimFun R b c) (R a c) • transFunFun R a b c • isoElimFun R a b)

  end HasIsomorphisms

  class IsCategory [HasFullFunOp V] extends
    IsPreCategory R,
    HasIsomorphisms R, HasIsomorphisms.HasIsoEq R, HasIsomorphisms.HasIsoEq.HasIsoEqExt R

end MetaRelation
