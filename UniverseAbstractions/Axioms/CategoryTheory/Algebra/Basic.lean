/-
Formalization of (potentially weak) semigroups, monoids, and groups, as single-object variants of
the corresponding definitions in `CategoryTheory/Basic.lean`.

This enables the use of existing extensionality definitions from `CategoryTheory/Extensional`. In
particular, if `U` is `IsCategory.univ type`, i.e. the universe of 1-categories, and thus `A : U`
is a category, then `IsMonoidExt A` turns `A` into a monoidal category.
-/



import UniverseAbstractions.Axioms.CategoryTheory.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe x u uu



namespace Algebra

  open MetaRelation CategoryTheory

  variable {U : Universe.{u, uu}} [IsHomUniverse U]

  def unitRel (A : U) := unitRelation PUnit.{x} A

  -- Implicitly treat all instances of `A` as instances of `(unitRel A) _ _` so that type
  -- classes on `unitRel A` are found.
  local instance (priority := high) coeSort : CoeSort U (Sort u) :=
  ⟨λ A => (unitRel.{x} A) PUnit.unit PUnit.unit⟩

  class IsSemigroup (A : U) where
  [hasTrans      : HasTrans      (unitRel.{x} A)]
  [hasTransFun   : HasTransFun   (unitRel.{x} A)]
  [isAssociative : IsAssociative (unitRel.{x} A)]

  namespace IsSemigroup

    section

      variable (A : U) [h : IsSemigroup A]

      instance : HasTrans      (unitRel.{x} A) := h.hasTrans
      instance : HasTransFun   (unitRel.{x} A) := h.hasTransFun
      instance : IsAssociative (unitRel.{x} A) := h.isAssociative

      def semicatDesc : SemicatDesc ⟨unitRel.{x} A⟩ :=
      { homHasTrans      := h.hasTrans,
        homHasTransFun   := h.hasTransFun,
        homIsAssociative := h.isAssociative }

    end

    variable {A : U} [h : IsSemigroup A]

    def assoc₄ (a b c d : A) : ((d • c) • b) • a ≃ d • (c • (b • a)) :=
    IsAssociative.assoc₄ a b c d

  end IsSemigroup

  class IsMonoid (A : U) where
  [isPreorder            : IsPreorder            (unitRel.{x} A)]
  [hasTransFun           : HasTransFun           (unitRel.{x} A)]
  [isCategoricalPreorder : IsCategoricalPreorder (unitRel.{x} A)]

  namespace IsMonoid

    variable (A : U) [h : IsMonoid A]

    instance : HasRefl               (unitRel.{x} A) := h.isPreorder.toHasRefl
    instance : HasTrans              (unitRel.{x} A) := h.isPreorder.toHasTrans
    instance : IsPreorder            (unitRel.{x} A) := h.isPreorder
    instance : HasTransFun           (unitRel.{x} A) := h.hasTransFun
    instance : IsCategoricalPreorder (unitRel.{x} A) := h.isCategoricalPreorder

    instance isSemigroup : IsSemigroup A := ⟨⟩

    def categoryDesc : CatDesc ⟨unitRel.{x} A⟩ :=
    { homIsPreorder            := h.isPreorder,
      homHasTransFun           := h.hasTransFun,
      homIsCategoricalPreorder := h.isCategoricalPreorder }

  end IsMonoid

  class IsGroup (A : U) where
  [isEquivalence         : IsEquivalence         (unitRel.{x} A)]
  [hasSymmFun            : HasSymmFun            (unitRel.{x} A)]
  [hasTransFun           : HasTransFun           (unitRel.{x} A)]
  [isGroupoidEquivalence : IsGroupoidEquivalence (unitRel.{x} A)]

  namespace IsGroup

    variable (A : U) [h : IsGroup A]

    instance : HasRefl               (unitRel.{x} A) := h.isEquivalence.toHasRefl
    instance : HasSymm               (unitRel.{x} A) := h.isEquivalence.toHasSymm
    instance : HasTrans              (unitRel.{x} A) := h.isEquivalence.toHasTrans
    instance : IsEquivalence         (unitRel.{x} A) := h.isEquivalence
    instance : HasTransFun           (unitRel.{x} A) := h.hasTransFun
    instance : HasSymmFun            (unitRel.{x} A) := h.hasSymmFun
    instance : IsGroupoidEquivalence (unitRel.{x} A) := h.isGroupoidEquivalence

    instance isMonoid : IsMonoid A := ⟨⟩

    def groupoidDesc : GrpoidDesc ⟨unitRel.{x} A⟩ :=
    { homIsEquivalence         := h.isEquivalence,
      homHasSymmFun            := h.hasSymmFun,
      homHasTransFun           := h.hasTransFun,
      homIsGroupoidEquivalence := h.isGroupoidEquivalence }

  end IsGroup

end Algebra
