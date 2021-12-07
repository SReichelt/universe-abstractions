/-
A version of higher category that works for universes, i.e. every universe with functors (more
specifically, with linear functor operations and extensionality) is a category according to this
definition. If a universe has equivalences, those are isomorphisms in that category.
-/



import UniverseAbstractions.Axioms.CategoryTheory.Meta



set_option autoBoundImplicitLocal false
--set_option pp.universes true
set_option synthInstance.maxHeartbeats 1000

universe u v vv w ww iv ivv iw



namespace CategoryTheory

  open MetaRelation MetaFunctor MetaQuantification HasTransFun HasSymmFun IsAssociative
       IsCategoricalPreorder IsGroupoidEquivalence

  class HasMorphisms (V : outParam Universe.{v, vv}) (α : Sort u) : Sort (max 1 u vv) where
  (Hom : MetaRelation α V)

  infix:20 " ⇾ " => CategoryTheory.HasMorphisms.Hom

  class IsSemicategory (V : outParam Universe.{v, vv}) [outParam (HasIdentity.{v, iv} V)]
                       [outParam (HasLinearFunctors V)] (α : Sort u) extends
    HasMorphisms V α : Sort (max 1 u v vv iv) where
  [homHasTrans         : HasTrans         Hom]
  [homHasTransFun      : HasTransFun      Hom]
  [homIsAssociative    : IsAssociative    Hom]
  [homIsAssociativeExt : IsAssociativeExt Hom]

  namespace IsSemicategory

    variable {V : Universe.{v, vv}} [HasIdentity.{v, iv} V] [HasLinearFunctors V] {α : Sort u}
             [h : IsSemicategory V α]

    instance : HasTrans         h.Hom := h.homHasTrans
    instance : HasTransFun      h.Hom := h.homHasTransFun
    instance : IsAssociative    h.Hom := h.homIsAssociative
    instance : IsAssociativeExt h.Hom := h.homIsAssociativeExt

  end IsSemicategory

  class IsCategory (V : outParam Universe.{v, vv}) [outParam (HasIdentity.{v, iv} V)]
                   [outParam (HasLinearFunctors V)] (α : Sort u) extends
    HasMorphisms V α : Sort (max 1 u v vv iv) where
  [homIsPreorder               : IsPreorder               Hom]
  [homHasTransFun              : HasTransFun              Hom]
  [homIsCategoricalPreorder    : IsCategoricalPreorder    Hom]
  [homIsCategoricalPreorderExt : IsCategoricalPreorderExt Hom]

  namespace IsCategory

    variable {V : Universe.{v, vv}} [HasIdentity.{v, iv} V] [HasLinearFunctors V] {α : Sort u}
             [hCat : IsCategory V α]

    instance : IsPreorder               hCat.Hom := hCat.homIsPreorder
    instance : HasTransFun              hCat.Hom := hCat.homHasTransFun
    instance : IsCategoricalPreorder    hCat.Hom := hCat.homIsCategoricalPreorder
    instance : IsCategoricalPreorderExt hCat.Hom := hCat.homIsCategoricalPreorderExt

    instance isSemicategory : IsSemicategory V α := ⟨⟩

    def idHom (a : α) : a ⇾ a := HasRefl.refl a

  end IsCategory

  class IsGroupoid (V : outParam Universe.{v, vv}) [outParam (HasIdentity.{v, iv} V)]
                   [outParam (HasStandardFunctors V)] (α : Sort u) extends
    HasMorphisms V α : Sort (max 1 u v vv iv) where
  [homIsEquivalence            : IsEquivalence            Hom]
  [homHasSymmFun               : HasSymmFun               Hom]
  [homHasTransFun              : HasTransFun              Hom]
  [homIsGroupoidEquivalence    : IsGroupoidEquivalence    Hom]
  [homIsGroupoidEquivalenceExt : IsGroupoidEquivalenceExt Hom]

  namespace IsGroupoid

    variable {V : Universe.{v, vv}} [HasIdentity.{v, iv} V] [HasStandardFunctors V] {α : Sort u}
             [hGrp : IsGroupoid V α]

    instance : IsEquivalence            hGrp.Hom := hGrp.homIsEquivalence
    instance : HasTransFun              hGrp.Hom := hGrp.homHasTransFun
    instance : HasSymmFun               hGrp.Hom := hGrp.homHasSymmFun
    instance : IsGroupoidEquivalence    hGrp.Hom := hGrp.homIsGroupoidEquivalence
    instance : IsGroupoidEquivalenceExt hGrp.Hom := hGrp.homIsGroupoidEquivalenceExt

    instance isCategory : IsCategory V α := ⟨⟩

  end IsGroupoid



  class IsMorphismFunctor {W : Universe.{w, ww}} [HasIdentity.{w, iw} W] [HasInternalFunctors W]
                          {α : Sort u} {β : Sort v}
                          [hα : HasMorphisms W α] [hβ : HasMorphisms W β]
                          (φ : α → β) where
  (F : PreFunctor hα.Hom hβ.Hom φ)

  class IsSemicategoryFunctor {W : Universe.{w, ww}} [HasIdentity.{w, iw} W] [HasLinearFunctors W]
                              {α : Sort u} {β : Sort v}
                              [hα : IsSemicategory W α] [hβ : IsSemicategory W β]
                              (φ : α → β) extends
    IsMorphismFunctor φ where
  [hTrans    : IsTransFunctor                   F]
  [hTransExt : IsTransFunctor.IsTransFunctorExt F]

  namespace IsSemicategoryFunctor

    variable {W : Universe.{w, ww}} [HasIdentity.{w, iw} W] [HasLinearFunctors W]
             {α : Sort u} {β : Sort v}
             [IsSemicategory W α] [IsSemicategory W β]
             (φ : α → β) [hφ : IsSemicategoryFunctor φ]

    instance : IsTransFunctor                   hφ.F := hφ.hTrans
    instance : IsTransFunctor.IsTransFunctorExt hφ.F := hφ.hTransExt

  end IsSemicategoryFunctor

  class IsCategoryFunctor {W : Universe.{w, ww}} [HasIdentity.{w, iw} W] [HasLinearFunctors W]
                          {α : Sort u} {β : Sort v}
                          [hα : IsCategory W α] [hβ : IsCategory W β]
                          (φ : α → β) extends
    IsMorphismFunctor φ where
  [hPreorder : IsPreorderFunctor                F]
  [hTransExt : IsTransFunctor.IsTransFunctorExt F]

  namespace IsCategoryFunctor

    variable {W : Universe.{w, ww}} [HasIdentity.{w, iw} W] [HasLinearFunctors W]
             {α : Sort u} {β : Sort v}
             [hα : IsCategory W α] [hβ : IsCategory W β]
             (φ : α → β) [hφ : IsCategoryFunctor φ]

    instance : IsPreorderFunctor                hφ.F := hφ.hPreorder
    instance : IsTransFunctor.IsTransFunctorExt hφ.F := hφ.hTransExt

    instance isSemicategoryFunctor : IsSemicategoryFunctor φ := ⟨⟩

  end IsCategoryFunctor

  class IsGroupoidFunctor {W : Universe.{w, ww}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]
                          {α : Sort u} {β : Sort v}
                          [hα : IsGroupoid W α] [hβ : IsGroupoid W β]
                          (φ : α → β) extends
    IsMorphismFunctor φ where
  [hEquivalence : IsEquivalenceFunctor             F]
  [hSymmExt     : IsSymmFunctor.IsSymmFunctorExt   F]
  [hTransExt    : IsTransFunctor.IsTransFunctorExt F]

  namespace IsGroupoidFunctor

    variable {W : Universe.{w, ww}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]
             {α : Sort u} {β : Sort v}
             [IsGroupoid W α] [IsGroupoid W β]
             (φ : α → β) [hφ : IsGroupoidFunctor φ]

    instance : IsEquivalenceFunctor             hφ.F := hφ.hEquivalence
    instance : IsSymmFunctor.IsSymmFunctorExt   hφ.F := hφ.hSymmExt
    instance : IsTransFunctor.IsTransFunctorExt hφ.F := hφ.hTransExt

    instance isCategoryFunctor : IsCategoryFunctor φ := ⟨⟩

  end IsGroupoidFunctor



  class IsNaturalTransformation {W : Universe.{w, ww}} [HasIdentity.{w, iw} W] [HasLinearFunctors W]
                                {α : Sort u} {β : Sort v}
                                [hα : IsSemicategory W α] [hβ : IsSemicategory W β] {φ ψ : α → β}
                                [hφ : IsSemicategoryFunctor φ] [hψ : IsSemicategoryFunctor ψ]
                                (η : MetaQuantification hβ.Hom φ ψ) where
  [isNatural    : IsNatural              hφ.F hψ.F η]
  [isNaturalExt : IsNatural.IsNaturalExt hφ.F hψ.F η]

  namespace IsNaturalTransformation

    variable {W : Universe.{w, ww}} [HasIdentity.{w, iw} W] [HasLinearFunctors W]
             {α : Sort u} {β : Sort v} [hα : IsSemicategory W α] [hβ : IsSemicategory W β]
             {φ ψ : α → β} [hφ : IsSemicategoryFunctor φ] [hψ : IsSemicategoryFunctor ψ]
             (η : MetaQuantification hβ.Hom φ ψ) [hη : IsNaturalTransformation η]

    instance : IsNatural              hφ.F hψ.F η := hη.isNatural
    instance : IsNatural.IsNaturalExt hφ.F hψ.F η := hη.isNaturalExt

  end IsNaturalTransformation

end CategoryTheory
