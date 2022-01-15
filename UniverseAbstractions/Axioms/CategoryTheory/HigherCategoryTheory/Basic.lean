import UniverseAbstractions.Axioms.CategoryTheory.Basic
import UniverseAbstractions.Axioms.CategoryTheory.HigherCategoryTheory.Meta



set_option autoBoundImplicitLocal false
set_option synthInstance.maxHeartbeats 3000
--set_option pp.universes true

universe u u' u'' v vv w ww iv iw



namespace CategoryTheory

  open MetaRelation MetaFunctor MetaQuantification HasTransFun HasSymmFun
       IsAssociative IsCategoricalPreorder IsGroupoidEquivalence IsNatural
       IsSemicategory IsCategory IsGroupoid IsSemicategoryFunctor IsCategoryFunctor
       HasLinearFunOp HasAffineFunOp

  namespace IsSemicategory

    variable {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv} V]

    class IsSemicategoryExt (α : Sort u) [hα : IsSemicategory V α] where
    [homIsAssociativeExt : IsAssociativeExt hα.Hom]

    namespace IsSemicategoryExt

      variable (α : Sort u) [hα : IsSemicategory V α] [h : IsSemicategoryExt α]

      instance : IsAssociativeExt hα.Hom := h.homIsAssociativeExt

    end IsSemicategoryExt

  end IsSemicategory

  namespace IsCategory

    variable {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv} V]

    class IsCategoryExt (α : Sort u) [hα : IsCategory V α] where
    [homIsCategoricalPreorderExt : IsCategoricalPreorderExt hα.Hom]

    namespace IsCategoryExt

      variable (α : Sort u) [hα : IsCategory V α] [h : IsCategoryExt α]

      instance : IsCategoricalPreorderExt hα.Hom := h.homIsCategoricalPreorderExt

      instance isSemicategoryExt : IsSemicategory.IsSemicategoryExt α := ⟨⟩

    end IsCategoryExt

  end IsCategory

  namespace IsGroupoid

    variable {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv} V] [HasSubLinearFunOp V]
             [HasNonLinearFunOp V]

    instance : HasAffineFunOp V := ⟨⟩
    instance : HasFullFunOp   V := ⟨⟩

    class IsGroupoidExt (α : Sort u) [hα : IsGroupoid V α] where
    [homIsGroupoidEquivalenceExt : IsGroupoidEquivalenceExt hα.Hom]

    namespace IsGroupoidExt

      variable (α : Sort u) [hα : IsGroupoid V α] [h : IsGroupoidExt α]

      instance : IsGroupoidEquivalenceExt hα.Hom := h.homIsGroupoidEquivalenceExt

      instance isCategoryExt : IsCategory.IsCategoryExt α := ⟨⟩

    end IsGroupoidExt

  end IsGroupoid



  namespace IsSemicategoryFunctor

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]

    class IsSemicategoryFunctorExt {α : Sort u} {β : Sort v}
                                   [hα : IsSemicategory W α] [hβ : IsSemicategory W β] (φ : α → β)
                                   [hφ : IsSemicategoryFunctor φ] where
    [hTransExt : IsTransFunctor.IsTransFunctorExt hφ.F]

    namespace IsSemicategoryFunctorExt

      section

        variable {α : Sort u} {β : Sort v} [IsSemicategory W α] [IsSemicategory W β] (φ : α → β)
                 [hφ : IsSemicategoryFunctor φ] [h : IsSemicategoryFunctorExt φ]

        instance : IsTransFunctor.IsTransFunctorExt hφ.F := h.hTransExt

      end

      instance idFun [HasLinearFunExt W] (α : Sort u) [hα : IsSemicategory W α] :
        IsSemicategoryFunctorExt (@id α) :=
      { hTransExt := MetaFunctor.idFun.isTransFunctorExt hα.Hom }

      instance constFun [HasSubLinearFunOp W] [HasAffineFunExt W] (α : Sort u) {β : Sort v}
                        [hα : IsSemicategory W α] [hβ : IsCategory W β] [hβExt : IsCategoryExt β]
                        (b : β) :
        IsSemicategoryFunctorExt (Function.const α b) :=
      { hTransExt := MetaFunctor.constFun.isTransFunctorExt hα.Hom hβ.Hom b }

      instance compFun [HasLinearFunExt W] {α : Sort u} {β : Sort u'} {γ : Sort u''}
                       [hα : IsSemicategory W α] [hβ : IsSemicategory W β] [hγ : IsSemicategory W γ]
                       (φ : α → β) (ψ : β → γ)
                       [hφ : IsSemicategoryFunctor φ] [hψ : IsSemicategoryFunctor ψ]
                       [hφExt : IsSemicategoryFunctorExt φ] [hψExt : IsSemicategoryFunctorExt ψ] :
        IsSemicategoryFunctorExt (ψ ∘ φ) :=
      let _ : HasTransFun (MetaRelation.lift (MetaRelation.lift hγ.Hom ψ) φ) := inferInstance;
      let _ : IsTransFunctor (MetaFunctor.lift hψ.F φ) := inferInstance;
      let _ : IsTransFunctor.IsTransFunctorExt (MetaFunctor.lift hψ.F φ) := inferInstance;
      { hTransExt := MetaFunctor.compFun.isTransFunctorExt hφ.F (MetaFunctor.lift hψ.F φ) }

    end IsSemicategoryFunctorExt

  end IsSemicategoryFunctor

  namespace IsCategoryFunctor

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]

    class IsCategoryFunctorExt {α : Sort u} {β : Sort v}
                               [hα : IsCategory W α] [hβ : IsCategory W β] (φ : α → β)
                               [hφ : IsCategoryFunctor φ] extends
      IsSemicategoryFunctorExt φ

    namespace IsCategoryFunctorExt

      section

        variable {α : Sort u} {β : Sort v} [IsCategory W α] [IsCategory W β] (φ : α → β)
                 [hφ : IsCategoryFunctor φ] [h : IsCategoryFunctorExt φ]

        instance : IsTransFunctor.IsTransFunctorExt hφ.F := h.hTransExt

      end

      instance idFun [HasLinearFunExt W] (α : Sort u) [hα : IsCategory W α] :
        IsCategoryFunctorExt (@id α) :=
      { toIsSemicategoryFunctorExt := IsSemicategoryFunctorExt.idFun α }

      instance constFun [HasSubLinearFunOp W] [HasAffineFunExt W] (α : Sort u) {β : Sort v}
                        [hα : IsCategory W α] [hβ : IsCategory W β] [hβExt : IsCategoryExt β]
                        (b : β) :
        IsCategoryFunctorExt (Function.const α b) :=
      { toIsSemicategoryFunctorExt := IsSemicategoryFunctorExt.constFun α b }

      instance compFun [HasLinearFunExt W] {α : Sort u} {β : Sort u'} {γ : Sort u''}
                       [hα : IsCategory W α] [hβ : IsCategory W β] [hγ : IsCategory W γ]
                       (φ : α → β) (ψ : β → γ)
                       [hφ : IsCategoryFunctor φ] [hψ : IsCategoryFunctor ψ]
                       [hφExt : IsCategoryFunctorExt φ] [hψExt : IsCategoryFunctorExt ψ] :
        IsCategoryFunctorExt (ψ ∘ φ) :=
      { toIsSemicategoryFunctorExt := IsSemicategoryFunctorExt.compFun φ ψ }

    end IsCategoryFunctorExt

  end IsCategoryFunctor

  namespace IsGroupoidFunctor

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]

    class IsGroupoidFunctorExt {α : Sort u} {β : Sort v}
                               [hα : IsGroupoid W α] [hβ : IsGroupoid W β] (φ : α → β)
                               [hφ : IsGroupoidFunctor φ] extends
      IsCategoryFunctorExt φ where
    [hSymmExt : IsSymmFunctor.IsSymmFunctorExt hφ.F]

    namespace IsGroupoidFunctorExt

      section

        variable {α : Sort u} {β : Sort v} [hα : IsGroupoid W α] [hβ : IsGroupoid W β] (φ : α → β)

        def fromCategoryFunctorExt [hφ : IsCategoryFunctor φ] [hφExt : IsCategoryFunctorExt φ] :
          IsGroupoidFunctorExt φ (hφ := IsGroupoidFunctor.fromCategoryFunctor φ) :=
        sorry

        variable [hφ : IsGroupoidFunctor φ] [h : IsGroupoidFunctorExt φ]

        instance : IsSymmFunctor.IsSymmFunctorExt hφ.F := h.hSymmExt

      end

      instance idFun [HasLinearFunExt W] (α : Sort u) [hα : IsGroupoid W α] :
        IsGroupoidFunctorExt (@id α) :=
      { toIsCategoryFunctorExt := IsCategoryFunctorExt.idFun α,
        hSymmExt               := MetaFunctor.idFun.isSymmFunctorExt hα.Hom }

      instance constFun [HasSubLinearFunOp W] [HasNonLinearFunOp W] [HasAffineFunExt W]
                        (α : Sort u) {β : Sort v} [hα : IsGroupoid W α] [hβ : IsGroupoid W β]
                        [hβExt : IsGroupoidExt β] (b : β) :
        IsGroupoidFunctorExt (Function.const α b) :=
      let _ : HasFullFunOp W := ⟨⟩
      { toIsCategoryFunctorExt := IsCategoryFunctorExt.constFun α b,
        hSymmExt               := MetaFunctor.constFun.isSymmFunctorExt hα.Hom hβ.Hom b }

      instance compFun [HasLinearFunExt W] {α : Sort u} {β : Sort u'} {γ : Sort u''}
                       [hα : IsGroupoid W α] [hβ : IsGroupoid W β] [hγ : IsGroupoid W γ]
                       (φ : α → β) (ψ : β → γ)
                       [hφ : IsGroupoidFunctor φ] [hψ : IsGroupoidFunctor ψ]
                       [hφExt : IsGroupoidFunctorExt φ] [hψExt : IsGroupoidFunctorExt ψ] :
        IsGroupoidFunctorExt (ψ ∘ φ) :=
      let _ : HasSymmFun (MetaRelation.lift (MetaRelation.lift hγ.Hom ψ) φ) := inferInstance;
      let _ : IsSymmFunctor.IsSymmFunctorExt (MetaFunctor.lift hψ.F φ) := inferInstance;
      { toIsCategoryFunctorExt := IsCategoryFunctorExt.compFun φ ψ,
        hSymmExt               := MetaFunctor.compFun.isSymmFunctorExt hφ.F (MetaFunctor.lift hψ.F φ) }

    end IsGroupoidFunctorExt

  end IsGroupoidFunctor



  namespace IsNaturalTransformation

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W] {α : Sort u} {β : Sort v}

    class IsNaturalTransformationExt [hα : HasMorphisms W α] [hβ : IsSemicategory W β] {φ ψ : α → β}
                                     [hφ : IsMorphismFunctor φ] [hψ : IsMorphismFunctor ψ]
                                     (η : MetaQuantification hβ.Hom φ ψ)
                                     [hη : IsNaturalTransformation η] where
    [hNatExt : IsNaturalExt hφ.F hψ.F η]

    namespace IsNaturalTransformationExt

      section

        variable [hα : HasMorphisms W α] [hβ : IsSemicategory W β] {φ ψ : α → β}
                 [hφ : IsMorphismFunctor φ] [hψ : IsMorphismFunctor ψ]
                 (η : MetaQuantification hβ.Hom φ ψ) [hη : IsNaturalTransformation η]
                 [h : IsNaturalTransformationExt η]

        instance : IsNaturalExt hφ.F hψ.F η := h.hNatExt

      end

      instance refl [hα : HasMorphisms W α] [hβ : IsCategory W β] [hβExt : IsCategoryExt β]
                    (φ : α → β) [hφ : IsMorphismFunctor φ] :
        IsNaturalTransformationExt (MetaQuantification.refl hβ.Hom φ) :=
      ⟨⟩

      instance symm [HasSubLinearFunOp W] [HasNonLinearFunOp W] [hα : HasMorphisms W α]
                    [hβ : IsGroupoid W β] [hβExt : IsGroupoidExt β] {φ ψ : α → β}
                    [hφ : IsMorphismFunctor φ] [hψ : IsMorphismFunctor ψ]
                    (η : MetaQuantification hβ.Hom φ ψ) [hη : IsNaturalTransformation η]
                    [hηExt : IsNaturalTransformationExt η] :
        IsNaturalTransformationExt (MetaQuantification.symm hβ.Hom η) :=
      ⟨⟩

      instance trans [hα : HasMorphisms W α] [hβ : IsSemicategory W β] [hβExt : IsSemicategoryExt β]
                     {φ ψ χ : α → β}
                     [hφ : IsMorphismFunctor φ] [hψ : IsMorphismFunctor ψ] [hχ : IsMorphismFunctor χ]
                     (η : MetaQuantification hβ.Hom φ ψ) (ε : MetaQuantification hβ.Hom ψ χ)
                     [hη : IsNaturalTransformation η] [hε : IsNaturalTransformation ε]
                     [hηExt : IsNaturalTransformationExt η] [hεExt : IsNaturalTransformationExt ε] :
        IsNaturalTransformationExt (MetaQuantification.trans hβ.Hom η ε) :=
      ⟨⟩

    end IsNaturalTransformationExt

  end IsNaturalTransformation

end CategoryTheory
