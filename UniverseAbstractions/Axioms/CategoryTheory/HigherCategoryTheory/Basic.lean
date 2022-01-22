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
             (α : Sort u) [hα : IsSemicategory V α]

    class IsSemicategoryExt where
    [homIsAssociativeExt : IsAssociativeExt hα.Hom]

    namespace IsSemicategoryExt

      variable [h : IsSemicategoryExt α]

      instance : IsAssociativeExt hα.Hom := h.homIsAssociativeExt

    end IsSemicategoryExt

  end IsSemicategory

  namespace IsCategory

    variable {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv} V]
             (α : Sort u) [hα : IsCategory V α]

    class IsCategoryExt where
    [homIsCategoricalPreorderExt : IsCategoricalPreorderExt hα.Hom]

    namespace IsCategoryExt

      variable [h : IsCategoryExt α]

      instance : IsCategoricalPreorderExt hα.Hom := h.homIsCategoricalPreorderExt

      instance isSemicategoryExt : IsSemicategory.IsSemicategoryExt α := ⟨⟩

    end IsCategoryExt

  end IsCategory

  namespace IsGroupoid

    variable {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv} V] [HasSubLinearFunOp V]
             [HasNonLinearFunOp V] (α : Sort u) [hα : IsGroupoid V α]

    instance : HasAffineFunOp V := ⟨⟩
    instance : HasFullFunOp   V := ⟨⟩

    class IsGroupoidExt where
    [homIsGroupoidEquivalenceExt : IsGroupoidEquivalenceExt hα.Hom]

    namespace IsGroupoidExt

      variable [h : IsGroupoidExt α]

      instance : IsGroupoidEquivalenceExt hα.Hom := h.homIsGroupoidEquivalenceExt

      instance isCategoryExt : IsCategory.IsCategoryExt α := ⟨⟩

    end IsGroupoidExt

  end IsGroupoid



  namespace IsSemicategoryFunctor

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]

    class IsSemicategoryFunctorExt {α : Sort u} {β : Sort v}
                                   [hα : IsSemicategory W α] [hβ : IsSemicategory W β]
                                   (F : MorphismFunctor α β) [hF : IsSemicategoryFunctor F] extends
      IsTransFunctor.IsTransFunctorExt F.F

    namespace IsSemicategoryFunctorExt

      instance idFun [HasLinearFunExt W] (α : Sort u) [hα : IsSemicategory W α] :
        IsSemicategoryFunctorExt (MorphismFunctor.idFun α) :=
      { toIsTransFunctorExt := MetaFunctor.idFun.isTransFunctorExt hα.Hom }

      instance constFun [HasSubLinearFunOp W] [HasAffineFunExt W] (α : Sort u) {β : Sort v}
                        [hα : IsSemicategory W α] [hβ : IsCategory W β] [hβExt : IsCategoryExt β]
                        (b : β) :
        IsSemicategoryFunctorExt (MorphismFunctor.constFun α b) :=
      { toIsTransFunctorExt := MetaFunctor.constFun.isTransFunctorExt hα.Hom hβ.Hom b }

      instance compFun [HasLinearFunExt W] {α : Sort u} {β : Sort u'} {γ : Sort u''}
                       [hα : IsSemicategory W α] [hβ : IsSemicategory W β] [hγ : IsSemicategory W γ]
                       (F : MorphismFunctor α β) (G : MorphismFunctor β γ)
                       [hF : IsSemicategoryFunctor F] [hG : IsSemicategoryFunctor G]
                       [hφExt : IsSemicategoryFunctorExt F] [hψExt : IsSemicategoryFunctorExt G] :
        IsSemicategoryFunctorExt (MorphismFunctor.compFun F G) :=
      let _ : HasTransFun (MetaRelation.lift (MetaRelation.lift hγ.Hom G.φ) F.φ) := inferInstance;
      let _ : IsTransFunctor (MetaFunctor.lift G.F F.φ) := inferInstance;
      let _ : IsTransFunctor.IsTransFunctorExt (MetaFunctor.lift G.F F.φ) := inferInstance;
      { toIsTransFunctorExt := MetaFunctor.compFun.isTransFunctorExt F.F (MetaFunctor.lift G.F F.φ) }

    end IsSemicategoryFunctorExt

  end IsSemicategoryFunctor

  namespace IsCategoryFunctor

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]

    class IsCategoryFunctorExt {α : Sort u} {β : Sort v}
                               [hα : IsCategory W α] [hβ : IsCategory W β]
                               (F : MorphismFunctor α β) [hF : IsCategoryFunctor F] extends
      IsSemicategoryFunctorExt F

    namespace IsCategoryFunctorExt

      instance idFun [HasLinearFunExt W] (α : Sort u) [hα : IsCategory W α] :
        IsCategoryFunctorExt (MorphismFunctor.idFun α) :=
      { toIsSemicategoryFunctorExt := IsSemicategoryFunctorExt.idFun α }

      instance constFun [HasSubLinearFunOp W] [HasAffineFunExt W] (α : Sort u) {β : Sort v}
                        [hα : IsCategory W α] [hβ : IsCategory W β] [hβExt : IsCategoryExt β]
                        (b : β) :
        IsCategoryFunctorExt (MorphismFunctor.constFun α b) :=
      { toIsSemicategoryFunctorExt := IsSemicategoryFunctorExt.constFun α b }

      instance compFun [HasLinearFunExt W] {α : Sort u} {β : Sort u'} {γ : Sort u''}
                       [hα : IsCategory W α] [hβ : IsCategory W β] [hγ : IsCategory W γ]
                       (F : MorphismFunctor α β) (G : MorphismFunctor β γ)
                       [hF : IsCategoryFunctor F] [hG : IsCategoryFunctor G]
                       [hφExt : IsCategoryFunctorExt F] [hψExt : IsCategoryFunctorExt G] :
        IsCategoryFunctorExt (MorphismFunctor.compFun F G) :=
      { toIsSemicategoryFunctorExt := IsSemicategoryFunctorExt.compFun F G }

    end IsCategoryFunctorExt

  end IsCategoryFunctor

  namespace IsGroupoidFunctor

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]

    class IsGroupoidFunctorExt {α : Sort u} {β : Sort v}
                               [hα : IsGroupoid W α] [hβ : IsGroupoid W β]
                               (F : MorphismFunctor α β) [hF : IsGroupoidFunctor F] extends
      IsCategoryFunctorExt F, IsSymmFunctor.IsSymmFunctorExt F.F

    namespace IsGroupoidFunctorExt

      section

        variable {α : Sort u} {β : Sort v} [hα : IsGroupoid W α] [hβ : IsGroupoid W β]
                 (F : MorphismFunctor α β)

        def fromCategoryFunctorExt [hF : IsCategoryFunctor F] [hFExt : IsCategoryFunctorExt F] :
          IsGroupoidFunctorExt F (hF := IsGroupoidFunctor.fromCategoryFunctor F) :=
        sorry

      end

      instance idFun [HasLinearFunExt W] (α : Sort u) [hα : IsGroupoid W α] :
        IsGroupoidFunctorExt (MorphismFunctor.idFun α) :=
      { toIsCategoryFunctorExt := IsCategoryFunctorExt.idFun α,
        toIsSymmFunctorExt     := MetaFunctor.idFun.isSymmFunctorExt hα.Hom }

      instance constFun [HasSubLinearFunOp W] [HasNonLinearFunOp W] [HasAffineFunExt W]
                        (α : Sort u) {β : Sort v} [hα : IsGroupoid W α] [hβ : IsGroupoid W β]
                        [hβExt : IsGroupoidExt β] (b : β) :
        IsGroupoidFunctorExt (MorphismFunctor.constFun α b) :=
      { toIsCategoryFunctorExt := IsCategoryFunctorExt.constFun α b,
        toIsSymmFunctorExt     := MetaFunctor.constFun.isSymmFunctorExt hα.Hom hβ.Hom b }

      instance compFun [HasLinearFunExt W] {α : Sort u} {β : Sort u'} {γ : Sort u''}
                       [hα : IsGroupoid W α] [hβ : IsGroupoid W β] [hγ : IsGroupoid W γ]
                       (F : MorphismFunctor α β) (G : MorphismFunctor β γ)
                       [hF : IsGroupoidFunctor F] [hG : IsGroupoidFunctor G]
                       [hφExt : IsGroupoidFunctorExt F] [hψExt : IsGroupoidFunctorExt G] :
        IsGroupoidFunctorExt (MorphismFunctor.compFun F G) :=
      let _ : HasSymmFun (MetaRelation.lift (MetaRelation.lift hγ.Hom G.φ) F.φ) := inferInstance;
      let _ : IsSymmFunctor.IsSymmFunctorExt (MetaFunctor.lift G.F F.φ) := inferInstance;
      { toIsCategoryFunctorExt := IsCategoryFunctorExt.compFun F G,
        toIsSymmFunctorExt     := MetaFunctor.compFun.isSymmFunctorExt F.F (MetaFunctor.lift G.F F.φ) }

    end IsGroupoidFunctorExt

  end IsGroupoidFunctor



  namespace IsNaturalTransformation

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W] {α : Sort u} {β : Sort v}

    class IsNaturalTransformationExt [hα : HasMorphisms W α] [hβ : IsSemicategory W β]
                                     {F G : MorphismFunctor α β} (η : Quantification F G)
                                     [hη : IsNaturalTransformation η] extends
      IsNaturalExt F.F G.F η

    namespace IsNaturalTransformationExt

      instance refl [hα : HasMorphisms W α] [hβ : IsCategory W β] [hβExt : IsCategoryExt β]
                    (F : MorphismFunctor α β) :
        IsNaturalTransformationExt (MetaQuantification.refl hβ.Hom F.φ) :=
      ⟨⟩

      instance symm [HasSubLinearFunOp W] [HasNonLinearFunOp W] [hα : HasMorphisms W α]
                    [hβ : IsGroupoid W β] [hβExt : IsGroupoidExt β] {F G : MorphismFunctor α β}
                    (η : Quantification F G) [hη : IsNaturalTransformation η]
                    [hηExt : IsNaturalTransformationExt η] :
        IsNaturalTransformationExt (MetaQuantification.symm hβ.Hom η) :=
      ⟨⟩

      instance trans [hα : HasMorphisms W α] [hβ : IsSemicategory W β] [hβExt : IsSemicategoryExt β]
                     {F G H : MorphismFunctor α β} (η : Quantification F G) (ε : Quantification G H)
                     [hη : IsNaturalTransformation η] [hε : IsNaturalTransformation ε]
                     [hηExt : IsNaturalTransformationExt η] [hεExt : IsNaturalTransformationExt ε] :
        IsNaturalTransformationExt (MetaQuantification.trans hβ.Hom η ε) :=
      ⟨⟩

    end IsNaturalTransformationExt

  end IsNaturalTransformation

end CategoryTheory
