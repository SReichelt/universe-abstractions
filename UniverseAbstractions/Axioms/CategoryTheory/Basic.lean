/-
A version of higher category that works for universes, i.e. every universe with functors (more
specifically, with linear functor operations and extensionality) is a category according to this
definition. If a universe has equivalences, those are isomorphisms in that category.
-/



import UniverseAbstractions.Axioms.CategoryTheory.Meta



set_option autoBoundImplicitLocal false
--set_option pp.universes true
set_option synthInstance.maxHeartbeats 1000

universe u u' u'' v vv w ww iv ivv iw



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
             [h : IsCategory V α]

    instance : HasRefl                  h.Hom := h.homIsPreorder.toHasRefl
    instance : HasTrans                 h.Hom := h.homIsPreorder.toHasTrans
    instance : IsPreorder               h.Hom := h.homIsPreorder
    instance : HasTransFun              h.Hom := h.homHasTransFun
    instance : IsCategoricalPreorder    h.Hom := h.homIsCategoricalPreorder
    instance : IsCategoricalPreorderExt h.Hom := h.homIsCategoricalPreorderExt

    instance isSemicategory : IsSemicategory V α := ⟨⟩

    @[reducible] def idHom (a : α) : a ⇾ a := HasRefl.refl a

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
             [h : IsGroupoid V α]

    instance : HasRefl                  h.Hom := h.homIsEquivalence.toHasRefl
    instance : HasSymm                  h.Hom := h.homIsEquivalence.toHasSymm
    instance : HasTrans                 h.Hom := h.homIsEquivalence.toHasTrans
    instance : IsEquivalence            h.Hom := h.homIsEquivalence
    instance : HasTransFun              h.Hom := h.homHasTransFun
    instance : HasSymmFun               h.Hom := h.homHasSymmFun
    instance : IsGroupoidEquivalence    h.Hom := h.homIsGroupoidEquivalence
    instance : IsGroupoidEquivalenceExt h.Hom := h.homIsGroupoidEquivalenceExt

    instance isCategory : IsCategory V α := ⟨⟩

  end IsGroupoid



  class IsMorphismFunctor {W : Universe.{w, ww}} [HasIdentity.{w, iw} W] [HasInternalFunctors W]
                          {α : Sort u} {β : Sort v} [hα : HasMorphisms W α] [hβ : HasMorphisms W β]
                          (φ : α → β) where
  (F : PreFunctor hα.Hom hβ.Hom φ)

  namespace IsMorphismFunctor

    variable {W : Universe.{w, ww}} [HasIdentity.{w, iw} W]

    instance idFun [HasInternalFunctors W] [HasLinearFunOp W] (α : Sort u) [hα : HasMorphisms W α] :
      IsMorphismFunctor (@id α) :=
    ⟨MetaFunctor.idFun.metaFunctor hα.Hom⟩

    instance constFun [HasAffineFunctors W] (α : Sort u) {β : Sort v}
                      [hα : HasMorphisms W α] [hβ : IsCategory W β] (b : β) :
      IsMorphismFunctor (Function.const α b) :=
    ⟨MetaFunctor.constFun.metaFunctor hα.Hom hβ.Hom b⟩

    instance compFun [HasInternalFunctors W] [HasLinearFunOp W]
                     {α : Sort u} {β : Sort u'} {γ : Sort u''}
                     [hα : HasMorphisms W α] [hβ : HasMorphisms W β] [hγ : HasMorphisms W γ]
                     (φ : α → β) (ψ : β → γ) [hφ : IsMorphismFunctor φ] [hψ : IsMorphismFunctor ψ] :
      IsMorphismFunctor (ψ ∘ φ) :=
    ⟨MetaFunctor.compFun.metaFunctor hφ.F (MetaFunctor.lift hψ.F φ)⟩

  end IsMorphismFunctor

  class IsSemicategoryFunctor {W : Universe.{w, ww}} [HasIdentity.{w, iw} W] [HasLinearFunctors W]
                              {α : Sort u} {β : Sort v}
                              [hα : IsSemicategory W α] [hβ : IsSemicategory W β] (φ : α → β) extends
    IsMorphismFunctor φ where
  [hTrans    : IsTransFunctor                   F]
  [hTransExt : IsTransFunctor.IsTransFunctorExt F]

  namespace IsSemicategoryFunctor

    variable {W : Universe.{w, ww}} [HasIdentity.{w, iw} W]

    section

      variable [HasLinearFunctors W] {α : Sort u} {β : Sort v}
               [IsSemicategory W α] [IsSemicategory W β] (φ : α → β)
               [h : IsSemicategoryFunctor φ]

      instance : IsTransFunctor                   h.F := h.hTrans
      instance : IsTransFunctor.IsTransFunctorExt h.F := h.hTransExt

    end

    instance idFun [HasLinearFunctors W] (α : Sort u) [hα : IsSemicategory W α] :
      IsSemicategoryFunctor (@id α) :=
    { hTrans    := MetaFunctor.idFun.isTransFunctor    hα.Hom,
      hTransExt := MetaFunctor.idFun.isTransFunctorExt hα.Hom }

    instance constFun [HasAffineFunctors W] (α : Sort u) {β : Sort v}
                      [hα : IsSemicategory W α] [hβ : IsCategory W β] (b : β) :
      IsSemicategoryFunctor (Function.const α b) :=
    { hTrans    := MetaFunctor.constFun.isTransFunctor    hα.Hom hβ.Hom b,
      hTransExt := MetaFunctor.constFun.isTransFunctorExt hα.Hom hβ.Hom b }

    instance compFun [HasLinearFunctors W] {α : Sort u} {β : Sort u'} {γ : Sort u''}
                     [hα : IsSemicategory W α] [hβ : IsSemicategory W β] [hγ : IsSemicategory W γ]
                     (φ : α → β) (ψ : β → γ)
                     [hφ : IsSemicategoryFunctor φ] [hψ : IsSemicategoryFunctor ψ] :
      IsSemicategoryFunctor (ψ ∘ φ) :=
    let _ : HasTransFun (MetaRelation.lift (MetaRelation.lift hγ.Hom ψ) φ) := inferInstance;
    let _ : IsTransFunctor (MetaFunctor.lift hψ.F φ) := inferInstance;
    let _ : IsTransFunctor.IsTransFunctorExt (MetaFunctor.lift hψ.F φ) := inferInstance;
    { hTrans    := MetaFunctor.compFun.isTransFunctor    hφ.F (MetaFunctor.lift hψ.F φ),
      hTransExt := MetaFunctor.compFun.isTransFunctorExt hφ.F (MetaFunctor.lift hψ.F φ) }

  end IsSemicategoryFunctor

  class IsCategoryFunctor {W : Universe.{w, ww}} [HasIdentity.{w, iw} W] [HasLinearFunctors W]
                          {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
                          (φ : α → β) extends
    IsMorphismFunctor φ where
  [hPreorder : IsPreorderFunctor                F]
  [hTransExt : IsTransFunctor.IsTransFunctorExt F]

  namespace IsCategoryFunctor

    variable {W : Universe.{w, ww}} [HasIdentity.{w, iw} W]

    section

      variable [HasLinearFunctors W] {α : Sort u} {β : Sort v} [IsCategory W α] [IsCategory W β]
               (φ : α → β) [h : IsCategoryFunctor φ]

      instance : IsPreorderFunctor                h.F := h.hPreorder
      instance : IsTransFunctor.IsTransFunctorExt h.F := h.hTransExt

      instance isSemicategoryFunctor : IsSemicategoryFunctor φ := ⟨⟩

    end

    instance idFun [HasLinearFunctors W] (α : Sort u) [hα : IsCategory W α] :
      IsCategoryFunctor (@id α) :=
    { hPreorder := MetaFunctor.idFun.isPreorderFunctor hα.Hom,
      hTransExt := MetaFunctor.idFun.isTransFunctorExt hα.Hom }

    instance constFun [HasAffineFunctors W] (α : Sort u) {β : Sort v}
                      [hα : IsCategory W α] [hβ : IsCategory W β] (b : β) :
      IsCategoryFunctor (Function.const α b) :=
    { hPreorder := MetaFunctor.constFun.isPreorderFunctor hα.Hom hβ.Hom b,
      hTransExt := MetaFunctor.constFun.isTransFunctorExt hα.Hom hβ.Hom b }

    instance compFun [HasLinearFunctors W] {α : Sort u} {β : Sort u'} {γ : Sort u''}
                     [hα : IsCategory W α] [hβ : IsCategory W β] [hγ : IsCategory W γ]
                     (φ : α → β) (ψ : β → γ)
                     [hφ : IsCategoryFunctor φ] [hψ : IsCategoryFunctor ψ] :
      IsCategoryFunctor (ψ ∘ φ) :=
    let _ : HasTransFun (MetaRelation.lift (MetaRelation.lift hγ.Hom ψ) φ) := inferInstance;
    let _ : IsPreorderFunctor (MetaFunctor.lift hψ.F φ) := inferInstance;
    let _ : IsTransFunctor.IsTransFunctorExt (MetaFunctor.lift hψ.F φ) := inferInstance;
    { hPreorder := MetaFunctor.compFun.isPreorderFunctor hφ.F (MetaFunctor.lift hψ.F φ),
      hTransExt := MetaFunctor.compFun.isTransFunctorExt hφ.F (MetaFunctor.lift hψ.F φ) }

  end IsCategoryFunctor

  class IsGroupoidFunctor {W : Universe.{w, ww}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]
                          {α : Sort u} {β : Sort v} [hα : IsGroupoid W α] [hβ : IsGroupoid W β]
                          (φ : α → β) extends
    IsMorphismFunctor φ where
  [hEquivalence : IsEquivalenceFunctor             F]
  [hSymmExt     : IsSymmFunctor.IsSymmFunctorExt   F]
  [hTransExt    : IsTransFunctor.IsTransFunctorExt F]

  namespace IsGroupoidFunctor

    variable {W : Universe.{w, ww}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]

    section

      variable {α : Sort u} {β : Sort v} [IsGroupoid W α] [IsGroupoid W β]
               (φ : α → β) [h : IsGroupoidFunctor φ]

      instance : IsEquivalenceFunctor             h.F := h.hEquivalence
      instance : IsSymmFunctor.IsSymmFunctorExt   h.F := h.hSymmExt
      instance : IsTransFunctor.IsTransFunctorExt h.F := h.hTransExt

      instance isCategoryFunctor : IsCategoryFunctor φ := ⟨⟩

    end

    instance idFun (α : Sort u) [hα : IsGroupoid W α] :
      IsGroupoidFunctor (@id α) :=
    { hEquivalence := MetaFunctor.idFun.isEquivalenceFunctor hα.Hom,
      hTransExt    := MetaFunctor.idFun.isTransFunctorExt    hα.Hom,
      hSymmExt     := MetaFunctor.idFun.isSymmFunctorExt     hα.Hom }

    instance constFun (α : Sort u) {β : Sort v} [hα : IsGroupoid W α] [hβ : IsGroupoid W β]
                      (b : β) :
      IsGroupoidFunctor (Function.const α b) :=
    { hEquivalence := MetaFunctor.constFun.isEquivalenceFunctor hα.Hom hβ.Hom b,
      hTransExt    := MetaFunctor.constFun.isTransFunctorExt    hα.Hom hβ.Hom b,
      hSymmExt     := MetaFunctor.constFun.isSymmFunctorExt     hα.Hom hβ.Hom b }

    instance compFun {α : Sort u} {β : Sort u'} {γ : Sort u''}
                     [hα : IsGroupoid W α] [hβ : IsGroupoid W β] [hγ : IsGroupoid W γ]
                     (φ : α → β) (ψ : β → γ)
                     [hφ : IsGroupoidFunctor φ] [hψ : IsGroupoidFunctor ψ] :
      IsGroupoidFunctor (ψ ∘ φ) :=
    let _ : HasSymmFun (MetaRelation.lift (MetaRelation.lift hγ.Hom ψ) φ) := inferInstance;
    let _ : HasTransFun (MetaRelation.lift (MetaRelation.lift hγ.Hom ψ) φ) := inferInstance;
    let _ : IsEquivalenceFunctor (MetaFunctor.lift hψ.F φ) := inferInstance;
    let _ : IsSymmFunctor (MetaFunctor.lift hψ.F φ) := inferInstance;
    let _ : IsSymmFunctor.IsSymmFunctorExt (MetaFunctor.lift hψ.F φ) := inferInstance;
    let _ : IsTransFunctor.IsTransFunctorExt (MetaFunctor.lift hψ.F φ) := inferInstance;
    { hEquivalence := MetaFunctor.compFun.isEquivalenceFunctor hφ.F (MetaFunctor.lift hψ.F φ),
      hTransExt    := MetaFunctor.compFun.isTransFunctorExt    hφ.F (MetaFunctor.lift hψ.F φ),
      hSymmExt     := MetaFunctor.compFun.isSymmFunctorExt     hφ.F (MetaFunctor.lift hψ.F φ) }

  end IsGroupoidFunctor



  class IsNaturalTransformation {W : Universe.{w, ww}} [HasIdentity.{w, iw} W] [HasLinearFunctors W]
                                {α : Sort u} {β : Sort v}
                                [hα : HasMorphisms W α] [hβ : IsSemicategory W β] {φ ψ : α → β}
                                [hφ : IsMorphismFunctor φ] [hψ : IsMorphismFunctor ψ]
                                (η : MetaQuantification hβ.Hom φ ψ) where
  [isNatural    : IsNatural              hφ.F hψ.F η]
  [isNaturalExt : IsNatural.IsNaturalExt hφ.F hψ.F η]

  namespace IsNaturalTransformation

    variable {W : Universe.{w, ww}} [HasIdentity.{w, iw} W]

    section

      variable [HasLinearFunctors W] {α : Sort u} {β : Sort v}
               [hα : HasMorphisms W α] [hβ : IsSemicategory W β] {φ ψ : α → β}
               [hφ : IsMorphismFunctor φ] [hψ : IsMorphismFunctor ψ]
               (η : MetaQuantification hβ.Hom φ ψ) [hη : IsNaturalTransformation η]

      instance : IsNatural              hφ.F hψ.F η := hη.isNatural
      instance : IsNatural.IsNaturalExt hφ.F hψ.F η := hη.isNaturalExt

    end

    instance refl [HasLinearFunctors W] {α : Sort u} {β : Sort v}
                  [hα : HasMorphisms W α] [hβ : IsCategory W β] (φ : α → β)
                  [hφ : IsMorphismFunctor φ] :
      IsNaturalTransformation (MetaQuantification.refl hβ.Hom φ) :=
    ⟨⟩

    instance symm [HasStandardFunctors W] {α : Sort u} {β : Sort v}
                  [hα : HasMorphisms W α] [hβ : IsGroupoid W β] {φ ψ : α → β}
                  [hφ : IsMorphismFunctor φ] [hψ : IsMorphismFunctor ψ]
                  (η : MetaQuantification hβ.Hom φ ψ) [hη : IsNaturalTransformation η] :
      IsNaturalTransformation (MetaQuantification.symm hβ.Hom η) :=
    ⟨⟩

    instance trans [HasLinearFunctors W] {α : Sort u} {β : Sort v}
                   [hα : HasMorphisms W α] [hβ : IsSemicategory W β] {φ ψ χ : α → β}
                   [hφ : IsMorphismFunctor φ] [hψ : IsMorphismFunctor ψ] [hχ : IsMorphismFunctor χ]
                   (η : MetaQuantification hβ.Hom φ ψ) [hη : IsNaturalTransformation η]
                   (ε : MetaQuantification hβ.Hom ψ χ) [hε : IsNaturalTransformation ε] :
      IsNaturalTransformation (MetaQuantification.trans hβ.Hom η ε) :=
    ⟨⟩

  end IsNaturalTransformation

end CategoryTheory
