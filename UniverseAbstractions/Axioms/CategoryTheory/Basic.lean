/-
A version of higher category that works for universes, i.e. every universe with functors (more
specifically, with linear functor operations and extensionality) is a category according to this
definition. If a universe has equivalences, those are isomorphisms in that category.
-/



import UniverseAbstractions.Axioms.CategoryTheory.Meta



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u u' u'' v vv w ww iv iw



namespace CategoryTheory

  open MetaRelation MetaFunctor MetaQuantification HasTransFun HasSymmFun
       IsAssociative IsCategoricalPreorder IsGroupoidEquivalence

  class IsHomUniverse (V : Universe.{v, vv}) extends
    HasIdentity.{v, iv} V, HasInternalFunctors V, HasLinearFunOp V

  class HasMorphisms (V : outParam Universe.{v, vv})[outParam (IsHomUniverse.{v, vv, iv} V)]
                     (α : Sort u) : Sort (max 1 u vv) where
  (Hom : MetaRelation α V)

  infix:20 " ⇾ " => CategoryTheory.HasMorphisms.Hom

  class IsSemicategory (V : outParam Universe.{v, vv}) [outParam (IsHomUniverse.{v, vv, iv} V)]
                       (α : Sort u) extends
    HasMorphisms V α : Sort (max 1 u v vv iv) where
  [homHasTrans      : HasTrans      Hom]
  [homHasTransFun   : HasTransFun   Hom]
  [homIsAssociative : IsAssociative Hom]

  namespace IsSemicategory

    variable {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv} V] {α : Sort u}
             [h : IsSemicategory V α]

    instance : HasTrans      h.Hom := h.homHasTrans
    instance : HasTransFun   h.Hom := h.homHasTransFun
    instance : IsAssociative h.Hom := h.homIsAssociative

  end IsSemicategory

  class IsCategory (V : outParam Universe.{v, vv}) [outParam (IsHomUniverse.{v, vv, iv} V)]
                   (α : Sort u) extends
    HasMorphisms V α : Sort (max 1 u v vv iv) where
  [homIsPreorder            : IsPreorder            Hom]
  [homHasTransFun           : HasTransFun           Hom]
  [homIsCategoricalPreorder : IsCategoricalPreorder Hom]

  namespace IsCategory

    variable {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv} V] {α : Sort u} [h : IsCategory V α]

    instance : HasRefl               h.Hom := h.homIsPreorder.toHasRefl
    instance : HasTrans              h.Hom := h.homIsPreorder.toHasTrans
    instance : IsPreorder            h.Hom := h.homIsPreorder
    instance : HasTransFun           h.Hom := h.homHasTransFun
    instance : IsCategoricalPreorder h.Hom := h.homIsCategoricalPreorder

    instance isSemicategory : IsSemicategory V α := ⟨⟩

    @[reducible] def idHom (a : α) : a ⇾ a := HasRefl.refl a

  end IsCategory

  class IsGroupoid (V : outParam Universe.{v, vv}) [outParam (IsHomUniverse.{v, vv, iv} V)]
                   (α : Sort u) extends
    HasMorphisms V α : Sort (max 1 u v vv iv) where
  [homIsEquivalence         : IsEquivalence         Hom]
  [homHasSymmFun            : HasSymmFun            Hom]
  [homHasTransFun           : HasTransFun           Hom]
  [homIsGroupoidEquivalence : IsGroupoidEquivalence Hom]

  namespace IsGroupoid

    variable {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv} V] {α : Sort u} [h : IsGroupoid V α]

    instance : HasRefl               h.Hom := h.homIsEquivalence.toHasRefl
    instance : HasSymm               h.Hom := h.homIsEquivalence.toHasSymm
    instance : HasTrans              h.Hom := h.homIsEquivalence.toHasTrans
    instance : IsEquivalence         h.Hom := h.homIsEquivalence
    instance : HasTransFun           h.Hom := h.homHasTransFun
    instance : HasSymmFun            h.Hom := h.homHasSymmFun
    instance : IsGroupoidEquivalence h.Hom := h.homIsGroupoidEquivalence

    instance isCategory : IsCategory V α := ⟨⟩

  end IsGroupoid



  class IsMorphismFunctor {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                          {α : Sort u} {β : Sort v} [hα : HasMorphisms W α] [hβ : HasMorphisms W β]
                          (φ : α → β) where
  (F : PreFunctor hα.Hom hβ.Hom φ)

  namespace IsMorphismFunctor

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]

    @[reducible] def preFunctor {α : Sort u} {β : Sort v}
                                [hα : HasMorphisms W α] [hβ : HasMorphisms W β]
                                (φ : α → β) [hφ : IsMorphismFunctor φ] :
      PreFunctor hα.Hom hβ.Hom φ :=
    hφ.F

    instance idFun (α : Sort u) [hα : HasMorphisms W α] :
      IsMorphismFunctor (@id α) :=
    ⟨MetaFunctor.idFun.metaFunctor hα.Hom⟩

    instance constFun [HasSubLinearFunOp W] (α : Sort u) {β : Sort v}
                      [hα : HasMorphisms W α] [hβ : IsCategory W β] (b : β) :
      IsMorphismFunctor (Function.const α b) :=
    let _ : HasAffineFunOp W := ⟨⟩;
    ⟨MetaFunctor.constFun.metaFunctor hα.Hom hβ.Hom b⟩

    instance compFun {α : Sort u} {β : Sort u'} {γ : Sort u''}
                     [hα : HasMorphisms W α] [hβ : HasMorphisms W β] [hγ : HasMorphisms W γ]
                     (φ : α → β) (ψ : β → γ) [hφ : IsMorphismFunctor φ] [hψ : IsMorphismFunctor ψ] :
      IsMorphismFunctor (ψ ∘ φ) :=
    ⟨MetaFunctor.compFun.metaFunctor hφ.F (MetaFunctor.lift hψ.F φ)⟩

  end IsMorphismFunctor

  class IsSemicategoryFunctor {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                              {α : Sort u} {β : Sort v}
                              [hα : IsSemicategory W α] [hβ : IsSemicategory W β] (φ : α → β) extends
    IsMorphismFunctor φ where
  [hTrans : IsTransFunctor F]

  namespace IsSemicategoryFunctor

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]

    section

      variable {α : Sort u} {β : Sort v} [IsSemicategory W α] [IsSemicategory W β] (φ : α → β)
               [h : IsSemicategoryFunctor φ]

      instance : IsTransFunctor h.F := h.hTrans

    end

    instance idFun (α : Sort u) [hα : IsSemicategory W α] :
      IsSemicategoryFunctor (@id α) :=
    { hTrans := MetaFunctor.idFun.isTransFunctor hα.Hom }

    instance constFun [HasSubLinearFunOp W] (α : Sort u) {β : Sort v}
                      [hα : IsSemicategory W α] [hβ : IsCategory W β] (b : β) :
      IsSemicategoryFunctor (Function.const α b) :=
    let _ : HasAffineFunOp W := ⟨⟩;
    { hTrans := MetaFunctor.constFun.isTransFunctor hα.Hom hβ.Hom b }

    instance compFun {α : Sort u} {β : Sort u'} {γ : Sort u''}
                     [hα : IsSemicategory W α] [hβ : IsSemicategory W β] [hγ : IsSemicategory W γ]
                     (φ : α → β) (ψ : β → γ)
                     [hφ : IsSemicategoryFunctor φ] [hψ : IsSemicategoryFunctor ψ] :
      IsSemicategoryFunctor (ψ ∘ φ) :=
    let _ : HasTransFun (MetaRelation.lift (MetaRelation.lift hγ.Hom ψ) φ) := inferInstance;
    let _ : IsTransFunctor (MetaFunctor.lift hψ.F φ) := inferInstance;
    { hTrans := MetaFunctor.compFun.isTransFunctor hφ.F (MetaFunctor.lift hψ.F φ) }

  end IsSemicategoryFunctor

  class IsCategoryFunctor {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                          {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
                          (φ : α → β) extends
    IsMorphismFunctor φ where
  [hPreorder : IsPreorderFunctor F]

  namespace IsCategoryFunctor

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]

    section

      variable {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
               (φ : α → β) [h : IsCategoryFunctor φ]

      instance : IsPreorderFunctor h.F := h.hPreorder

      instance isSemicategoryFunctor : IsSemicategoryFunctor φ := ⟨⟩

      def mapHalfInv {a b : α} {f : a ⇾ b} {g : b ⇾ a} (hfg : HalfInv hα.Hom f g) :
        HalfInv hβ.Hom (h.F f) (h.F g) :=
      h.hPreorder.reflEq a •
      HasCongrArg.congrArg (h.F.baseFun a a) hfg •
      (h.hPreorder.transEq f g)⁻¹

    end

    instance idFun (α : Sort u) [hα : IsCategory W α] :
      IsCategoryFunctor (@id α) :=
    { hPreorder := MetaFunctor.idFun.isPreorderFunctor hα.Hom }

    instance constFun [HasSubLinearFunOp W] (α : Sort u) {β : Sort v}
                      [hα : IsCategory W α] [hβ : IsCategory W β] (b : β) :
      IsCategoryFunctor (Function.const α b) :=
    let _ : HasAffineFunOp W := ⟨⟩;
    { hPreorder := MetaFunctor.constFun.isPreorderFunctor hα.Hom hβ.Hom b }

    instance compFun {α : Sort u} {β : Sort u'} {γ : Sort u''}
                     [hα : IsCategory W α] [hβ : IsCategory W β] [hγ : IsCategory W γ]
                     (φ : α → β) (ψ : β → γ)
                     [hφ : IsCategoryFunctor φ] [hψ : IsCategoryFunctor ψ] :
      IsCategoryFunctor (ψ ∘ φ) :=
    let _ : HasTransFun (MetaRelation.lift (MetaRelation.lift hγ.Hom ψ) φ) := inferInstance;
    let _ : IsPreorderFunctor (MetaFunctor.lift hψ.F φ) := inferInstance;
    { hPreorder := MetaFunctor.compFun.isPreorderFunctor hφ.F (MetaFunctor.lift hψ.F φ) }

  end IsCategoryFunctor

  class IsGroupoidFunctor {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                          {α : Sort u} {β : Sort v} [hα : IsGroupoid W α] [hβ : IsGroupoid W β]
                          (φ : α → β) extends
    IsMorphismFunctor φ where
  [hEquivalence : IsEquivalenceFunctor F]

  namespace IsGroupoidFunctor

    open IsCategoryFunctor

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]

    section

      variable {α : Sort u} {β : Sort v} [hα : IsGroupoid W α] [hβ : IsGroupoid W β] (φ : α → β)

      def fromCategoryFunctor [hφ : IsCategoryFunctor φ] : IsGroupoidFunctor φ :=
      { hEquivalence := { symmEq := λ e => HalfInv.unique hβ.Hom (leftInv (hφ.F e))
                                                                 (mapHalfInv φ (rightInv e)) } }

      variable [h : IsGroupoidFunctor φ]

      instance : IsEquivalenceFunctor h.F := h.hEquivalence

      instance isCategoryFunctor : IsCategoryFunctor φ := ⟨⟩

    end

    instance idFun (α : Sort u) [hα : IsGroupoid W α] :
      IsGroupoidFunctor (@id α) :=
    { hEquivalence := MetaFunctor.idFun.isEquivalenceFunctor hα.Hom }

    instance constFun [HasSubLinearFunOp W] (α : Sort u) {β : Sort v}
                      [hα : IsGroupoid W α] [hβ : IsGroupoid W β] (b : β) :
      IsGroupoidFunctor (Function.const α b) :=
    let _ : HasAffineFunOp W := ⟨⟩;
    { hEquivalence := MetaFunctor.constFun.isEquivalenceFunctor hα.Hom hβ.Hom b }

    instance compFun {α : Sort u} {β : Sort u'} {γ : Sort u''}
                     [hα : IsGroupoid W α] [hβ : IsGroupoid W β] [hγ : IsGroupoid W γ]
                     (φ : α → β) (ψ : β → γ)
                     [hφ : IsGroupoidFunctor φ] [hψ : IsGroupoidFunctor ψ] :
      IsGroupoidFunctor (ψ ∘ φ) :=
    let _ : HasSymmFun (MetaRelation.lift (MetaRelation.lift hγ.Hom ψ) φ) := inferInstance;
    let _ : HasTransFun (MetaRelation.lift (MetaRelation.lift hγ.Hom ψ) φ) := inferInstance;
    let _ : IsEquivalenceFunctor (MetaFunctor.lift hψ.F φ) := inferInstance;
    let _ : IsSymmFunctor (MetaFunctor.lift hψ.F φ) := inferInstance;
    { hEquivalence := MetaFunctor.compFun.isEquivalenceFunctor hφ.F (MetaFunctor.lift hψ.F φ) }

  end IsGroupoidFunctor



  class IsNaturalTransformation {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                                {α : Sort u} {β : Sort v}
                                [hα : HasMorphisms W α] [hβ : IsSemicategory W β] {φ ψ : α → β}
                                [hφ : IsMorphismFunctor φ] [hψ : IsMorphismFunctor ψ]
                                (η : MetaQuantification hβ.Hom φ ψ) extends
    IsNatural hφ.F hψ.F η

  namespace IsNaturalTransformation

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W] {α : Sort u} {β : Sort v}

    instance refl [hα : HasMorphisms W α] [hβ : IsCategory W β] (φ : α → β)
                  [hφ : IsMorphismFunctor φ] :
      IsNaturalTransformation (MetaQuantification.refl hβ.Hom φ) :=
    ⟨⟩

    instance symm [hα : HasMorphisms W α] [hβ : IsGroupoid W β] {φ ψ : α → β}
                  [hφ : IsMorphismFunctor φ] [hψ : IsMorphismFunctor ψ]
                  (η : MetaQuantification hβ.Hom φ ψ) [hη : IsNaturalTransformation η] :
      IsNaturalTransformation (MetaQuantification.symm hβ.Hom η) :=
    ⟨⟩

    instance trans [hα : HasMorphisms W α] [hβ : IsSemicategory W β] {φ ψ χ : α → β}
                   [hφ : IsMorphismFunctor φ] [hψ : IsMorphismFunctor ψ] [hχ : IsMorphismFunctor χ]
                   (η : MetaQuantification hβ.Hom φ ψ) (ε : MetaQuantification hβ.Hom ψ χ)
                   [hη : IsNaturalTransformation η] [hε : IsNaturalTransformation ε] :
      IsNaturalTransformation (MetaQuantification.trans hβ.Hom η ε) :=
    ⟨⟩

  end IsNaturalTransformation

end CategoryTheory
