/-
A version of higher category that works for universes, i.e. every universe with functors (more
specifically, with linear functor operations and extensionality) is a category according to this
definition. If a universe has equivalences, those are isomorphisms in that category.
-/



import UniverseAbstractions.Axioms.CategoryTheory.Meta



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u u' u'' v vv w ww iv ivv iw



namespace CategoryTheory

  open MetaRelation MetaFunctor MetaQuantification HasTransFun HasSymmFun
       IsAssociative IsCategoricalPreorder IsGroupoidEquivalence

  class IsHomUniverse (V : Universe.{v, vv}) extends
    HasIdentity.{v, iv, vv, ivv} V, HasInternalFunctors V, HasLinearFunOp V

  class HasMorphisms (V : outParam Universe.{v, vv}) [outParam (IsHomUniverse.{v, vv, iv} V)]
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



  structure MorphismFunctor {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                            (α : Sort u) (β : Sort v)
                            [hα : HasMorphisms W α] [hβ : HasMorphisms W β] where
  {φ : α → β}
  (F : PreFunctor hα.Hom hβ.Hom φ)

  namespace MorphismFunctor

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]

    def idFun (α : Sort u) [hα : HasMorphisms W α] :
      MorphismFunctor α α :=
    ⟨MetaFunctor.idFun.metaFunctor hα.Hom⟩

    def constFun [HasSubLinearFunOp W] (α : Sort u) {β : Sort v}
                 [hα : HasMorphisms W α] [hβ : IsCategory W β] (b : β) :
      MorphismFunctor α β :=
    ⟨MetaFunctor.constFun.metaFunctor hα.Hom hβ.Hom b⟩

    def compFun {α : Sort u} {β : Sort u'} {γ : Sort u''}
                [hα : HasMorphisms W α] [hβ : HasMorphisms W β] [hγ : HasMorphisms W γ]
                (F : MorphismFunctor α β) (G : MorphismFunctor β γ) :
      MorphismFunctor α γ :=
    ⟨MetaFunctor.compFun.metaFunctor F.F (MetaFunctor.lift G.F F.φ)⟩

  end MorphismFunctor

  class IsSemicategoryFunctor {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                              {α : Sort u} {β : Sort v}
                              [hα : IsSemicategory W α] [hβ : IsSemicategory W β]
                              (F : MorphismFunctor α β) extends
    IsTransFunctor F.F

  namespace IsSemicategoryFunctor

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]

    instance idFun (α : Sort u) [hα : IsSemicategory W α] :
      IsSemicategoryFunctor (MorphismFunctor.idFun α) :=
    { toIsTransFunctor := MetaFunctor.idFun.isTransFunctor hα.Hom }

    instance constFun [HasSubLinearFunOp W] (α : Sort u) {β : Sort v}
                      [hα : IsSemicategory W α] [hβ : IsCategory W β] (b : β) :
      IsSemicategoryFunctor (MorphismFunctor.constFun α b) :=
    { toIsTransFunctor := MetaFunctor.constFun.isTransFunctor hα.Hom hβ.Hom b }

    instance compFun {α : Sort u} {β : Sort u'} {γ : Sort u''}
                     [hα : IsSemicategory W α] [hβ : IsSemicategory W β] [hγ : IsSemicategory W γ]
                     (F : MorphismFunctor α β) (G : MorphismFunctor β γ)
                     [hF : IsSemicategoryFunctor F] [hG : IsSemicategoryFunctor G] :
      IsSemicategoryFunctor (MorphismFunctor.compFun F G) :=
    let _ : HasTransFun (MetaRelation.lift (MetaRelation.lift hγ.Hom G.φ) F.φ) := inferInstance;
    let _ : IsTransFunctor (MetaFunctor.lift G.F F.φ) := inferInstance;
    { toIsTransFunctor := MetaFunctor.compFun.isTransFunctor F.F (MetaFunctor.lift G.F F.φ) }

  end IsSemicategoryFunctor

  class IsCategoryFunctor {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                          {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
                          (F : MorphismFunctor α β) extends
    IsPreorderFunctor F.F

  namespace IsCategoryFunctor

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]

    section

      variable {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
               (F : MorphismFunctor α β) [h : IsCategoryFunctor F]

      instance isSemicategoryFunctor : IsSemicategoryFunctor F := ⟨⟩

      def mapHalfInv {a b : α} {f : a ⇾ b} {g : b ⇾ a} (hfg : HalfInv hα.Hom f g) :
        HalfInv hβ.Hom (F.F f) (F.F g) :=
      h.reflEq a •
      HasCongrArg.congrArg (F.F.baseFun a a) hfg •
      (h.transEq f g)⁻¹

    end

    instance idFun (α : Sort u) [hα : IsCategory W α] :
      IsCategoryFunctor (MorphismFunctor.idFun α) :=
    { toIsPreorderFunctor := MetaFunctor.idFun.isPreorderFunctor hα.Hom }

    instance constFun [HasSubLinearFunOp W] (α : Sort u) {β : Sort v}
                      [hα : IsCategory W α] [hβ : IsCategory W β] (b : β) :
      IsCategoryFunctor (MorphismFunctor.constFun α b) :=
    { toIsPreorderFunctor := MetaFunctor.constFun.isPreorderFunctor hα.Hom hβ.Hom b }

    instance compFun {α : Sort u} {β : Sort u'} {γ : Sort u''}
                     [hα : IsCategory W α] [hβ : IsCategory W β] [hγ : IsCategory W γ]
                     (F : MorphismFunctor α β) (G : MorphismFunctor β γ)
                     [hF : IsCategoryFunctor F] [hG : IsCategoryFunctor G] :
      IsCategoryFunctor (MorphismFunctor.compFun F G) :=
    let _ : HasTransFun (MetaRelation.lift (MetaRelation.lift hγ.Hom G.φ) F.φ) := inferInstance;
    let _ : IsPreorderFunctor (MetaFunctor.lift G.F F.φ) := inferInstance;
    { toIsPreorderFunctor := MetaFunctor.compFun.isPreorderFunctor F.F (MetaFunctor.lift G.F F.φ) }

  end IsCategoryFunctor

  class IsGroupoidFunctor {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                          {α : Sort u} {β : Sort v} [hα : IsGroupoid W α] [hβ : IsGroupoid W β]
                          (F : MorphismFunctor α β) extends
    IsEquivalenceFunctor F.F

  namespace IsGroupoidFunctor

    open IsCategoryFunctor

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]

    section

      variable {α : Sort u} {β : Sort v} [hα : IsGroupoid W α] [hβ : IsGroupoid W β]
               (F : MorphismFunctor α β)

      def fromCategoryFunctor [hF : IsCategoryFunctor F] : IsGroupoidFunctor F :=
      { symmEq := λ e => HalfInv.unique hβ.Hom (leftInv (F.F e))
                                               (mapHalfInv F (rightInv e)) }

      variable [h : IsGroupoidFunctor F]

      instance isCategoryFunctor : IsCategoryFunctor F := ⟨⟩

    end

    instance idFun (α : Sort u) [hα : IsGroupoid W α] :
      IsGroupoidFunctor (MorphismFunctor.idFun α) :=
    { toIsEquivalenceFunctor := MetaFunctor.idFun.isEquivalenceFunctor hα.Hom }

    instance constFun [HasSubLinearFunOp W] (α : Sort u) {β : Sort v}
                      [hα : IsGroupoid W α] [hβ : IsGroupoid W β] (b : β) :
      IsGroupoidFunctor (MorphismFunctor.constFun α b) :=
    { toIsEquivalenceFunctor := MetaFunctor.constFun.isEquivalenceFunctor hα.Hom hβ.Hom b }

    instance compFun {α : Sort u} {β : Sort u'} {γ : Sort u''}
                     [hα : IsGroupoid W α] [hβ : IsGroupoid W β] [hγ : IsGroupoid W γ]
                     (F : MorphismFunctor α β) (G : MorphismFunctor β γ)
                     [hF : IsGroupoidFunctor F] [hG : IsGroupoidFunctor G] :
      IsGroupoidFunctor (MorphismFunctor.compFun F G) :=
    let _ : HasSymmFun (MetaRelation.lift (MetaRelation.lift hγ.Hom G.φ) F.φ) := inferInstance;
    let _ : HasTransFun (MetaRelation.lift (MetaRelation.lift hγ.Hom G.φ) F.φ) := inferInstance;
    let _ : IsEquivalenceFunctor (MetaFunctor.lift G.F F.φ) := inferInstance;
    let _ : IsSymmFunctor (MetaFunctor.lift G.F F.φ) := inferInstance;
    { toIsEquivalenceFunctor := MetaFunctor.compFun.isEquivalenceFunctor F.F (MetaFunctor.lift G.F F.φ) }

  end IsGroupoidFunctor



  def Quantification {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W] {α : Sort u} {β : Sort v}
                     [hα : HasMorphisms W α] [hβ : IsSemicategory W β] (F G : MorphismFunctor α β) :=
  MetaQuantification hβ.Hom F.φ G.φ

  namespace Quantification

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W] {α : Sort u} {β : Sort v}

    @[reducible] def refl' [hα : HasMorphisms W α] [hβ : IsCategory W β] {φ : α → β}
                           (F₁ F₂ : PreFunctor hα.Hom hβ.Hom φ) :
      Quantification ⟨F₁⟩ ⟨F₂⟩ :=
    MetaQuantification.refl hβ.Hom φ

    @[reducible] def refl [hα : HasMorphisms W α] [hβ : IsCategory W β] (F : MorphismFunctor α β) :
      Quantification F F :=
    MetaQuantification.refl hβ.Hom F.φ

    @[reducible] def symm [hα : HasMorphisms W α] [hβ : IsGroupoid W β] {F G : MorphismFunctor α β}
                          (η : Quantification F G) :
      Quantification G F :=
    MetaQuantification.symm hβ.Hom η

    @[reducible] def trans [hα : HasMorphisms W α] [hβ : IsSemicategory W β]
                           {F G H : MorphismFunctor α β}
                           (η : Quantification F G) (ε : Quantification G H) :
      Quantification F H :=
    MetaQuantification.trans hβ.Hom η ε

  end Quantification

  class IsNaturalTransformation {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                                {α : Sort u} {β : Sort v}
                                [hα : HasMorphisms W α] [hβ : IsSemicategory W β]
                                {F G : MorphismFunctor α β} (η : Quantification F G) extends
    IsNatural F.F G.F η

  namespace IsNaturalTransformation

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W] {α : Sort u} {β : Sort v}

    def fromEq [hα : HasMorphisms W α] [hβ : IsCategory W β] {φ : α → β}
               {F G : PreFunctor hα.Hom hβ.Hom φ} (hEq : ∀ {a b : α} (f : a ⇾ b), F f ≃ G f) :
      IsNaturalTransformation (Quantification.refl' F G) :=
    { toIsNatural := IsNatural.fromEq F G hEq }

    instance refl [hα : HasMorphisms W α] [hβ : IsCategory W β] (F : MorphismFunctor α β) :
      IsNaturalTransformation (Quantification.refl F) :=
    ⟨⟩

    instance symm [hα : HasMorphisms W α] [hβ : IsGroupoid W β] {F G : MorphismFunctor α β}
                  (η : Quantification F G) [hη : IsNaturalTransformation η] :
      IsNaturalTransformation (Quantification.symm η) :=
    ⟨⟩

    instance trans [hα : HasMorphisms W α] [hβ : IsSemicategory W β] {F G H : MorphismFunctor α β}
                   (η : Quantification F G) (ε : Quantification G H)
                   [hη : IsNaturalTransformation η] [hε : IsNaturalTransformation ε] :
      IsNaturalTransformation (Quantification.trans η ε) :=
    ⟨⟩

  end IsNaturalTransformation

end CategoryTheory
