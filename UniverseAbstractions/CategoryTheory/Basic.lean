/-
A version of higher category that works for universes, i.e. every universe with functors (more
specifically, with linear functor operations and extensionality) is a category according to this
definition. If a universe has equivalences, those are isomorphisms in that category.
-/



import UniverseAbstractions.CategoryTheory.Meta



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u uu v vv iv ivv



namespace CategoryTheory

  open Universe MetaRelation MetaFunctor MetaQuantification HasTransFun HasSymmFun
       IsAssociative IsCategoricalPreorder IsGroupoidEquivalence
       HasFunctors HasCongrArg

  class IsHomUniverse (V : Universe.{v, vv}) extends
    HasIdentity.{v, iv, vv, ivv} V, HasInternalFunctors V, HasLinearFunOp V

  -- Note: We could replace `U` with `Sort u`, but that makes functor categories too large for
  -- `Category.univ` to be a morphism universe:
  -- * `Category` contains a `BundledRelation` and is thus at least as large as `uu`, which would
  --   become `u + 1`.
  -- * However, in the general case the objects of categories must have exactly the same Lean
  --   universe level as morphisms if we want the universe of categories to have internal functors:
  --   * On the one hand, since natural transformations are morphisms and their definition
  --     quantifies over objects, morphisms must be at least as large as objects (unless morphisms
  --     are `Prop`-valued).
  --   * On the other hand, functors contain morphisms and are thus at least as large. But having
  --     internal functors means that functors are objects of some category.
  -- TODO: What is the problem exactly?
  -- (At least the second point implies that there is no universe with internal functors that
  -- contains the category defined in `FunctorCategory.lean`.)
  structure BundledRelation (U : Universe.{u, uu}) (V : Universe.{v, vv}) :
    Sort (max 1 u uu vv) where
  (A   : U)
  (Hom : MetaRelation A V)

  section

    variable {U : Universe.{u, uu}} {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv, ivv} V]

    structure SemicatDesc (R : BundledRelation U V) : Sort (max 1 u v iv) where
    [homHasTrans      : HasTrans      R.Hom]
    [homHasTransFun   : HasTransFun   R.Hom]
    [homIsAssociative : IsAssociative R.Hom]

    structure CatDesc (R : BundledRelation U V) : Sort (max 1 u v iv) where
    [homIsPreorder            : IsPreorder            R.Hom]
    [homHasTransFun           : HasTransFun           R.Hom]
    [homIsCategoricalPreorder : IsCategoricalPreorder R.Hom]

    namespace CatDesc

      variable {R : BundledRelation U V} (desc : CatDesc R)

      def toSemicatDesc : SemicatDesc R :=
      let _ : IsPreorder            R.Hom := desc.homIsPreorder;
      let _ : HasTransFun           R.Hom := desc.homHasTransFun;
      let _ : IsCategoricalPreorder R.Hom := desc.homIsCategoricalPreorder;
      ⟨⟩

    end CatDesc

    structure GrpoidDesc (R : BundledRelation U V) : Sort (max 1 u v iv) where
    [homIsEquivalence         : IsEquivalence         R.Hom]
    [homHasSymmFun            : HasSymmFun            R.Hom]
    [homHasTransFun           : HasTransFun           R.Hom]
    [homIsGroupoidEquivalence : IsGroupoidEquivalence R.Hom]

    namespace GrpoidDesc

      variable {R : BundledRelation U V} (desc : GrpoidDesc R)

      def toCatDesc : CatDesc R :=
      let _ : IsEquivalence         R.Hom := desc.homIsEquivalence;
      let _ : HasTransFun           R.Hom := desc.homHasTransFun;
      let _ : HasSymmFun            R.Hom := desc.homHasSymmFun;
      let _ : IsGroupoidEquivalence R.Hom := desc.homIsGroupoidEquivalence;
      ⟨⟩

    end GrpoidDesc

  end



  class HasCatProp (U : Universe.{u, uu}) (V : Universe.{v, vv})
                   [IsHomUniverse.{v, vv, iv, ivv} V] where
  (Cat                            : MetaProperty (BundledRelation U V) V)
  (desc {R : BundledRelation U V} : Cat R → CatDesc R)

  namespace HasCatProp

    structure Category (U : Universe.{u, uu}) (V : Universe.{v, vv})
                       [IsHomUniverse.{v, vv, iv, ivv} V] [h : HasCatProp U V] :
      Sort (max 1 u uu v vv) where
    {R : BundledRelation U V}
    (C : h.Cat R)

    namespace Category

      section

        variable (U : Universe.{u, uu}) (V : Universe.{v, vv})
                 [IsHomUniverse.{v, vv, iv, ivv} V] [h : HasCatProp U V]

        instance hasInstances : HasInstances.{u} (Category U V) := ⟨λ A => A.R.A⟩

        def univ : Universe.{u, max 1 u uu v vv} := ⟨Category U V⟩

      end

      variable {U : Universe.{u, uu}} {V : Universe.{v, vv}}
               [IsHomUniverse.{v, vv, iv, ivv} V] [h : HasCatProp U V]

      def Hom (A : Category U V) : MetaRelation A V := A.R.Hom
      infix:20 " ⇾ " => CategoryTheory.HasCatProp.Category.Hom _

      instance (A : Category U V) : IsPreorder            (Hom A) := (h.desc A.C).homIsPreorder
      instance (A : Category U V) : HasTransFun           (Hom A) := (h.desc A.C).homHasTransFun
      instance (A : Category U V) : IsCategoricalPreorder (Hom A) := (h.desc A.C).homIsCategoricalPreorder

      @[reducible] def idHom {A : Category U V} (a : A) : a ⇾ a := HasRefl.refl a
      @[reducible] def compHom {A : Category U V} {a b c : A} (f : a ⇾ b) (g : b ⇾ c) : a ⇾ c := g • f

    end Category

    structure DefCat {U : Universe.{u, uu}} {V : Universe.{v, vv}}
                     [IsHomUniverse.{v, vv, iv, ivv} V] [h : HasCatProp U V]
                     {R : BundledRelation U V} (desc : CatDesc R) where
    (C   : h.Cat R)
    [hEq : IsPreorderEq (h.desc C).homIsPreorder desc.homIsPreorder]

    namespace DefCat

      open Category

      variable {U : Universe.{u, uu}} {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv, ivv} V]
               [h : HasCatProp U V] {R : BundledRelation U V} {desc : CatDesc R}

      def toCategory (A : DefCat desc) : Category U V :=
      { R := R,
        C := A.C }

      def catReflEq {A : DefCat desc} (a : toCategory A) :
        idHom a ≃' desc.homIsPreorder.refl a :=
      A.hEq.reflEq a

      def catTransEq {A : DefCat desc} {a b c : toCategory A} (f : a ⇾ b) (g : b ⇾ c) :
        g • f ≃' desc.homIsPreorder.trans f g :=
      A.hEq.transEq f g

    end DefCat

    class HasTrivialCatProp (U : Universe.{u, uu}) (V : Universe.{v, vv})
                            [IsHomUniverse.{v, vv, iv, ivv} V] [h : HasCatProp U V] where
    (cat {R : BundledRelation U V} (desc : CatDesc R) : DefCat desc)

    namespace HasTrivialCatProp

      variable {U : Universe.{u, uu}} {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv, ivv} V]
               [HasCatProp U V] [h : HasTrivialCatProp U V]

      def defCat {R : BundledRelation U V} {desc : CatDesc R} : DefCat desc := h.cat desc

    end HasTrivialCatProp

  end HasCatProp



  structure IsoDesc {U : Universe.{u, uu}} {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv, ivv} V]
                    [HasCatProp U V] {A : HasCatProp.Category U V} (a b : A) :
    Sort (max 1 v iv) where
  (toHom  : a ⇾ b)
  (invHom : b ⇾ a)
  [isInv  : IsInv toHom invHom]

  namespace IsoDesc

    open HasCatProp HasCatProp.Category

    variable {U V : Universe} [IsHomUniverse V] [HasCatProp U V] {A : Category U V}

    instance {a b : A} (e : IsoDesc a b) : IsInv e.toHom e.invHom := e.isInv

    def refl (a : A) : IsoDesc a a :=
    ⟨idHom a, idHom a⟩

    def symm {a b : A} (e : IsoDesc a b) : IsoDesc b a :=
    ⟨e.invHom, e.toHom⟩

    def trans {a b c : A} (e : IsoDesc a b) (f : IsoDesc b c) : IsoDesc a c :=
    ⟨f.toHom • e.toHom, e.invHom • f.invHom⟩

    def toInvEquiv' {a b : A} {e₁ e₂ : IsoDesc a b} (h : e₁.toHom ≃ e₂.toHom) :
      e₂.invHom ≃ e₁.invHom :=
    HalfInv.unique e₁.isInv.leftInv (HalfInv.congrArgLeft h e₂.isInv.rightInv)

    def toInvEquiv {a b : A} {e₁ e₂ : IsoDesc a b} (h : e₁.toHom ≃ e₂.toHom) :
      e₁.invHom ≃ e₂.invHom :=
    (toInvEquiv' h)⁻¹

  end IsoDesc



  class HasIsoRel {U : Universe.{u, uu}} {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv, ivv} V]
                  [HasCatProp U V] (A : HasCatProp.Category U V) where
  (Iso                                  : MetaRelation A V)
  (desc {a b : A}                       : Iso a b → IsoDesc a b)
  (defToHomFun (a b : A)                : Iso a b ⟶{λ e => (desc e).toHom} (a ⇾ b))
  (toHomInj {a b : A} {e₁ e₂ : Iso a b} : (desc e₁).toHom ≃ (desc e₂).toHom → e₁ ≃ e₂)

  @[reducible] def HasCatProp.Category.Iso {U V : Universe} [IsHomUniverse V] [HasCatProp U V]
                                           (A : HasCatProp.Category U V) [h : HasIsoRel A] :=
  h.Iso

  infix:20 " ⇿ " => CategoryTheory.HasCatProp.Category.Iso _

  namespace HasIsoRel

    open HasCatProp HasCatProp.Category

    variable {U V : Universe} [IsHomUniverse V] [HasCatProp U V]

    section

      variable (A : Category U V) [h : HasIsoRel A]

      def isoRel : BundledRelation U V := ⟨A.R.A, h.Iso⟩

      def toHomMetaFunctor : MetaFunctor h.Iso (Hom A) := MetaFunctor.fromDefFun h.defToHomFun

    end

    section

      variable {A : Category U V} [h : HasIsoRel A]

      @[reducible] def toHom  {a b : A} (e : a ⇿ b) : a ⇾ b := (h.desc e).toHom
      @[reducible] def invHom {a b : A} (e : a ⇿ b) : b ⇾ a := (h.desc e).invHom

      def leftInv  {a b : A} (e : a ⇿ b) : HalfInv (toHom e) (invHom e) :=
      (h.desc e).isInv.leftInv
      def rightInv {a b : A} (e : a ⇿ b) : HalfInv (invHom e) (toHom e) :=
      (h.desc e).isInv.rightInv

      def toHomCongrArg  {a b : A} {e₁ e₂ : a ⇿ b} (he : e₁ ≃ e₂) : toHom  e₁ ≃ toHom  e₂ :=
      defCongrArg (h.defToHomFun a b) he
      def invHomCongrArg {a b : A} {e₁ e₂ : a ⇿ b} (he : e₁ ≃ e₂) : invHom e₁ ≃ invHom e₂ :=
      IsoDesc.toInvEquiv (toHomCongrArg he)

      structure DefIso {a b : A} (desc : IsoDesc a b) where
      (e    : a ⇿ b)
      (toEq : toHom e ≃ desc.toHom)

      def byToDef  {a b : A} {desc : IsoDesc a b} {e : DefIso desc} : toHom  e.e ≃ desc.toHom  :=
      e.toEq
      def byInvDef {a b : A} {desc : IsoDesc a b} {e : DefIso desc} : invHom e.e ≃ desc.invHom :=
      IsoDesc.toInvEquiv e.toEq

    end

    class HasTrivialIsomorphismCondition (A : Category U V) [h : HasIsoRel A] where
    (iso {a b : A} (desc : IsoDesc a b) : DefIso desc)

    namespace HasTrivialIsomorphismCondition

      variable {A : Category U V} [HasIsoRel A] [h : HasTrivialIsomorphismCondition A]

      def defIso {a b : A} {desc : IsoDesc a b} : DefIso desc := h.iso desc

    end HasTrivialIsomorphismCondition

  end HasIsoRel

  class HasIsoOp {U : Universe.{u, uu}} {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv, ivv} V]
                 [HasCatProp U V] (A : HasCatProp.Category U V) extends
    HasIsoRel A where
  (defRefl (a : A) : HasIsoRel.DefIso (IsoDesc.refl a))
  (defSymm {a b : A} (e : a ⇿ b) : HasIsoRel.DefIso (IsoDesc.symm (desc e)))
  (defTrans {a b c : A} (e : a ⇿ b) (f : b ⇿ c) :
     HasIsoRel.DefIso (IsoDesc.trans (desc e) (desc f)))

  namespace HasIsoOp

    open HasCatProp HasCatProp.Category HasIsoRel

    variable {U V : Universe} [IsHomUniverse V] [HasCatProp U V]

    section

      variable (A : Category U V)

      instance hasTrivialIsoOp [hIso : HasIsoRel A] [h : HasTrivialIsomorphismCondition A] :
        HasIsoOp A :=
      { defRefl  := λ _   => HasTrivialIsomorphismCondition.defIso,
        defSymm  := λ _   => HasTrivialIsomorphismCondition.defIso,
        defTrans := λ _ _ => HasTrivialIsomorphismCondition.defIso }

      variable [h : HasIsoOp A]

      instance isoIsPreorder : IsPreorder h.Iso :=
      { refl  := λ a   => (h.defRefl a).e,
        trans := λ e f => (h.defTrans e f).e }

      instance isoIsEquivalence : IsEquivalence h.Iso :=
      { symm := λ e => (h.defSymm e).e }

      instance toHomIsPreorderFunctor : IsPreorderFunctor (toHomMetaFunctor A) :=
      { reflEq  := λ a   => byToDef • byDef,
        transEq := λ e f => (congrArgTrans byDef byDef)⁻¹ • byToDef • byDef }

    end

    section

      variable {A : Category U V} [h : HasIsoOp A]

      @[reducible] def idIso (a : A) : a ⇿ a := HasRefl.refl a

      def toHomReflEq (a : A) : toHom (idIso a) ≃ idHom a := byToDef
      def toHomSymmEq {a b : A} (e : a ⇿ b) : toHom e⁻¹ ≃ invHom e := byToDef
      def toHomTransEq {a b c : A} (e : a ⇿ b) (f : b ⇿ c) : toHom (f • e) ≃ toHom f • toHom e :=
      byToDef

      def invHomReflEq (a : A) : invHom (idIso a) ≃ idHom a := byInvDef
      def invHomSymmEq {a b : A} (e : a ⇿ b) : invHom e⁻¹ ≃ toHom e := byInvDef
      def invHomTransEq {a b c : A} (e : a ⇿ b) (f : b ⇿ c) : invHom (f • e) ≃ invHom e • invHom f :=
      byInvDef

      def isoAssoc {a b c d : A} (e : a ⇿ b) (f : b ⇿ c) (g : c ⇿ d) :
        (g • f) • e ≃ g • (f • e) :=
      h.toHomInj ((congrArgTransRight (toHomTransEq e f) (toHom g) •
                   toHomTransEq (f • e) g)⁻¹ •
                  assoc (toHom e) (toHom f) (toHom g) •
                  (congrArgTransLeft (toHom e) (toHomTransEq f g) •
                   toHomTransEq e (g • f)))

      def isoRightId {a b : A} (e : a ⇿ b) : e • idIso a ≃ e :=
      h.toHomInj (rightId (toHom e) •
                  (congrArgTransRight (toHomReflEq a) (toHom e) •
                   toHomTransEq (idIso a) e))

      def isoLeftId {a b : A} (e : a ⇿ b) : idIso b • e ≃ e :=
      h.toHomInj (leftId (toHom e) •
                  (congrArgTransLeft (toHom e) (toHomReflEq b) •
                   toHomTransEq e (idIso b)))

      def isoLeftInv {a b : A} (e : a ⇿ b) : e⁻¹ • e ≃ idIso a :=
      h.toHomInj ((toHomReflEq a)⁻¹ •
                  leftInv e •
                  (congrArgTransLeft (toHom e) (toHomSymmEq e) •
                   toHomTransEq e e⁻¹))

      def isoRightInv {a b : A} (e : a ⇿ b) : e • e⁻¹ ≃ idIso b :=
      h.toHomInj ((toHomReflEq b)⁻¹ •
                  rightInv e •
                  (congrArgTransRight (toHomSymmEq e) (toHom e) •
                   toHomTransEq e⁻¹ e))

    end

    section

      variable (A : Category U V) [h : HasIsoOp A]

      instance isoIsCategoricalPreorder : IsCategoricalPreorder h.Iso :=
      { assoc   := isoAssoc,
        rightId := isoRightId,
        leftId  := isoLeftId }

      instance isoIsGroupoidEquivalence : IsGroupoidEquivalence h.Iso :=
      { leftInv  := isoLeftInv,
        rightInv := isoRightInv }

      def isoCatDesc [isoHasTransFun : HasTransFun h.Iso] : CatDesc (isoRel A) :=
      { homIsPreorder            := isoIsPreorder A,
        homHasTransFun           := isoHasTransFun,
        homIsCategoricalPreorder := isoIsCategoricalPreorder A }

      def isoGrpoidDesc [isoHasSymmFun : HasSymmFun h.Iso] [isoHasTransFun : HasTransFun h.Iso] :
        GrpoidDesc (isoRel A) :=
      { homIsEquivalence         := isoIsEquivalence A,
        homHasSymmFun            := isoHasSymmFun,
        homHasTransFun           := isoHasTransFun,
        homIsGroupoidEquivalence := isoIsGroupoidEquivalence A }

    end

  end HasIsoOp

  class HasIsomorphisms {U : Universe.{u, uu}} {V : Universe.{v, vv}}
                        [IsHomUniverse.{v, vv, iv, ivv} V] [HasCatProp U V]
                        (A : HasCatProp.Category U V) extends
    HasIsoOp A where
  [isoHasSymmFun  : HasSymmFun  Iso]
  [isoHasTransFun : HasTransFun Iso]
  (defIsoCat      : HasCatProp.DefCat (HasIsoOp.isoCatDesc A))

  namespace HasIsomorphisms

    open HasCatProp HasCatProp.Category HasIsoRel HasIsoOp

    variable {U V : Universe} [IsHomUniverse V] [HasCatProp U V]
             (A : Category U V) [h : HasIsomorphisms A]

    instance : HasSymmFun  h.Iso := h.isoHasSymmFun
    instance : HasTransFun h.Iso := h.isoHasTransFun

    def iso : Category U V := DefCat.toCategory h.defIsoCat

    @[reducible] def Iso' : MetaRelation A V := Hom (iso A)
    infix:20 " ⇿' " => CategoryTheory.HasIsomorphisms.Iso' _

  end HasIsomorphisms



  class IsCatUniverse (U : Universe.{u, uu}) (V : Universe.{v, vv})
                      [IsHomUniverse.{v, vv, iv, ivv} V] where
  [hasCat : HasCatProp U V]
  [hasIso (A : HasCatProp.Category U V) : HasIsomorphisms A]

  namespace IsCatUniverse

    open HasCatProp HasCatProp.Category HasIsoOp

    instance (U V : Universe) [IsHomUniverse V] [h : IsCatUniverse U V] : HasCatProp U V :=
    h.hasCat

    variable {U V : Universe} [IsHomUniverse V] [h : IsCatUniverse U V]

    instance (A : Category U V) : HasIsomorphisms A := h.hasIso A

    instance hasEquivalenceRelation (A : Category U V) : HasEquivalenceRelation A V :=
    { R := Iso A,
      h := isoIsEquivalence A }

    instance hasInstanceEquivalences : HasInstanceEquivalences (univ U V) V :=
    ⟨hasEquivalenceRelation⟩

  end IsCatUniverse

  class IsSortCatUniverse (V : Universe.{v, vv}) [IsHomUniverse.{v, vv, iv, ivv} V] extends
    IsCatUniverse sort.{u} V

  namespace IsSortCatUniverse

    variable (V : Universe.{v, vv}) [IsHomUniverse V] [h : IsSortCatUniverse.{u} V]

    @[reducible] def univ : Universe.{u, max (u + 1) v vv} := HasCatProp.Category.univ sort.{u} V

  end IsSortCatUniverse

end CategoryTheory
