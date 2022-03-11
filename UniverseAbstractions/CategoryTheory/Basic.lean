/-
A version of higher category that works for universes, i.e. every universe with functors (more
specifically, with linear functor operations and extensionality) is a category according to this
definition. If a universe has equivalences, those are isomorphisms in that category.
-/



import UniverseAbstractions.CategoryTheory.Meta



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u uu u' uu' v vv iv ivv



namespace CategoryTheory

  open MetaRelation MetaFunctor MetaQuantification HasTransFun HasSymmFun
       IsAssociative IsCategoricalPreorder IsGroupoidEquivalence

  class IsHomUniverse (V : Universe.{v, vv}) extends
    HasIdentity.{v, iv, vv, ivv} V, HasInternalFunctors V, HasLinearFunOp V

  -- Note: We could replace `U` with `Sort u`, but that implies replacing `uu` with `u + 1`, which
  -- is too large in higher-category use cases.
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



  -- TODO: Figure out how to replace `sort` with a more generic universe.
  class IsCatUniverse (V : Universe.{v, vv}) [IsHomUniverse.{v, vv, iv, ivv} V] where
  [hasCat : HasCatProp sort.{max 1 u v} V]

  namespace IsCatUniverse

    variable (V : Universe.{v, vv}) [IsHomUniverse.{v, vv, iv, ivv} V]
             [hCatUniv : IsCatUniverse.{u} V]

    instance : HasCatProp sort.{max 1 u v} V := hCatUniv.hasCat

    @[reducible] def Category := HasCatProp.Category sort.{max 1 u v} V

    def univ : Universe.{max 1 u v, max (max 1 u v + 1) vv} := ⟨Category V⟩

  end IsCatUniverse

end CategoryTheory
