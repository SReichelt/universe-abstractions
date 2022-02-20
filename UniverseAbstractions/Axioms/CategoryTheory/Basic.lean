/-
A version of higher category that works for universes, i.e. every universe with functors (more
specifically, with linear functor operations and extensionality) is a category according to this
definition. If a universe has equivalences, those are isomorphisms in that category.
-/



import UniverseAbstractions.Axioms.CategoryTheory.Meta



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v vv iv ivv



namespace CategoryTheory

  open MetaRelation MetaFunctor MetaQuantification HasTransFun HasSymmFun
       IsAssociative IsCategoricalPreorder IsGroupoidEquivalence

  class IsHomUniverse (V : Universe.{v, vv}) extends
    HasIdentity.{v, iv, vv, ivv} V, HasInternalFunctors V, HasLinearFunOp V

  structure BundledRelation (V : Universe.{v, vv}) : Sort (max (u + 1) vv) where
  {α   : Sort u}
  (Hom : MetaRelation α V)

  section

    variable {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv, ivv} V]

    structure SemicatDesc (R : BundledRelation.{u} V) : Sort (max 1 u v iv) where
    [homHasTrans      : HasTrans      R.Hom]
    [homHasTransFun   : HasTransFun   R.Hom]
    [homIsAssociative : IsAssociative R.Hom]

    structure CatDesc (R : BundledRelation.{u} V) : Sort (max 1 u v iv) where
    [homIsPreorder            : IsPreorder            R.Hom]
    [homHasTransFun           : HasTransFun           R.Hom]
    [homIsCategoricalPreorder : IsCategoricalPreorder R.Hom]

    namespace CatDesc

      variable {R : BundledRelation.{u} V} (desc : CatDesc R)

      def toSemicatDesc : SemicatDesc R :=
      let _ : IsPreorder            R.Hom := desc.homIsPreorder;
      let _ : HasTransFun           R.Hom := desc.homHasTransFun;
      let _ : IsCategoricalPreorder R.Hom := desc.homIsCategoricalPreorder;
      ⟨⟩

    end CatDesc

    structure GrpoidDesc (R : BundledRelation.{u} V) : Sort (max 1 u v iv) where
    [homIsEquivalence         : IsEquivalence         R.Hom]
    [homHasSymmFun            : HasSymmFun            R.Hom]
    [homHasTransFun           : HasTransFun           R.Hom]
    [homIsGroupoidEquivalence : IsGroupoidEquivalence R.Hom]

    namespace GrpoidDesc

      variable {R : BundledRelation.{u} V} (desc : GrpoidDesc R)

      def toCatDesc : CatDesc R :=
      let _ : IsEquivalence         R.Hom := desc.homIsEquivalence;
      let _ : HasTransFun           R.Hom := desc.homHasTransFun;
      let _ : HasSymmFun            R.Hom := desc.homHasSymmFun;
      let _ : IsGroupoidEquivalence R.Hom := desc.homIsGroupoidEquivalence;
      ⟨⟩

    end GrpoidDesc

  end



  class HasCatProp (V : Universe.{v, vv}) [IsHomUniverse.{v, vv, iv, ivv} V] where
  (Cat                              : MetaProperty (BundledRelation.{u} V) V)
  (desc {R : BundledRelation.{u} V} : Cat R → CatDesc R)

  namespace HasCatProp

    structure Category (V : Universe.{v, vv}) [IsHomUniverse.{v, vv, iv, ivv} V]
                       [h : HasCatProp.{u} V] :
      Sort (max (u + 1) v vv) where
    {R : BundledRelation.{u} V}
    (C : h.Cat R)

    namespace Category

      section

        variable (V : Universe.{v, vv}) [IsHomUniverse.{v, vv, iv, ivv} V] [h : HasCatProp.{u} V]

        instance hasInstances : HasInstances.{u} (Category.{u} V) := ⟨λ A => A.R.α⟩

        def univ : Universe.{u, max (u + 1) v vv} := ⟨Category.{u} V⟩

      end

      variable {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv, ivv} V] [h : HasCatProp.{u} V]

      def Hom (A : Category V) : MetaRelation A V := A.R.Hom
      infix:20 " ⇾ " => CategoryTheory.HasCatProp.Category.Hom _

      instance (A : Category V) : IsPreorder            (Hom A) := (h.desc A.C).homIsPreorder
      instance (A : Category V) : HasTransFun           (Hom A) := (h.desc A.C).homHasTransFun
      instance (A : Category V) : IsCategoricalPreorder (Hom A) := (h.desc A.C).homIsCategoricalPreorder

      @[reducible] def idHom {A : Category V} (a : A) : a ⇾ a := HasRefl.refl a
      @[reducible] def compHom {A : Category V} {a b c : A} (f : a ⇾ b) (g : b ⇾ c) : a ⇾ c := g • f

    end Category

    structure DefCat {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv, ivv} V] [h : HasCatProp.{u} V]
                     {R : BundledRelation.{u} V} (desc : CatDesc R) where
    (C   : h.Cat R)
    [hEq : IsPreorderEq (h.desc C).homIsPreorder desc.homIsPreorder]

    namespace DefCat

      open Category

      variable {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv, ivv} V] [h : HasCatProp.{u} V]
               {R : BundledRelation.{u} V} {desc : CatDesc R}

      def toCategory (A : DefCat desc) : Category.{u} V :=
      { R := R,
        C := A.C }

      def catReflEq {A : DefCat desc} (a : toCategory A) :
        HasInstanceEquivalences.Rel (a ⇾ a) (idHom a)
                                            (desc.homIsPreorder.refl a) :=
      A.hEq.reflEq a

      def catTransEq {A : DefCat desc} {a b c : toCategory A} (f : a ⇾ b) (g : b ⇾ c) :
        HasInstanceEquivalences.Rel (a ⇾ c) (g • f)
                                            (desc.homIsPreorder.trans f g) :=
      A.hEq.transEq f g

    end DefCat

    class HasTrivialCatProp (V : Universe.{v, vv}) [IsHomUniverse.{v, vv, iv, ivv} V]
                            [h : HasCatProp.{u} V] where
    (cat {R : BundledRelation.{u} V} (desc : CatDesc R) : DefCat desc)

    namespace HasTrivialCatProp

      variable {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv, ivv} V] [HasCatProp.{u} V]
               [h : HasTrivialCatProp V]

      def defCat {R : BundledRelation.{u} V} {desc : CatDesc R} : DefCat desc := h.cat desc

    end HasTrivialCatProp

  end HasCatProp



  class IsCatUniverse (V : Universe.{v, vv}) [IsHomUniverse.{v, vv, iv, ivv} V] where
  [hasCat : HasCatProp.{max 1 u v} V]

  namespace IsCatUniverse

    variable (V : Universe.{v, vv}) [IsHomUniverse.{v, vv, iv, ivv} V]
             [hCatUniv : IsCatUniverse.{u} V]

    instance : HasCatProp.{max 1 u v} V := hCatUniv.hasCat

  end IsCatUniverse

end CategoryTheory
