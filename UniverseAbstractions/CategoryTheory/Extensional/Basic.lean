import UniverseAbstractions.CategoryTheory.Basic
import UniverseAbstractions.CategoryTheory.Extensional.Meta



set_option autoBoundImplicitLocal false
set_option synthInstance.maxHeartbeats 3000
--set_option pp.universes true

universe u v vv iv ivv



namespace CategoryTheory

  open MetaRelation IsAssociative IsCategoricalPreorder IsGroupoidEquivalence

  variable {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv, ivv} V]

  namespace SemicatDesc

    structure SemicatDescExt (R : BundledRelation.{u} V) extends SemicatDesc R :
      Sort (max 1 u v iv) where
    [homIsAssociativeExt : IsAssociativeExt R.Hom]

  end SemicatDesc

  namespace CatDesc

    structure CatDescExt (R : BundledRelation.{u} V) extends CatDesc R :
      Sort (max 1 u v iv) where
    [homIsCategoricalPreorderExt : IsCategoricalPreorderExt R.Hom]

    namespace CatDescExt

      variable {R : BundledRelation.{u} V} (desc : CatDescExt R)

      def toSemicatDescExt : SemicatDesc.SemicatDescExt R :=
      let _ : IsPreorder               R.Hom := desc.homIsPreorder;
      let _ : HasTransFun              R.Hom := desc.homHasTransFun;
      let _ : IsCategoricalPreorder    R.Hom := desc.homIsCategoricalPreorder;
      let _ : IsCategoricalPreorderExt R.Hom := desc.homIsCategoricalPreorderExt;
      ⟨toSemicatDesc desc.toCatDesc⟩

    end CatDescExt

  end CatDesc

  namespace GrpoidDesc

    variable [HasSubLinearFunOp V] [HasNonLinearFunOp V]

    local instance : HasAffineFunOp V := ⟨⟩
    local instance : HasFullFunOp   V := ⟨⟩

    class GrpoidDescExt (R : BundledRelation.{u} V) extends GrpoidDesc R :
      Sort (max 1 u v iv) where
    [homIsGroupoidEquivalenceExt : IsGroupoidEquivalenceExt R.Hom]

    namespace GrpoidDescExt

      variable {R : BundledRelation.{u} V} (desc : GrpoidDescExt R)

      def toCatDescExt : CatDesc.CatDescExt R :=
      let _ : IsEquivalence            R.Hom := desc.homIsEquivalence;
      let _ : HasTransFun              R.Hom := desc.homHasTransFun;
      let _ : HasSymmFun               R.Hom := desc.homHasSymmFun;
      let _ : IsGroupoidEquivalence    R.Hom := desc.homIsGroupoidEquivalence;
      let _ : IsGroupoidEquivalenceExt R.Hom := desc.homIsGroupoidEquivalenceExt;
      ⟨toCatDesc desc.toGrpoidDesc⟩

    end GrpoidDescExt

  end GrpoidDesc

end CategoryTheory
