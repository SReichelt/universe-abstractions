import UniverseAbstractions.Axioms.CategoryTheory.Isomorphisms
import UniverseAbstractions.Axioms.CategoryTheory.HigherCategoryTheory.Basic



set_option autoBoundImplicitLocal false
set_option synthInstance.maxHeartbeats 2000
--set_option pp.universes true

universe u v vv w ww iv iw



namespace CategoryTheory

  open MetaRelation MetaFunctor MetaQuantification HasTransFun HasSymmFun
       IsAssociative IsCategoricalPreorder IsGroupoidEquivalence IsSymmFunctor IsTransFunctor
       IsCategory IsGroupoid IsGroupoidFunctor
       HasFunProp HasFunProp.Functor HasIsoRel HasIsoOp HasIsomorphisms
       HasFunctors HasCongrArg HasCongrFun HasLinearFunOp

  namespace IsCategory

    namespace HasIsomorphisms

      variable {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv} V] [HasSubLinearFunOp V]
               [HasNonLinearFunOp V]

      class HasIsomorphismsExt (α : Sort u) [hα : IsCategory V α] [h : HasIsomorphisms α] where
      [toHomIsTransFunctorExt      : IsTransFunctor.IsTransFunctorExt (toHomMetaFunctor α)]
      [isoIsGroupoidEquivalenceExt : IsGroupoidEquivalenceExt Iso (h := isoIsGroupoidEquivalence α)]

      namespace HasIsomorphismsExt

        variable (α : Sort u) [hα : IsCategory V α] [hαIso : HasIsomorphisms α]
                 [h : HasIsomorphismsExt α]

        instance : IsTransFunctor.IsTransFunctorExt (toHomMetaFunctor α) := h.toHomIsTransFunctorExt
        instance : IsGroupoidEquivalenceExt hαIso.Iso := h.isoIsGroupoidEquivalenceExt

        def isoGroupoidExt : IsGroupoidExt α (hα := isoGroupoid α) :=
        let _ := isoGroupoid α;
        { homIsGroupoidEquivalenceExt := h.isoIsGroupoidEquivalenceExt }

      end HasIsomorphismsExt

    end HasIsomorphisms

  end IsCategory


  namespace IsGroupoid

    open HasIsomorphisms

    variable {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv} V] [HasSubLinearFunOp V]
             [HasNonLinearFunOp V] [HasLinearFunExt V] (α : Sort u) [hα : IsGroupoid V α]
             [hαExt : IsGroupoidExt α]

    instance hasIsomorphismsExt : HasIsomorphismsExt α :=
    { toHomIsTransFunctorExt      := IsTransFunctorExt.translate (idFun.metaFunctor hα.Hom),
      isoIsGroupoidEquivalenceExt := IsGroupoidEquivalenceExt.translate hα.Hom }

  end IsGroupoid



  namespace IsIsoUniverse

    class IsIsoUniverseExt (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw} W]
                           [HasSubLinearFunOp W] [HasNonLinearFunOp W]
                           [hFunUniv : IsFunUniverse.{u} W] [hNatUniv : IsNatUniverse.{u} W]
                           [hIsoUniv : IsIsoUniverse.{u} W] where
    [hasIsoExt (α : Sort (max 1 u w)) [IsCategory W α] : HasIsomorphismsExt α]

    namespace IsIsoUniverseExt

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iv} W] [HasSubLinearFunOp W]
               [HasNonLinearFunOp W] [IsFunUniverse.{u} W] [IsNatUniverse.{u} W]
               [IsIsoUniverse.{u} W] [h : IsIsoUniverseExt.{u} W]

      instance (α : Sort (max 1 u w)) [IsCategory W α] : HasIsomorphismsExt α := h.hasIsoExt α

    end IsIsoUniverseExt

  end IsIsoUniverse

end CategoryTheory
