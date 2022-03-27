import UniverseAbstractions.CategoryTheory.Basic
import UniverseAbstractions.CategoryTheory.Functors
import UniverseAbstractions.CategoryTheory.NaturalTransformations
import UniverseAbstractions.CategoryTheory.Functors.Nested
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Lemmas.DerivedProductFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u uu v vv uv uuvv w ww iw iww



namespace CategoryTheory

  open Universe MetaRelation MetaFunctor HasTransFun HasSymmFun IsCategoricalPreorder
       HasCatProp HasCatProp.Category HasFunProp HasFunProp.Functor HasIsoRel HasIsoOp HasIsoNat
       HasFunctors

  namespace BundledRelation

    def productRel {U : Universe.{u, uu}} {V : Universe.{v, vv}} {W : Universe.{w, ww}}
                   [IsHomUniverse.{w, ww, iw, iww} W] [HasInternalProducts W]
                   (R : BundledRelation U W) (S : BundledRelation V W) :
      BundledRelation sort.{max 1 u v} W :=
    { A   := PProd R.A S.A,
      Hom := productRelation (lift R.Hom PProd.fst) (lift S.Hom PProd.snd) }

    def productCatDesc {U : Universe.{u, uu}} {V : Universe.{v, vv}} {W : Universe.{w, ww}}
                       [IsHomUniverse.{w, ww, iw, iww} W] [HasInternalProducts W]
                       [HasProducts.HasProductEq W W] [HasCatProp U W] [HasCatProp V W]
                       (A : Category U W) (B : Category V W) :
      CatDesc (productRel A.R B.R) :=
    let R : MetaRelation (PProd A.R.A B.R.A) W := MetaRelation.lift (Category.Hom A) PProd.fst;
    let S : MetaRelation (PProd A.R.A B.R.A) W := MetaRelation.lift (Category.Hom B) PProd.snd;
    { homIsPreorder            := productRelation.isPreorder            R S,
      homHasTransFun           := productRelation.hasTransFun           R S,
      homIsCategoricalPreorder := productRelation.isCategoricalPreorder R S }

  end BundledRelation



  class IsProdUniverse (U : Universe.{u, uu}) (V : Universe.{v, vv}) (W : Universe.{w, ww})
                       [IsHomUniverse.{w, ww, iw, iww} W] [HasInternalProducts W]
                       [HasProducts.HasProductEq W W] [HasCatProp U W] [HasCatProp V W]
                       [HasCatProp sort.{max 1 u v} W] where
  (defProductCat (A : Category U W) (B : Category V W) :
     DefCat (BundledRelation.productCatDesc A B))

  namespace IsProdUniverse

    section

      variable {U : Universe.{u, uu}} {V : Universe.{v, vv}} {W : Universe.{w, ww}}
               [IsHomUniverse W] [HasInternalProducts W] [HasProducts.HasProductEq W W]
               [HasCatProp U W] [HasCatProp V W] [HasCatProp sort.{max 1 u v} W]
               [h : IsProdUniverse U V W]

      def productCat (A : Category U W) (B : Category V W) : Category sort.{max 1 u v} W :=
      DefCat.toCategory (h.defProductCat A B)

    end

    section

      variable (U : Universe.{u, uu}) (V : Universe.{v, vv}) (W : Universe.{w, ww})
               [IsHomUniverse W] [HasInternalProducts W] [HasProducts.HasProductEq W W]
               [HasCatProp U W] [HasCatProp V W] [HasCatProp sort.{max 1 u v} W]
               [h : IsProdUniverse U V W]

      instance hasProducts : HasProducts (univ U W) (univ V W) (univ sort.{max 1 u v} W) :=
      { Prod  := productCat,
        intro := PProd.mk,
        fst   := PProd.fst,
        snd   := PProd.snd }

    end

    section

      variable (U : Universe.{u, uu}) (V : Universe.{v, vv}) (W : Universe.{w, ww})
               [IsHomUniverse W] [HasInternalProducts W] [HasProducts.HasProductEq W W]
               [IsCatUniverse U W] [IsCatUniverse V W] [IsCatUniverse sort.{max 1 u v} W]
               [h : IsProdUniverse U V W]

      instance hasProductEq : HasProducts.HasProductEq (univ U W) (univ V W) :=
      { introEq := λ P   => idIso P,
        fstEq   := λ a b => idIso a,
        sndEq   := λ a b => idIso b }

    end

  end IsProdUniverse



  class IsSortProdUniverse (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw, iww} W]
                           [IsSortNatUniverse.{u} W] [HasInternalProducts W]
                           [HasInternalProducts.HasProductExt W] extends
    IsProdUniverse sort.{max 1 u w} sort.{max 1 u w} W

  namespace IsSortProdUniverse

    open HasInternalProducts IsSortNatUniverse

    variable (W : Universe.{w, ww}) [IsHomUniverse W] [IsSortNatUniverse.{u} W]
             [HasInternalProducts W] [HasProductExt W] [h : IsSortProdUniverse W]

    instance hasInternalProducts : HasInternalProducts (univ W) :=
    { defIntroFun    := sorry,
      defIntroFunFun := sorry,
      defElimFun     := sorry,
      defElimFunFun  := sorry }

    instance hasProductExt [HasLinearCatFun W] : HasProductExt (univ W) :=
    { introEqExt      := sorry,
      elimEqExt       := sorry,
      elimEqExtExt    := sorry,
      elimEqExtExtExt := sorry }

  end IsSortProdUniverse

end CategoryTheory
