import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Relations
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.CategoryTheory.Basic
import UniverseAbstractions.Lemmas.DerivedFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w vw iv iw



class MetaFunctor {α : Sort u} {V : Universe.{v}} {W : Universe.{w}} {VW : Universe.{vw}}
                  [HasFunctors V W VW] (R : MetaRelation α V) (S : MetaRelation α W) :
  Sort (max 1 u vw) where
(baseFun (a b : α) : R a b ⟶ S a b)

namespace MetaFunctor

  open MetaRelation IsPreCategory IsoDesc.Equiv HasIsomorphisms HasIsoDescEq HasIsoElimFun
       HasFunctors HasCongrArg HasLinearFunOp

  section

    variable {α : Sort u} {V : Universe.{v}} {W : Universe.{w}} {VW : Universe.{vw}}
             [HasIdentity.{w, iw} W] [HasFunctors V W VW]
             {R : MetaRelation α V} {S : MetaRelation α W}

    instance coeFun : CoeFun (MetaFunctor R S) (λ _ => ∀ {a b}, R a b → S a b) :=
    ⟨λ F {a b} => apply (F.baseFun a b)⟩

    variable (F : MetaFunctor R S)

    class IsReflFunctor  [HasRefl  R] [HasRefl  S] where
    (reflEq  (a     : α)                         : F (HasRefl.refl a) ≃ HasRefl.refl (R := S) a)

    class IsSymmFunctor  [HasSymm  R] [HasSymm  S] where
    (symmEq  {a b   : α} (f : R a b)             : F f⁻¹ ≃ (F f)⁻¹)

    class IsTransFunctor [HasTrans R] [HasTrans S] where
    (transEq {a b c : α} (f : R a b) (g : R b c) : F (g • f) ≃ F g • F f)

    class IsPreorderFunctor [IsPreorder R] [IsPreorder S] extends
      IsReflFunctor F, IsTransFunctor F

    class IsEquivalenceFunctor [IsEquivalence R] [IsEquivalence S] extends
      IsPreorderFunctor F, IsSymmFunctor F

  end

  section

    variable {α : Sort u} {V : Universe} [HasIdentity V] [HasInternalFunctors V]
             {R S : MetaRelation α V} (F : MetaFunctor R S)

    class IsSymmFunctor.IsSymmFunctorExt [HasLinearFunOp V]
                                         [HasSymm R] [HasSymmFun R]
                                         [HasSymm S] [HasSymmFun S]
                                         [IsSymmFunctor F] where
    (symmEqExt (a b : α) :
       F.baseFun b a • HasSymmFun.symmFun R a b
       ≃{byArgDef ▻ λ f => symmEq f ◅ byDef}
       HasSymmFun.symmFun S a b • F.baseFun a b)

    class IsTransFunctor.IsTransFunctorExt [HasLinearFunOp V]
                                           [HasTrans R] [HasTransFun R]
                                           [HasTrans S] [HasTransFun S]
                                           [IsTransFunctor F] where
    (transEqExt {a b : α} (f : R a b) (c : α) :
       F.baseFun a c • HasTransFun.transFun R f c
       ≃{byArgDef ▻ λ g => transEq f g ◅ byDef}
       HasTransFun.transFun S (F f) c • F.baseFun b c)
    (transEqExtExt (a b c : α) :
       revCompFunFun (R b c) (F.baseFun a c) • HasTransFun.transFunFun R a b c
       ≃{byDef • byArgDef ▻ λ f => transEqExt f c ◅ byDef • byArgDef • byArgDef}
       compFunFun (F.baseFun b c) (S a c) • HasTransFun.transFunFun S a b c • F.baseFun a b)

    class IsSemigroupoidFunctor [HasLinearFunOp V] [IsSemigroupoid R] [IsSemigroupoid S] extends
      IsTransFunctor F, IsTransFunctor.IsTransFunctorExt F

    class IsPreCategoryFunctor [HasLinearFunOp V] [IsPreCategory R] [IsPreCategory S] extends
      IsSemigroupoidFunctor F, IsReflFunctor F

    namespace IsPreCategoryFunctor

      variable [HasLinearFunOp V] [IsPreCategory R] [IsPreCategory S] [IsPreCategoryFunctor F]

      def mapHalfInv {a b : α} {f : R a b} {g : R b a} (h : HalfInv R f g) :
        HalfInv S (F f) (F g) :=
      IsReflFunctor.reflEq a • congrArg (F.baseFun a a) h • (IsTransFunctor.transEq f g)⁻¹

      def mapIsoDesc {a b : α} (e : (IsoDesc.rel R) a b) : (IsoDesc.rel S) a b :=
      { f        := F e.f,
        g        := F e.g,
        leftInv  := mapHalfInv F e.leftInv,
        rightInv := mapHalfInv F e.rightInv }

      def mapIsoDescReflEq (a : α) :
        mapIsoDesc F (IsoDesc.refl R a) ≃ IsoDesc.refl S a :=
      IsReflFunctor.reflEq a

      def mapIsoDescSymmEq {a b : α} (e : (IsoDesc.rel R) a b) :
        mapIsoDesc F e⁻¹ ≃ (mapIsoDesc F e)⁻¹ :=
      HasEquivalenceRelation.refl (mapIsoDesc F e)⁻¹

      def mapIsoDescTransEq {a b c : α} (e : (IsoDesc.rel R) a b) (f : (IsoDesc.rel R) b c) :
        mapIsoDesc F (f • e) ≃ mapIsoDesc F f • mapIsoDesc F e :=
      IsTransFunctor.transEq e.f f.f

      def congrArgIsoDesc {a b : α} {e₁ e₂ : (IsoDesc.rel R) a b} (h : e₁ ≃ e₂) :
        mapIsoDesc F e₁ ≃ mapIsoDesc F e₂ :=
      congrArg (F.baseFun a b) h

    end IsPreCategoryFunctor

    class IsGroupoidFunctor [HasFullFunOp V] [IsGroupoid R] [IsGroupoid S] extends
      IsPreCategoryFunctor F, IsSymmFunctor F

    open IsPreCategoryFunctor

    class HasIsoFunctor [HasLinearFunOp V]
                        [IsPreCategory R] [HasIsomorphisms R]
                        [IsPreCategory S] [HasIsomorphisms S] extends
      IsPreCategoryFunctor F where
    (isoFun : MetaFunctor (Iso R) (Iso S))
    (isoFunEq {a b : α} (e : Iso R a b) : isoDesc (isoFun e) ≃ (mapIsoDesc F) (isoDesc e))

    namespace HasIsoFunctor

      variable [HasLinearFunOp V] [IsPreCategory R] [HasIsomorphisms R] [HasIsoDescEq R]
               [IsPreCategory S] [HasIsomorphisms S] [HasIsoDescEq S] [HasIsoFunctor F]

      def isoReflEq (a : α) :
        (isoFun F) (HasRefl.refl a) ≃ HasRefl.refl (R := Iso S) a :=
      isoDescInj ((isoDescReflEq a)⁻¹ •
                  mapIsoDescReflEq F a •
                  congrArgIsoDesc F (isoDescReflEq a) •
                  isoFunEq (HasRefl.refl a))

      def isoSymmEq {a b : α} (e : Iso R a b) :
        (isoFun F) e⁻¹ ≃ ((isoFun F) e)⁻¹ :=
      isoDescInj ((isoDescSymmEq ((isoFun F) e))⁻¹ •
                  symmEquiv S (isoFunEq e) •
                  congrArgIsoDesc F (isoDescSymmEq e) •
                  isoFunEq e⁻¹)

      def isoTransEq {a b c : α} (e : Iso R a b) (f : Iso R b c) :
        (isoFun F) (f • e) ≃ (isoFun F) f • (isoFun F) e :=
      isoDescInj ((transEquiv S (isoFunEq e) (isoFunEq f) •
                  isoDescTransEq ((isoFun F) e) ((isoFun F) f))⁻¹ •
                  mapIsoDescTransEq F (isoDesc e) (isoDesc f) •
                  congrArgIsoDesc F (isoDescTransEq e f) •
                  isoFunEq (f • e))

      instance isEquivalenceFunctor : IsEquivalenceFunctor (isoFun F) :=
      { reflEq  := isoReflEq  F,
        symmEq  := isoSymmEq  F,
        transEq := isoTransEq F }

      class HasIsoFunctorExt [HasIsoElimFun R] [HasIsoElimFun S] where
      (isoFunEqExt (a b : α) : isoElimFun S a b • (isoFun F).baseFun a b
                               ≃{byDef ▻ λ e => isoFunEq e ◅ byArgDef}
                               F.baseFun a b • isoElimFun R a b)
      [symmFunExt  : IsSymmFunctor.IsSymmFunctorExt   (isoFun F)]
      [transFunExt : IsTransFunctor.IsTransFunctorExt (isoFun F)]

      namespace HasIsoFunctorExt

        variable [HasIsoElimFun R] [HasIsoElimFun S] [HasIsoFunctorExt F]

        instance isSymmFunctorExt  : IsSymmFunctor.IsSymmFunctorExt   (isoFun F) := symmFunExt
        instance isTransFunctorExt : IsTransFunctor.IsTransFunctorExt (isoFun F) := transFunExt

      end HasIsoFunctorExt

    end HasIsoFunctor

    class IsCategoryFunctor [HasFullFunOp V] [IsCategory R] [IsCategory S] extends
      HasIsoFunctor F, HasIsoFunctor.HasIsoFunctorExt F

    namespace IsCategoryFunctor

      open HasIsoFunctor

      variable [HasFullFunOp V] [IsCategory R] [IsCategory S] [IsCategoryFunctor F]

      instance isSemigroupoidFunctor : IsSemigroupoidFunctor (isoFun F) := ⟨⟩
      instance isPreCategoryFunctor  : IsPreCategoryFunctor  (isoFun F) := ⟨⟩
      instance isGroupoidFunctor     : IsGroupoidFunctor     (isoFun F) := ⟨⟩

    end IsCategoryFunctor

  end

end MetaFunctor
