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

  open MetaRelation HasSymmFun HasTransFun HasFunctors HasCongrArg HasLinearFunOp

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

    variable {α : Sort u} {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasInternalFunctors V]
             {R S : MetaRelation α V} (F : MetaFunctor R S)

    class IsSymmFunctor.IsSymmFunctorExt [HasLinearFunOp V]
                                         [HasSymm R] [HasSymmFun R]
                                         [HasSymm S] [HasSymmFun S]
                                         [IsSymmFunctor F] where
    (symmEqExt (a b : α) :
       F.baseFun b a • symmFun R a b
       ≃{byArgDef ▻ λ f => symmEq f ◅ byDef}
       symmFun S a b • F.baseFun a b)

    class IsTransFunctor.IsTransFunctorExt [HasLinearFunOp V]
                                           [HasTrans R] [HasTransFun R]
                                           [HasTrans S] [HasTransFun S]
                                           [IsTransFunctor F] where
    (transEqExt {a b : α} (f : R a b) (c : α) :
       F.baseFun a c • transFun R f c
       ≃{byArgDef ▻ λ g => transEq f g ◅ byDef}
       transFun S (F f) c • F.baseFun b c)
    (transEqExtExt (a b c : α) :
       revCompFunFun (R b c) (F.baseFun a c) • transFunFun R a b c
       ≃{byDef • byArgDef ▻ λ f => transEqExt f c ◅ byDef • byArgDef • byArgDef}
       compFunFun (F.baseFun b c) (S a c) • transFunFun S a b c • F.baseFun a b)

  end

  @[reducible] def PreFunctor {α : Sort u} {β : Sort v} {W : Universe.{w}}
                              [HasIdentity.{w, iw} W] [HasInternalFunctors W]
                              (R : MetaRelation α W) (S : MetaRelation β W) (φ : α → β) :=
  MetaFunctor R (lift S φ)

end MetaFunctor



namespace CategoryTheory

  open MetaRelation MetaFunctor IsPreCategory IsoDesc.Equiv HasIsomorphisms HasIsoDescEq HasIsoToHomFun
       HasFunctors HasCongrArg HasLinearFunOp

  class IsSemigroupoidFunctor {M : HomUniverse.{w, iw}} {α : Sort u} {β : Sort v}
                              [hα : IsSemigroupoid M α] [hβ : IsSemigroupoid M β]
                              (φ : α → β) where
  (F         : PreFunctor hα.Hom hβ.Hom φ)
  [hTrans    : IsTransFunctor F]
  [hTransExt : IsTransFunctor.IsTransFunctorExt F]

  namespace IsSemigroupoidFunctor

    variable {M : HomUniverse.{w, iw}} {α : Sort u} {β : Sort v}
             [IsSemigroupoid M α] [IsSemigroupoid M β]
             (φ : α → β) [hφ : IsSemigroupoidFunctor φ]

    instance : IsTransFunctor hφ.F := hφ.hTrans
    instance : IsTransFunctor.IsTransFunctorExt hφ.F := hφ.hTransExt

  end IsSemigroupoidFunctor

  class IsPreCategoryFunctor {M : HomUniverse.{w, iw}} {α : Sort u} {β : Sort v}
                             [hα : IsPreCategory M α] [hβ : IsPreCategory M β]
                             (φ : α → β) extends
    IsSemigroupoidFunctor φ where
  [hRefl : IsReflFunctor F]

  namespace IsPreCategoryFunctor

    variable {M : HomUniverse.{w, iw}} {α : Sort u} {β : Sort v}
             [IsPreCategory M α] [IsPreCategory M β]
             (φ : α → β) [hφ : IsPreCategoryFunctor φ]

    instance : IsReflFunctor hφ.F := hφ.hRefl

    def mapHalfInv {a b : α} {f : Hom a b} {g : Hom b a} (h : HalfInv Hom f g) :
      HalfInv Hom (hφ.F f) (hφ.F g) :=
    hφ.hRefl.reflEq a • congrArg (hφ.F.baseFun a a) h • (hφ.hTrans.transEq f g)⁻¹

    def mapIsoDesc {a b : α} (e : IsoDesc.rel a b) : IsoDesc.rel (φ a) (φ b) :=
    { toHom    := hφ.F e.toHom,
      invHom   := hφ.F e.invHom,
      leftInv  := mapHalfInv φ e.leftInv,
      rightInv := mapHalfInv φ e.rightInv }

    def mapIsoDescReflEq (a : α) :
      mapIsoDesc φ (IsoDesc.refl a) ≃ IsoDesc.refl (φ a) :=
    hφ.hRefl.reflEq a

    def mapIsoDescSymmEq {a b : α} (e : IsoDesc.rel a b) :
      mapIsoDesc φ e⁻¹ ≃ (mapIsoDesc φ e)⁻¹ :=
    HasEquivalenceRelation.refl (mapIsoDesc φ e)⁻¹

    def mapIsoDescTransEq {a b c : α} (e : IsoDesc.rel a b) (f : IsoDesc.rel b c) :
      mapIsoDesc φ (f • e) ≃ mapIsoDesc φ f • mapIsoDesc φ e :=
    hφ.hTrans.transEq e.toHom f.toHom

    def congrArgIsoDesc {a b : α} {e₁ e₂ : IsoDesc.rel a b} (h : e₁ ≃ e₂) :
      mapIsoDesc φ e₁ ≃ mapIsoDesc φ e₂ :=
    congrArg (hφ.F.baseFun a b) h

  end IsPreCategoryFunctor

  class IsGroupoidFunctor {M : IsoUniverse.{w, iw}} {α : Sort u} {β : Sort v}
                          [hα : IsGroupoid M α] [hβ : IsGroupoid M β]
                          (φ : α → β) extends
    IsPreCategoryFunctor φ where
  [hSymm    : IsSymmFunctor F]
  [hSymmExt : IsSymmFunctor.IsSymmFunctorExt F]

  namespace IsGroupoidFunctor

    variable {M : IsoUniverse.{w, iw}} {α : Sort u} {β : Sort v}
             [IsGroupoid M α] [IsGroupoid M β]
             (φ : α → β) [hφ : IsGroupoidFunctor φ]

    instance : IsSymmFunctor hφ.F := hφ.hSymm
    instance : IsSymmFunctor.IsSymmFunctorExt hφ.F := hφ.hSymmExt

  end IsGroupoidFunctor



  open IsPreCategoryFunctor

  class IsIsoFunctor {M : HomUniverse.{w, iw}} {α : Sort u} {β : Sort v}
                     [IsPreCategory M α] [IsPreCategory M β]
                     [iα : HasIsomorphisms α] [iβ : HasIsomorphisms β]
                     (φ : α → β) [IsPreCategoryFunctor φ] where
  (E : PreFunctor iα.Iso iβ.Iso φ)
  (isoFunEq {a b : α} (e : Iso a b) : isoDesc (E e) ≃ mapIsoDesc φ (isoDesc e))

  namespace IsIsoFunctor

    variable {M : HomUniverse.{w, iw}} {α : Sort u} {β : Sort v}
             [hα : IsPreCategory M α] [hβ : IsPreCategory M β]
             [iα : HasIsomorphisms α] [iβ : HasIsomorphisms β]
             [HasIsoDescEq α] [HasIsoDescEq β]
             (φ : α → β) [hφ : IsPreCategoryFunctor φ] [iφ : IsIsoFunctor φ]

    def isoReflEq (a : α) :
      iφ.E (HasRefl.refl a) ≃ HasRefl.refl (R := iβ.Iso) (φ a) :=
    isoDescInj ((isoDescReflEq (φ a))⁻¹ •
                mapIsoDescReflEq φ a •
                congrArgIsoDesc φ (isoDescReflEq a) •
                isoFunEq (HasRefl.refl a))

    def isoSymmEq {a b : α} (e : Iso a b) :
      iφ.E e⁻¹ ≃ (iφ.E e)⁻¹ :=
    isoDescInj ((isoDescSymmEq (iφ.E e))⁻¹ •
                symmEquiv (isoFunEq e) •
                congrArgIsoDesc φ (isoDescSymmEq e) •
                isoFunEq e⁻¹)

    def isoTransEq {a b c : α} (e : Iso a b) (f : Iso b c) :
      iφ.E (f • e) ≃ iφ.E f • iφ.E e :=
    isoDescInj ((transEquiv (isoFunEq e) (isoFunEq f) •
                isoDescTransEq (iφ.E e) (iφ.E f))⁻¹ •
                mapIsoDescTransEq φ (isoDesc e) (isoDesc f) •
                congrArgIsoDesc φ (isoDescTransEq e f) •
                isoFunEq (f • e))

    instance isEquivalenceFunctor : IsEquivalenceFunctor iφ.E :=
    { reflEq  := isoReflEq  φ,
      symmEq  := isoSymmEq  φ,
      transEq := isoTransEq φ }

    class IsIsoFunctorExt [HasIsoToHomFun α] [HasIsoToHomFun β] where
    (isoFunEqExt (a b : α) : toHomFun (φ a) (φ b) • iφ.E.baseFun a b
                             ≃{byDef ▻ λ e => isoFunEq e ◅ byArgDef}
                             hφ.F.baseFun a b • toHomFun a b)
    [symmFunExt  : IsSymmFunctor.IsSymmFunctorExt   iφ.E]
    [transFunExt : IsTransFunctor.IsTransFunctorExt iφ.E]

    namespace IsIsoFunctorExt

      variable [HasIsoToHomFun α] [HasIsoToHomFun β] [IsIsoFunctorExt φ]

      instance isSymmFunctorExt  : IsSymmFunctor.IsSymmFunctorExt   iφ.E := symmFunExt
      instance isTransFunctorExt : IsTransFunctor.IsTransFunctorExt iφ.E := transFunExt

    end IsIsoFunctorExt

  end IsIsoFunctor

  class IsCategoryFunctor {M : IsoUniverse.{w, iw}} {α : Sort u} {β : Sort v}
                          [IsCategory M α] [IsCategory M β]
                          (φ : α → β) extends
    IsPreCategoryFunctor φ, IsIsoFunctor φ, IsIsoFunctor.IsIsoFunctorExt φ

  -- TODO: Show that this is also a groupoid functor with respect to `IsCategory.isoGroupoid`,
  --       and vice versa, that a groupoid functor is a category functor.

end CategoryTheory
