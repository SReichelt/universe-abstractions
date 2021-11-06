import UniverseAbstractions.Axioms.CategoryTheory.Meta
import UniverseAbstractions.Axioms.CategoryTheory.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w vw iv iw



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

    def mapHalfInv {a b : α} {f : a ⇾ b} {g : b ⇾ a} (h : HalfInv Hom f g) :
      HalfInv Hom (hφ.F f) (hφ.F g) :=
    hφ.hRefl.reflEq a • congrArg (hφ.F.baseFun a a) h • (hφ.hTrans.transEq f g)⁻¹

    def mapIsoDesc {a b : α} (e : a ⇽⇾ b) : φ a ⇽⇾ φ b :=
    { toHom    := hφ.F e.toHom,
      invHom   := hφ.F e.invHom,
      leftInv  := mapHalfInv φ e.leftInv,
      rightInv := mapHalfInv φ e.rightInv }

    def mapIsoDescReflEq (a : α) :
      mapIsoDesc φ (IsoDesc.refl a) ≃ IsoDesc.refl (φ a) :=
    hφ.hRefl.reflEq a

    def mapIsoDescSymmEq {a b : α} (e : a ⇽⇾ b) :
      mapIsoDesc φ e⁻¹ ≃ (mapIsoDesc φ e)⁻¹ :=
    HasEquivalenceRelation.refl (mapIsoDesc φ e)⁻¹

    def mapIsoDescTransEq {a b c : α} (e : a ⇽⇾ b) (f : b ⇽⇾ c) :
      mapIsoDesc φ (f • e) ≃ mapIsoDesc φ f • mapIsoDesc φ e :=
    hφ.hTrans.transEq e.toHom f.toHom

    def congrArgIsoDesc {a b : α} {e₁ e₂ : a ⇽⇾ b} (h : e₁ ≃ e₂) :
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
  (isoFunEq {a b : α} (e : a ⇿ b) : isoDesc (E e) ≃ mapIsoDesc φ (isoDesc e))

  namespace IsIsoFunctor

    variable {M : HomUniverse.{w, iw}} {α : Sort u} {β : Sort v}
             [hα : IsPreCategory M α] [hβ : IsPreCategory M β]
             [iα : HasIsomorphisms α] [iβ : HasIsomorphisms β]
             [HasIsoDescEq α] [HasIsoDescEq β]
             (φ : α → β) [hφ : IsPreCategoryFunctor φ] [iφ : IsIsoFunctor φ]

    def isoReflEq (a : α) :
      iφ.E (idIso a) ≃ idIso (φ a) :=
    isoDescInj ((isoDescReflEq (φ a))⁻¹ •
                mapIsoDescReflEq φ a •
                congrArgIsoDesc φ (isoDescReflEq a) •
                isoFunEq (idIso a))

    def isoSymmEq {a b : α} (e : a ⇿ b) :
      iφ.E e⁻¹ ≃ (iφ.E e)⁻¹ :=
    isoDescInj ((isoDescSymmEq (iφ.E e))⁻¹ •
                invEquiv (isoFunEq e) •
                congrArgIsoDesc φ (isoDescSymmEq e) •
                isoFunEq e⁻¹)

    def isoTransEq {a b c : α} (e : a ⇿ b) (f : b ⇿ c) :
      iφ.E (f • e) ≃ iφ.E f • iφ.E e :=
    isoDescInj ((compEquiv (isoFunEq e) (isoFunEq f) •
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
