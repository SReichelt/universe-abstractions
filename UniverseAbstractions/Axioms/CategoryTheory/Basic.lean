import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Relations
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Lemmas.DerivedFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v iv



namespace MetaRelation

  open HasFunctors HasLinearFunOp

  variable {α : Sort u} {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasInternalFunctors V]
           (R : MetaRelation α V)

  class HasSymmFun [HasSymm R] where
  (defSymmFun (a b : α) : R a b ⟶{λ f => f⁻¹} R b a)

  namespace HasSymmFun

    variable [HasSymm R] [h : HasSymmFun R]

    @[reducible] def symmFun (a b : α) : R a b ⟶ R b a := h.defSymmFun a b

    instance symm.isFunApp {a b : α} {e : R a b} : IsFunApp (R a b) e⁻¹ :=
    { F := symmFun R a b,
      a := e,
      e := byDef }

  end HasSymmFun

  class HasTransFun [HasTrans R] where
  (defTransFun    {a b   : α} (f : R a b) (c : α) : R b c ⟶{λ g => g • f} R a c)
  (defTransFunFun (a b c : α)                     : R a b ⟶{λ f => defTransFun f c} (R b c ⟶ R a c))

  namespace HasTransFun

    variable [HasTrans R] [h : HasTransFun R]

    @[reducible] def transFun {a b : α} (f : R a b) (c : α) : R b c ⟶ R a c := h.defTransFun f c
    @[reducible] def transFunFun (a b c : α) : R a b ⟶ R b c ⟶ R a c := h.defTransFunFun a b c

    instance trans.isFunApp {a b c : α} {f : R a b} {g : R b c} : IsFunApp (R b c) (g • f) :=
    { F := transFun R f c,
      a := g,
      e := byDef }

    instance transFun.isFunApp {a b c : α} {f : R a b} : IsFunApp (R a b) (transFun R f c) :=
    { F := transFunFun R a b c,
      a := f,
      e := byDef }

    variable [HasLinearFunOp V]

    def defRevTransFun (a : α) {b c : α} (g : R b c) : (R a b) ⟶{λ f => g • f} (R a c) :=
    swapFun (transFunFun R a b c) g
    ◄ byDef₂

    @[reducible] def revTransFun (a : α) {b c : α} (g : R b c) : R a b ⟶ R a c := defRevTransFun R a g

    def defRevTransFunFun (a b c : α) : R b c ⟶{λ g => revTransFun R a g} (R a b ⟶ R a c) :=
    defSwapFunFun (transFunFun R a b c)

    @[reducible] def revTransFunFun (a b c : α) : R b c ⟶ R a b ⟶ R a c := defRevTransFunFun R a b c

    instance revTransFun.isFunApp {a b c : α} {g : R b c} : IsFunApp (R b c) (revTransFun R a g) :=
    { F := revTransFunFun R a b c,
      a := g,
      e := byDef }

  end HasTransFun

  open HasRefl HasCongrArg HasTransFun HasSymmFun HasSubLinearFunOp HasFullFunOp

  class IsAssociative [HasTrans R] where
  (assoc {a b c d : α} (f : R a b) (g : R b c) (h : R c d) : (h • g) • f ≃ h • (g • f))

  class IsAssociative.IsAssociativeExt [HasTrans R] [IsAssociative R] [HasTransFun R] [HasLinearFunOp V] where
  (assocExt {a b c : α} (f : R a b) (g : R b c) (d : α) :
     transFun R f d • transFun R g d
     ≃{byDef • byArgDef ▻ λ h => assoc f g h ◅}
     transFun R (g • f) d)
  (assocExtExt {a b : α} (f : R a b) (c d : α) :
     revCompFunFun (R c d) (transFun R f d) • transFunFun R b c d
     ≃{byDef • byArgDef ▻ λ g => assocExt f g d ◅ byDef • byArgDef}
     transFunFun R a c d • transFun R f c)
  (assocExtExtExt (a b c d : α) :
     compFunFun (transFunFun R b c d) (R c d ⟶ R a d) •
     revCompFunFunFun (R c d) (R b d) (R a d) •
     transFunFun R a b d
     ≃{byDef • byArgDef • byArgDef₂ • byArgDef ▻
       λ f => assocExtExt f c d
       ◅ byDef • byArgDef}
     revCompFunFun (R b c) (transFunFun R a c d) • transFunFun R a b c)

  class IsSemigroupoid [HasLinearFunOp V] extends
    HasTrans R, IsAssociative R,
    HasTransFun R, IsAssociative.IsAssociativeExt R

  class IsCategoricalPreorder [IsPreorder R] extends IsAssociative R where
  (rightId {a b : α} (f : R a b) : f • refl a ≃ f)
  (leftId  {a b : α} (f : R a b) : refl b • f ≃ f)

  class IsCategoricalPreorder.IsCategoricalPreorderExt [IsPreorder R] [IsCategoricalPreorder R]
                                                       [HasTransFun R] [HasLinearFunOp V] extends
    IsAssociative.IsAssociativeExt R where
  (rightIdExt (a b : α) : transFun    R (refl a) b ≃{▻ λ f => rightId f ◅} idFun (R a b))
  (leftIdExt  (a b : α) : revTransFun R a (refl b) ≃{▻ λ f => leftId  f ◅} idFun (R a b))

  class IsCategory [HasLinearFunOp V] extends
    IsPreorder R, IsCategoricalPreorder R,
    HasTransFun R, IsCategoricalPreorder.IsCategoricalPreorderExt R

  instance categoryIsSemigroupoid [HasLinearFunOp V] [IsCategory R] : IsSemigroupoid R := ⟨⟩

  class IsGroupoidEquivalence [IsEquivalence R] extends IsCategoricalPreorder R where
  (leftInv  {a b : α} (f : R a b) : f⁻¹ • f ≃ refl (R := R) a)
  (rightInv {a b : α} (f : R a b) : f • f⁻¹ ≃ refl (R := R) b)

  class IsGroupoidEquivalence.IsGroupoidEquivalenceExt [IsEquivalence R] [IsGroupoidEquivalence R]
                                                       [HasTransFun R] [HasSymmFun R] [HasFullFunOp V] extends
    IsCategoricalPreorder.IsCategoricalPreorderExt R where
  (leftInvExt  (a b : α) : substFun (symmFun R a b) (transFunFun    R a b a)
                           ≃{byDef • byArgDef • byFunDef ▻ λ f => leftInv  f ◅}
                           constFun (R a b) (refl a))
  (rightInvExt (a b : α) : substFun (symmFun R a b) (revTransFunFun R b a b)
                           ≃{byDef • byArgDef • byFunDef ▻ λ f => rightInv f ◅}
                           constFun (R a b) (refl b))

  class IsGroupoid [HasFullFunOp V] extends
    IsEquivalence R, IsGroupoidEquivalence R,
    HasTransFun R, HasSymmFun R, IsGroupoidEquivalence.IsGroupoidEquivalenceExt R

  instance groupoidIsCategory [HasFullFunOp V] [IsGroupoid R] : IsCategory R := ⟨⟩

end MetaRelation
