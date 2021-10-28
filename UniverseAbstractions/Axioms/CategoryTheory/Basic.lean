import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Relations
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Lemmas.DerivedFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v iv



namespace MetaRelation

  open HasRefl HasFunctors HasCongrArg HasCongrFun HasLinearFunOp HasSubLinearFunOp HasFullFunOp
       HasTransFun HasSymmFun

  variable {α : Sort u} {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasInternalFunctors V]
           (R : MetaRelation α V)

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
