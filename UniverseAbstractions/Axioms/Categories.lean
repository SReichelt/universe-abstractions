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

  variable {α : Sort u} {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasEmbeddedFunctors V]
           (R : MetaRelation α V)

  class HasSymmFun [HasSymm R] where
  (defSymmFun (a b : α) : R a b ⟶[λ f => f⁻¹] R b a)

  namespace HasSymmFun

    variable [HasSymm R] [h : HasSymmFun R]

    @[reducible] def symmFun (a b : α) : R a b ⟶ R b a := h.defSymmFun a b

  end HasSymmFun

  class HasTransFun [HasTrans R] where
  (defTransFun    {a b   : α} (f : R a b) (c : α) : R b c ⟶[λ g => g • f] R a c)
  (defTransFunFun (a b c : α)                     : R a b ⟶[λ f => defTransFun f c] (R b c ⟶ R a c))

  namespace HasTransFun

    variable [HasTrans R] [h : HasTransFun R]

    @[reducible] def transFun {a b : α} (f : R a b) (c : α) : R b c ⟶ R a c := h.defTransFun f c
    @[reducible] def transFunFun (a b c : α) : R a b ⟶ R b c ⟶ R a c := h.defTransFunFun a b c

    variable [HasLinearFunOp V]

    def defRevTransFun (a : α) {b c : α} (g : R b c) : (R a b) ⟶[λ f => g • f] (R a c) :=
    swapFun (transFunFun R a b c) g
    ◄ byDef₂

    @[reducible] def revTransFun (a : α) {b c : α} (g : R b c) : R a b ⟶ R a c := defRevTransFun R a g

    def defRevTransFunFun (a b c : α) : R b c ⟶[λ g => revTransFun R a g] (R a b ⟶ R a c) :=
    defSwapFunFun (transFunFun R a b c)

    @[reducible] def revTransFunFun (a b c : α) : R b c ⟶ R a b ⟶ R a c := defRevTransFunFun R a b c

  end HasTransFun

  open HasRefl HasCongrArg HasTransFun HasSymmFun HasSubLinearFunOp HasFullFunOp

  class IsSemigroupoid [HasTrans R] [HasTransFun R] [HasLinearFunOp V] where
  (assoc {a b c d : α} (f : R a b) (g : R b c) (h : R c d) : (h • g) • f ≃ h • (g • f))
  (assocExt {a b c : α} (f : R a b) (g : R b c) (d : α) :
     transFun R f d • transFun R g d
     ≃[λ h => byDef⁻¹ • assoc f g h • (byDef • byArgDef • byDef)]
     transFun R (g • f) d)
  (assocExtExt {a b : α} (f : R a b) (c d : α) :
     revCompFunFun (R c d) (transFun R f d) • transFunFun R b c d
     ≃[λ g => (byDef • byArgDef • byDef)⁻¹ • assocExt f g d • (byDef • byArgDef • byDef)]
     transFunFun R a c d • transFun R f c)
  (assocExtExtExt (a b c d : α) :
     compFunFun (transFunFun R b c d) (R c d ⟶ R a d) •
     revCompFunFunFun (R c d) (R b d) (R a d) •
     transFunFun R a b d
     ≃[λ f => (byDef • byArgDef • byDef)⁻¹ •
              assocExtExt f c d •
              (byDef • byArgDef • byArgDef₂ • byArgDef • byDef)]
     revCompFunFun (R b c) (transFunFun R a c d) • transFunFun R a b c)

  class IsCategory [IsPreorder R] [HasTransFun R] [HasLinearFunOp V] extends IsSemigroupoid R where
  (rightId {a b : α} (f : R a b) : f • refl a ≃ f)
  (leftId  {a b : α} (f : R a b) : refl b • f ≃ f)
  (rightIdExt (a b : α) : transFun    R (refl a) b
                          ≃[λ f => byDef⁻¹ • rightId f • byDef]
                          idFun (R a b))
  (leftIdExt  (a b : α) : revTransFun R a (refl b)
                          ≃[λ f => byDef⁻¹ • leftId  f • byDef]
                          idFun (R a b))

  class IsGroupoid [IsEquivalence R] [HasTransFun R] [HasSymmFun R] [HasFullFunOp V] extends IsCategory R where
  (leftInv  {a b : α} (f : R a b) : f⁻¹ • f ≃ refl (R := R) a)
  (rightInv {a b : α} (f : R a b) : f • f⁻¹ ≃ refl (R := R) b)
  (leftInvExt  (a b : α) : substFun (symmFun R a b) (transFunFun    R a b a)
                           ≃[λ f => byDef⁻¹ • leftInv  f • (byDef • byArgDef • byFunDef • byDef)]
                           constFun (R a b) (refl a))
  (rightInvExt (a b : α) : substFun (symmFun R a b) (revTransFunFun R b a b)
                           ≃[λ f => byDef⁻¹ • rightInv f • (byDef • byArgDef • byFunDef • byDef)]
                           constFun (R a b) (refl b))

end MetaRelation
