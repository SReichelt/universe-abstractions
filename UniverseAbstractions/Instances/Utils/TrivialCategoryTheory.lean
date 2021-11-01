import UniverseAbstractions.Instances.Utils.Trivial
import UniverseAbstractions.Axioms.CategoryTheory.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true
set_option synthInstance.maxHeartbeats 10000

universe u v



namespace MetaRelation

  open IsCategoricalPreorder IsGroupoidEquivalence HasIsomorphisms HasIsoDescEq

  variable {α : Sort u} {V : Universe.{v}} [HasIdentity V] (R : MetaRelation α V)

  section HasTrivialIdentity

    open HasTrivialIdentity

    variable [h : HasTrivialIdentity V]

    instance isAssociative [HasTrans R] : IsAssociative R :=
    { assoc := λ _ _ _ => eq }

    instance isCategoricalPreorder [IsPreorder R] : IsCategoricalPreorder R :=
    { rightId := λ _ => eq,
      leftId  := λ _ => eq }

    instance isGroupoidEquivalence [IsEquivalence R] : IsGroupoidEquivalence R :=
    { leftInv  := λ _ => eq,
      rightInv := λ _ => eq }

    instance hasIsoDescEq [HasInternalFunctors V] [HasLinearFunOp V] [IsPreCategory R]
                          [HasIsomorphisms R] :
      HasIsoDescEq R :=
    { isoDescReflEq  := λ _   => h.eq,
      isoDescSymmEq  := λ _   => h.eq,
      isoDescTransEq := λ _ _ => h.eq }

  end HasTrivialIdentity

  section HasTrivialFunctoriality

    open HasTrivialFunctoriality

    variable [HasInternalFunctors V] [HasTrivialFunctoriality V V]

    instance hasIsoElimFun [IsPreCategory R] [hIso : HasIsomorphisms R] :
      HasIsoElimFun R :=
    { isoSymmFun    := hasSymmFun  hIso.Iso,
      isoTransFun   := hasTransFun hIso.Iso,
      defIsoElimFun := λ _ _ => defFun }

  end HasTrivialFunctoriality

  section HasTrivialExtensionality

    open HasTrivialExtensionality

    variable [HasInternalFunctors V] [HasTrivialExtensionality V V]

    instance isAssociativeExt [HasTrans R] [IsAssociative R]
                              [HasTransFun R] [HasLinearFunOp V] :
      IsAssociative.IsAssociativeExt R :=
    { assocExt       := λ _ _ _   => funEq,
      assocExtExt    := λ _ _ _   => funEq,
      assocExtExtExt := λ _ _ _ _ => funEq }

    instance isCategoricalPreorderExt [IsPreorder R] [IsCategoricalPreorder R]
                                      [HasTransFun R] [HasLinearFunOp V] :
      IsCategoricalPreorderExt R :=
    { rightIdExt := λ _ _ => funEq,
      leftIdExt  := λ _ _ => funEq }

    instance isGroupoidEquivalenceExt [IsEquivalence R] [IsGroupoidEquivalence R]
                                      [HasTransFun R] [HasSymmFun R] [HasFullFunOp V] :
      IsGroupoidEquivalenceExt R :=
    { leftInvExt  := λ _ _ => funEq,
      rightInvExt := λ _ _ => funEq }

    instance hasIsoDescEqExt [HasFullFunOp V] [IsPreCategory R]
                             [hIso : HasIsomorphisms R] [HasIsoDescEq R]
                             [HasIsoElimFun R] :
      HasIsoDescEqExt R :=
    { isoGroupoidExt       := isGroupoidEquivalenceExt hIso.Iso,
      isoDescTransEqExt    := λ _ _   => funEq,
      isoDescTransEqExtExt := λ _ _ _ => funEq }

  end HasTrivialExtensionality

end MetaRelation



namespace HasTrivialIdentity

  open HasLinearFunOp HasEquivOp

  instance hasEquivOpEq (U : Universe) [HasIdentity U] [HasTrivialIdentity U]
                        [HasInternalFunctors U] [HasLinearFunOp U] [HasLinearFunExt U]
                        [HasInternalEquivalences U] [HasEquivOp U] :
    HasEquivOpEq U :=
  ⟨⟩

end HasTrivialIdentity

namespace HasTrivialExtensionality

  open HasLinearFunOp HasEquivOp HasEquivOpFun

  instance hasEquivOpFunExt (U : Universe) [HasIdentity U] [HasInternalFunctors U]
                            [HasTrivialExtensionality U U] [HasFullFunOp U]
                            [HasInternalEquivalences U] [HasEquivOp U] [HasEquivOpFun U]
                            [HasEquivOpEq U] :
    HasEquivOpFunExt U :=
  ⟨⟩

end HasTrivialExtensionality
