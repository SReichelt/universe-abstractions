import UniverseAbstractions.Instances.Utils.Trivial
import UniverseAbstractions.Axioms.CategoryTheory.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true
set_option synthInstance.maxHeartbeats 10000

universe u v



namespace MetaRelation

  variable {α : Sort u} {V : Universe.{v}} [HasIdentity V] (R : MetaRelation α V)

  section HasTrivialIdentity

    open HasTrivialIdentity

    variable [HasTrivialIdentity V]

    instance isAssociative [HasTrans R] : IsAssociative R :=
    { assoc := λ _ _ _ => eq }

    instance isCategoricalPreorder [IsPreorder R] : IsCategoricalPreorder R :=
    { rightId := λ _ => eq,
      leftId  := λ _ => eq }

    instance isGroupoidEquivalence [IsEquivalence R] : IsGroupoidEquivalence R :=
    { leftInv  := λ _ => eq,
      rightInv := λ _ => eq }

  end HasTrivialIdentity

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
      IsCategoricalPreorder.IsCategoricalPreorderExt R :=
    { rightIdExt := λ _ _ => funEq,
      leftIdExt  := λ _ _ => funEq }

    instance isGroupoidEquivalenceExt [IsEquivalence R] [IsGroupoidEquivalence R]
                                      [HasTransFun R] [HasSymmFun R] [HasFullFunOp V] :
      IsGroupoidEquivalence.IsGroupoidEquivalenceExt R :=
    { leftInvExt  := λ _ _ => funEq,
      rightInvExt := λ _ _ => funEq }

  end HasTrivialExtensionality

end MetaRelation
