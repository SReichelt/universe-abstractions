import UniverseAbstractions.Instances.Utils.Trivial
import UniverseAbstractions.Axioms.CategoryTheory.Meta
import UniverseAbstractions.Axioms.CategoryTheory.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true
set_option synthInstance.maxHeartbeats 10000

universe u u' v w vw iv iw



section MetaRelation

  open MetaRelation IsCategoricalPreorder IsGroupoidEquivalence

  variable {α : Sort u} {V : Universe.{v}} [HasIdentity V] (R : MetaRelation α V)

  namespace HasTrivialIdentity

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

  namespace HasTrivialExtensionality

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

  end HasTrivialExtensionality

end MetaRelation



section MetaFunctor

  open MetaRelation MetaFunctor

  namespace HasTrivialIdentity

    variable {α : Sort u} {V W VW : Universe} [HasIdentity W] [HasTrivialIdentity W]
             [HasFunctors V W VW] {R : MetaRelation α V} {S : MetaRelation α W}
             (F : MetaFunctor R S)

    instance isReflFunctor  [HasRefl  R] [HasRefl  S] : IsReflFunctor  F := ⟨λ _   => eq⟩
    instance isSymmFunctor  [HasSymm  R] [HasSymm  S] : IsSymmFunctor  F := ⟨λ _   => eq⟩
    instance isTransFunctor [HasTrans R] [HasTrans S] : IsTransFunctor F := ⟨λ _ _ => eq⟩

    instance isPreorderFunctor    [IsPreorder    R] [IsPreorder    S] : IsPreorderFunctor    F := ⟨⟩
    instance isEquivalenceFunctor [IsEquivalence R] [IsEquivalence S] : IsEquivalenceFunctor F := ⟨⟩

  end HasTrivialIdentity

  namespace HasTrivialExtensionality

    variable {α : Sort u} {V : Universe} [HasIdentity V] [HasInternalFunctors V]
             [HasTrivialExtensionality V V] {R S : MetaRelation α V} (F : MetaFunctor R S)

    instance isSymmFunctorExt [HasLinearFunOp V] [HasSymm R] [HasSymmFun R]
                              [HasSymm S] [HasSymmFun S] [IsSymmFunctor F] :
      IsSymmFunctor.IsSymmFunctorExt F :=
    { symmEqExt := λ _ _ => funEq }

    instance isTransFunctorExt [HasLinearFunOp V] [HasTrans R] [HasTransFun R]
                               [HasTrans S] [HasTransFun S] [IsTransFunctor F] :
      IsTransFunctor.IsTransFunctorExt F :=
    { transEqExt    := λ _ _   => funEq,
      transEqExtExt := λ _ _ _ => funEq }

  end HasTrivialExtensionality

end MetaFunctor



section MetaQuantification

  open MetaRelation MetaFunctor MetaQuantification IsNatural

  namespace HasTrivialIdentity

    variable {α : Sort u} {β : Sort u'} {V : Universe.{v}} {W : Universe.{w}}
             {VW : Universe.{vw}} [HasFunctors V W VW] [HasIdentity.{w, iw} W]
             [HasTrivialIdentity W] {R : MetaRelation α V} {S : MetaRelation β W}

    instance isNatural {φ ψ : α → β} (F : PreFunctor R S φ) (G : PreFunctor R S ψ)
                       (η : MetaQuantification S φ ψ) [hTrans : HasTrans S] :
      IsNatural F G η :=
    { nat := λ _ => eq }

  end HasTrivialIdentity

  namespace HasTrivialExtensionality

    variable {α : Sort u} {β : Sort u'} {W : Universe.{w}} [HasIdentity.{w, iw} W]
             [HasInternalFunctors W] [HasTrivialExtensionality W W]
             {R : MetaRelation α W} {S : MetaRelation β W}

    instance isNaturalExt [HasLinearFunOp W] [HasTrans S] [HasTransFun S]
                          {φ ψ : α → β} (F : PreFunctor R S φ) (G : PreFunctor R S ψ)
                          (η : MetaQuantification S φ ψ) [h : IsNatural F G η] :
      IsNaturalExt F G η :=
    { natExt := λ _ _ => funEq }

  end HasTrivialExtensionality

end MetaQuantification
