import UniverseAbstractions.Instances.Utils.Trivial
import UniverseAbstractions.Axioms.CategoryTheory.Basic
import UniverseAbstractions.Axioms.CategoryTheory.Functors



set_option autoBoundImplicitLocal false
--set_option pp.universes true
set_option synthInstance.maxHeartbeats 10000

universe u v iv w iw



namespace MetaRelation

  open IsCategoricalPreorder IsPreGroupoidEquivalence IsGroupoidEquivalence

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
    { leftInv  := λ _   => eq,
      rightInv := λ _   => eq,
      reflInv  := λ _   => eq,
      symmInv  := λ _   => eq,
      transInv := λ _ _ => eq }

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
      IsCategoricalPreorderExt R :=
    { rightIdExt := λ _ _ => funEq,
      leftIdExt  := λ _ _ => funEq }

    instance isPreGroupoidEquivalenceExt [IsEquivalence R] [IsPreGroupoidEquivalence R]
                                         [HasTransFun R] [HasSymmFun R] [HasFullFunOp V] :
      IsPreGroupoidEquivalenceExt R :=
    { leftInvExt  := λ _ _ => funEq,
      rightInvExt := λ _ _ => funEq }

    instance isGroupoidEquivalenceExt [IsEquivalence R] [IsGroupoidEquivalence R]
                                      [HasTransFun R] [HasSymmFun R] [HasFullFunOp V] :
      IsGroupoidEquivalenceExt R :=
    { symmInvExt     := λ _ _   => funEq,
      transInvExt    := λ _ _   => funEq,
      transInvExtExt := λ _ _ _ => funEq }

  end HasTrivialExtensionality

end MetaRelation



namespace MetaFunctor

  open MetaRelation

  section HasTrivialIdentity

    open HasTrivialIdentity

    variable {α : Sort u} {V W VW : Universe} [HasIdentity W] [HasTrivialIdentity W]
             [HasFunctors V W VW] {R : MetaRelation α V} {S : MetaRelation α W}
             (F : MetaFunctor R S)

    instance isReflFunctor  [HasRefl  R] [HasRefl  S] : IsReflFunctor  F := ⟨λ _   => eq⟩
    instance isSymmFunctor  [HasSymm  R] [HasSymm  S] : IsSymmFunctor  F := ⟨λ _   => eq⟩
    instance isTransFunctor [HasTrans R] [HasTrans S] : IsTransFunctor F := ⟨λ _ _ => eq⟩

    instance isPreorderFunctor    [IsPreorder    R] [IsPreorder    S] : IsPreorderFunctor    F := ⟨⟩
    instance isEquivalenceFunctor [IsEquivalence R] [IsEquivalence S] : IsEquivalenceFunctor F := ⟨⟩

  end HasTrivialIdentity

  section HasTrivialExtensionality

    open HasTrivialExtensionality

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



namespace CategoryTheory

  open MetaRelation MetaFunctor HasIsomorphisms HasIsoToHomFun IsIsoFunctor

  section HasTrivialIdentity

    open HasTrivialIdentity

    variable {M : HomUniverse.{v, iv}} [HasTrivialIdentity M.V]

    instance hasIsoDescEq (α : Sort u) [IsPreCategory M α] [HasIsomorphisms α] :
      HasIsoDescEq α :=
    { isoDescReflEq  := λ _   => eq (U := M.V),
      isoDescSymmEq  := λ _   => eq (U := M.V),
      isoDescTransEq := λ _ _ => eq (U := M.V) }

  end HasTrivialIdentity

  section HasTrivialFunctoriality

    open HasTrivialFunctoriality

    variable {M : HomUniverse.{v, iv}} [HasTrivialFunctoriality M.V M.V]

    instance hasIsoToHomFun (α : Sort u) [IsPreCategory M α] [hIso : HasIsomorphisms α] :
      HasIsoToHomFun α :=
    { isoSymmFun  := hasSymmFun  hIso.Iso,
      isoTransFun := hasTransFun hIso.Iso,
      defToHomFun := λ _ _ => defFun }

  end HasTrivialFunctoriality

  section HasTrivialExtensionality

    open HasTrivialExtensionality

    variable {M : IsoUniverse.{w, iw}} [HasTrivialExtensionality M.V M.V]

    instance hasIsoToHomFunExt (α : Sort u) [IsPreCategory M.toHomUniverse α]
                               [hIso : HasIsomorphisms α] [HasIsoDescEq α] [HasIsoToHomFun α] :
      HasIsoToHomFunExt α :=
    { toHomFunExt    := isTransFunctorExt (toHomMetaFunctor α),
      isoGroupoidExt := isGroupoidEquivalenceExt hIso.Iso }

    instance isIsoFunctorExt {α : Sort u} {β : Sort v}
                             [IsPreCategory M.toHomUniverse α] [IsPreCategory M.toHomUniverse β]
                             [HasIsomorphisms α] [HasIsomorphisms β]
                             [HasIsoDescEq α] [HasIsoDescEq β]
                             [HasIsoToHomFun α] [HasIsoToHomFun β]
                             (φ : α → β) [IsPreCategoryFunctor φ] [iφ : IsIsoFunctor φ] :
      IsIsoFunctorExt φ :=
    { isoFunEqExt := λ _ _ => funEq,
      symmFunExt  := isSymmFunctorExt  iφ.E,
      transFunExt := isTransFunctorExt iφ.E }

  end HasTrivialExtensionality

end CategoryTheory



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
