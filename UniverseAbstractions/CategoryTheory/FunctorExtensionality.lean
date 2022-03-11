import UniverseAbstractions.CategoryTheory.Basic
import UniverseAbstractions.CategoryTheory.Functors
import UniverseAbstractions.CategoryTheory.NaturalTransformations
import UniverseAbstractions.CategoryTheory.Isomorphisms
import UniverseAbstractions.CategoryTheory.FunctorExtensionality.LinearNatIso
import UniverseAbstractions.CategoryTheory.FunctorExtensionality.AffineNatIso
import UniverseAbstractions.CategoryTheory.FunctorExtensionality.FullNatIso



set_option autoBoundImplicitLocal false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 1000
--set_option pp.universes true

universe u w ww iw iww



namespace CategoryTheory

  open IsCatUniverse HasIsoNat HasIsoNaturality

  namespace IsIsoUniverse

    variable (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw, iww} W] [IsCatUniverse.{u} W]
             [IsFunUniverse.{u} W] [IsNatUniverse.{u} W] [h : IsIsoUniverse.{u} W]

    class HasLinearNaturalIsomorphisms [hLinFun : IsFunUniverse.HasLinearFunctors W]
                                       [hNatLinFun : IsNatUniverse.HasLinearFunctors W] where
    [hasRightIdNat        (A B     : Category W) : HasRightIdNat        A B]
    [hasLeftIdNat         (A B     : Category W) : HasLeftIdNat         A B]
    [hasSwapRevAppNat     (A B     : Category W) : HasSwapRevAppNat     A B]
    [hasSwapCompFunNat    (A B C   : Category W) : HasSwapCompFunNat    A B C]
    [hasSwapRevCompFunNat (A B C   : Category W) : HasSwapRevCompFunNat A B C]
    [hasCompAssocNat      (A B C D : Category W) : HasCompAssocNat      A B C D]

    namespace HasLinearNaturalIsomorphisms

      variable [IsFunUniverse.HasLinearFunctors W] [IsNatUniverse.HasLinearFunctors W]

      -- Lean bug :-(
      noncomputable instance trivial [h : HasTrivialNaturalIsomorphisms W] : HasLinearNaturalIsomorphisms W :=
      { hasRightIdNat        := λ _ _     => { defRightIdNat              := λ _ => HasTrivialNaturalityCondition.defNatIso,
                                               defRightIdNatNat           := DefNatNatIso.trivial DefNatNatIsoBase.trivial },
        hasLeftIdNat         := λ _ _     => { defLeftIdNat               := λ _ => HasTrivialNaturalityCondition.defNatIso,
                                               defLeftIdNatNat            := DefNatNatIso.trivial DefNatNatIsoBase.trivial },
        hasSwapRevAppNat     := λ _ _     => { defSwapRevAppNat           := λ _ => HasTrivialNaturalityCondition.defNatIso,
                                               defSwapRevAppNatNat        := DefNatNatIso.trivial DefNatNatIsoBase.trivial },
        hasSwapCompFunNat    := λ _ _ _   => { defSwapCompFunNat          := λ _ _ => HasTrivialNaturalityCondition.defNatIso,
                                               defSwapCompFunNatNat       := λ _ => DefNatNatIso.trivial DefNatNatIsoBase.trivial,
                                               defSwapCompFunNatNatNat    := DefNatNatNatIso.trivial DefNatNatNatIsoBase.trivial DefNatNatIsoBase.trivial },
        hasSwapRevCompFunNat := λ _ _ _   => { defSwapRevCompFunNat       := λ _ _ => HasTrivialNaturalityCondition.defNatIso,
                                               defSwapRevCompFunNatNat    := λ _ => DefNatNatIso.trivial DefNatNatIsoBase.trivial,
                                               defSwapRevCompFunNatNatNat := DefNatNatNatIso.trivial DefNatNatNatIsoBase.trivial DefNatNatIsoBase.trivial },
        hasCompAssocNat      := λ _ _ _ _ => { defCompAssocNat            := λ _ _ _ => HasTrivialNaturalityCondition.defNatIso,
                                               defCompAssocNatNat         := λ _ _ => DefNatNatIso.trivial DefNatNatIsoBase.trivial,
                                               defCompAssocNatNatNat      := λ _ => DefNatNatNatIso.trivial DefNatNatNatIsoBase.trivial DefNatNatIsoBase.trivial,
                                               defCompAssocNatNatNatNat   := DefNatNatNatNatIso.trivial DefNatNatNatNatIsoBase.trivial DefNatNatNatIsoBase.trivial DefNatNatIsoBase.trivial } }

      instance hasLinearFunExt [h : HasLinearNaturalIsomorphisms W] :
        HasLinearFunOp.HasLinearFunExt (univ W) :=
      { rightId              := λ {A B} F         => ((h.hasRightIdNat A B).defRightIdNat F).η,
        rightIdExt           := λ A B             => (h.hasRightIdNat A B).defRightIdNatNat.η,
        leftId               := λ {A B} F         => ((h.hasLeftIdNat A B).defLeftIdNat F).η,
        leftIdExt            := λ A B             => (h.hasLeftIdNat A B).defLeftIdNatNat.η,
        swapRevApp           := λ {A B} F         => ((h.hasSwapRevAppNat A B).defSwapRevAppNat F).η,
        swapRevAppExt        := λ A B             => (h.hasSwapRevAppNat A B).defSwapRevAppNatNat.η,
        swapCompFun          := λ {A B} F a C     => ((h.hasSwapCompFunNat A B C).defSwapCompFunNat F a).η,
        swapCompFunExt       := λ {A B} F C       => ((h.hasSwapCompFunNat A B C).defSwapCompFunNatNat F).η,
        swapCompFunExtExt    := λ A B C           => (h.hasSwapCompFunNat A B C).defSwapCompFunNatNatNat.η,
        swapRevCompFun       := λ {A B C} G a     => ((h.hasSwapRevCompFunNat A B C).defSwapRevCompFunNat G a).η,
        swapRevCompFunExt    := λ A {B C} G       => ((h.hasSwapRevCompFunNat A B C).defSwapRevCompFunNatNat G).η,
        swapRevCompFunExtExt := λ A B C           => (h.hasSwapRevCompFunNat A B C).defSwapRevCompFunNatNatNat.η,
        compAssoc            := λ {A B C D} F G H => ((h.hasCompAssocNat A B C D).defCompAssocNat F G H).η,
        compAssocExt         := λ {A B C} F G D   => ((h.hasCompAssocNat A B C D).defCompAssocNatNat F G).η,
        compAssocExtExt      := λ {A B} F C D     => ((h.hasCompAssocNat A B C D).defCompAssocNatNatNat F).η,
        compAssocExtExtExt   := λ A B C D         => (h.hasCompAssocNat A B C D).defCompAssocNatNatNatNat.η }

    end HasLinearNaturalIsomorphisms

    instance hasLinearFunctors [IsFunUniverse.HasLinearFunctors W] [IsNatUniverse.HasLinearFunctors W]
                               [h : HasLinearNaturalIsomorphisms W] :
      HasLinearFunctors (univ W) :=
    ⟨⟩

    class HasAffineNaturalIsomorphisms [HasSubLinearFunOp W]
                                       [hAffFun : IsFunUniverse.HasAffineFunctors W]
                                       [hNatAffFun : IsNatUniverse.HasAffineFunctors W] extends
      HasLinearNaturalIsomorphisms W where
    [hasRightConstNat (A B C : Category W) : HasRightConstNat A B C]
    [hasLeftConstNat  (A B C : Category W) : HasLeftConstNat  A B C]

    namespace HasAffineNaturalIsomorphisms

      variable [HasSubLinearFunOp W] [IsFunUniverse.HasAffineFunctors W]
               [IsNatUniverse.HasAffineFunctors W]

      -- Lean bug :-(
      noncomputable instance trivial [h : HasTrivialNaturalIsomorphisms W] : HasAffineNaturalIsomorphisms W :=
      { hasRightConstNat := λ _ _ _ => { defRightConstNat       := λ _ _ => HasTrivialNaturalityCondition.defNatIso,
                                         defRightConstNatNat    := λ _ => DefNatNatIso.trivial DefNatNatIsoBase.trivial,
                                         defRightConstNatNatNat := DefNatNatNatIso.trivial DefNatNatNatIsoBase.trivial DefNatNatIsoBase.trivial },
        hasLeftConstNat  := λ _ _ _ => { defLeftConstNat        := λ _ _ => HasTrivialNaturalityCondition.defNatIso,
                                         defLeftConstNatNat     := λ _ => DefNatNatIso.trivial DefNatNatIsoBase.trivial,
                                         defLeftConstNatNatNat  := DefNatNatNatIso.trivial DefNatNatNatIsoBase.trivial DefNatNatIsoBase.trivial } }

      instance hasAffineFunExt [h : HasAffineNaturalIsomorphisms W] :
        HasAffineFunOp.HasAffineFunExt (univ W) :=
      { rightConst       := λ A {B C} b G => ((h.hasRightConstNat A B C).defRightConstNat b G).η,
        rightConstExt    := λ A {B} b C   => ((h.hasRightConstNat A B C).defRightConstNatNat b).η,
        rightConstExtExt := λ A B C       => (h.hasRightConstNat A B C).defRightConstNatNatNat.η,
        leftConst        := λ {A B C} F c => ((h.hasLeftConstNat A B C).defLeftConstNat F c).η,
        leftConstExt     := λ {A B} F C   => ((h.hasLeftConstNat A B C).defLeftConstNatNat F).η,
        leftConstExtExt  := λ A B C       => (h.hasLeftConstNat A B C).defLeftConstNatNatNat.η }

    end HasAffineNaturalIsomorphisms

    instance hasAffineFunctors [HasSubLinearFunOp W]
                               [IsFunUniverse.HasAffineFunctors W] [IsNatUniverse.HasAffineFunctors W]
                               [h : HasAffineNaturalIsomorphisms W] :
      HasAffineFunctors (univ W) :=
    ⟨⟩

    class HasFullNaturalIsomorphisms [HasSubLinearFunOp W] [HasNonLinearFunOp W]
                                     [hAffFun : IsFunUniverse.HasAffineFunctors W]
                                     [hNatFullFun : IsNatUniverse.HasFullFunctors W] extends
      HasAffineNaturalIsomorphisms W where
    [hasDupSwapNat  (A B   : Category W) : HasDupSwapNat  A B]
    [hasDupConstNat (A B   : Category W) : HasDupConstNat A B]
    [hasRightDupNat (A B C : Category W) : HasRightDupNat A B C]
    [hasSubstDupNat (A B C : Category W) : HasSubstDupNat A B C]

    namespace HasFullNaturalIsomorphisms

      variable [HasSubLinearFunOp W] [HasNonLinearFunOp W] [IsFunUniverse.HasAffineFunctors W]
               [IsNatUniverse.HasFullFunctors W]

      -- Lean bug :-(
      noncomputable instance trivial [h : HasTrivialNaturalIsomorphisms W] : HasFullNaturalIsomorphisms W :=
      { hasDupSwapNat  := λ _ _   => { defDupSwapNat        := λ _ => HasTrivialNaturalityCondition.defNatIso,
                                       defDupSwapNatNat     := DefNatNatIso.trivial DefNatNatIsoBase.trivial },
        hasDupConstNat := λ _ _   => { defDupConstNat       := λ _ => HasTrivialNaturalityCondition.defNatIso,
                                       defDupConstNatNat    := DefNatNatIso.trivial DefNatNatIsoBase.trivial },
        hasRightDupNat := λ _ _ _ => { defRightDupNat       := λ _ _ => HasTrivialNaturalityCondition.defNatIso,
                                       defRightDupNatNat    := λ _ => DefNatNatIso.trivial DefNatNatIsoBase.trivial,
                                       defRightDupNatNatNat := DefNatNatNatIso.trivial DefNatNatNatIsoBase.trivial DefNatNatIsoBase.trivial },
        hasSubstDupNat := λ _ _ _ => { defSubstDupNat       := λ _ _ => HasTrivialNaturalityCondition.defNatIso,
                                       defSubstDupNatNat    := λ _ => DefNatNatIso.trivial DefNatNatIsoBase.trivial,
                                       defSubstDupNatNatNat := DefNatNatNatIso.trivial DefNatNatNatIsoBase.trivial DefNatNatIsoBase.trivial } }

      instance hasFullFunExt [h : HasFullNaturalIsomorphisms W] :
        HasFullFunOp.HasFullFunExt (univ W) :=
      { dupSwap        := λ {A B} F     => ((h.hasDupSwapNat A B).defDupSwapNat F).η,
        dupSwapExt     := λ A B         => (h.hasDupSwapNat A B).defDupSwapNatNat.η,
        dupConst       := λ {A B} F     => ((h.hasDupConstNat A B).defDupConstNat F).η,
        dupConstExt    := λ A B         => (h.hasDupConstNat A B).defDupConstNatNat.η,
        rightDup       := λ {A B C} F G => ((h.hasRightDupNat A B C).defRightDupNat F G).η,
        rightDupExt    := λ {A B} F C   => ((h.hasRightDupNat A B C).defRightDupNatNat F).η,
        rightDupExtExt := λ A B C       => (h.hasRightDupNat A B C).defRightDupNatNatNat.η,
        substDup       := λ {A B C} F G => ((h.hasSubstDupNat A B C).defSubstDupNat F G).η,
        substDupExt    := λ {A B} F C   => ((h.hasSubstDupNat A B C).defSubstDupNatNat F).η,
        substDupExtExt := λ A B C       => (h.hasSubstDupNat A B C).defSubstDupNatNatNat.η }

    end HasFullNaturalIsomorphisms

    instance hasStandardFunctors [HasSubLinearFunOp W] [HasNonLinearFunOp W]
                                 [IsFunUniverse.HasAffineFunctors W] [IsNatUniverse.HasFullFunctors W]
                                 [h : HasFullNaturalIsomorphisms W] :
      HasStandardFunctors (univ W) :=
    ⟨⟩

  end IsIsoUniverse

end CategoryTheory
