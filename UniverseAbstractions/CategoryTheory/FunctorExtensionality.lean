import UniverseAbstractions.CategoryTheory.Basic
import UniverseAbstractions.CategoryTheory.Functors
import UniverseAbstractions.CategoryTheory.NaturalTransformations
import UniverseAbstractions.CategoryTheory.Functors.Nested
import UniverseAbstractions.CategoryTheory.FunctorExtensionality.LinearNatIso
import UniverseAbstractions.CategoryTheory.FunctorExtensionality.AffineNatIso
import UniverseAbstractions.CategoryTheory.FunctorExtensionality.FullNatIso



set_option autoBoundImplicitLocal false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 1000
--set_option pp.universes true

universe u w ww iw iww



namespace CategoryTheory

  open HasCatProp HasIsoNaturality

  namespace IsSortNatUniverse

    variable (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw, iww} W] [h : IsSortNatUniverse.{u} W]

    class HasLinearNatIso [HasLinearCatFun.{u} W] where
    [hasRightIdNat        (A B     : Category sort.{max 1 u w} W) : HasRightIdNat        A B]
    [hasLeftIdNat         (A B     : Category sort.{max 1 u w} W) : HasLeftIdNat         A B]
    [hasSwapRevAppNat     (A B     : Category sort.{max 1 u w} W) : HasSwapRevAppNat     A B]
    [hasSwapCompFunNat    (A B C   : Category sort.{max 1 u w} W) : HasSwapCompFunNat    A B C]
    [hasSwapRevCompFunNat (A B C   : Category sort.{max 1 u w} W) : HasSwapRevCompFunNat A B C]
    [hasCompAssocNat      (A B C D : Category sort.{max 1 u w} W) : HasCompAssocNat      A B C D]

    namespace HasLinearNatIso

      variable [HasLinearCatFun.{u} W]

      -- Lean bug :-(
      noncomputable instance trivial [h : HasTrivialNaturalIsomorphisms W] : HasLinearNatIso W :=
      { hasRightIdNat        := λ _ _     => { defRightIdNat              := λ _ => HasTrivialIsoNaturalityCondition.defNatIso,
                                               defRightIdNatNat           := DefNatNatIso.trivial DefNatNatIsoBase.trivial },
        hasLeftIdNat         := λ _ _     => { defLeftIdNat               := λ _ => HasTrivialIsoNaturalityCondition.defNatIso,
                                               defLeftIdNatNat            := DefNatNatIso.trivial DefNatNatIsoBase.trivial },
        hasSwapRevAppNat     := λ _ _     => { defSwapRevAppNat           := λ _ => HasTrivialIsoNaturalityCondition.defNatIso,
                                               defSwapRevAppNatNat        := DefNatNatIso.trivial DefNatNatIsoBase.trivial },
        hasSwapCompFunNat    := λ _ _ _   => { defSwapCompFunNat          := λ _ _ => HasTrivialIsoNaturalityCondition.defNatIso,
                                               defSwapCompFunNatNat       := λ _ => DefNatNatIso.trivial DefNatNatIsoBase.trivial,
                                               defSwapCompFunNatNatNat    := DefNatNatNatIso.trivial DefNatNatNatIsoBase.trivial DefNatNatIsoBase.trivial },
        hasSwapRevCompFunNat := λ _ _ _   => { defSwapRevCompFunNat       := λ _ _ => HasTrivialIsoNaturalityCondition.defNatIso,
                                               defSwapRevCompFunNatNat    := λ _ => DefNatNatIso.trivial DefNatNatIsoBase.trivial,
                                               defSwapRevCompFunNatNatNat := DefNatNatNatIso.trivial DefNatNatNatIsoBase.trivial DefNatNatIsoBase.trivial },
        hasCompAssocNat      := λ _ _ _ _ => { defCompAssocNat            := λ _ _ _ => HasTrivialIsoNaturalityCondition.defNatIso,
                                               defCompAssocNatNat         := λ _ _ => DefNatNatIso.trivial DefNatNatIsoBase.trivial,
                                               defCompAssocNatNatNat      := λ _ => DefNatNatNatIso.trivial DefNatNatNatIsoBase.trivial DefNatNatIsoBase.trivial,
                                               defCompAssocNatNatNatNat   := DefNatNatNatNatIso.trivial DefNatNatNatNatIsoBase.trivial DefNatNatNatIsoBase.trivial DefNatNatIsoBase.trivial } }

      instance hasLinearFunExt [h : HasLinearNatIso W] : HasLinearFunOp.HasLinearFunExt (univ.{u} W) :=
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

      instance hasLinearFunctors [HasLinearNatIso W] : HasLinearFunctors (univ.{u} W) := ⟨⟩

    end HasLinearNatIso

    class HasAffineNatIso [HasSubLinearFunOp W] [HasAffineCatFun.{u} W] extends
      HasLinearNatIso W where
    [hasRightConstNat (A B C : Category sort.{max 1 u w} W) : HasRightConstNat A B C]
    [hasLeftConstNat  (A B C : Category sort.{max 1 u w} W) : HasLeftConstNat  A B C]

    namespace HasAffineNatIso

      variable [HasSubLinearFunOp W] [HasAffineCatFun.{u} W]

      -- Lean bug :-(
      noncomputable instance trivial [h : HasTrivialNaturalIsomorphisms W] : HasAffineNatIso W :=
      { hasRightConstNat := λ _ _ _ => { defRightConstNat       := λ _ _ => HasTrivialIsoNaturalityCondition.defNatIso,
                                         defRightConstNatNat    := λ _ => DefNatNatIso.trivial DefNatNatIsoBase.trivial,
                                         defRightConstNatNatNat := DefNatNatNatIso.trivial DefNatNatNatIsoBase.trivial DefNatNatIsoBase.trivial },
        hasLeftConstNat  := λ _ _ _ => { defLeftConstNat        := λ _ _ => HasTrivialIsoNaturalityCondition.defNatIso,
                                         defLeftConstNatNat     := λ _ => DefNatNatIso.trivial DefNatNatIsoBase.trivial,
                                         defLeftConstNatNatNat  := DefNatNatNatIso.trivial DefNatNatNatIsoBase.trivial DefNatNatIsoBase.trivial } }

      instance hasAffineFunExt [h : HasAffineNatIso W] :
        HasAffineFunOp.HasAffineFunExt (univ.{u} W) :=
      { rightConst       := λ A {B C} b G => ((h.hasRightConstNat A B C).defRightConstNat b G).η,
        rightConstExt    := λ A {B} b C   => ((h.hasRightConstNat A B C).defRightConstNatNat b).η,
        rightConstExtExt := λ A B C       => (h.hasRightConstNat A B C).defRightConstNatNatNat.η,
        leftConst        := λ {A B C} F c => ((h.hasLeftConstNat A B C).defLeftConstNat F c).η,
        leftConstExt     := λ {A B} F C   => ((h.hasLeftConstNat A B C).defLeftConstNatNat F).η,
        leftConstExtExt  := λ A B C       => (h.hasLeftConstNat A B C).defLeftConstNatNatNat.η }

      instance hasAffineFunctors [HasAffineNatIso W] : HasAffineFunctors (univ.{u} W) := ⟨⟩

    end HasAffineNatIso

    class HasFullNatIso [HasSubLinearFunOp W] [HasNonLinearFunOp W] [HasFullCatFun.{u} W] extends
      HasAffineNatIso W where
    [hasDupSwapNat  (A B   : Category sort.{max 1 u w} W) : HasDupSwapNat  A B]
    [hasDupConstNat (A B   : Category sort.{max 1 u w} W) : HasDupConstNat A B]
    [hasRightDupNat (A B C : Category sort.{max 1 u w} W) : HasRightDupNat A B C]
    [hasSubstDupNat (A B C : Category sort.{max 1 u w} W) : HasSubstDupNat A B C]

    namespace HasFullNatIso

      variable [HasSubLinearFunOp W] [HasNonLinearFunOp W] [HasFullCatFun.{u} W]

      -- Lean bug :-(
      noncomputable instance trivial [h : HasTrivialNaturalIsomorphisms W] : HasFullNatIso W :=
      { hasDupSwapNat  := λ _ _   => { defDupSwapNat        := λ _ => HasTrivialIsoNaturalityCondition.defNatIso,
                                       defDupSwapNatNat     := DefNatNatIso.trivial DefNatNatIsoBase.trivial },
        hasDupConstNat := λ _ _   => { defDupConstNat       := λ _ => HasTrivialIsoNaturalityCondition.defNatIso,
                                       defDupConstNatNat    := DefNatNatIso.trivial DefNatNatIsoBase.trivial },
        hasRightDupNat := λ _ _ _ => { defRightDupNat       := λ _ _ => HasTrivialIsoNaturalityCondition.defNatIso,
                                       defRightDupNatNat    := λ _ => DefNatNatIso.trivial DefNatNatIsoBase.trivial,
                                       defRightDupNatNatNat := DefNatNatNatIso.trivial DefNatNatNatIsoBase.trivial DefNatNatIsoBase.trivial },
        hasSubstDupNat := λ _ _ _ => { defSubstDupNat       := λ _ _ => HasTrivialIsoNaturalityCondition.defNatIso,
                                       defSubstDupNatNat    := λ _ => DefNatNatIso.trivial DefNatNatIsoBase.trivial,
                                       defSubstDupNatNatNat := DefNatNatNatIso.trivial DefNatNatNatIsoBase.trivial DefNatNatIsoBase.trivial } }

      instance hasFullFunExt [h : HasFullNatIso W] :
        HasFullFunOp.HasFullFunExt (univ.{u} W) :=
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

      instance hasStandardFunctors [HasFullNatIso W] : HasStandardFunctors (univ.{u} W) := ⟨⟩

    end HasFullNatIso

  end IsSortNatUniverse

end CategoryTheory
