import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors



namespace UniverseAbstractions.Layer1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 2000

open HasFunctors HasPiAppFun HasPiAppFunPi HasSwapPi HasSwapPi₂ HasSwapPiFun HasCompFunPi
     HasRevCompFunPi₂ HasRevCompFunPiFun HasDupPi HasDupPiFun HasSubstPi HasRevSubstPi₂
     HasRevSubstPiFun HasPiSelfAppPi HasPiSelfAppPi₂



-- This file derives some functors that are defined axiomatically in `Layer1/Axioms/Functors.lean`
-- from simpler functors defined in the same file. In particular, `HasLinearLogic` and
-- `HasNonLinearLogic` are defined as they are precisely because the remaining required functors
-- can be derived as done here.



namespace HasLinearLogic

  variable {U : Universe} [HasLinearLogic U]

  -- The "swap" functor swaps the arguments of a nested functor.
  -- Its plain version `swapFun` actually just fixes the second argument.
  -- The presence of `swapFun₂` establishes that when something is functorial in two arguments given
  -- in a specific order, it is also functorial in the two arguments given in the reverse order.
  --
  -- Due to the dependencies between swapping and composition, we need to define them in the order
  -- `swapFun` -> `compFun₂` -> `swapFun₂` -> `compFun₃` -> `swapFun₃`.
  -- This only happens if we start with `revCompFun₃` instead of `compFun₃`, but `revCompFun₃` is
  -- arguably the more fundamental variant (and we may want to rename all `rev` functors at some
  -- point).

  section

    variable {A B C : U}

    -- We essentially transform `Λ a => F a b` into `Λ a => (Λ Fa => Fa b) (F a)`.

    def defSwapFun (F : A ⥤ B ⥤ C) (b : B) : A ⥤{λ a => F a b} C := ⟨revAppFun b C ⊙ F⟩

    instance hasSwapPi : HasSwapPi (Function.const A (Function.const B C)) := ⟨defSwapFun⟩
    instance : HasSwapPi (λ _ : A => Function.const B C) := hasSwapPi
    instance : HasSwapPi (λ (_ : A) (_ : B) => C) := hasSwapPi

  end

  section

    variable (A : U) {B : U} (b : B) (C : U)

    def defRevSwapFun₂ : (A ⥤ B ⥤ C) ⥤{revSwapFun b} (A ⥤ C) := ⟨revCompFun₂ A (revAppFun b C)⟩

    @[reducible] def revSwapFun₂ : (A ⥤ B ⥤ C) ⥤ (A ⥤ C) := defRevSwapFun₂ A b C

  end

  section

    variable (A B C : U)

    @[reducible] def defRevSwapFun₃ : B ⥤{λ b => revSwapFun₂ A b C} ((A ⥤ B ⥤ C) ⥤ (A ⥤ C)) :=
      ⟨revCompFun₃ A (B ⥤ C) C ⊙ revAppFun₂ B C⟩

    @[reducible] def revSwapFun₃ : B ⥤ (A ⥤ B ⥤ C) ⥤ (A ⥤ C) := defRevSwapFun₃ A B C

    instance revSwapFun₂.isFunApp {b : B} : IsFunApp (revSwapFun₂ A b C) := ⟨revSwapFun₃ A B C, b⟩

    instance revSwapFun₃.isFunApp : IsFunApp (revSwapFun₃ A B C) := revCompFun.isFunApp B

  end

  section

    variable {A B C : U}

    def defSwapFun₂ (F : A ⥤ B ⥤ C) : B ⥤{swapFun F} (A ⥤ C) := ⟨compFun₂ F C ⊙ revAppFun₂ B C⟩

    instance hasSwapPi₂ : HasSwapPi₂ (Function.const A (Function.const B C)) := ⟨defSwapFun₂⟩
    instance : HasSwapPi₂ (λ _ : A => Function.const B C) := hasSwapPi₂
    instance : HasSwapPi₂ (λ (_ : A) (_ : B) => C) := hasSwapPi₂

    instance swapFun.isFunApp₂' {F : A ⥤ B ⥤ C} {b : B} : IsFunApp₂' (swapFun F b) :=
      ⟨⟨revSwapFun₂ A b C, F⟩⟩

  end

  section

    variable (A B C : U)

    def defSwapFun₃ : (A ⥤ B ⥤ C) ⥤{swapFun₂} (B ⥤ A ⥤ C) :=
      ⟨compFun₂ (revAppFun₂ B C) (A ⥤ C) ⊙ compFun₃ A (B ⥤ C) C⟩

    instance hasSwapPiFun : HasSwapPiFun (Function.const A (Function.const B C)) :=
      ⟨defSwapFun₃ A B C⟩
    instance : HasSwapPiFun (λ _ : A => Function.const B C) := hasSwapPiFun A B C
    instance : HasSwapPiFun (λ (_ : A) (_ : B) => C) := hasSwapPiFun A B C

    instance swapFun₃.isFunApp : IsFunApp (swapFun₃ A B C) :=
      revCompFun.isFunApp (A ⥤ B ⥤ C)

    instance compFun₃.isFunApp : IsFunApp (compFun₃ A B C) :=
      swapFun₂.isFunApp (B ⥤ C) (A ⥤ B) (A ⥤ C)

  end

end HasLinearLogic



namespace HasNonLinearLogic

  variable {U : Universe} [HasLinearLogic U] [HasNonLinearLogic U]

  section

    variable {A B C : U}

    -- The S combinator (see https://en.wikipedia.org/wiki/SKI_combinator_calculus).
    -- We give two versions of the functor that differ in their argument order, analogously to
    -- composition.
    --
    -- The implementation essentially transforms `Λ a => G a (F a)` into
    -- `dupFun (Λ a a' => G a (F a'))`, which is `dupFun (Λ a => G a ⊙ F)`.
    --
    -- (The reverse order of `a` and `a'` also works and yields `dupFun (swapFun₂ G ⊙ F)`, but in
    -- the functoriality algorithm we generally prefer applying constant functors to variable
    -- arguments, so we do the same here. Note, however, that the reverse version would generalize
    -- to the case `G : Pi₂ Q` with `Q : A → B → V`.)

    def defSubstFun (F : A ⥤ B) (G : A ⥤ B ⥤ C) : A ⥤{λ a => G a (F a)} C :=
      ⟨dupFun (compFun₂ F C ⊙ G)⟩

    instance hasSubstPi : HasSubstPi (Function.const A (Function.const B C)) := ⟨defSubstFun⟩
    instance : HasSubstPi (λ _ : A => Function.const B C) := hasSubstPi
    instance : HasSubstPi (λ (_ : A) (_ : B) => C) := hasSubstPi

  end

  section

    variable {A B C : U}

    def defRevSubstFun₂ (G : A ⥤ B ⥤ C) : (A ⥤ B) ⥤{revSubstFun G} (A ⥤ C) :=
      ⟨dupFun₂ A C ⊙ compFun₂ G (A ⥤ C) ⊙ compFun₃ A B C⟩

    instance hasRevSubstPi₂ : HasRevSubstPi₂ (Function.const A (Function.const B C)) :=
      ⟨defRevSubstFun₂⟩
    instance : HasRevSubstPi₂ (λ _ : A => Function.const B C) := hasRevSubstPi₂
    instance : HasRevSubstPi₂ (λ (_ : A) (_ : B) => C) := hasRevSubstPi₂

  end

  section

    variable (A B C : U)

    def defRevSubstFun₃ : (A ⥤ B ⥤ C) ⥤{revSubstFun₂} ((A ⥤ B) ⥤ (A ⥤ C)) :=
      ⟨revCompFun₂ (A ⥤ B) (dupFun₂ A C) ⊙
       compFun₂ (compFun₃ A B C) (A ⥤ A ⥤ C) ⊙
       compFun₃ A (B ⥤ C) (A ⥤ C)⟩

    instance hasRevSubstPiFun : HasRevSubstPiFun (Function.const A (Function.const B C)) :=
      ⟨defRevSubstFun₃ A B C⟩
    instance : HasRevSubstPiFun (λ _ : A => Function.const B C) := hasRevSubstPiFun A B C
    instance : HasRevSubstPiFun (λ (_ : A) (_ : B) => C) := hasRevSubstPiFun A B C

    instance revSubstFun₃.isFunApp : IsFunApp (revSubstFun₃ A B C) :=
      revCompFun.isFunApp (A ⥤ B ⥤ C)

    instance substFun₃.isFunApp : IsFunApp (substFun₃ A B C) :=
      swapFun₂.isFunApp (A ⥤ B ⥤ C) (A ⥤ B) (A ⥤ C)

  end

  section

    -- The O combinator, which is a specialized version of `substFun` that can sometimes provide a
    -- shortcut for the functoriality algorithm. (Note that the "unreversed" variant is less useful
    -- because using a constant twice is not special.)

    variable {A B : U}

    def defRevSelfAppFun (F : (A ⥤ B) ⥤ A) : (A ⥤ B) ⥤{λ G => G (F G)} B :=
      ⟨dupFun (compFun₂ F B)⟩

    instance hasPiSelfAppPi : HasPiSelfAppPi (Function.const A B) := ⟨defRevSelfAppFun⟩
    instance : HasPiSelfAppPi (λ _ : A => B) := hasPiSelfAppPi

  end

  section

    variable (A B : U)

    def defRevSelfAppFun₂ : ((A ⥤ B) ⥤ A) ⥤{revSelfAppFun} ((A ⥤ B) ⥤ B) :=
      ⟨dupFun₂ (A ⥤ B) B ⊙ compFun₃ (A ⥤ B) A B⟩

    instance hasPiSelfAppPi₂ : HasPiSelfAppPi₂ (Function.const A B) := ⟨defRevSelfAppFun₂ A B⟩
    instance : HasPiSelfAppPi₂ (λ _ : A => B) := hasPiSelfAppPi₂ A B

    instance revSelfAppFun₂.isFunApp : IsFunApp (revSelfAppFun₂ A B) :=
      revCompFun.isFunApp ((A ⥤ B) ⥤ A)

  end

end HasNonLinearLogic
