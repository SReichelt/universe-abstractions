import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors



namespace UniverseAbstractions.Layer1

set_option autoImplicit false

universe u

open HasFunctors HasPiAppFun HasPiAppFunPi HasSwapPi HasSwapPi₂ HasSwapPiFun HasCompFunPi
     HasRevCompFunPi₂ HasRevCompFunPiFun HasDupPi HasDupPiFun HasSubstPi HasRevSubstPi₂
     HasRevSubstPiFun HasPiSelfAppPi HasPiSelfAppPi₂



-- This file derives some functors that are defined axiomatically in `Layer1/Axioms/Functors.lean`
-- from simpler functors defined in the same file. In particular, `HasLinearLogic` and
-- `HasNonLinearLogic` are defined as they are precisely because the remaining required functors
-- can be derived as done here.



namespace HasExternalLinearLogic

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

    variable {α β : Sort u} {U : Universe.{u}} [HasUnivFunctors U U] [HasExternalLinearLogic α U]
             [HasExternalLinearLogic β U] {C : U}

    -- We essentially transform `Λ a => F a b` into `Λ a => (Λ Fa => Fa b) (F a)`.

    def defSwapFun (F : α ⥤ β ⥤ C) (b : β) : α ⥤{λ a => F a b} C := ⟨revAppFun b C ⊙ F⟩

    instance hasSwapPi : HasSwapPi (Function.const α (Function.const β C)) := ⟨defSwapFun⟩
    instance : HasSwapPi (λ _ : α => Function.const β C) := hasSwapPi
    instance : HasSwapPi (λ (_ : α) (_ : β) => C) := hasSwapPi

  end

  section

    variable (α : Sort u) {β : Sort u} (b : β) {U : Universe.{u}} [HasUnivFunctors U U]
             [HasExternalLinearLogic α U] [HasExternalLinearLogic β U] (C : U)

    def defRevSwapFun₂ : (α ⥤ β ⥤ C) ⥤{revSwapFun b} (α ⥤ C) := ⟨revCompFun₂ α (revAppFun b C)⟩

    @[reducible] def revSwapFun₂ : (α ⥤ β ⥤ C) ⥤ (α ⥤ C) := defRevSwapFun₂ α b C

  end

  section

    variable (α β : Sort u) {U : Universe.{u}} [HasUnivFunctors U U] [HasExternalLinearLogic α U]
             [HasExternalLinearLogic β U] (C : U)

    @[reducible] def defRevSwapFun₃ : β ⥤{λ b => revSwapFun₂ α b C} ((α ⥤ β ⥤ C) ⥤ (α ⥤ C)) :=
      ⟨revCompFun₃ α (β ⥤ C) C ⊙ revAppFun₂ β C⟩

    @[reducible] def revSwapFun₃ : β ⥤ (α ⥤ β ⥤ C) ⥤ (α ⥤ C) := defRevSwapFun₃ α β C

    instance revSwapFun₂.isFunApp {b : β} : IsFunApp (revSwapFun₂ α b C) := ⟨revSwapFun₃ α β C, b⟩

    instance revSwapFun₃.isFunApp : IsFunApp (revSwapFun₃ α β C) := revCompFun.isFunApp β

  end

  section

    variable {α β : Sort u} {U : Universe.{u}} [HasLinearLogic U] [HasExternalLinearLogic α U]
             [HasExternalLinearLogic β U] {C : U}

    def defSwapFun₂ (F : α ⥤ β ⥤ C) : β ⥤{swapFun F} (α ⥤ C) := ⟨compFun₂ F C ⊙ revAppFun₂ β C⟩

    instance hasSwapPi₂ : HasSwapPi₂ (Function.const α (Function.const β C)) := ⟨defSwapFun₂⟩
    instance : HasSwapPi₂ (λ _ : α => Function.const β C) := hasSwapPi₂
    instance : HasSwapPi₂ (λ (_ : α) (_ : β) => C) := hasSwapPi₂

    instance swapFun.isFunApp₂' {F : α ⥤ β ⥤ C} {b : β} : IsFunApp₂' (swapFun F b) :=
      ⟨⟨revSwapFun₂ α b C, F⟩⟩

  end

  section

    variable (α β : Sort u) {U : Universe.{u}} [HasLinearLogic U] [HasExternalLinearLogic α U]
             [HasExternalLinearLogic β U] (C : U)

    def defSwapFun₃ : (α ⥤ β ⥤ C) ⥤{swapFun₂} (β ⥤ α ⥤ C) :=
      ⟨compFun₂ (revAppFun₂ β C) (α ⥤ C) ⊙ compFun₃ α (β ⥤ C) C⟩

    instance hasSwapPiFun : HasSwapPiFun (Function.const α (Function.const β C)) :=
      ⟨defSwapFun₃ α β C⟩
    instance : HasSwapPiFun (λ _ : α => Function.const β C) := hasSwapPiFun α β C
    instance : HasSwapPiFun (λ (_ : α) (_ : β) => C) := hasSwapPiFun α β C

    instance swapFun₃.isFunApp : IsFunApp (swapFun₃ α β C) :=
      revCompFun.isFunApp (α ⥤ β ⥤ C)

  end

  section

    variable (α : Sort u) {U : Universe.{u}} [HasLinearLogic U] [HasExternalLinearLogic α U]
             (B C : U)

    instance compFun₃.isFunApp : IsFunApp (compFun₃ α B C) :=
      swapFun₂.isFunApp (B ⥤ C) (α ⥤ B) (α ⥤ C)

  end

end HasExternalLinearLogic



namespace HasExternalNonLinearLogic

  section

    variable {α : Sort u} {U : Universe.{u}} [HasLinearLogic U] [HasExternalLinearLogic α U]
             [HasExternalNonLinearLogic α U] {B C : U}

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

    def defSubstFun (F : α ⥤ B) (G : α ⥤ B ⥤ C) : α ⥤{λ a => G a (F a)} C :=
      ⟨dupFun (compFun₂ F C ⊙ G)⟩

    instance hasSubstPi : HasSubstPi (Function.const α (Function.const B C)) := ⟨defSubstFun⟩
    instance : HasSubstPi (λ _ : α => Function.const B C) := hasSubstPi
    instance : HasSubstPi (λ (_ : α) (_ : B) => C) := hasSubstPi

  end

  section

    variable {α : Sort u} {U : Universe.{u}} [HasLinearLogic U] [HasExternalLinearLogic α U]
             [HasExternalNonLinearLogic α U] {B C : U}

    def defRevSubstFun₂ (G : α ⥤ B ⥤ C) : (α ⥤ B) ⥤{revSubstFun G} (α ⥤ C) :=
      ⟨dupFun₂ α C ⊙ compFun₂ G (α ⥤ C) ⊙ compFun₃ α B C⟩

    instance hasRevSubstPi₂ : HasRevSubstPi₂ (Function.const α (Function.const B C)) :=
      ⟨defRevSubstFun₂⟩
    instance : HasRevSubstPi₂ (λ _ : α => Function.const B C) := hasRevSubstPi₂
    instance : HasRevSubstPi₂ (λ (_ : α) (_ : B) => C) := hasRevSubstPi₂

  end

  section

    variable (α : Sort u) {U : Universe.{u}} [HasLinearLogic U] [HasExternalLinearLogic α U]
             [HasExternalNonLinearLogic α U] (B C : U)

    def defRevSubstFun₃ : (α ⥤ B ⥤ C) ⥤{revSubstFun₂} ((α ⥤ B) ⥤ (α ⥤ C)) :=
      ⟨revCompFun₂ (α ⥤ B) (dupFun₂ α C) ⊙
       compFun₂ (compFun₃ α B C) (α ⥤ α ⥤ C) ⊙
       compFun₃ α (B ⥤ C) (α ⥤ C)⟩

    instance hasRevSubstPiFun : HasRevSubstPiFun (Function.const α (Function.const B C)) :=
      ⟨defRevSubstFun₃ α B C⟩
    instance : HasRevSubstPiFun (λ _ : α => Function.const B C) := hasRevSubstPiFun α B C
    instance : HasRevSubstPiFun (λ (_ : α) (_ : B) => C) := hasRevSubstPiFun α B C

    instance revSubstFun₃.isFunApp : IsFunApp (revSubstFun₃ α B C) :=
      revCompFun.isFunApp (α ⥤ B ⥤ C)

    instance substFun₃.isFunApp : IsFunApp (substFun₃ α B C) :=
      swapFun₂.isFunApp (α ⥤ B ⥤ C) (α ⥤ B) (α ⥤ C)

  end

end HasExternalNonLinearLogic


namespace HasNonLinearLogic

  variable {U : Universe} [HasLinearLogic U] [HasNonLinearLogic U]

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
