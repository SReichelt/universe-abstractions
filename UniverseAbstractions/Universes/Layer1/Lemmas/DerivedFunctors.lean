import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors



namespace UniverseAbstractions.Layer1

set_option autoImplicit false

universe u

open HasPiType HasFunctors HasExternalLinearLogic HasExternalNonLinearLogic

variable {U : Universe.{u}} [hU : HasLinearLogic U]



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

    variable {α β : Sort u} [HasExternalLinearLogic α U] [HasExternalLinearLogic β U] {C : U}

    -- We essentially transform `Λ a => F a b` into `Λ a => (Λ Fa => Fa b) (F a)`.

    def swapFun (F : α ⥤ β ⥤ C) (b : β) : α ⥤ C := revAppFun b C ⊙ F
    abbrev revSwapFun (b : β) (F : α ⥤ β ⥤ C) : α ⥤ C := swapFun F b

  end

  section

    variable (α : Sort u) {β : Sort u} [HasExternalLinearLogic α U] [HasExternalLinearLogic β U]

    def revSwapFun₂ (b : β) (C : U) : (α ⥤ β ⥤ C) ⥤ (α ⥤ C) := revCompFun₂ α (revAppFun b C)

  end

  section

    variable (α β : Sort u) [hα : HasExternalLinearLogic α U] [hβ : HasExternalLinearLogic β U]
             (C : U)

    def revSwapFun₃ : β ⥤ (α ⥤ β ⥤ C) ⥤ (α ⥤ C) :=
      revCompFun₃ α (β ⥤ C) C ⊙ revAppFun₂ β C

    instance revSwapFun₂.isFunApp {b : β} : IsFunApp (revSwapFun₂ α b C) := ⟨revSwapFun₃ α β C, b⟩

    instance revSwapFun₃.isFunApp : IsFunApp (revSwapFun₃ α β C) := revCompFun.isFunApp β

    local instance : HasType U (∀ a, Pi ((λ (_ : α) (_ : β) => C) a)) := hα.hFun (β ⥤ C)
    instance hasSwapPi : HasSwapPi (λ (_ : α) (_ : β) => C) := ⟨swapFun⟩

  end

  section

    variable {α : Sort u} [h : HasExternalLinearLogic α U]

    def compFun₂ {B : U} (F : α ⥤ B) (C : U) : (B ⥤ C) ⥤ (α ⥤ C) := swapFun (revCompFun₃ α B C) F

    instance compFun.isFunApp₂' {B C : U} {F : α ⥤ B} {G : B ⥤ C} : IsFunApp₂' (G ⊙ F) :=
      ⟨⟨compFun₂ F C, G⟩⟩

  end

  section

    variable {α β : Sort u} [hα : HasExternalLinearLogic α U] [hβ : HasExternalLinearLogic β U]
             {C : U}

    def swapFun₂ (F : α ⥤ β ⥤ C) : β ⥤ (α ⥤ C) := compFun₂ F C ⊙ revAppFun₂ β C

    instance swapFun.isFunApp {F : α ⥤ β ⥤ C} {b : β} : IsFunApp (swapFun F b) := ⟨swapFun₂ F, b⟩

    instance swapFun.isFunApp₂' {F : α ⥤ β ⥤ C} {b : β} : IsFunApp₂' (swapFun F b) :=
      ⟨⟨revSwapFun₂ α b C, F⟩⟩

    local instance : HasType U (∀ a, Pi ((λ (_ : α) (_ : β) => C) a)) := hα.hFun (β ⥤ C)
    instance hasSwapPi₂ : HasSwapPi₂ (λ (_ : α) (_ : β) => C) := ⟨swapFun₂⟩

  end

  section

    variable (α : Sort u) [h : HasExternalLinearLogic α U] (B C : U)

    def compFun₃ : (α ⥤ B) ⥤ (B ⥤ C) ⥤ (α ⥤ C) := swapFun₂ (revCompFun₃ α B C)

    instance compFun₂.isFunApp {F : α ⥤ B} : IsFunApp (compFun₂ F C) := ⟨compFun₃ α B C, F⟩

  end

  section

    variable (α β : Sort u) [hα : HasExternalLinearLogic α U] [hβ : HasExternalLinearLogic β U]
             (C : U)

    def swapFun₃ : (α ⥤ β ⥤ C) ⥤ (β ⥤ α ⥤ C) :=
      compFun₂ (revAppFun₂ β C) (α ⥤ C) ⊙ compFun₃ α (β ⥤ C) C

    instance swapFun₂.isFunApp {F : α ⥤ β ⥤ C} : IsFunApp (swapFun₂ F) := ⟨swapFun₃ α β C, F⟩

    instance swapFun₃.isFunApp : IsFunApp (swapFun₃ α β C) := revCompFun.isFunApp (α ⥤ β ⥤ C)

    local instance : HasType U (∀ a, Pi ((λ (_ : α) (_ : β) => C) a)) := hα.hFun (β ⥤ C)
    instance hasSwapPiFun : HasSwapPiFun (λ (_ : α) (_ : β) => C) := ⟨swapFun₃ α β C⟩

  end

  section

    variable (α : Sort u) [h : HasExternalLinearLogic α U] (B C : U)

    instance compFun₃.isFunApp : IsFunApp (compFun₃ α B C) :=
      swapFun₂.isFunApp (B ⥤ C) (α ⥤ B) (α ⥤ C)

  end

end HasExternalLinearLogic



namespace HasExternalNonLinearLogic

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
  -- to the case `G : Pi₂ Q` with `Q : α → β → V`.)

  section

    variable {α : Sort u} [hLin : HasExternalLinearLogic α U]
             [hNonLin : HasExternalNonLinearLogic α U] {B C : U}

    def substFun (F : α ⥤ B) (G : α ⥤ B ⥤ C) : α ⥤ C := dupFun (compFun₂ F C ⊙ G)
    abbrev revSubstFun (G : α ⥤ B ⥤ C) (F : α ⥤ B) : α ⥤ C := substFun F G

    local instance : HasType U (∀ a, Pi ((λ (_ : α) (_ : B) => C) a)) := hLin.hFun (B ⥤ C)
    instance hasSubstPi : HasSubstPi (λ (_ : α) (_ : B) => C) := ⟨substFun⟩

    def revSubstFun₂ (G : α ⥤ B ⥤ C) : (α ⥤ B) ⥤ (α ⥤ C) :=
      dupFun₂ α C ⊙ compFun₂ G (α ⥤ C) ⊙ compFun₃ α B C

    instance revSubstFun.isFunApp {F : α ⥤ B} {G : α ⥤ B ⥤ C} : IsFunApp (revSubstFun G F) :=
      ⟨revSubstFun₂ G, F⟩

    local instance : HasType U (∀ F : α ⥤ B, [∀ a, (λ (_ : α) (_ : B) => C) a (F a) | U]) :=
      (hU.hFun (α ⥤ B)).hFun (α ⥤ C)
    instance hasRevSubstPi₂ : HasRevSubstPi₂ (λ (_ : α) (_ : B) => C) := ⟨revSubstFun₂⟩

  end

  section

    variable (α : Sort u) [hLin : HasExternalLinearLogic α U]
             [hNonLin : HasExternalNonLinearLogic α U] (B C : U)

    def revSubstFun₃ : (α ⥤ B ⥤ C) ⥤ (α ⥤ B) ⥤ (α ⥤ C) :=
      revCompFun₂ (α ⥤ B) (dupFun₂ α C) ⊙
      compFun₂ (compFun₃ α B C) (α ⥤ α ⥤ C) ⊙
      compFun₃ α (B ⥤ C) (α ⥤ C)

    instance revSubstFun₂.isFunApp {G : α ⥤ B ⥤ C} : IsFunApp (revSubstFun₂ G) :=
      ⟨revSubstFun₃ α B C, G⟩

    instance revSubstFun.isFunApp₂ {G : α ⥤ B ⥤ C} {F : α ⥤ B} : IsFunApp₂ (revSubstFun G F) :=
      ⟨revSubstFun₃ α B C, G, F⟩

    instance revSubstFun₃.isFunApp : IsFunApp (revSubstFun₃ α B C) :=
      revCompFun.isFunApp (α ⥤ B ⥤ C)

    local instance : HasType U (∀ a, Pi ((λ (_ : α) (_ : B) => C) a)) := hLin.hFun (B ⥤ C)
    local instance : HasType U (∀ F : α ⥤ B, [∀ a, (λ (_ : α) (_ : B) => C) a (F a) | U]) :=
      (hU.hFun (α ⥤ B)).hFun (α ⥤ C)
    instance hasRevSubstPiFun : HasRevSubstPiFun (λ (_ : α) (_ : B) => C) := ⟨revSubstFun₃ α B C⟩

  end

  section

    variable {α : Sort u} [hLin : HasExternalLinearLogic α U]
             [hNonLin : HasExternalNonLinearLogic α U]

    def substFun₂ {B : U} (F : α ⥤ B) (C : U) : (α ⥤ B ⥤ C) ⥤ (α ⥤ C) :=
      swapFun (revSubstFun₃ α B C) F

    instance revSubstFun.isFunApp₂' {B C : U} {F : α ⥤ B} {G : α ⥤ B ⥤ C} :
        IsFunApp₂' (revSubstFun G F) :=
      ⟨⟨substFun₂ F C, G⟩⟩

  end

  section

    variable (α : Sort u) [hLin : HasExternalLinearLogic α U]
             [hNonLin : HasExternalNonLinearLogic α U] (B C : U)

    def substFun₃ : (α ⥤ B) ⥤ (α ⥤ B ⥤ C) ⥤ (α ⥤ C) := swapFun₂ (revSubstFun₃ α B C)

    instance substFun₂.isFunApp {F : α ⥤ B} : IsFunApp (substFun₂ F C) := ⟨substFun₃ α B C, F⟩

    instance substFun₃.isFunApp : IsFunApp (substFun₃ α B C) :=
      swapFun₂.isFunApp (α ⥤ B ⥤ C) (α ⥤ B) (α ⥤ C)

  end

end HasExternalNonLinearLogic


namespace HasNonLinearLogic

  -- The O combinator, which is a specialized version of `substFun` that can sometimes provide a
  -- shortcut for the functoriality algorithm. (Note that the "unreversed" variant is less useful
  -- because using a constant twice is not special.)

  variable [HasNonLinearLogic U]

  section

    variable {A B : U}

    def revSelfAppFun (F : (A ⥤ B) ⥤ A) : (A ⥤ B) ⥤ B := dupFun (compFun₂ F B)

    instance hasPiSelfAppPi : HasPiSelfAppPi (λ _ : A => B) := ⟨revSelfAppFun⟩

  end

  section

    variable (A B : U)

    def revSelfAppFun₂ : ((A ⥤ B) ⥤ A) ⥤ (A ⥤ B) ⥤ B := dupFun₂ (A ⥤ B) B ⊙ compFun₃ (A ⥤ B) A B

    instance revSelfAppFun.isFunApp {F : (A ⥤ B) ⥤ A} : IsFunApp (revSelfAppFun F) :=
      ⟨revSelfAppFun₂ A B, F⟩

    instance revSelfAppFun₂.isFunApp : IsFunApp (revSelfAppFun₂ A B) :=
      revCompFun.isFunApp ((A ⥤ B) ⥤ A)

    local instance : HasType U (∀ F : (A ⥤ B) ⥤ A, [∀ G : A ⥤ B, (λ _ => B) (F G) | U]) :=
      (hU.hFun ((A ⥤ B) ⥤ A)).hFun ((A ⥤ B) ⥤ B)
    instance hasPiSelfAppPi₂ : HasPiSelfAppPi₂ (λ _ : A => B) := ⟨revSelfAppFun₂ A B⟩

  end

end HasNonLinearLogic
