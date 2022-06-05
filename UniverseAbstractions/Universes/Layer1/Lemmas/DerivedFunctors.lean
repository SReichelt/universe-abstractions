import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors



namespace UniverseAbstractions.Layer1

set_option autoBoundImplicitLocal false

universe u

open HasFunctors HasRevAppFun HasSwapFun HasSwapFun₃ HasCompFun HasRevCompFun₂ HasRevCompFun₃
     HasDupFun HasDupFun₂ HasRevSelfAppFun HasSubstFun HasRevSubstFun₂ HasRevSubstFun₃



-- This file derives some additional functors from the axioms in `Layer1/Axioms/Functors.lean`, in
-- order to prove functoriality automatically (`Layer1/Meta/Tactics/Functoriality.lean`).



namespace HasRevAppFun

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

    variable {α β : Sort u} {U : Universe.{u}} [HasFunctors α U] [HasFunctors β U]
             [HasUnivFunctors U U] [HasRevAppFun β U] {C : U} [HasCompFun α (β ⥤ C) U]

    def defSwapFun (F : α ⥤ β ⥤ C) (b : β) : α ⥤{λ a => F a b} C := ⟨revAppFun b C ⊙ F⟩

    @[reducible] def swapFun (F : α ⥤ β ⥤ C) (b : β) : α ⥤ C := (defSwapFun F b).inst
    @[reducible] def revSwapFun (b : β) (F : α ⥤ β ⥤ C) : α ⥤ C := swapFun F b

  end

  section

    variable (α : Sort u) {β : Sort u} {U : Universe.{u}} [HasFunctors α U] [HasFunctors β U]
             [HasUnivFunctors U U] [HasRevCompFun₂ α U U] [HasRevAppFun β U]

    def defRevSwapFun₂ (b : β) (C : U) : (α ⥤ β ⥤ C) ⥤{revSwapFun b} (α ⥤ C) :=
      ⟨revCompFun₂ α (revAppFun b C)⟩

    @[reducible] def revSwapFun₂ (b : β) (C : U) : (α ⥤ β ⥤ C) ⥤ (α ⥤ C) :=
      (defRevSwapFun₂ α b C).inst

  end

  section

    variable (α β : Sort u) {U : Universe.{u}} [HasFunctors α U] [HasFunctors β U]
             [HasUnivFunctors U U] [HasRevCompFun₃ α U U] [HasRevCompFun₂ β U U] [HasRevAppFun β U]
             (C : U)

    @[reducible] def defRevSwapFun₃ : β ⥤{λ b => revSwapFun₂ α b C} ((α ⥤ β ⥤ C) ⥤ (α ⥤ C)) :=
      ⟨revCompFun₃ α (β ⥤ C) C ⊙ revAppFun₂ β C⟩

    @[reducible] def revSwapFun₃ : β ⥤ (α ⥤ β ⥤ C) ⥤ (α ⥤ C) := (defRevSwapFun₃ α β C).inst

    instance revSwapFun₂.isFunApp {b : β} : IsFunApp β (revSwapFun₂ α b C) :=
      ⟨revSwapFun₃ α β C, b⟩

    instance revSwapFun₃.isFunApp :
        IsFunApp (β ⥤ (β ⥤ C) ⥤ C) (revSwapFun₃ α β C) :=
      revCompFun.isFunApp β

  end

end HasRevAppFun


namespace HasFunctors

  section Helpers

    variable {U : Universe.{u}} [HasUnivFunctors U U] {Y : U}

    -- These could be low-priority instances, but currently the `functoriality` tactic doesn't need
    -- or want them.

    def IsFunApp₂.isFunApp₂' {α β : Sort u} [HasFunctors α U] [HasFunctors β U]
                             [HasCompFun α (β ⥤ Y) U] [HasRevAppFun β U] {y : Y}
                             [hApp : IsFunApp₂ α β y] :
        IsFunApp₂' α β y :=
      let _ : IsFunApp β y := IsFunApp₂.isFunApp
      ⟨⟨swapFun hApp.F hApp.b, hApp.a⟩⟩

    def IsFunApp₃.isFunApp₃' {α β γ : Sort u} [HasFunctors α U] [HasFunctors β U] [HasFunctors γ U]
                             [HasRevCompFun₂ α U U] [HasCompFun β (γ ⥤ Y) U] [HasRevAppFun β U]
                             [HasRevAppFun γ U] {y : Y} [hApp : IsFunApp₃ α β γ y] :
        IsFunApp₃' α β γ y :=
      let _ : IsFunApp₂ β γ y := IsFunApp₃.isFunApp₂
      let _ : IsFunApp₂' β γ y := IsFunApp₂.isFunApp₂'
      ⟨⟨swapFun (swapFun hApp.F hApp.b) hApp.c, hApp.a⟩⟩

    def IsFunApp₄.isFunApp₄' {α β γ δ : Sort u} [HasFunctors α U] [HasFunctors β U]
                             [HasFunctors γ U] [HasFunctors δ U] [HasRevCompFun₂ α U U]
                             [HasRevCompFun₂ β U U] [HasCompFun γ (δ ⥤ Y) U] [HasRevAppFun β U]
                             [HasRevAppFun γ U] [HasRevAppFun δ U] {y : Y}
                             [hApp : IsFunApp₄ α β γ δ y] :
        IsFunApp₄' α β γ δ y :=
      let _ : IsFunApp₃ β γ δ y := IsFunApp₄.isFunApp₃
      let _ : IsFunApp₃' β γ δ y := IsFunApp₃.isFunApp₃'
      ⟨⟨swapFun (swapFun (swapFun hApp.F hApp.b) hApp.c) hApp.d, hApp.a⟩⟩

  end Helpers

end HasFunctors


namespace HasRevCompFun₃

  section

    variable {α : Sort u} {U : Universe.{u}} [HasFunctors α U] [HasLinearLogic U]
             [HasRevCompFun₃ α U U] {B : U}

    def defCompFun₂ (F : α ⥤ B) (C : U) : (B ⥤ C) ⥤{compFun F} (α ⥤ C) :=
      ⟨swapFun (revCompFun₃ α B C) F⟩

    @[reducible] def compFun₂ (F : α ⥤ B) (C : U) : (B ⥤ C) ⥤ (α ⥤ C) := (defCompFun₂ F C).inst

  end

  section

    variable {α β : Sort u} {U : Universe.{u}} [HasFunctors α U] [HasFunctors β U]
             [HasLinearLogic U] [HasRevCompFun₃ α U U] [HasRevCompFun₂ β U U] [HasRevAppFun β U]

    def defSwapFun₂ {C : U} (F : α ⥤ β ⥤ C) : β ⥤{swapFun F} (α ⥤ C) :=
      ⟨compFun₂ F C ⊙ revAppFun₂ β C⟩

    instance hasSwapFun : HasSwapFun α β U := ⟨λ F => ⟨defSwapFun F, defSwapFun₂ F⟩⟩

    instance swapFun.isFunApp₂' {C : U} {F : α ⥤ β ⥤ C} {b : β} :
        IsFunApp₂' (α ⥤ β ⥤ C) β (HasSwapFun.swapFun F b) :=
      ⟨⟨revSwapFun₂ α b C, F⟩⟩

  end

  section

    variable (α : Sort u) {U : Universe.{u}} [HasFunctors α U] [HasLinearLogic U]
             [HasRevCompFun₃ α U U]

    def defCompFun₃ (B C : U) : (α ⥤ B) ⥤{λ F => compFun₂ F C} ((B ⥤ C) ⥤ (α ⥤ C)) :=
      ⟨swapFun₂ (revCompFun₃ α B C)⟩

    @[reducible] def compFun₃ (B C : U) : (α ⥤ B) ⥤ (B ⥤ C) ⥤ (α ⥤ C) := (defCompFun₃ α B C).inst

    instance compFun₂.isFunApp {B C : U} {F : α ⥤ B} : IsFunApp (α ⥤ B) (compFun₂ F C) :=
      ⟨compFun₃ α B C, F⟩

    instance compFun.isFunApp₂' {B C : U} {F : α ⥤ B} {G : B ⥤ C} :
        IsFunApp₂' (B ⥤ C) (α ⥤ B) (HasCompFun.compFun F G) :=
      ⟨⟨compFun₂ F C, G⟩⟩

  end

  section

    variable (α β : Sort u) {U : Universe.{u}} [HasFunctors α U] [HasFunctors β U]
             [HasLinearLogic U] [HasRevCompFun₃ α U U] [HasRevCompFun₃ β U U] [HasRevAppFun β U]

    def defSwapFun₃ (C : U) : (α ⥤ β ⥤ C) ⥤{swapFun₂} (β ⥤ α ⥤ C) :=
      ⟨compFun₂ (revAppFun₂ β C) (α ⥤ C) ⊙ compFun₃ α (β ⥤ C) C⟩

    instance hasSwapFun₃ : HasSwapFun₃ α β U := ⟨defSwapFun₃ α β⟩

    instance swapFun₃.isFunApp (C : U) :
        IsFunApp ((α ⥤ β ⥤ C) ⥤ ((β ⥤ C) ⥤ C) ⥤ (α ⥤ C)) (swapFun₃ α β C) :=
      revCompFun.isFunApp (α ⥤ β ⥤ C)

  end

  section

    variable (α : Sort u) {U : Universe.{u}} [HasFunctors α U] [HasLinearLogic U]
             [HasRevCompFun₃ α U U]

    instance compFun₃.isFunApp {B C : U} :
        IsFunApp ((B ⥤ C) ⥤ (α ⥤ B) ⥤ (α ⥤ C)) (compFun₃ α B C) :=
      swapFun₂.isFunApp (B ⥤ C) (α ⥤ B) (α ⥤ C)

  end

end HasRevCompFun₃


namespace HasDupFun

  section

    variable {α : Sort u} {U : Universe.{u}} [HasFunctors α U] [HasLinearLogic U]
             [HasRevCompFun₃ α U U] [HasDupFun α U] {B : U}

    -- The S combinator (see https://en.wikipedia.org/wiki/SKI_combinator_calculus).
    -- We give two versions of the functor that differ in their argument order, analogously to
    -- composition.

    def defSubstFun {C : U} (F : α ⥤ B) (G : α ⥤ B ⥤ C) : α ⥤{λ a => G a (F a)} C :=
      ⟨dupFun (HasRevCompFun₃.compFun₂ F C ⊙ G)⟩

    instance hasSubstFun : HasSubstFun α B U := ⟨defSubstFun⟩

  end

end HasDupFun


namespace HasDupFun₂

  section

    variable {α : Sort u} {U : Universe.{u}} [HasFunctors α U] [HasLinearLogic U]
             [HasRevCompFun₃ α U U] [HasDupFun₂ α U]

    def defRevSubstFun₂ {B C : U} (G : α ⥤ B ⥤ C) : (α ⥤ B) ⥤{revSubstFun G} (α ⥤ C) :=
      ⟨dupFun₂ α C ⊙ HasRevCompFun₃.compFun₂ G (α ⥤ C) ⊙ compFun₃ α B C⟩

    instance hasRevSubstFun₂ : HasRevSubstFun₂ α U U :=
      ⟨λ G => ⟨λ F => HasDupFun.defSubstFun F G, defRevSubstFun₂ G⟩⟩

    instance {B C : U} (F : α ⥤ B) (G : α ⥤ B ⥤ C) : IsFunApp (α ⥤ B) (substFun F G) :=
      HasRevSubstFun₂.substFun.isFunApp

    def defSubstFun₂ {B : U} (F : α ⥤ B) (C : U) : (α ⥤ B ⥤ C) ⥤{substFun F} (α ⥤ C) :=
      ⟨dupFun₂ α C ⊙ revCompFun₂ α (HasRevCompFun₃.compFun₂ F C)⟩

    @[reducible] def substFun₂ {B : U} (F : α ⥤ B) (C : U) : (α ⥤ B ⥤ C) ⥤ (α ⥤ C) :=
      (defSubstFun₂ F C).inst

  end

  section

    variable (α : Sort u) {U : Universe.{u}} [HasFunctors α U] [HasLinearLogic U]
             [HasRevCompFun₃ α U U] [HasDupFun₂ α U]

    def defRevSubstFun₃ (B C : U) : (α ⥤ B ⥤ C) ⥤{revSubstFun₂} ((α ⥤ B) ⥤ (α ⥤ C)) :=
      ⟨revCompFun₂ (α ⥤ B) (dupFun₂ α C) ⊙
       HasRevCompFun₃.compFun₂ (compFun₃ α B C) (α ⥤ α ⥤ C) ⊙
       compFun₃ α (B ⥤ C) (α ⥤ C)⟩

    instance hasRevSubstFun₃ : HasRevSubstFun₃ α U U := ⟨defRevSubstFun₃ α⟩

    instance revSubstFun₃.isFunApp {B C : U} :
        IsFunApp ((α ⥤ B ⥤ C) ⥤ (α ⥤ B) ⥤ (α ⥤ α ⥤ C)) (revSubstFun₃ α B C) :=
      revCompFun.isFunApp (α ⥤ B ⥤ C)

    def defSubstFun₃ (B C : U) : (α ⥤ B) ⥤{λ F => substFun₂ F C} ((α ⥤ B ⥤ C) ⥤ (α ⥤ C)) :=
      ⟨revCompFun₂ (α ⥤ B ⥤ C) (dupFun₂ α C) ⊙ revCompFun₃ α (B ⥤ C) (α ⥤ C) ⊙ compFun₃ α B C⟩

    @[reducible] def substFun₃ (B C : U) : (α ⥤ B) ⥤ (α ⥤ B ⥤ C) ⥤ (α ⥤ C) :=
      (defSubstFun₃ α B C).inst

    instance substFun₂.isFunApp {B C : U} {F : α ⥤ B} : IsFunApp (α ⥤ B) (substFun₂ F C) :=
      ⟨substFun₃ α B C, F⟩

    instance substFun.isFunApp₂' {B C : U} {F : α ⥤ B} {G : α ⥤ B ⥤ C} :
        IsFunApp₂' (α ⥤ B ⥤ C) (α ⥤ B) (HasSubstFun.substFun F G) :=
      ⟨⟨substFun₂ F C, G⟩⟩

    instance substFun₃.isFunApp {B C : U} :
        IsFunApp ((α ⥤ B) ⥤ (α ⥤ B ⥤ C) ⥤ (α ⥤ α ⥤ C)) (substFun₃ α B C) :=
      revCompFun.isFunApp (α ⥤ B)

  end

end HasDupFun₂


namespace HasNonLinearLogic

  variable {U : Universe.{u}} [HasLinearLogic U] [HasNonLinearLogic U]

  -- A specialized version of `substFun` that can sometimes provide a shortcut for the
  -- functoriality algorithm. (Note that the "unreversed" variant is less useful because using a
  -- constant twice is not special.)

  def defRevSelfAppFun {A B : U} (F : (A ⥤ B) ⥤ A) : (A ⥤ B) ⥤{λ G => G (F G)} B :=
    ⟨dupFun (HasRevCompFun₃.compFun₂ F B)⟩

  @[reducible] def revSelfAppFun {A B : U} (F : (A ⥤ B) ⥤ A) : (A ⥤ B) ⥤ B :=
    (defRevSelfAppFun F).inst

  def defRevSelfAppFun₂ (A B : U) : ((A ⥤ B) ⥤ A) ⥤{revSelfAppFun} ((A ⥤ B) ⥤ B) :=
    ⟨dupFun₂ (A ⥤ B) B ⊙ compFun₃ (A ⥤ B) A B⟩

  instance hasRevSelfAppFun : HasRevSelfAppFun U U :=
    ⟨λ A B => ⟨defRevSelfAppFun, defRevSelfAppFun₂ A B⟩⟩

  instance revSelfAppFun₂.isFunApp {A B : U} :
      IsFunApp (((A ⥤ B) ⥤ A) ⥤ ((A ⥤ B) ⥤ (A ⥤ B) ⥤ B)) (revSelfAppFun₂ A B) :=
    revCompFun.isFunApp ((A ⥤ B) ⥤ A)

end HasNonLinearLogic
