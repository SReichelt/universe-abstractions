import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors



namespace UniverseAbstractions.Layer1

set_option autoBoundImplicitLocal false

open HasFunctors



-- This file derives some additional functors from the axioms in `Layer1/Axioms/Functors.lean`, in
-- order to prove functoriality automatically (`Layer1/Meta/Tactics/Functoriality.lean`).



namespace HasLinearLogic

  variable {U : Universe} [HasFunctors U] [HasLinearLogic U]

  -- The "swap" functor swaps the arguments of a nested functor.
  -- Its plain version `swapFun` actually just fixes the second argument.
  -- The presence of `swapFun₂` establishes that when something is functorial in two arguments
  -- given in a specific order, it is also functorial in the two arguments given in the reverse
  -- order.

  def defSwapFun₃ (A B C : U) : (A ⟶ B ⟶ C) ⟶ B ⟶ A ⟶{λ F b a => F a b} C :=
  ⟨λ F => ⟨λ b => ⟨revAppFun b C ⊙ F⟩,
           ⟨compFun₂ F C ⊙ revAppFun₂ B C⟩⟩,
   ⟨compFun₂ (revAppFun₂ B C) (A ⟶ C) ⊙ compFun₃ A (B ⟶ C) C⟩⟩

  @[reducible] def swapFun {A B C : U} (F : A ⟶ B ⟶ C) (b : B) : A ⟶ C := (((defSwapFun₃ A B C).app F).app b).F
  @[reducible] def swapFun₂ {A B C : U} (F : A ⟶ B ⟶ C) : B ⟶ A ⟶ C := ((defSwapFun₃ A B C).app F).F
  abbrev swapFun₃ (A B C : U) : (A ⟶ B ⟶ C) ⟶ (B ⟶ A ⟶ C) := (defSwapFun₃ A B C).F

  instance swapFun.isFunApp {A B C : U} {F : A ⟶ B ⟶ C} {b : B} : IsFunApp B (swapFun F b) :=
  ⟨swapFun₂ F, b⟩

  instance swapFun₂.isFunApp {A B C : U} {F : A ⟶ B ⟶ C} : IsFunApp (A ⟶ B ⟶ C) (swapFun₂ F) :=
  ⟨swapFun₃ A B C, F⟩

  instance swapFun₃.isFunApp {A B C : U} :
    IsFunApp ((((B ⟶ C) ⟶ C) ⟶ (A ⟶ C)) ⟶ (B ⟶ A ⟶ C)) (swapFun₃ A B C) :=
  compFun.isFunApp

  def defSwapDefFun₂ {A B C : U} {f : A → B → C} (F : A ⟶ B ⟶{f} C) :
    B ⟶ A ⟶{λ b a => f a b} C :=
  ⟨λ b => ⟨swapFun F.F b⟩,
   ⟨swapFun₂ F.F⟩⟩

  instance defSwapDefFun₂.isFunApp {A B C : U} {f : A → B → C} (F : A ⟶ B ⟶{f} C) :
    IsFunApp (A ⟶ B ⟶ C) (defSwapDefFun₂ F).F :=
  swapFun₂.isFunApp

  def defSwapDefFun₃ {A B C D : U} {f : A → B → C → D} (F : A ⟶ B ⟶ C ⟶{f} D) :
    B ⟶ A ⟶ C ⟶{λ b a c => f a b c} D :=
  ⟨λ b => ⟨λ a => (F.app a).app b,
           ⟨swapFun F.F b⟩⟩,
   ⟨swapFun₂ F.F⟩⟩

  instance defSwapDefFun₃.isFunApp {A B C D : U} {f : A → B → C → D} (F : A ⟶ B ⟶ C ⟶{f} D) :
    IsFunApp (A ⟶ B ⟶ C ⟶ D) (defSwapDefFun₃ F).F :=
  swapFun₂.isFunApp

  -- These could be low-priority instances, but currently the `functoriality` tactic doesn't need or
  -- want them.
  def IsFunApp₂.isFunApp₂' {A B C : U} {c : C} [hApp : IsFunApp₂ A B c] :
    IsFunApp₂' A B c :=
  let _ : IsFunApp B c := IsFunApp₂.isFunApp;
  ⟨⟨swapFun hApp.F hApp.b, hApp.a⟩⟩

  def IsFunApp₃.isFunApp₃' {A B C D : U} {d : D} [hApp : IsFunApp₃ A B C d] :
    IsFunApp₃' A B C d :=
  let _ : IsFunApp₂ B C d := IsFunApp₃.isFunApp₂;
  let _ : IsFunApp₂' B C d := IsFunApp₂.isFunApp₂';
  ⟨⟨swapFun (swapFun hApp.F hApp.b) hApp.c, hApp.a⟩⟩

  def IsFunApp₄.isFunApp₄' {A B C D E : U} (e : E) [hApp : IsFunApp₄ A B C D e] :
    IsFunApp₄' A B C D e :=
  let _ : IsFunApp₃ B C D e := IsFunApp₄.isFunApp₃;
  let _ : IsFunApp₃' B C D e := IsFunApp₃.isFunApp₃';
  ⟨⟨swapFun (swapFun (swapFun hApp.F hApp.b) hApp.c) hApp.d, hApp.a⟩⟩

  -- Apply the "swap" functor to itself.

  @[reducible] def defRevSwapFun₃ (A B C : U) : B ⟶ (A ⟶ B ⟶ C) ⟶ A ⟶{λ b F a => F a b} C :=
  defSwapDefFun₃ (defSwapFun₃ A B C)

  @[reducible] def revSwapFun {A B C : U} (b : B) (F : A ⟶ B ⟶ C) : A ⟶ C :=
  (((defRevSwapFun₃ A B C).app b).app F).F

  @[reducible] def revSwapFun₂ (A : U) {B : U} (b : B) (C : U) : (A ⟶ B ⟶ C) ⟶ (A ⟶ C) :=
  ((defRevSwapFun₃ A B C).app b).F

  @[reducible] def revSwapFun₃ (A B C : U) : B ⟶ (A ⟶ B ⟶ C) ⟶ (A ⟶ C) :=
  (defRevSwapFun₃ A B C).F

  instance swapFun.isFunApp₂' {A B C : U} {F : A ⟶ B ⟶ C} {b : B} :
    IsFunApp₂' (A ⟶ B ⟶ C) B (swapFun F b) :=
  ⟨⟨revSwapFun₂ A b C, F⟩⟩

  instance revSwapFun₂.isFunApp {A B C : U} {b : B} : IsFunApp B (revSwapFun₂ A b C) :=
  ⟨revSwapFun₃ A B C, b⟩

  -- Use the "swap" functor to obtain composition in reverse order.

  @[reducible] def defRevCompFun₃ (A B C : U) : (B ⟶ C) ⟶ (A ⟶ B) ⟶ A ⟶{λ G F a => G (F a)} C :=
  defSwapDefFun₃ (defCompFun₃ A B C)

  @[reducible] def revCompFun {A B C : U} (G : B ⟶ C) (F : A ⟶ B) : A ⟶ C :=
  (((defRevCompFun₃ A B C).app G).app F).F

  @[reducible] def revCompFun₂ (A : U) {B C : U} (G : B ⟶ C) : (A ⟶ B) ⟶ (A ⟶ C) :=
  ((defRevCompFun₃ A B C).app G).F

  @[reducible] def revCompFun₃ (A B C : U) : (B ⟶ C) ⟶ (A ⟶ B) ⟶ (A ⟶ C) :=
  (defRevCompFun₃ A B C).F

  instance compFun.isFunApp₂' {A B C : U} {F : A ⟶ B} {G : B ⟶ C} :
    IsFunApp₂' (A ⟶ B) (B ⟶ C) (compFun F G) :=
  ⟨⟨revCompFun₂ A G, F⟩⟩

  instance revCompFun₂.isFunApp {A B C : U} {G : B ⟶ C} : IsFunApp (B ⟶ C) (revCompFun₂ A G) :=
  ⟨revCompFun₃ A B C, G⟩

end HasLinearLogic



namespace HasNonLinearLogic

  open HasLinearLogic

  variable {U : Universe} [HasFunctors U] [HasLinearLogic U] [HasNonLinearLogic U]

  -- A specialized version of `substFun` below that can sometimes provide a shortcut for the
  -- functoriality algorithm. (Note that the "unreversed" variant is less useful because using a
  -- constant twice is not special.)

  def defRevSelfAppFun₂ (A B : U) : ((A ⟶ B) ⟶ A) ⟶ (A ⟶ B) ⟶{λ F G => G (F G)} B :=
  ⟨λ F => ⟨dupFun (compFun₂ F B)⟩,
   ⟨dupFun₂ (A ⟶ B) B ⊙ compFun₃ (A ⟶ B) A B⟩⟩

  @[reducible] def revSelfAppFun {A B : U} (F : (A ⟶ B) ⟶ A) : (A ⟶ B) ⟶ B :=
  ((defRevSelfAppFun₂ A B).app F).F

  @[reducible] def revSelfAppFun₂ (A B : U) : ((A ⟶ B) ⟶ A) ⟶ (A ⟶ B) ⟶ B :=
  (defRevSelfAppFun₂ A B).F

  instance revSelfAppFun.isFunApp {A B : U} {F : (A ⟶ B) ⟶ A} :
    IsFunApp ((A ⟶ B) ⟶ A) (revSelfAppFun F) :=
  ⟨revSelfAppFun₂ A B, F⟩

  instance revSelfAppFun₂.isFunApp {A B : U} :
    IsFunApp (((A ⟶ B) ⟶ (A ⟶ B) ⟶ B) ⟶ ((A ⟶ B) ⟶ B)) (revSelfAppFun₂ A B) :=
  compFun.isFunApp

  -- The S combinator (see https://en.wikipedia.org/wiki/SKI_combinator_calculus).
  -- We give two versions of the functor that differ in their argument order, analogously to
  -- composition.

  def defSubstFun₃ (A B C : U) : (A ⟶ B) ⟶ (A ⟶ B ⟶ C) ⟶ A ⟶{λ F G a => G a (F a)} C :=
  ⟨λ F => ⟨λ G => ⟨dupFun (compFun₂ F C ⊙ G)⟩,
           ⟨dupFun₂ A C ⊙ revCompFun₂ A (compFun₂ F C)⟩⟩,
   ⟨revCompFun₂ (A ⟶ B ⟶ C) (dupFun₂ A C) ⊙ revCompFun₃ A (B ⟶ C) (A ⟶ C) ⊙ compFun₃ A B C⟩⟩

  @[reducible] def substFun {A B C : U} (F : A ⟶ B) (G : A ⟶ B ⟶ C) : A ⟶ C :=
  (((defSubstFun₃ A B C).app F).app G).F

  @[reducible] def substFun₂ {A B : U} (F : A ⟶ B) (C : U) : (A ⟶ B ⟶ C) ⟶ (A ⟶ C) :=
  ((defSubstFun₃ A B C).app F).F

  @[reducible] def substFun₃ (A B C : U) : (A ⟶ B) ⟶ (A ⟶ B ⟶ C) ⟶ (A ⟶ C) :=
  (defSubstFun₃ A B C).F

  instance substFun.isFunApp {A B C : U} {F : A ⟶ B} {G : A ⟶ B ⟶ C} :
    IsFunApp (A ⟶ B ⟶ C) (substFun F G) :=
  ⟨substFun₂ F C, G⟩

  instance substFun.isFunApp₂ {A B C : U} {F : A ⟶ B} {G : A ⟶ B ⟶ C} :
    IsFunApp₂ (A ⟶ B) (A ⟶ B ⟶ C) (substFun F G) :=
  ⟨substFun₃ A B C, F, G⟩

  instance substFun₂.isFunApp {A B C : U} {F : A ⟶ B} :
    IsFunApp (A ⟶ B) (substFun₂ F C) :=
  ⟨substFun₃ A B C, F⟩

  instance substFun₃.isFunApp {A B C : U} :
    IsFunApp (((A ⟶ B ⟶ C) ⟶ (A ⟶ A ⟶ C)) ⟶ ((A ⟶ B ⟶ C) ⟶ (A ⟶ C))) (substFun₃ A B C) :=
  compFun.isFunApp

  -- Substitution with reverse argument order.

  @[reducible] def defRevSubstFun₃ (A B C : U) : (A ⟶ B ⟶ C) ⟶ (A ⟶ B) ⟶ A ⟶{λ G F a => G a (F a)} C :=
  defSwapDefFun₃ (defSubstFun₃ A B C)

  @[reducible] def revSubstFun {A B C : U} (G : A ⟶ B ⟶ C) (F : A ⟶ B) : A ⟶ C :=
  (((defRevSubstFun₃ A B C).app G).app F).F

  @[reducible] def revSubstFun₂ {A B C : U} (G : A ⟶ B ⟶ C) : (A ⟶ B) ⟶ (A ⟶ C) :=
  ((defRevSubstFun₃ A B C).app G).F

  @[reducible] def revSubstFun₃ (A B C : U) : (A ⟶ B ⟶ C) ⟶ (A ⟶ B) ⟶ (A ⟶ C) :=
  (defRevSubstFun₃ A B C).F

  instance substFun.isFunApp₂' {A B C : U} {F : A ⟶ B} {G : A ⟶ B ⟶ C} :
    IsFunApp₂' (A ⟶ B) (A ⟶ B ⟶ C) (substFun F G) :=
  ⟨⟨revSubstFun₂ G, F⟩⟩

  instance revSubstFun₂.isFunApp {A B C : U} {G : A ⟶ B ⟶ C} :
    IsFunApp (A ⟶ B ⟶ C) (revSubstFun₂ G) :=
  ⟨revSubstFun₃ A B C, G⟩

end HasNonLinearLogic
