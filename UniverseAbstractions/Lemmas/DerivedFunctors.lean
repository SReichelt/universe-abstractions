import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.MetaRelations
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors



set_option autoBoundImplicitLocal false
--set_option pp.universes true



-- This file derives some additional functors from the axioms in `Axioms/Universe/Functors.lean`.
-- The additional functors are mainly needed for the `makeFunctor` and `functoriality` tactics in
-- `Tactics/Functoriality.lean`. In order for those tactics to work correctly, they must be given
-- as a "definitional" version first, with a proof of the expected mapping behavior.



namespace HasLinearFunOp

  open HasFunctors HasCongrArg HasCongrFun

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasLinearFunOp U]

  -- The "swap" functor swaps the arguments of a nested functor.
  -- Its plain version `swapFun` actually just fixes the second argument.
  -- The presence of `swapFunFun` establishes that when something is functorial in two arguments
  -- given in a specific order, it is also functorial in the two arguments given in the reverse
  -- order.

  def defSwapFun {A B C : U} (F : A ⟶ B ⟶ C) (b : B) : A ⟶{λ a => F a b} C :=
  revAppFun b C • F
  ◄ byDef

  instance hasSwapFun : HasSwapFun U U U := ⟨defSwapFun⟩

  @[reducible] def swapFun {A B C : U} (F : A ⟶ B ⟶ C) (b : B) : A ⟶ C := HasSwapFun.swapFun F b

  def defSwapFunFun {A B C : U} (F : A ⟶ B ⟶ C) : B ⟶{λ b => swapFun F b} (A ⟶ C) :=
  compFunFun F C • revAppFunFun B C
  ◄ byDefDef

  instance hasSwapFunFun : HasSwapFunFun U U U := ⟨defSwapFunFun⟩

  @[reducible] def swapFunFun {A B C : U} (F : A ⟶ B ⟶ C) : B ⟶ A ⟶ C := HasSwapFunFun.swapFunFun F

  def defSwapFunFunFun (A B C : U) : (A ⟶ B ⟶ C) ⟶{λ F => swapFunFun F} (B ⟶ A ⟶ C) :=
  compFunFun (revAppFunFun B C) (A ⟶ C) • compFunFunFun A (B ⟶ C) C
  ◄ byDefDef

  @[reducible] def swapFunFunFun (A B C : U) : (A ⟶ B ⟶ C) ⟶ (B ⟶ A ⟶ C) := defSwapFunFunFun A B C

  instance swapFun.isFunApp {A B C : U} {F : A ⟶ B ⟶ C} {b : B} :
    IsFunApp B (swapFun F b) :=
  HasSwapFunFun.swapFun.isFunApp

  instance {A B C : U} {F : A ⟶ B ⟶ C} {b : B} :
    IsFunApp B (fromDefFun (defSwapFun F b)) :=
  swapFun.isFunApp

  instance swapFunFun.isFunApp {A B C : U} {F : A ⟶ B ⟶ C} :
    IsFunApp (A ⟶ B ⟶ C) (swapFunFun F) :=
  { F := swapFunFunFun A B C,
    a := F,
    e := byDef }

  instance {A B C : U} {F : A ⟶ B ⟶ C} :
    IsFunApp (A ⟶ B ⟶ C) (fromDefFun (defSwapFunFun F)) :=
  swapFunFun.isFunApp

  instance swapFunFunFun.isFunApp {A B C : U} :
    IsFunApp ((((B ⟶ C) ⟶ C) ⟶ (A ⟶ C)) ⟶ (B ⟶ A ⟶ C)) (swapFunFunFun A B C) :=
  compFun.isFunApp

  -- Use the "swap" functor to obtain composition in reverse order.

  @[reducible] def revCompFun {A B C : U} (G : B ⟶ C) (F : A ⟶ B) : A ⟶ C := compFun F G

  def defRevCompFunFun (A : U) {B C : U} (G : B ⟶ C) : (A ⟶ B) ⟶{λ F => revCompFun G F} (A ⟶ C) :=
  swapFun (compFunFunFun A B C) G
  ◄ byDef₂

  instance hasRevCompFunFun : HasRevCompFunFun U U := ⟨defRevCompFunFun⟩

  @[reducible] def revCompFunFun (A : U) {B C : U} (G : B ⟶ C) : (A ⟶ B) ⟶ (A ⟶ C) := HasRevCompFunFun.revCompFunFun A G

  def defRevCompFunFunFun (A B C : U) : (B ⟶ C) ⟶{λ G => revCompFunFun A G} ((A ⟶ B) ⟶ (A ⟶ C)) :=
  defSwapFunFun (compFunFunFun A B C)

  @[reducible] def revCompFunFunFun (A B C : U) : (B ⟶ C) ⟶ (A ⟶ B) ⟶ (A ⟶ C) := defRevCompFunFunFun A B C

  instance revCompFunFun.isFunApp {A B C : U} {G : B ⟶ C} :
    IsFunApp (B ⟶ C) (revCompFunFun A G) :=
  { F := revCompFunFunFun A B C,
    a := G,
    e := byDef }

  instance {A B C : U} {G : B ⟶ C} :
    IsFunApp (B ⟶ C) (fromDefFun (defRevCompFunFun A G)) :=
  revCompFunFun.isFunApp

  instance revCompFunFunFun.isFunApp {A B C : U} :
    IsFunApp ((A ⟶ B) ⟶ (B ⟶ C) ⟶ (A ⟶ C)) (revCompFunFunFun A B C) :=
  swapFunFun.isFunApp

  instance compFun.isFunApp₂ {A B C : U} {F : A ⟶ B} {G : B ⟶ C} :
    IsFunApp₂ (A ⟶ B) (B ⟶ C) (compFun F G) :=
  ⟨HasRevCompFunFun.compFun.isFunApp⟩

  -- From composition in reverse order, we can directly obtain swapping in reverse order.

  @[reducible] def revSwapFun {A B C : U} (b : B) (F : A ⟶ B ⟶ C) : A ⟶ C := swapFun F b

  def defRevSwapFunFun (A : U) {B : U} (b : B) (C : U) : (A ⟶ B ⟶ C) ⟶{λ F => revSwapFun b F} (A ⟶ C) :=
  defRevCompFunFun A (revAppFun b C)

  @[reducible] def revSwapFunFun (A : U) {B : U} (b : B) (C : U) : (A ⟶ B ⟶ C) ⟶ (A ⟶ C) := defRevSwapFunFun A b C

  def defRevSwapFunFunFun (A B C : U) : B ⟶{λ b => revSwapFunFun A b C} ((A ⟶ B ⟶ C) ⟶ (A ⟶ C)) :=
  revCompFunFunFun A (B ⟶ C) C • revAppFunFun B C
  ◄ byDefDef

  @[reducible] def revSwapFunFunFun (A B C : U) : B ⟶ (A ⟶ B ⟶ C) ⟶ (A ⟶ C) := defRevSwapFunFunFun A B C

  instance revSwapFunFun.isFunApp {A B C : U} {b : B} :
    IsFunApp B (revSwapFunFun A b C) :=
  { F := revSwapFunFunFun A B C,
    a := b,
    e := byDef }

  instance revSwapFunFunFun.isFunApp {A B C : U} :
    IsFunApp (((B ⟶ C) ⟶ C) ⟶ (A ⟶ B ⟶ C) ⟶ (A ⟶ C)) (revSwapFunFunFun A B C) :=
  compFun.isFunApp

  instance swapFun.isFunApp₂ {A B C : U} {F : A ⟶ B ⟶ C} {b : B} :
    IsFunApp₂ (A ⟶ B ⟶ C) B (swapFun F b) :=
  ⟨{ F := revSwapFunFun A b C,
     a := F,
     e := byDef }⟩

end HasLinearFunOp



namespace HasNonLinearFunOp

  open HasFunctors HasCongrArg HasCongrFun HasLinearFunOp HasNonLinearFunOp

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasLinearFunOp U] [HasNonLinearFunOp U]

  -- The S combinator (see https://en.wikipedia.org/wiki/SKI_combinator_calculus), which in our case says
  -- that if we can functorially construct a functor `G a : B ⟶ C` and an argument `F a : B` from `a`,
  -- then the construction of `(G a) (F a)` from `a` is also functorial.
  -- We give two versions of the functor that differ in their argument order, analogously to composition.

  def defSubstFun {A B C : U} (F : A ⟶ B) (G : A ⟶ B ⟶ C) : A ⟶{λ a => G a (F a)} C :=
  dupFun (compFunFun F C • G)
  ◄ byDef₂ • byFunDef

  instance hasSubstFun : HasSubstFun U U U := ⟨defSubstFun⟩

  @[reducible] def substFun {A B C : U} (F : A ⟶ B) (G : A ⟶ B ⟶ C) : A ⟶ C := HasSubstFun.substFun F G

  def defSubstFunFun {A B : U} (F : A ⟶ B) (C : U) : (A ⟶ B ⟶ C) ⟶{λ G => substFun F G} (A ⟶ C) :=
  dupFunFun A C • revCompFunFun A (compFunFun F C)
  ◄ byDefDef

  @[reducible] def substFunFun {A B : U} (F : A ⟶ B) (C : U) : (A ⟶ B ⟶ C) ⟶ (A ⟶ C) := defSubstFunFun F C

  def defSubstFunFunFun (A B C : U) : (A ⟶ B) ⟶{λ F => substFunFun F C} ((A ⟶ B ⟶ C) ⟶ (A ⟶ C)) :=
  revCompFunFun (A ⟶ B ⟶ C) (dupFunFun A C) •
  revCompFunFunFun A (B ⟶ C) (A ⟶ C) •
  compFunFunFun A B C
  ◄ byDef • congrArg (revCompFunFun (A ⟶ B ⟶ C) (dupFunFun A C)) (byDefDef • byDef)

  @[reducible] def substFunFunFun (A B C : U) : (A ⟶ B) ⟶ (A ⟶ B ⟶ C) ⟶ (A ⟶ C) :=
  defSubstFunFunFun A B C

  instance substFun.isFunApp {A B C : U} {F : A ⟶ B} {G : A ⟶ B ⟶ C} :
    IsFunApp (A ⟶ B ⟶ C) (substFun F G) :=
  { F := substFunFun F C,
    a := G,
    e := byDef }

  instance {A B C : U} {F : A ⟶ B} {G : A ⟶ B ⟶ C} :
    IsFunApp (A ⟶ B ⟶ C) (fromDefFun (defSubstFun F G)) :=
  substFun.isFunApp

  instance substFunFun.isFunApp {A B C : U} {F : A ⟶ B} :
    IsFunApp (A ⟶ B) (substFunFun F C) :=
  { F := substFunFunFun A B C,
    a := F,
    e := byDef }

  instance substFunFunFun.isFunApp {A B C : U} :
    IsFunApp (((A ⟶ B ⟶ C) ⟶ (A ⟶ A ⟶ C)) ⟶ ((A ⟶ B ⟶ C) ⟶ (A ⟶ C))) (substFunFunFun A B C) :=
  compFun.isFunApp

  -- Substitution with reverse argument order.

  @[reducible] def revSubstFun {A B C : U} (G : A ⟶ B ⟶ C) (F : A ⟶ B) := substFun F G

  def defRevSubstFunFun {A B C : U} (G : A ⟶ B ⟶ C) : (A ⟶ B) ⟶{λ F => revSubstFun G F} (A ⟶ C) :=
  dupFunFun A C • compFunFun G (A ⟶ C) • compFunFunFun A B C
  ◄ byDefDefDef • byArgDef

  instance hasRevSubstFunFun : HasRevSubstFunFun U U := ⟨defRevSubstFunFun⟩

  @[reducible] def revSubstFunFun {A B C : U} (G : A ⟶ B ⟶ C) : (A ⟶ B) ⟶ (A ⟶ C) := HasRevSubstFunFun.revSubstFunFun G

  def defRevSubstFunFunFun (A B C : U) : (A ⟶ B ⟶ C) ⟶{λ G => revSubstFunFun G} ((A ⟶ B) ⟶ (A ⟶ C)) :=
  revCompFunFun (A ⟶ B) (dupFunFun A C) •
  compFunFun (compFunFunFun A B C) (A ⟶ A ⟶ C) •
  compFunFunFun A (B ⟶ C) (A ⟶ C)
  ◄ byDef • congrArg (revCompFunFun (A ⟶ B) (dupFunFun A C)) (byDefDef • byDef)

  @[reducible] def revSubstFunFunFun (A B C : U) : (A ⟶ B ⟶ C) ⟶ (A ⟶ B) ⟶ (A ⟶ C) :=
  defRevSubstFunFunFun A B C

  instance revSubstFunFun.isFunApp {A B C : U} {G : A ⟶ B ⟶ C} :
    IsFunApp (A ⟶ B ⟶ C) (revSubstFunFun G) :=
  { F := revSubstFunFunFun A B C,
    a := G,
    e := byDef }

  instance {A B C : U} {G : A ⟶ B ⟶ C} :
    IsFunApp (A ⟶ B ⟶ C) (fromDefFun (defRevSubstFunFun G)) :=
  revSubstFunFun.isFunApp

  instance revSubstFunFunFun.isFunApp {A B C : U} :
    IsFunApp (((A ⟶ B) ⟶ (A ⟶ A ⟶ C)) ⟶ ((A ⟶ B) ⟶ (A ⟶ C))) (revSubstFunFunFun A B C) :=
  compFun.isFunApp

  instance substFun.isFunApp₂ {A B C : U} {F : A ⟶ B} {G : A ⟶ B ⟶ C} :
    IsFunApp₂ (A ⟶ B) (A ⟶ B ⟶ C) (substFun F G) :=
  ⟨HasRevSubstFunFun.substFun.isFunApp⟩

  -- A version of reverse composition where the functor has two arguments.

  def defBiCompFun {A B C D : U} (F : A ⟶ B) (G : A ⟶ C) (H : B ⟶ C ⟶ D) :
    A ⟶{λ a => H (F a) (G a)} D :=
  substFun G (H • F)
  ◄ byFunDef

  instance hasBiCompFun : HasBiCompFun U U U U := ⟨defBiCompFun⟩

  @[reducible] def biCompFun {A B C D : U} (F : A ⟶ B) (G : A ⟶ C) (H : B ⟶ C ⟶ D) :
    A ⟶ D :=
  HasBiCompFun.biCompFun F G H

  @[reducible] def revBiCompFun {A B C D : U} (H : B ⟶ C ⟶ D) (F : A ⟶ B) (G : A ⟶ C) :
    A ⟶ D :=
  biCompFun F G H

  def defRevBiCompFunFun {A B C D : U} (H : B ⟶ C ⟶ D) (F : A ⟶ B) :
    (A ⟶ C) ⟶{λ G => revBiCompFun H F G} (A ⟶ D) :=
  defRevSubstFunFun (H • F)

  instance hasRevBiCompFunFun : HasRevBiCompFunFun U U U := ⟨defRevBiCompFunFun⟩

  @[reducible] def revBiCompFunFun {A B C D : U} (H : B ⟶ C ⟶ D) (F : A ⟶ B) :
    (A ⟶ C) ⟶ (A ⟶ D) :=
  HasRevBiCompFunFun.revBiCompFunFun H F

  def defRevBiCompFunFunFun (A : U) {B C D : U} (H : B ⟶ C ⟶ D) :
    (A ⟶ B) ⟶{λ F => revBiCompFunFun H F} ((A ⟶ C) ⟶ (A ⟶ D)) :=
  revSubstFunFunFun A C D • revCompFunFun A H
  ◄ byDefDef

  instance hasRevBiCompFunFunFun : HasRevBiCompFunFunFun U U := ⟨defRevBiCompFunFunFun⟩

  @[reducible] def revBiCompFunFunFun (A : U) {B C D : U} (H : B ⟶ C ⟶ D) :
    (A ⟶ B) ⟶ (A ⟶ C) ⟶ (A ⟶ D) :=
  HasRevBiCompFunFunFun.revBiCompFunFunFun A H

  def defRevBiCompFunFunFunFun (A B C D : U) :
    (B ⟶ C ⟶ D) ⟶{λ H => revBiCompFunFunFun A H} ((A ⟶ B) ⟶ (A ⟶ C) ⟶ (A ⟶ D)) :=
  revCompFunFun (A ⟶ B) (revSubstFunFunFun A C D) • revCompFunFunFun A B (C ⟶ D)
  ◄ byDefDef

  @[reducible] def revBiCompFunFunFunFun (A B C D : U) :
    (B ⟶ C ⟶ D) ⟶ (A ⟶ B) ⟶ (A ⟶ C) ⟶ (A ⟶ D) :=
  defRevBiCompFunFunFunFun A B C D

  instance revBiCompFun.isFunApp {A B C D : U} {H : B ⟶ C ⟶ D} {F : A ⟶ B} {G : A ⟶ C} :
    IsFunApp (A ⟶ C) (revBiCompFun H F G) :=
  HasRevBiCompFunFun.biCompFun.isFunApp

  instance revBiCompFunFun.isFunApp {A B C D : U} {H : B ⟶ C ⟶ D} {F : A ⟶ B} :
    IsFunApp (A ⟶ B) (revBiCompFunFun H F) :=
  HasRevBiCompFunFunFun.revBiCompFunFun.isFunApp

  instance revBiCompFunFunFun.isFunApp {A B C D : U} {H : B ⟶ C ⟶ D} :
    IsFunApp (B ⟶ C ⟶ D) (revBiCompFunFunFun A H) :=
  { F := revBiCompFunFunFunFun A B C D,
    a := H,
    e := byDef }

  instance {A B C D : U} {H : B ⟶ C ⟶ D} :
    IsFunApp (B ⟶ C ⟶ D) (fromDefFun (defRevBiCompFunFunFun A H)) :=
  revBiCompFunFunFun.isFunApp

  instance revBiCompFunFunFunFun.isFunApp {A B C D : U} :
    IsFunApp (((A ⟶ B) ⟶ A ⟶ C ⟶ D) ⟶ (A ⟶ B) ⟶ (A ⟶ C) ⟶ A ⟶ D) (revBiCompFunFunFunFun A B C D) :=
  compFun.isFunApp

end HasNonLinearFunOp
