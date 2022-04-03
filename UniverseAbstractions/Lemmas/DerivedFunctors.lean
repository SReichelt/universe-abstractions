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

  open HasFunctors HasCongrArg

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasLinearFunOp U]

  -- The "swap" functor swaps the arguments of a nested functor.
  -- Its plain version `swapFun` actually just fixes the second argument.
  -- The presence of `swapFunFun` establishes that when something is functorial in two arguments
  -- given in a specific order, it is also functorial in the two arguments given in the reverse
  -- order.

  def defSwapFun (A B C : U) : (A ⟶ B ⟶ C) ⟶ B ⟶ A ⟶{λ F b a => F a b} C :=
  ⟨λ F => ⟨λ b => revAppFun b C • F
                  ◄ byDef,
           compFunFun F C • revAppFunFun B C
           ◄ byDefDef⟩,
   compFunFun (revAppFunFun B C) (A ⟶ C) • compFunFunFun A (B ⟶ C) C
   ◄ byDefDef⟩

  instance hasSwapFunFun : HasSwapFunFun U U U :=
  { defSwapFun    := λ {A B C} F b => ((defSwapFun A B C).defFun F).defFun b
    defSwapFunFun := λ {A B C} F   => ((defSwapFun A B C).defFun F).defFunFun }

  @[reducible] def swapFun {A B C : U} (F : A ⟶ B ⟶ C) (b : B) : A ⟶ C := HasSwapFun.swapFun F b
  @[reducible] def swapFunFun {A B C : U} (F : A ⟶ B ⟶ C) : B ⟶ A ⟶ C := HasSwapFunFun.swapFunFun F
  @[reducible] def swapFunFunFun (A B C : U) : (A ⟶ B ⟶ C) ⟶ (B ⟶ A ⟶ C) := defSwapFun A B C

  instance swapFun.isFunApp {A B C : U} {F : A ⟶ B ⟶ C} {b : B} :
    IsFunApp B (swapFun F b) :=
  HasSwapFunFun.swapFun.isFunApp

  instance swapFunFun.isFunApp {A B C : U} {F : A ⟶ B ⟶ C} :
    IsFunApp (A ⟶ B ⟶ C) (swapFunFun F) :=
  { F := swapFunFunFun A B C,
    a := F,
    e := byDef }

  instance swapFunFunFun.isFunApp {A B C : U} :
    IsFunApp ((((B ⟶ C) ⟶ C) ⟶ (A ⟶ C)) ⟶ (B ⟶ A ⟶ C)) (swapFunFunFun A B C) :=
  compFun.isFunApp

  def swapFun.congrArg {A B C : U} (F : A ⟶ B ⟶ C) {b₁ b₂ : B} (hb : b₁ ≃ b₂) :
    swapFun F b₁ ≃ swapFun F b₂ :=
  defCongrArg (HasSwapFunFun.defSwapFunFun F) hb

  def swapFunFun.congrArg {A B C : U} {F₁ F₂ : A ⟶ B ⟶ C} (hF : F₁ ≃ F₂) :
    swapFunFun F₁ ≃ swapFunFun F₂ :=
  defCongrArg (defSwapFun A B C).defFunFunFun hF

  def defSwapDefFun₃ {A B C D : U} {f : A → B → C → D} (F : A ⟶ B ⟶ C ⟶{f} D) :
    B ⟶ A ⟶ C ⟶{λ b a c => f a b c} D :=
  ⟨λ b => ⟨λ a => (F.defFun a).defFun b,
           HasSwapFun.defSwapDefFun (DefFun₃.defFunFun F) b⟩,
   HasSwapFunFun.defSwapFunFun (fromDefFun₃ F)⟩

  -- Apply the "swap" functor to itself.

  def defRevSwapFun (A B C : U) : B ⟶ (A ⟶ B ⟶ C) ⟶ A ⟶{λ b F a => F a b} C :=
  defSwapDefFun₃ (defSwapFun A B C)

  @[reducible] def revSwapFun {A B C : U} (b : B) (F : A ⟶ B ⟶ C) : A ⟶ C := swapFun F b
  @[reducible] def revSwapFunFun (A : U) {B : U} (b : B) (C : U) : (A ⟶ B ⟶ C) ⟶ (A ⟶ C) := (defRevSwapFun A B C).defFun b
  @[reducible] def revSwapFunFunFun (A B C : U) : B ⟶ (A ⟶ B ⟶ C) ⟶ (A ⟶ C) := defRevSwapFun A B C

  instance revSwapFunFun.isFunApp {A B C : U} {b : B} :
    IsFunApp B (revSwapFunFun A b C) :=
  { F := revSwapFunFunFun A B C,
    a := b,
    e := byDef }

  instance revSwapFunFunFun.isFunApp {A B C : U} :
    IsFunApp ((A ⟶ B ⟶ C) ⟶ B ⟶ (A ⟶ C)) (revSwapFunFunFun A B C) :=
  swapFunFun.isFunApp

  instance swapFun.isFunApp₂ {A B C : U} {F : A ⟶ B ⟶ C} {b : B} :
    IsFunApp₂ (A ⟶ B ⟶ C) B (swapFun F b) :=
  ⟨{ F := revSwapFunFun A b C,
     a := F,
     e := byDef }⟩

  def revSwapFun.congrArg {A B C : U} (b : B) {F₁ F₂ : A ⟶ B ⟶ C} (hF : F₁ ≃ F₂) :
    revSwapFun b F₁ ≃ revSwapFun b F₂ :=
  defCongrArg ((defRevSwapFun A B C).defFun b).defFunFun hF

  def revSwapFunFun.congrArg (A : U) {B : U} {b₁ b₂ : B} (hb : b₁ ≃ b₂) (C : U) :
    revSwapFunFun A b₁ C ≃ revSwapFunFun A b₂ C :=
  swapFun.congrArg (swapFunFunFun A B C) hb

  -- Use the "swap" functor to obtain composition in reverse order.

  def defRevCompFun (A B C : U) : (B ⟶ C) ⟶ (A ⟶ B) ⟶ A ⟶{λ G F a => G (F a)} C :=
  defSwapDefFun₃ (defCompFun A B C)

  instance hasRevCompFunFun : HasRevCompFunFun U U :=
  { defRevCompFunFun := λ A {B C} G => ((defRevCompFun A B C).defFun G).defFunFun }

  @[reducible] def revCompFun {A B C : U} (G : B ⟶ C) (F : A ⟶ B) : A ⟶ C := compFun F G
  @[reducible] def revCompFunFun (A : U) {B C : U} (G : B ⟶ C) : (A ⟶ B) ⟶ (A ⟶ C) := HasRevCompFunFun.revCompFunFun A G
  @[reducible] def revCompFunFunFun (A B C : U) : (B ⟶ C) ⟶ (A ⟶ B) ⟶ (A ⟶ C) := defRevCompFun A B C

  instance revCompFunFun.isFunApp {A B C : U} {G : B ⟶ C} :
    IsFunApp (B ⟶ C) (revCompFunFun A G) :=
  { F := revCompFunFunFun A B C,
    a := G,
    e := byDef }

  instance revCompFunFunFun.isFunApp {A B C : U} :
    IsFunApp ((A ⟶ B) ⟶ (B ⟶ C) ⟶ (A ⟶ C)) (revCompFunFunFun A B C) :=
  swapFunFun.isFunApp

  instance compFun.isFunApp₂ {A B C : U} {F : A ⟶ B} {G : B ⟶ C} :
    IsFunApp₂ (A ⟶ B) (B ⟶ C) (compFun F G) :=
  ⟨HasRevCompFunFun.compFun.isFunApp⟩

  def revCompFun.congrArg {A B C : U} (G : B ⟶ C) {F₁ F₂ : A ⟶ B} (hF : F₁ ≃ F₂) :
    revCompFun G F₁ ≃ revCompFun G F₂ :=
  defCongrArg ((defRevCompFun A B C).defFun G).defFunFun hF

  def revCompFunFun.congrArg (A : U) {B C : U} {G₁ G₂ : B ⟶ C} (hG : G₁ ≃ G₂) :
    revCompFunFun A G₁ ≃ revCompFunFun A G₂ :=
  defCongrArg (defRevCompFun A B C).defFunFunFun hG

end HasLinearFunOp



namespace HasNonLinearFunOp

  open HasFunctors HasCongrArg HasCongrFun HasLinearFunOp HasNonLinearFunOp

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasLinearFunOp U] [HasNonLinearFunOp U]

  -- The S combinator (see https://en.wikipedia.org/wiki/SKI_combinator_calculus), which in our case says
  -- that if we can functorially construct a functor `G a : B ⟶ C` and an argument `F a : B` from `a`,
  -- then the construction of `(G a) (F a)` from `a` is also functorial.
  -- We give two versions of the functor that differ in their argument order, analogously to composition.

  def defSubstFun (A B C : U) : (A ⟶ B) ⟶ (A ⟶ B ⟶ C) ⟶ A ⟶{λ F G a => G a (F a)} C :=
  ⟨λ F => ⟨λ G => dupFun (compFunFun F C • G)
                  ◄ byDef₂ • byFunDef,
           dupFunFun A C • revCompFunFun A (compFunFun F C)
           ◄ byDefDef⟩,
   revCompFunFun (A ⟶ B ⟶ C) (dupFunFun A C) •
   revCompFunFunFun A (B ⟶ C) (A ⟶ C) •
   compFunFunFun A B C
   ◄ byDef • congrArg (revCompFunFun (A ⟶ B ⟶ C) (dupFunFun A C)) (byDefDef • byDef)⟩

  instance hasSubstFun : HasSubstFun U U U := ⟨λ {A B C} F G => ((defSubstFun A B C).defFun F).defFun G⟩

  @[reducible] def substFun {A B C : U} (F : A ⟶ B) (G : A ⟶ B ⟶ C) : A ⟶ C := HasSubstFun.substFun F G
  @[reducible] def substFunFun {A B : U} (F : A ⟶ B) (C : U) : (A ⟶ B ⟶ C) ⟶ (A ⟶ C) := ((defSubstFun A B C).defFun F).defFunFun
  @[reducible] def substFunFunFun (A B C : U) : (A ⟶ B) ⟶ (A ⟶ B ⟶ C) ⟶ (A ⟶ C) := defSubstFun A B C

  instance substFun.isFunApp {A B C : U} {F : A ⟶ B} {G : A ⟶ B ⟶ C} :
    IsFunApp (A ⟶ B ⟶ C) (substFun F G) :=
  { F := substFunFun F C,
    a := G,
    e := byDef }

  instance substFunFun.isFunApp {A B C : U} {F : A ⟶ B} :
    IsFunApp (A ⟶ B) (substFunFun F C) :=
  { F := substFunFunFun A B C,
    a := F,
    e := byDef }

  instance substFunFunFun.isFunApp {A B C : U} :
    IsFunApp (((A ⟶ B ⟶ C) ⟶ (A ⟶ A ⟶ C)) ⟶ ((A ⟶ B ⟶ C) ⟶ (A ⟶ C))) (substFunFunFun A B C) :=
  compFun.isFunApp

  def substFun.congrArg {A B C : U} (F : A ⟶ B) {G₁ G₂ : A ⟶ B ⟶ C} (hG : G₁ ≃ G₂) :
    substFun F G₁ ≃ substFun F G₂ :=
  defCongrArg ((defSubstFun A B C).defFun F).defFunFun hG

  def substFunFun.congrArg {A B : U} {F₁ F₂ : A ⟶ B} (hF : F₁ ≃ F₂) (C : U) :
    substFunFun F₁ C ≃ substFunFun F₂ C :=
  defCongrArg (defSubstFun A B C).defFunFunFun hF

  -- Substitution with reverse argument order.

  def defRevSubstFun (A B C : U) : (A ⟶ B ⟶ C) ⟶ (A ⟶ B) ⟶ A ⟶{λ G F a => G a (F a)} C :=
  defSwapDefFun₃ (defSubstFun A B C)

  instance hasRevSubstFunFun : HasRevSubstFunFun U U :=
  { defRevSubstFunFun := λ A {B C} G => ((defRevSubstFun A B C).defFun G).defFunFun }

  @[reducible] def revSubstFun {A B C : U} (G : A ⟶ B ⟶ C) (F : A ⟶ B) := substFun F G
  @[reducible] def revSubstFunFun {A B C : U} (G : A ⟶ B ⟶ C) : (A ⟶ B) ⟶ (A ⟶ C) := HasRevSubstFunFun.revSubstFunFun G
  @[reducible] def revSubstFunFunFun (A B C : U) : (A ⟶ B ⟶ C) ⟶ (A ⟶ B) ⟶ (A ⟶ C) := defRevSubstFun A B C

  instance revSubstFunFun.isFunApp {A B C : U} {G : A ⟶ B ⟶ C} :
    IsFunApp (A ⟶ B ⟶ C) (revSubstFunFun G) :=
  { F := revSubstFunFunFun A B C,
    a := G,
    e := byDef }

  instance revSubstFunFunFun.isFunApp {A B C : U} :
    IsFunApp ((A ⟶ B) ⟶ (A ⟶ B ⟶ C) ⟶ (A ⟶ C)) (revSubstFunFunFun A B C) :=
  swapFunFun.isFunApp

  instance substFun.isFunApp₂ {A B C : U} {F : A ⟶ B} {G : A ⟶ B ⟶ C} :
    IsFunApp₂ (A ⟶ B) (A ⟶ B ⟶ C) (substFun F G) :=
  ⟨HasRevSubstFunFun.substFun.isFunApp⟩

  def revSubstFun.congrArg {A B C : U} (G : A ⟶ B ⟶ C) {F₁ F₂ : A ⟶ B} (hF : F₁ ≃ F₂) :
    revSubstFun G F₁ ≃ revSubstFun G F₂ :=
  defCongrArg ((defRevSubstFun A B C).defFun G).defFunFun hF

  def revSubstFunFun.congrArg {A B C : U} {G₁ G₂ : A ⟶ B ⟶ C} (hG : G₁ ≃ G₂) :
    revSubstFunFun G₁ ≃ revSubstFunFun G₂ :=
  defCongrArg (defRevSubstFun A B C).defFunFunFun hG

  -- A version of reverse composition where the functor has two arguments.

  def defRevBiCompFun (A B C D : U) :
    (B ⟶ C ⟶ D) ⟶ (A ⟶ B) ⟶ (A ⟶ C) ⟶ A ⟶{λ H F G a => H (F a) (G a)} D :=
  ⟨λ H => ⟨λ F => ⟨λ G => substFun G (H • F)
                          ◄ byFunDef,
                   HasRevSubstFunFun.defRevSubstFunFun (H • F)⟩,
           revSubstFunFunFun A C D • revCompFunFun A H
           ◄ byDefDef⟩,
   revCompFunFun (A ⟶ B) (revSubstFunFunFun A C D) • revCompFunFunFun A B (C ⟶ D)
   ◄ byDefDef⟩

  instance hasRevBiCompFunFunFun : HasRevBiCompFunFunFun U U :=
  { defBiCompFun          := λ {A B C D} F G H => (((defRevBiCompFun A B C D).defFun H).defFun F).defFun G,
    defRevBiCompFunFun    := λ {A B C D} H F   => (((defRevBiCompFun A B C D).defFun H).defFun F).defFunFun,
    defRevBiCompFunFunFun := λ A {B C} D H     => ((defRevBiCompFun A B C D).defFun H).defFunFunFun }

  @[reducible] def biCompFun {A B C D : U} (F : A ⟶ B) (G : A ⟶ C) (H : B ⟶ C ⟶ D) :
    A ⟶ D :=
  HasBiCompFun.biCompFun F G H

  @[reducible] def revBiCompFun {A B C D : U} (H : B ⟶ C ⟶ D) (F : A ⟶ B) (G : A ⟶ C) :
    A ⟶ D :=
  biCompFun F G H

  @[reducible] def revBiCompFunFun {A B C D : U} (H : B ⟶ C ⟶ D) (F : A ⟶ B) :
    (A ⟶ C) ⟶ (A ⟶ D) :=
  HasRevBiCompFunFun.revBiCompFunFun H F

  @[reducible] def revBiCompFunFunFun (A : U) {B C D : U} (H : B ⟶ C ⟶ D) :
    (A ⟶ B) ⟶ (A ⟶ C) ⟶ (A ⟶ D) :=
  HasRevBiCompFunFunFun.revBiCompFunFunFun A H

  @[reducible] def revBiCompFunFunFunFun (A B C D : U) :
    (B ⟶ C ⟶ D) ⟶ (A ⟶ B) ⟶ (A ⟶ C) ⟶ (A ⟶ D) :=
  defRevBiCompFun A B C D

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

  instance revBiCompFunFunFunFun.isFunApp {A B C D : U} :
    IsFunApp (((A ⟶ B) ⟶ A ⟶ C ⟶ D) ⟶ (A ⟶ B) ⟶ (A ⟶ C) ⟶ A ⟶ D) (revBiCompFunFunFunFun A B C D) :=
  compFun.isFunApp

end HasNonLinearFunOp
