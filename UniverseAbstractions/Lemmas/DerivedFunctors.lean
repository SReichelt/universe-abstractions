import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors



set_option autoBoundImplicitLocal false
--set_option pp.universes true



-- This file derives some additional functors from the axioms in `Axioms/Universe/Functors.lean`.
-- The additional functors are mainly needed for the `makeFunctor` and `functoriality` tactics in
-- `Tactics/Functoriality.lean`. In order for those tactics to work correctly, they must be given
-- as a "definitional" version first, with the expected mapping behavior.

-- TODO: We should also introduce dependent variants where appropriate, and extend the functoriality tactics accordingly.



namespace HasLinearFunOp

  variable {U : Universe} [HasEmbeddedFunctors U] [HasLinearFunOp U]

  -- The "swap" functor swaps the arguments of a nested functor.
  -- Its plain version `swapFun` actually just fixes the second argument.
  -- The presence of `swapFunFun` establishes that when something is functorial in two arguments
  -- given in a specific order, it is also functorial in the two arguments given in the reverse
  -- order.

  def defSwapFun {A B C : U} (F : A ⟶ B ⟶ C) (b : B) : A ⟶[λ a => F a b] C :=
  appFun b C ⊙ F
  ◄ λ _ => by simp

  @[reducible] def swapFun {A B C : U} (F : A ⟶ B ⟶ C) (b : B) : A ⟶ C := defSwapFun F b

  def defSwapFunFun {A B C : U} (F : A ⟶ B ⟶ C) : B ⟶[λ b => swapFun F b] (A ⟶ C) :=
  compFunFun F C ⊙ appFunFun B C
  ◄ λ _ => by simp [swapFun, defSwapFun]

  @[reducible] def swapFunFun {A B C : U} (F : A ⟶ B ⟶ C) : B ⟶ A ⟶ C := defSwapFunFun F

  def defSwapFunFunFun (A B C : U) : (A ⟶ B ⟶ C) ⟶[λ F => swapFunFun F] (B ⟶ A ⟶ C) :=
  compFunFun (appFunFun B C) (A ⟶ C) ⊙ compFunFunFun A (B ⟶ C) C
  ◄ λ _ => by simp [swapFunFun, defSwapFunFun]

  @[reducible] def swapFunFunFun (A B C : U) : (A ⟶ B ⟶ C) ⟶ (B ⟶ A ⟶ C) := defSwapFunFunFun A B C

  -- We can apply the "swap" functor to itself to obtain its functoriality in reverse order.

  @[reducible] def revSwapFun {A B C : U} (b : B) (F : A ⟶ B ⟶ C) : A ⟶ C := swapFun F b

  def defRevSwapFunFun (A : U) {B : U} (b : B) (C : U) : (A ⟶ B ⟶ C) ⟶[λ F => revSwapFun b F] (A ⟶ C) :=
  swapFun (swapFunFunFun A B C) b
  ◄ λ _ => by simp

  @[reducible] def revSwapFunFun (A : U) {B : U} (b : B) (C : U) : (A ⟶ B ⟶ C) ⟶ (A ⟶ C) := defRevSwapFunFun A b C

  def defRevSwapFunFunFun (A B C : U) : B ⟶[λ b => revSwapFunFun A b C] ((A ⟶ B ⟶ C) ⟶ (A ⟶ C)) :=
  swapFunFun (swapFunFunFun A B C)
  ◄ λ _ => by simp [revSwapFunFun, defRevSwapFunFun]

  @[reducible] def revSwapFunFunFun (A B C : U) : B ⟶ (A ⟶ B ⟶ C) ⟶ (A ⟶ C) := defRevSwapFunFunFun A B C

  -- Same for composition.

  def defRevCompFunFun (A : U) {B C : U} (G : B ⟶ C) : (A ⟶ B) ⟶[λ F => revCompFun G F] (A ⟶ C) :=
  swapFun (compFunFunFun A B C) G
  ◄ λ _ => by simp

  @[reducible] def revCompFunFun (A : U) {B C : U} (G : B ⟶ C) : (A ⟶ B) ⟶ (A ⟶ C) := defRevCompFunFun A G

  def defRevCompFunFunFun (A B C : U) : (B ⟶ C) ⟶[λ G => revCompFunFun A G] ((A ⟶ B) ⟶ (A ⟶ C)) :=
  swapFunFun (compFunFunFun A B C)
  ◄ λ _ => by simp [revCompFunFun, defRevCompFunFun]

  @[reducible] def revCompFunFunFun (A B C : U) : (B ⟶ C) ⟶ (A ⟶ B) ⟶ (A ⟶ C) := defRevCompFunFunFun A B C

end HasLinearFunOp



namespace HasFullFunOp

  variable {U : Universe} [HasEmbeddedFunctors U] [HasFullFunOp U]

  -- The S combinator (see https://en.wikipedia.org/wiki/SKI_combinator_calculus), which in our case says
  -- that if we can functorially construct a functor `G a : B ⟶ C` and an argument `F a : B` from `a`,
  -- then the construction of `(G a) (F a)` from `a` is also functorial.
  -- We give two versions of the functor that differ in their argument order, analogously to composition.

  def defSubstFun {A B C : U} (F : A ⟶ B) (G : A ⟶ B ⟶ C) : A ⟶[λ a => G a (F a)] C :=
  HasNonLinearFunOp.dupFun (HasLinearFunOp.swapFunFun G ⊙ F)
  ◄ λ _ => by simp

  @[reducible] def substFun {A B C : U} (F : A ⟶ B) (G : A ⟶ B ⟶ C) : A ⟶ C := defSubstFun F G

  def defSubstFunFun {A B : U} (F : A ⟶ B) (C : U) : (A ⟶ B ⟶ C) ⟶[λ G => substFun F G] (A ⟶ C) :=
  HasNonLinearFunOp.dupFunFun A C ⊙ HasLinearFunOp.compFunFun F (A ⟶ C) ⊙ HasLinearFunOp.swapFunFunFun A B C
  ◄ λ _ => by simp [substFun, defSubstFun]

  @[reducible] def substFunFun {A B : U} (F : A ⟶ B) (C : U) : (A ⟶ B ⟶ C) ⟶ (A ⟶ C) := defSubstFunFun F C

  def defSubstFunFunFun (A B C : U) : (A ⟶ B) ⟶[λ F => substFunFun F C] ((A ⟶ B ⟶ C) ⟶ (A ⟶ C)) :=
  HasLinearFunOp.revCompFunFun (A ⟶ B ⟶ C) (HasNonLinearFunOp.dupFunFun A C) ⊙
  HasLinearFunOp.compFunFun (HasLinearFunOp.swapFunFunFun A B C) (A ⟶ A ⟶ C) ⊙
  HasLinearFunOp.compFunFunFun A B (A ⟶ C)
  ◄ λ _ => by simp [substFunFun, defSubstFunFun]

  @[reducible] def substFunFunFun (A B C : U) : (A ⟶ B) ⟶ (A ⟶ B ⟶ C) ⟶ (A ⟶ C) :=
  defSubstFunFunFun A B C

  -- Substitution with reverse argument order.

  @[reducible] def revSubstFun {A B C : U} (G : A ⟶ B ⟶ C) (F : A ⟶ B) := substFun F G

  def defRevSubstFunFun {A B C : U} (G : A ⟶ B ⟶ C) : (A ⟶ B) ⟶[λ F => revSubstFun G F] (A ⟶ C) :=
  HasLinearFunOp.swapFun (substFunFunFun A B C) G
  ◄ λ _ => by simp

  @[reducible] def revSubstFunFun {A B C : U} (G : A ⟶ B ⟶ C) : (A ⟶ B) ⟶ (A ⟶ C) := defRevSubstFunFun G

  def defRevSubstFunFunFun (A B C : U) : (A ⟶ B ⟶ C) ⟶[λ G => revSubstFunFun G] ((A ⟶ B) ⟶ (A ⟶ C)) :=
  HasLinearFunOp.swapFunFun (substFunFunFun A B C)
  ◄ λ _ => by simp [revSubstFunFun, defRevSubstFunFun]

  @[reducible] def revSubstFunFunFun (A B C : U) : (A ⟶ B ⟶ C) ⟶ (A ⟶ B) ⟶ (A ⟶ C) :=
  defRevSubstFunFunFun A B C

end HasFullFunOp



-- TODO: Replace equality with instance equivalence
-- TODO: `swapApp` is provable from `swapFunFun` being self-inverse (`swapConst` also?)
-- TODO: Recover more readable variants

def DependentOperation {A : Sort _} {U : Universe} [HasEmbeddedFunctors U] (P : A → A → U) :=
∀ a b c, P a b ⟶ P b c ⟶ P a c

def DependentOperation.Associative {A : Sort _} {U : Universe} [HasEmbeddedFunctors U] [HasLinearFunOp U]
                                   (P : A → A → U) (R : DependentOperation P) (a b c d : A) :=
HasLinearFunOp.swapFunFun (HasLinearFunOp.compFunFunFun (P c d) (P b d) (P a d) ⊙ R b c d) ⊙ R a b d =
HasLinearFunOp.revCompFunFun (P b c) (R a c d) ⊙ R a b c

class HasLinearFunOpEquiv (U : Universe) [HasEmbeddedFunctors U] [HasLinearFunOp U] where
(rightId   (A B     : U) : HasLinearFunOp.compFunFun (HasLinearFunOp.idFun A) B = HasLinearFunOp.idFun (A ⟶ B))
(leftId    (A B     : U) : HasLinearFunOp.revCompFunFun A (HasLinearFunOp.idFun B) = HasLinearFunOp.idFun (A ⟶ B))
(swapApp   (A B C   : U) : HasLinearFunOp.swapFunFun (HasLinearFunOp.appFunFun A B) = HasLinearFunOp.idFun (A ⟶ B))
(compAssoc (A B C D : U) : DependentOperation.Associative HasFunctors.Fun HasLinearFunOp.compFunFunFun A B C D)

class HasAffineFunOpEquiv (U : Universe) [HasEmbeddedFunctors U] [HasAffineFunOp U] extends HasLinearFunOpEquiv U where
(swapConst  (A B   : U) : HasLinearFunOp.swapFunFun (HasSubLinearFunOp.constFunFun A B) = HasSubLinearFunOp.constFun A (HasLinearFunOp.idFun B))
(leftConst  (A B C : U) : HasLinearFunOp.revCompFunFunFun A B C ⊙ HasSubLinearFunOp.constFunFun B C = HasSubLinearFunOp.constFunFun (A ⟶ B) (A ⟶ C) ⊙ HasSubLinearFunOp.constFunFun A C)
(rightConst (A B C : U) : HasLinearFunOp.compFunFunFun A B C ⊙ HasSubLinearFunOp.constFunFun A B = HasLinearFunOp.revCompFunFun (B ⟶ C) (HasSubLinearFunOp.constFunFun A C) ⊙ HasLinearFunOp.appFunFun B C)

class HasFullFunOpEquiv (U : Universe) [HasEmbeddedFunctors U] [HasFullFunOp U] extends HasAffineFunOpEquiv U where
(dupConst (A B : U) : HasNonLinearFunOp.dupFunFun A B ⊙ HasSubLinearFunOp.constFunFun A (A ⟶ B) = HasLinearFunOp.idFun (A ⟶ B))
