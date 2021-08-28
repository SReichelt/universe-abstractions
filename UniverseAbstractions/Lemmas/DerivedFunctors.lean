import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors



set_option autoBoundImplicitLocal false
--set_option pp.universes true



-- This file derives some additional functors from the axioms in `Axioms/Universe/Functors.lean`.
-- The additional functors are mainly needed for the `makeFunctor` and `functoriality` tactics in
-- `Tactics/Functoriality.lean`. In order for those tactics to work correctly, they must be given
-- as a "definitional" version first, with the expected mapping behavior.



namespace HasLinearFunOp

  variable {U : Universe} [HasEmbeddedFunctors U] [HasLinearFunOp U]

  -- The "swap" functor swaps the arguments of a nested functor.
  -- Its plain version `swapFun` actually just fixes the second argument.
  -- The presence of `swapFunFun` establishes that when something is functorial in two arguments
  -- given in a specific order, it is also functorial in the two arguments given in the reverse
  -- order.

  def defSwapFun {α β γ : U} (F : α ⟶ β ⟶ γ) (b : β) : α ⟶[λ a => F a b] γ :=
  appFun b γ ⊙ F
  ◄ λ _ => by simp

  @[reducible] def swapFun {α β γ : U} (F : α ⟶ β ⟶ γ) (b : β) : α ⟶ γ := defSwapFun F b

  def defSwapFunFun {α β γ : U} (F : α ⟶ β ⟶ γ) : β ⟶[λ b => swapFun F b] (α ⟶ γ) :=
  compFunFun F γ ⊙ appFunFun β γ
  ◄ λ _ => by simp [swapFun, defSwapFun]

  @[reducible] def swapFunFun {α β γ : U} (F : α ⟶ β ⟶ γ) : β ⟶ α ⟶ γ := defSwapFunFun F

  def defSwapFunFunFun (α β γ : U) : (α ⟶ β ⟶ γ) ⟶[λ F => swapFunFun F] (β ⟶ α ⟶ γ) :=
  compFunFun (appFunFun β γ) (α ⟶ γ) ⊙ compFunFunFun α (β ⟶ γ) γ
  ◄ λ _ => by simp [swapFunFun, defSwapFunFun]

  @[reducible] def swapFunFunFun (α β γ : U) : (α ⟶ β ⟶ γ) ⟶ (β ⟶ α ⟶ γ) := defSwapFunFunFun α β γ

  -- We can apply the "swap" functor to itself to obtain its functoriality in reverse order.

  @[reducible] def revSwapFun {α β γ : U} (b : β) (F : α ⟶ β ⟶ γ) : α ⟶ γ := swapFun F b

  def defRevSwapFunFun (α : U) {β : U} (b : β) (γ : U) : (α ⟶ β ⟶ γ) ⟶[λ F => revSwapFun b F] (α ⟶ γ) :=
  swapFun (swapFunFunFun α β γ) b
  ◄ λ _ => by simp

  @[reducible] def revSwapFunFun (α : U) {β : U} (b : β) (γ : U) : (α ⟶ β ⟶ γ) ⟶ (α ⟶ γ) := defRevSwapFunFun α b γ

  def defRevSwapFunFunFun (α β γ : U) : β ⟶[λ b => revSwapFunFun α b γ] ((α ⟶ β ⟶ γ) ⟶ (α ⟶ γ)) :=
  swapFunFun (swapFunFunFun α β γ)
  ◄ λ _ => by simp [revSwapFunFun, defRevSwapFunFun]

  @[reducible] def revSwapFunFunFun (α β γ : U) : β ⟶ (α ⟶ β ⟶ γ) ⟶ (α ⟶ γ) := defRevSwapFunFunFun α β γ

  -- Same for composition.

  def defRevCompFunFun (α : U) {β γ : U} (G : β ⟶ γ) : (α ⟶ β) ⟶[λ F => revCompFun G F] (α ⟶ γ) :=
  swapFun (compFunFunFun α β γ) G
  ◄ λ _ => by simp

  @[reducible] def revCompFunFun (α : U) {β γ : U} (G : β ⟶ γ) : (α ⟶ β) ⟶ (α ⟶ γ) := defRevCompFunFun α G

  def defRevCompFunFunFun (α β γ : U) : (β ⟶ γ) ⟶[λ G => revCompFunFun α G] ((α ⟶ β) ⟶ (α ⟶ γ)) :=
  swapFunFun (compFunFunFun α β γ)
  ◄ λ _ => by simp [revCompFunFun, defRevCompFunFun]

  @[reducible] def revCompFunFunFun (α β γ : U) : (β ⟶ γ) ⟶ (α ⟶ β) ⟶ (α ⟶ γ) := defRevCompFunFunFun α β γ

end HasLinearFunOp



namespace HasFullFunOp

  variable {U : Universe} [HasEmbeddedFunctors U] [HasFullFunOp U]

  -- The S combinator (see https://en.wikipedia.org/wiki/SKI_combinator_calculus), which in our case says
  -- that if we can functorially construct a functor `G a : β ⟶ γ` and an argument `F a : β` from `a`,
  -- then the construction of `(G a) (F a)` from `a` is also functorial.
  -- We give two versions of the functor that differ in their argument order, analogously to composition.

  def defSubstFun {α β γ : U} (F : α ⟶ β) (G : α ⟶ β ⟶ γ) : α ⟶[λ a => G a (F a)] γ :=
  HasNonLinearFunOp.dupFun (HasLinearFunOp.swapFunFun G ⊙ F)
  ◄ λ _ => by simp

  @[reducible] def substFun {α β γ : U} (F : α ⟶ β) (G : α ⟶ β ⟶ γ) : α ⟶ γ := defSubstFun F G

  def defSubstFunFun {α β : U} (F : α ⟶ β) (γ : U) : (α ⟶ β ⟶ γ) ⟶[λ G => substFun F G] (α ⟶ γ) :=
  HasNonLinearFunOp.dupFunFun α γ ⊙ HasLinearFunOp.compFunFun F (α ⟶ γ) ⊙ HasLinearFunOp.swapFunFunFun α β γ
  ◄ λ _ => by simp [substFun, defSubstFun]

  @[reducible] def substFunFun {α β : U} (F : α ⟶ β) (γ : U) : (α ⟶ β ⟶ γ) ⟶ (α ⟶ γ) := defSubstFunFun F γ

  def defSubstFunFunFun (α β γ : U) : (α ⟶ β) ⟶[λ F => substFunFun F γ] ((α ⟶ β ⟶ γ) ⟶ (α ⟶ γ)) :=
  HasLinearFunOp.revCompFunFun (α ⟶ β ⟶ γ) (HasNonLinearFunOp.dupFunFun α γ) ⊙
  HasLinearFunOp.compFunFun (HasLinearFunOp.swapFunFunFun α β γ) (α ⟶ α ⟶ γ) ⊙
  HasLinearFunOp.compFunFunFun α β (α ⟶ γ)
  ◄ λ _ => by simp [substFunFun, defSubstFunFun]

  @[reducible] def substFunFunFun (α β γ : U) : (α ⟶ β) ⟶ (α ⟶ β ⟶ γ) ⟶ (α ⟶ γ) :=
  defSubstFunFunFun α β γ

  -- Substitution with reverse argument order.

  @[reducible] def revSubstFun {α β γ : U} (G : α ⟶ β ⟶ γ) (F : α ⟶ β) := substFun F G

  def defRevSubstFunFun {α β γ : U} (G : α ⟶ β ⟶ γ) : (α ⟶ β) ⟶[λ F => revSubstFun G F] (α ⟶ γ) :=
  HasLinearFunOp.swapFun (substFunFunFun α β γ) G
  ◄ λ _ => by simp

  @[reducible] def revSubstFunFun {α β γ : U} (G : α ⟶ β ⟶ γ) : (α ⟶ β) ⟶ (α ⟶ γ) := defRevSubstFunFun G

  def defRevSubstFunFunFun (α β γ : U) : (α ⟶ β ⟶ γ) ⟶[λ G => revSubstFunFun G] ((α ⟶ β) ⟶ (α ⟶ γ)) :=
  HasLinearFunOp.swapFunFun (substFunFunFun α β γ)
  ◄ λ _ => by simp [revSubstFunFun, defRevSubstFunFun]

  @[reducible] def revSubstFunFunFun (α β γ : U) : (α ⟶ β ⟶ γ) ⟶ (α ⟶ β) ⟶ (α ⟶ γ) :=
  defRevSubstFunFunFun α β γ

end HasFullFunOp



-- TODO: Replace equality with instance equivalence
-- TODO: `swapApp` is provable from `swapFunFun` being self-inverse (`swapConst` also?)
-- TODO: Recover more readable variants

def DependentOperation {α : Sort _} {U : Universe} [HasEmbeddedFunctors U] (P : α → α → U) :=
∀ a b c, P a b ⟶ P b c ⟶ P a c

def DependentOperation.Associative {α : Sort _} {U : Universe} [HasEmbeddedFunctors U] [HasLinearFunOp U]
                                   (P : α → α → U) (R : DependentOperation P) (a b c d : α) :=
HasLinearFunOp.swapFunFun (HasLinearFunOp.compFunFunFun (P c d) (P b d) (P a d) ⊙ R b c d) ⊙ R a b d =
HasLinearFunOp.revCompFunFun (P b c) (R a c d) ⊙ R a b c

class HasLinearFunOpEquiv (U : Universe) [HasEmbeddedFunctors U] [HasLinearFunOp U] where
(rightId   (α β     : U) : HasLinearFunOp.compFunFun (HasLinearFunOp.idFun α) β = HasLinearFunOp.idFun (α ⟶ β))
(leftId    (α β     : U) : HasLinearFunOp.revCompFunFun α (HasLinearFunOp.idFun β) = HasLinearFunOp.idFun (α ⟶ β))
(swapApp   (α β γ   : U) : HasLinearFunOp.swapFunFun (HasLinearFunOp.appFunFun α β) = HasLinearFunOp.idFun (α ⟶ β))
(compAssoc (α β γ δ : U) : DependentOperation.Associative HasFunctors.Fun HasLinearFunOp.compFunFunFun α β γ δ)

class HasAffineFunOpEquiv (U : Universe) [HasEmbeddedFunctors U] [HasAffineFunOp U] extends HasLinearFunOpEquiv U where
(swapConst  (α β   : U) : HasLinearFunOp.swapFunFun (HasSubLinearFunOp.constFunFun α β) = HasSubLinearFunOp.constFun α (HasLinearFunOp.idFun β))
(leftConst  (α β γ : U) : HasLinearFunOp.revCompFunFunFun α β γ ⊙ HasSubLinearFunOp.constFunFun β γ = HasSubLinearFunOp.constFunFun (α ⟶ β) (α ⟶ γ) ⊙ HasSubLinearFunOp.constFunFun α γ)
(rightConst (α β γ : U) : HasLinearFunOp.compFunFunFun α β γ ⊙ HasSubLinearFunOp.constFunFun α β = HasLinearFunOp.revCompFunFun (β ⟶ γ) (HasSubLinearFunOp.constFunFun α γ) ⊙ HasLinearFunOp.appFunFun β γ)

class HasFullFunOpEquiv (U : Universe) [HasEmbeddedFunctors U] [HasFullFunOp U] extends HasAffineFunOpEquiv U where
(dupConst (α β : U) : HasNonLinearFunOp.dupFunFun α β ⊙ HasSubLinearFunOp.constFunFun α (α ⟶ β) = HasLinearFunOp.idFun (α ⟶ β))
