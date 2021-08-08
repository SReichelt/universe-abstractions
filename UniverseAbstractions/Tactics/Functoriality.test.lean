import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Tactics.Functoriality



set_option autoBoundImplicitLocal false
--set_option pp.universes true
--set_option pp.all true



-- This file contains tests for the `makeFunctor` and `functoriality` tactics, mostly used
-- implicitly via the `Λ` notation.
--
-- It exercises all special cases in the tactic. If a case fails, there will be an error in the
-- corresponding `def`.
--
-- The output of the `#print` statements can be inspected manually to verify that the tactic
-- produced a well-optimized functor using the available operations.
-- See especially `#print testTestCompComp`, `#print testTestComp₂`, and `#print testTestDupArg`,
-- where the tactic definitely provides an advantage over proving functoriality by hand.



variable {U : Universe} [HasFunOp U]

def testRaw (α β : U) (F : α ⟶ β) : α ⟶ β := by makeFunctor (HasEmbeddedFunctors.funCoe F)
#print testRaw

def testRawFunct (α β : U) (F : α ⟶ β) : α ⟶[HasEmbeddedFunctors.funCoe F] β :=
by functoriality

def testConst (α β : U) (b : β) : α ⟶ β := Λ a => b
#print testConst

def testNamedConst (α β : U) (b : β) : α ⟶ β := by makeFunctor (Function.const ⌈α⌉ b)
#print testNamedConst

def testConstFunct (α β : U) (b : β) : α ⟶[Function.const ⌈α⌉ b] β :=
by functoriality

def testTestConst (α β : U) : β ⟶ (α ⟶ β) := Λ b => testConst α β b
#print testTestConst

def testId (α : U) : α ⟶ α := Λ a => a
#print testId

def testNamedId (α : U) : α ⟶ α := by makeFunctor id
#print testNamedId

def testTestId (α β : U) : β ⟶ (α ⟶ α) := Λ b => testId α
#print testTestId

def testFun (α β : U) (F : α ⟶ β) : α ⟶ β := Λ a => F a
#print testFun

def apply {α β : U} (F : α ⟶ β) (a : α) := F a
def testIndirFun (α β : U) (F : α ⟶ β) : α ⟶ β := Λ a => apply F a
#print testIndirFun

def testFromToDefFun (α β : U) : (α ⟶ β) ⟶ (α ⟶ β) :=
Λ F => HasEmbeddedFunctors.fromDefFun (HasEmbeddedFunctors.toDefFun F)
#print testFromToDefFun
theorem testFromToDefFunEff (α β : U) (F : α ⟶ β) :
  testFromToDefFun α β F = F :=
by simp [testFromToDefFun]

def testApp (α β : U) (a : α) : (α ⟶ β) ⟶ β := Λ F => F a
#print testApp

def testTestApp (α β : U) : α ⟶ (α ⟶ β) ⟶ β := Λ a => testApp α β a
#print testTestApp

def testIndirApp (α β : U) (a : α) : (α ⟶ β) ⟶ β := Λ F => apply F a
#print testIndirApp

def testFixSnd (α β γ : U) (F : α ⟶ β ⟶ γ) (c : β) : α ⟶ γ := Λ a => F a c
#print testFixSnd

def testTestFixSnd (α β γ : U) (F : α ⟶ β ⟶ γ) : (α ⟶ β ⟶ γ) ⟶ (β ⟶ α ⟶ γ) := Λ F b => testFixSnd α β γ F b
#print testTestFixSnd

def testRevTestFixSnd (α β γ : U) (F : α ⟶ β ⟶ γ) : β ⟶ (α ⟶ β ⟶ γ) ⟶ (α ⟶ γ) := Λ b F => testFixSnd α β γ F b
#print testRevTestFixSnd

def testComp (α β γ : U) (F : α ⟶ β) (G : β ⟶ γ) : α ⟶ γ := Λ a => G (F a)
#print testComp

def testTestComp (α β γ : U) : (α ⟶ β) ⟶ (β ⟶ γ) ⟶ (α ⟶ γ) := Λ F G => testComp α β γ F G
#print testTestComp

def testRevTestComp (α β γ : U) : (β ⟶ γ) ⟶ (α ⟶ β) ⟶ (α ⟶ γ) := Λ G F => testComp α β γ F G
#print testRevTestComp

def comp {α β γ : U} (F : α ⟶ β) (G : β ⟶ γ) (a : α) := apply G (apply F a)
def testIndirComp (α β γ : U) (F : α ⟶ β) (G : β ⟶ γ) : α ⟶ γ := Λ a => comp F G a
#print testIndirComp

def testCompComp (α β γ δ : U) (F : α ⟶ β) (G : β ⟶ γ) (H : γ ⟶ δ) : α ⟶ δ := Λ a => H (G (F a))
#print testCompComp
theorem testCompCompEff (α β γ δ : U) (F : α ⟶ β) (G : β ⟶ γ) (H : γ ⟶ δ) (a : α) :
  (testCompComp α β γ δ F G H) a = H (G (F a)) :=
by simp [testCompComp]

def testCompCompFunct (α β γ δ : U) (F : α ⟶ β) (G : β ⟶ γ) (H : γ ⟶ δ) : α ⟶[λ a => H (G (F a))] δ :=
by functoriality

def testTestCompComp (α β γ δ : U) : (α ⟶ β) ⟶ (β ⟶ γ) ⟶ (γ ⟶ δ) ⟶ (α ⟶ δ) := Λ F G H => testCompComp α β γ δ F G H
#print testTestCompComp
theorem testTestCompCompEff (α β γ δ : U) (F : α ⟶ β) (G : β ⟶ γ) (H : γ ⟶ δ) (a : α) :
  (testTestCompComp α β γ δ F G H) a = H (G (F a)) :=
by simp [testTestCompComp]

-- TODO: This currently does not work because `functoriality` would need to output
-- `by simp [testCompComp]` but only outputs `by simp`. Maybe we could solve this by giving `simp`
-- a slightly different target type. E.g. we could let `constructFunctor` produce an unfolded
-- version of the function that we are constructing a functor for.
--def testTestCompCompFunct (α β γ δ : U) (F : α ⟶ β) (H : γ ⟶ δ) : (β ⟶ γ) ⟶[λ G => testCompComp α β γ δ F G H] (α ⟶ δ) :=
--by functoriality
def testTestCompCompFunct (α β γ δ : U) (F : α ⟶ β) (H : γ ⟶ δ) : (β ⟶ γ) ⟶[λ G => Λ a => H (G (F a))] (α ⟶ δ) :=
by functoriality

def testComp₂ (α β γ δ : U) (F : α ⟶ β ⟶ γ) (G : γ ⟶ δ) : α ⟶ β ⟶ δ := Λ a b => G (F a b)
#print testComp₂
theorem testComp₂Eff (α β γ δ : U) (F : α ⟶ β ⟶ γ) (G : γ ⟶ δ) (a : α) (b : β) :
  testComp₂ α β γ δ F G a b = G (F a b) :=
by simp [testComp₂]

def testTestComp₂ (α β γ δ : U) : (α ⟶ β ⟶ γ) ⟶ (γ ⟶ δ) ⟶ (α ⟶ β ⟶ δ) := Λ F G => testComp₂ α β γ δ F G
#print testTestComp₂
theorem testTestComp₂Eff (α β γ δ : U) (F : α ⟶ β ⟶ γ) (G : γ ⟶ δ) (a : α) (b : β) :
  testTestComp₂ α β γ δ F G a b = G (F a b) :=
by simp [testTestComp₂]

def testRevTestComp₂ (α β γ δ : U) : (γ ⟶ δ) ⟶ (α ⟶ β ⟶ γ) ⟶ (α ⟶ β ⟶ δ) := Λ G F => testComp₂ α β γ δ F G
#print testRevTestComp₂
theorem testRevTestComp₂Eff (α β γ δ : U) (G : γ ⟶ δ) (F : α ⟶ β ⟶ γ) (a : α) (b : β) :
  testRevTestComp₂ α β γ δ G F a b = G (F a b) :=
by simp [testRevTestComp₂]

def testDup (α β : U) (F : α ⟶ α ⟶ β) : α ⟶ β := Λ a => F a a
#print testDup

def testTestDup (α β : U) : (α ⟶ α ⟶ β) ⟶ (α ⟶ β) := Λ F => testDup α β F
#print testTestDup

def testDupArg (α β γ : U) (F : α ⟶ γ ⟶ α ⟶ β) (c : γ) : α ⟶ β := Λ a => F a c a
#print testDupArg

def testTestDupArg (α β γ : U) : (α ⟶ γ ⟶ α ⟶ β) ⟶ γ ⟶ (α ⟶ β) := Λ F c => testDupArg α β γ F c
#print testTestDupArg

def testSubst (α β γ : U) (F : α ⟶ β) (G : α ⟶ β ⟶ γ) : α ⟶ γ := Λ a => (G a) (F a)
#print testSubst

def testTestSubst (α β γ : U) : (α ⟶ β) ⟶ (α ⟶ β ⟶ γ) ⟶ (α ⟶ γ) := Λ F G => testSubst α β γ F G
#print testTestSubst

def testRevTestSubst (α β γ : U) : (α ⟶ β ⟶ γ) ⟶ (α ⟶ β) ⟶ (α ⟶ γ) := Λ G F => testSubst α β γ F G
#print testRevTestSubst
