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

def testRaw (A B : U) (F : A ⟶ B) : A ⟶ B := by makeFunctor (HasFunctors.funCoe F)
#print testRaw

def testRawFunct (A B : U) (F : A ⟶ B) : A ⟶[HasFunctors.funCoe F] B :=
by functoriality

def testConst (A B : U) (b : B) : A ⟶ B := Λ a => b
#print testConst

def testNamedConst (A B : U) (b : B) : A ⟶ B := by makeFunctor (Function.const ⌈A⌉ b)
#print testNamedConst

def testConstFunct (A B : U) (b : B) : A ⟶[Function.const ⌈A⌉ b] B :=
by functoriality

def testTestConst (A B : U) : B ⟶ (A ⟶ B) := Λ b => testConst A B b
#print testTestConst

def testId (A : U) : A ⟶ A := Λ a => a
#print testId

def testNamedId (A : U) : A ⟶ A := by makeFunctor id
#print testNamedId

def testTestId (A B : U) : B ⟶ (A ⟶ A) := Λ b => testId A
#print testTestId

def testFun (A B : U) (F : A ⟶ B) : A ⟶ B := Λ a => F a
#print testFun

def apply {A B : U} (F : A ⟶ B) (a : A) := F a
def testIndirFun (A B : U) (F : A ⟶ B) : A ⟶ B := Λ a => apply F a
#print testIndirFun

def testFromToDefFun (A B : U) : (A ⟶ B) ⟶ (A ⟶ B) :=
Λ F => HasFunctors.fromDefFun (HasFunctors.toDefFun F)
#print testFromToDefFun
theorem testFromToDefPiEff (A B : U) (F : A ⟶ B) :
  testFromToDefFun A B F = F :=
by simp [testFromToDefFun]

def testApp (A B : U) (a : A) : (A ⟶ B) ⟶ B := Λ F => F a
#print testApp

def testTestApp (A B : U) : A ⟶ (A ⟶ B) ⟶ B := Λ a => testApp A B a
#print testTestApp

def testIndirApp (A B : U) (a : A) : (A ⟶ B) ⟶ B := Λ F => apply F a
#print testIndirApp

def testFixSnd (A B C : U) (F : A ⟶ B ⟶ C) (b : B) : A ⟶ C := Λ a => F a b
#print testFixSnd

def testTestFixSnd (A B C : U) (F : A ⟶ B ⟶ C) : (A ⟶ B ⟶ C) ⟶ (B ⟶ A ⟶ C) := Λ F b => testFixSnd A B C F b
#print testTestFixSnd

def testRevTestFixSnd (A B C : U) (F : A ⟶ B ⟶ C) : B ⟶ (A ⟶ B ⟶ C) ⟶ (A ⟶ C) := Λ b F => testFixSnd A B C F b
#print testRevTestFixSnd

def testComp (A B C : U) (F : A ⟶ B) (G : B ⟶ C) : A ⟶ C := Λ a => G (F a)
#print testComp

def testTestComp (A B C : U) : (A ⟶ B) ⟶ (B ⟶ C) ⟶ (A ⟶ C) := Λ F G => testComp A B C F G
#print testTestComp

def testRevTestComp (A B C : U) : (B ⟶ C) ⟶ (A ⟶ B) ⟶ (A ⟶ C) := Λ G F => testComp A B C F G
#print testRevTestComp

def comp {A B C : U} (F : A ⟶ B) (G : B ⟶ C) (a : A) := apply G (apply F a)
def testIndirComp (A B C : U) (F : A ⟶ B) (G : B ⟶ C) : A ⟶ C := Λ a => comp F G a
#print testIndirComp

def testCompComp (A B C D : U) (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) : A ⟶ D := Λ a => H (G (F a))
#print testCompComp
theorem testCompCompEff (A B C D : U) (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) (a : A) :
  (testCompComp A B C D F G H) a = H (G (F a)) :=
by simp [testCompComp]

def testCompCompFunct (A B C D : U) (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) : A ⟶[λ a => H (G (F a))] D :=
by functoriality

def testTestCompComp (A B C D : U) : (A ⟶ B) ⟶ (B ⟶ C) ⟶ (C ⟶ D) ⟶ (A ⟶ D) := Λ F G H => testCompComp A B C D F G H
#print testTestCompComp
theorem testTestCompCompEff (A B C D : U) (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) (a : A) :
  (testTestCompComp A B C D F G H) a = H (G (F a)) :=
by simp [testTestCompComp]

-- TODO: This currently does not work because `functoriality` would need to output
-- `by simp [testCompComp]` but only outputs `by simp`. Maybe we could solve this by giving `simp`
-- a slightly different target type. E.g. we could let `constructFunctor` produce an unfolded
-- version of the function that we are constructing a functor for.
--def testTestCompCompFunct (A B C D : U) (F : A ⟶ B) (H : C ⟶ D) : (B ⟶ C) ⟶[λ G => testCompComp A B C D F G H] (A ⟶ D) :=
--by functoriality
def testTestCompCompFunct (A B C D : U) (F : A ⟶ B) (H : C ⟶ D) : (B ⟶ C) ⟶[λ G => Λ a => H (G (F a))] (A ⟶ D) :=
by functoriality

def testComp₂ (A B C D : U) (F : A ⟶ B ⟶ C) (G : C ⟶ D) : A ⟶ B ⟶ D := Λ a b => G (F a b)
#print testComp₂
theorem testComp₂Eff (A B C D : U) (F : A ⟶ B ⟶ C) (G : C ⟶ D) (a : A) (b : B) :
  testComp₂ A B C D F G a b = G (F a b) :=
by simp [testComp₂]

def testTestComp₂ (A B C D : U) : (A ⟶ B ⟶ C) ⟶ (C ⟶ D) ⟶ (A ⟶ B ⟶ D) := Λ F G => testComp₂ A B C D F G
#print testTestComp₂
theorem testTestComp₂Eff (A B C D : U) (F : A ⟶ B ⟶ C) (G : C ⟶ D) (a : A) (b : B) :
  testTestComp₂ A B C D F G a b = G (F a b) :=
by simp [testTestComp₂]

def testRevTestComp₂ (A B C D : U) : (C ⟶ D) ⟶ (A ⟶ B ⟶ C) ⟶ (A ⟶ B ⟶ D) := Λ G F => testComp₂ A B C D F G
#print testRevTestComp₂
theorem testRevTestComp₂Eff (A B C D : U) (G : C ⟶ D) (F : A ⟶ B ⟶ C) (a : A) (b : B) :
  testRevTestComp₂ A B C D G F a b = G (F a b) :=
by simp [testRevTestComp₂]

def testDup (A B : U) (F : A ⟶ A ⟶ B) : A ⟶ B := Λ a => F a a
#print testDup

def testTestDup (A B : U) : (A ⟶ A ⟶ B) ⟶ (A ⟶ B) := Λ F => testDup A B F
#print testTestDup

def testDupArg (A B C : U) (F : A ⟶ C ⟶ A ⟶ B) (c : C) : A ⟶ B := Λ a => F a c a
#print testDupArg

def testTestDupArg (A B C : U) : (A ⟶ C ⟶ A ⟶ B) ⟶ C ⟶ (A ⟶ B) := Λ F c => testDupArg A B C F c
#print testTestDupArg

def testSubst (A B C : U) (F : A ⟶ B) (G : A ⟶ B ⟶ C) : A ⟶ C := Λ a => (G a) (F a)
#print testSubst

def testTestSubst (A B C : U) : (A ⟶ B) ⟶ (A ⟶ B ⟶ C) ⟶ (A ⟶ C) := Λ F G => testSubst A B C F G
#print testTestSubst

def testRevTestSubst (A B C : U) : (A ⟶ B ⟶ C) ⟶ (A ⟶ B) ⟶ (A ⟶ C) := Λ G F => testSubst A B C F G
#print testRevTestSubst
