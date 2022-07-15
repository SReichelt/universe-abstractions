import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedFunctors
import UniverseAbstractions.Universes.Layer1.Meta.Tactics.Functoriality



namespace UniverseAbstractions.Layer1.Meta.Tactics.Functoriality.Test

set_option autoImplicit false
set_option trace.Meta.Tactic true
set_option linter.unusedVariables false

universe u uu

open HasPiType HasFunctors HasLinearLogic



-- This file contains tests for `makeFunctor` (mostly used implicitly via the `Λ` notation) and the
-- `functoriality` tactic (which mostly uses the same code).
--
-- It exercises all special cases in the tactic. If a case fails, there will be an error in the
-- corresponding `def`.
--
-- The output of the `#print` statements can be inspected manually to verify that the tactic
-- produced a well-optimized functor using the available operations.
-- See especially `#print testTestCompComp`, `#print testTestComp₂`, and `#print testTestDupArg`,
-- where the tactic definitely provides an advantage over proving functoriality by hand.



variable {U : Universe.{u, uu}} [HasFullLogic U] (A B C D : U)

def testRawFun (F : A ⥤ B) : A ⥤ B := makeFunctor (HasFunctors.apply F)
#print testRawFun

def testRawPi {P : A → U} [HasPiType P] (F : Pi P) : Pi P := makeFunctor (HasPiType.apply F)
#print testRawPi

def testRawFunct (F : A ⥤ B) : A ⥤{HasFunctors.apply F} B := by functoriality
#print testRawFunct

def testRawPiFunct {P : A → U} [HasPiType P] (F : Pi P) : DefPi P (HasPiType.apply F) :=
  by functoriality
#print testRawPiFunct

def testConst (b : B) : A ⥤ B := Λ a => b
#print testConst

def testNamedConst (b : B) : A ⥤ B := makeFunctor (Function.const A b)
#print testNamedConst

def testConstFunct (b : B) : A ⥤{Function.const A b} B := by functoriality
#print testConstFunct

def testTestConst : B ⥤ (A ⥤ B) := Λ b => testConst A B b
#print testTestConst

def testId : A ⥤ A := Λ a => a
#print testId

def testNamedId : A ⥤ A := makeFunctor id
#print testNamedId

def testTestId : B ⥤ (A ⥤ A) := Λ b => testId A
#print testTestId

def testFun (F : A ⥤ B) : A ⥤ B := Λ a => F a
#print testFun

def app {A B : U} (F : A ⥤ B) (a : A) := F a
def testIndirFun (F : A ⥤ B) : A ⥤ B := Λ a => app F a
#print testIndirFun

def testApp (a : A) : (A ⥤ B) ⥤ B := Λ F => F a
#print testApp

def testAppPi {P : A → U} [HasPiType P] [HasPiAppFun P] (a : A) : Pi P ⥤ P a := Λ F => F a
#print testAppPi

def testTestApp : A ⥤ (A ⥤ B) ⥤ B := Λ a => testApp A B a
#print testTestApp

def testTestApp' : A ⥤ (A ⥤ B) ⥤ B := Λ a F => F a
#print testTestApp'

def testIndirApp (a : A) : (A ⥤ B) ⥤ B := Λ F => app F a
#print testIndirApp

def testFixSnd (F : A ⥤ B ⥤ C) (b : B) : A ⥤ C := Λ a => F a b
#print testFixSnd

def testFixSndPi {P : A → B → U} [∀ a, HasPiType (P a)] [HasPiType (λ a => Pi (P a))]
                 [∀ b, HasPiType (λ a => P a b)] [HasSwapPi P] (F : Pi₂ P) (b : B) :
    Pi (λ a => P a b) :=
  Λ a => F a b
#print testFixSndPi

def testSwap : (A ⥤ B ⥤ C) ⥤ (B ⥤ A ⥤ C) := Λ F b => testFixSnd A B C F b
#print testSwap

def testRevSwap : B ⥤ (A ⥤ B ⥤ C) ⥤ (A ⥤ C) := Λ b F => testFixSnd A B C F b
#print testRevSwap

def testSwap₂₃ : (A ⥤ B ⥤ C ⥤ D) ⥤ (A ⥤ C ⥤ B ⥤ D) := Λ F a c b => F a b c
#print testSwap₂₃

def testComp (F : A ⥤ B) (G : B ⥤ C) : A ⥤ C := Λ a => G (F a)
#print testComp

def testCompFunPi {Q : B → U} [HasPiType Q] [∀ F : A ⥤ B, HasPiType (λ a => Q (F a))]
                  (F : A ⥤ B) (G : Pi Q) [HasCompFunPi A Q] :
    Pi (λ a => Q (F a)) :=
  Λ a => G (F a)
#print testCompFunPi

def testTestComp₁ (F : A ⥤ B) : (B ⥤ C) ⥤ (A ⥤ C) := Λ G => testComp A B C F G
#print testTestComp₁

def testTestComp : (A ⥤ B) ⥤ (B ⥤ C) ⥤ (A ⥤ C) := Λ F G => testComp A B C F G
#print testTestComp

def testRevTestComp₁ (G : B ⥤ C) : (A ⥤ B) ⥤ (A ⥤ C) := Λ F => testComp A B C F G
#print testRevTestComp₁

def testRevTestComp : (B ⥤ C) ⥤ (A ⥤ B) ⥤ (A ⥤ C) := Λ G F => testComp A B C F G
#print testRevTestComp

def comp {A B C : U} (F : A ⥤ B) (G : B ⥤ C) (a : A) := app G (app F a)
def testIndirComp (F : A ⥤ B) (G : B ⥤ C) : A ⥤ C := Λ a => comp F G a
#print testIndirComp

def testCompComp (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) : A ⥤ D := Λ a => H (G (F a))
#print testCompComp

def testCompCompFunct (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) : A ⥤{λ a => H (G (F a))} D :=
  by functoriality
#print testCompCompFunct

def testTestCompComp : (A ⥤ B) ⥤ (B ⥤ C) ⥤ (C ⥤ D) ⥤ (A ⥤ D) :=
  Λ F G H => testCompComp A B C D F G H
#print testTestCompComp

def testTestCompCompFunct (F : A ⥤ B) (H : C ⥤ D) :
    (B ⥤ C) ⥤{λ G => testCompComp A B C D F G H} (A ⥤ D) :=
  by functoriality
#print testTestCompCompFunct

def testTestCompCompFunct₂ (F : A ⥤ B) :
    (B ⥤ C) ⥤ (C ⥤ D) ⥤{λ G H => testCompComp A B C D F G H} (A ⥤ D) :=
  by functoriality
#print testTestCompCompFunct₂

def testTestCompCompFunct₃ :
    (A ⥤ B) ⥤ (B ⥤ C) ⥤ (C ⥤ D) ⥤{λ F G H => testCompComp A B C D F G H} (A ⥤ D) :=
  by functoriality
#print testTestCompCompFunct₃

def testComp₂ (F : A ⥤ B ⥤ C) (G : C ⥤ D) : A ⥤ B ⥤ D := Λ a b => G (F a b)
#print testComp₂

def testTestComp₂ : (A ⥤ B ⥤ C) ⥤ (C ⥤ D) ⥤ (A ⥤ B ⥤ D) := Λ F G => testComp₂ A B C D F G
#print testTestComp₂

def testRevTestComp₂ : (C ⥤ D) ⥤ (A ⥤ B ⥤ C) ⥤ (A ⥤ B ⥤ D) := Λ G F => testComp₂ A B C D F G
#print testRevTestComp₂

def testRevTestComp₂Funct :
    (C ⥤ D) ⥤{λ G => Λ F => testComp₂ A B C D F G} ((A ⥤ B ⥤ C) ⥤ (A ⥤ B ⥤ D)) :=
  by functoriality
#print testRevTestComp₂Funct

def testRevAppApp : A ⥤ (A ⥤ B) ⥤ (B ⥤ C) ⥤ C := Λ a F G => G (F a)
#print testRevAppApp

def testDup (F : A ⥤ A ⥤ B) : A ⥤ B := Λ a => F a a
#print testDup

def testDupPi {P : A → A → U} [∀ a, HasPiType (P a)] [HasPiType (λ a => Pi (P a))]
              [HasPiType (λ a => P a a)] [HasDupPi P] (F : Pi₂ P) :
    Pi (λ a => P a a) :=
  Λ a => F a a
#print testDupPi

def testTestDup : (A ⥤ A ⥤ B) ⥤ (A ⥤ B) := Λ F => testDup A B F
#print testTestDup

def testDupArg (F : A ⥤ C ⥤ A ⥤ B) (c : C) : A ⥤ B := Λ a => F a c a
#print testDupArg

def testTestDupArg : (A ⥤ C ⥤ A ⥤ B) ⥤ C ⥤ (A ⥤ B) := Λ F c => testDupArg A B C F c
#print testTestDupArg

def testSelfApp (G : A ⥤ B) : ((A ⥤ B) ⥤ A) ⥤ B := Λ F => G (F G)
#print testSelfApp

def testTestSelfApp : (A ⥤ B) ⥤ ((A ⥤ B) ⥤ A) ⥤ B := Λ G => testSelfApp A B G
#print testTestSelfApp

def testRevSelfApp (F : (A ⥤ B) ⥤ A) : (A ⥤ B) ⥤ B := Λ G => G (F G)
#print testRevSelfApp

def testRevSelfAppPi {P : A → U} [HasPiType P] [∀ F : Pi P ⥤ A, HasPiType (λ G => P (F G))]
                     [HasPiSelfAppPi P] (F : Pi P ⥤ A) :
    Pi (λ G : Pi P => P (F G)) :=
  Λ G => G (F G)
#print testRevSelfAppPi

def testTestRevSelfApp : ((A ⥤ B) ⥤ A) ⥤ (A ⥤ B) ⥤ B := Λ F => testRevSelfApp A B F
#print testTestRevSelfApp

def testSubst (F : A ⥤ B) (G : A ⥤ B ⥤ C) : A ⥤ C := Λ a => G a (F a)
#print testSubst

def testSubstPi {P : A → U} {Q : ∀ a, P a → U} [HasPiType P] [∀ a, HasPiType (Q a)]
                [HasPiType (λ a => Pi (Q a))] [∀ F : Pi P, HasPiType (λ a => Q a (F a))]
                [HasSubstPi Q] (F : Pi P) (G : Pi (λ a => Pi (Q a))) :
    Pi (λ a => Q a (F a)) :=
  Λ a => G a (F a)
#print testSubstPi

def testTestSubst : (A ⥤ B) ⥤ (A ⥤ B ⥤ C) ⥤ (A ⥤ C) := Λ F G => testSubst A B C F G
#print testTestSubst

def testRevTestSubst : (A ⥤ B ⥤ C) ⥤ (A ⥤ B) ⥤ (A ⥤ C) := Λ G F => testSubst A B C F G
#print testRevTestSubst

def testSubst₂ (F : A ⥤ B ⥤ C) (G : A ⥤ B ⥤ C ⥤ D) : A ⥤ B ⥤ D := Λ a b => G a b (F a b)
#print testSubst₂

def testDup₃ : (A ⥤ A ⥤ A ⥤ B) ⥤ (A ⥤ B) := Λ F a => F a a a
#print testDup₃
