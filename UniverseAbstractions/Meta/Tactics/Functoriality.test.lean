import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Lemmas.DerivedFunctors
import UniverseAbstractions.Lemmas.DerivedProductFunctors
import UniverseAbstractions.Meta.Tactics.Functoriality



set_option autoBoundImplicitLocal false
--set_option pp.universes true
--set_option pp.all true

universe u v iu iuv



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



variable {U : Universe.{u, v}} [HasIdentity.{u, iu, v, iuv} U] [HasInternalFunctors U] [HasFullFunOp U]

def testRaw (A B : U) (F : A ⟶ B) : A ⟶ B := by makeFunctor (HasFunctors.apply F)
#print testRaw
def testRawEff (A B : U) (F : A ⟶ B) (a : A) : (testRaw A B F) a ≃ F a := HasFunctors.byDef

def testRawFunct (A B : U) (F : A ⟶ B) : A ⟶{HasFunctors.apply F} B :=
by functoriality
#print testRawFunct

def testConst (A B : U) (b : B) : A ⟶ B := Λ a => b
#print testConst

def testNamedConst (A B : U) (b : B) : A ⟶ B := by makeFunctor (Function.const A b)
#print testNamedConst

def testConstFunct (A B : U) (b : B) : A ⟶{Function.const A b} B :=
by functoriality
#print testConstFunct

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

def testAppFun (A B : U) (F : A ⟶ B) : A ⟶ B := Λ a => (HasFunctors.appFun F) a
#print testAppFun
def testAppFunEff (A B : U) (F : A ⟶ B) (a : A) :
  (testAppFun A B F) a ≃ (HasFunctors.appFun F) a :=
HasFunctors.byDef

def apply {A B : U} (F : A ⟶ B) (a : A) := F a
def testIndirFun (A B : U) (F : A ⟶ B) : A ⟶ B := Λ a => apply F a
#print testIndirFun

def testFromToDefFun (A B : U) : (A ⟶ B) ⟶ (A ⟶ B) :=
Λ F => HasFunctors.fromDefFun (HasFunctors.toDefFun F)
#print testFromToDefFun
def testFromToDefPiEff (A B : U) (F : A ⟶ B) :
  testFromToDefFun A B F ≃ F :=
HasFunctors.byDef

def testApp (A B : U) (a : A) : (A ⟶ B) ⟶ B := Λ F => F a
#print testApp

def testTestApp (A B : U) : A ⟶ (A ⟶ B) ⟶ B := Λ a => testApp A B a
#print testTestApp

def testIndirApp (A B : U) (a : A) : (A ⟶ B) ⟶ B := Λ F => apply F a
#print testIndirApp

def testFixSnd (A B C : U) (F : A ⟶ B ⟶ C) (b : B) : A ⟶ C := Λ a => F a b
#print testFixSnd

def testSwap (A B C : U) : (A ⟶ B ⟶ C) ⟶ (B ⟶ A ⟶ C) := Λ F b => testFixSnd A B C F b
#print testSwap

def testRevSwap (A B C : U) : B ⟶ (A ⟶ B ⟶ C) ⟶ (A ⟶ C) := Λ b F => testFixSnd A B C F b
#print testRevSwap

def testSwap₂₃ (A B C D : U) : (A ⟶ B ⟶ C ⟶ D) ⟶ (A ⟶ C ⟶ B ⟶ D) := Λ F a c b => F a b c
#print testSwap₂₃

def testComp (A B C : U) (F : A ⟶ B) (G : B ⟶ C) : A ⟶ C := Λ a => G (F a)
#print testComp
def testCompEff (A B C : U) (F : A ⟶ B) (G : B ⟶ C) (a : A) :
  (testComp A B C F G) a ≃ G (F a) :=
HasFunctors.byDef

def testTestComp (A B C : U) : (A ⟶ B) ⟶ (B ⟶ C) ⟶ (A ⟶ C) := Λ F G => testComp A B C F G
#print testTestComp

def testRevTestComp (A B C : U) : (B ⟶ C) ⟶ (A ⟶ B) ⟶ (A ⟶ C) := Λ G F => testComp A B C F G
#print testRevTestComp

def comp {A B C : U} (F : A ⟶ B) (G : B ⟶ C) (a : A) := apply G (apply F a)
def testIndirComp (A B C : U) (F : A ⟶ B) (G : B ⟶ C) : A ⟶ C := Λ a => comp F G a
#print testIndirComp

def testCompComp (A B C D : U) (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) : A ⟶ D := Λ a => H (G (F a))
#print testCompComp
def testCompCompEff (A B C D : U) (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) (a : A) :
  (testCompComp A B C D F G H) a ≃ H (G (F a)) :=
HasFunctors.byDef

def testCompCompFunct (A B C D : U) (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) : A ⟶{λ a => H (G (F a))} D :=
by functoriality
#print testCompCompFunct

def testTestCompComp (A B C D : U) : (A ⟶ B) ⟶ (B ⟶ C) ⟶ (C ⟶ D) ⟶ (A ⟶ D) := Λ F G H => testCompComp A B C D F G H
#print testTestCompComp
def testTestCompCompEff (A B C D : U) (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) :
  (testTestCompComp A B C D) F G H ≃ testCompComp A B C D F G H :=
HasCongrFun.byDef₃

def testTestCompCompFunct (A B C D : U) (F : A ⟶ B) (H : C ⟶ D) : (B ⟶ C) ⟶{λ G => testCompComp A B C D F G H} (A ⟶ D) :=
by functoriality
#print testTestCompCompFunct

def testComp₂ (A B C D : U) (F : A ⟶ B ⟶ C) (G : C ⟶ D) : A ⟶ B ⟶ D := Λ a b => G (F a b)
#print testComp₂
def testComp₂Eff (A B C D : U) (F : A ⟶ B ⟶ C) (G : C ⟶ D) (a : A) (b : B) :
  testComp₂ A B C D F G a b ≃ G (F a b) :=
HasCongrFun.byDef₂

def testTestComp₂ (A B C D : U) : (A ⟶ B ⟶ C) ⟶ (C ⟶ D) ⟶ (A ⟶ B ⟶ D) := Λ F G => testComp₂ A B C D F G
#print testTestComp₂
def testTestComp₂Eff (A B C D : U) (F : A ⟶ B ⟶ C) (G : C ⟶ D) :
  (testTestComp₂ A B C D) F G ≃ testComp₂ A B C D F G :=
HasCongrFun.byDef₂

def testRevTestComp₂ (A B C D : U) : (C ⟶ D) ⟶ (A ⟶ B ⟶ C) ⟶ (A ⟶ B ⟶ D) := Λ G F => testComp₂ A B C D F G
#print testRevTestComp₂
def testRevTestComp₂Eff (A B C D : U) (G : C ⟶ D) (F : A ⟶ B ⟶ C) :
  (testRevTestComp₂ A B C D) G F ≃ testComp₂ A B C D F G :=
HasCongrFun.byDef₂

def testRevTestComp₂Funct (A B C D : U) : (C ⟶ D) ⟶{λ G => Λ F => testComp₂ A B C D F G} ((A ⟶ B ⟶ C) ⟶ (A ⟶ B ⟶ D)) :=
by functoriality
#print testRevTestComp₂Funct

def testRevAppApp (A B C : U) : A ⟶ (A ⟶ B) ⟶ (B ⟶ C) ⟶ C := Λ a F G => G (F a)
#print testRevAppApp
def testRevAppAppEff (A B C : U) (a : A) (F : A ⟶ B) (G : B ⟶ C) :
  (testRevAppApp A B C) a F G ≃ G (F a) :=
HasCongrFun.byDef₃

def testDup (A B : U) (F : A ⟶ A ⟶ B) : A ⟶ B := Λ a => F a a
#print testDup

def testTestDup (A B : U) : (A ⟶ A ⟶ B) ⟶ (A ⟶ B) := Λ F => testDup A B F
#print testTestDup

def testDupArg (A B C : U) (F : A ⟶ C ⟶ A ⟶ B) (c : C) : A ⟶ B := Λ a => F a c a
#print testDupArg

def testTestDupArg (A B C : U) : (A ⟶ C ⟶ A ⟶ B) ⟶ C ⟶ (A ⟶ B) := Λ F c => testDupArg A B C F c
#print testTestDupArg

def testSubst (A B C : U) (F : A ⟶ B) (G : A ⟶ B ⟶ C) : A ⟶ C := Λ a => G a (F a)
#print testSubst

def testTestSubst (A B C : U) : (A ⟶ B) ⟶ (A ⟶ B ⟶ C) ⟶ (A ⟶ C) := Λ F G => testSubst A B C F G
#print testTestSubst

def testRevTestSubst (A B C : U) : (A ⟶ B ⟶ C) ⟶ (A ⟶ B) ⟶ (A ⟶ C) := Λ G F => testSubst A B C F G
#print testRevTestSubst

def testSubst₂ (A B C D : U) (F : A ⟶ B ⟶ C) (G : A ⟶ B ⟶ C ⟶ D) : A ⟶ B ⟶ D := Λ a b => G a b (F a b)
#print testSubst₂

def testDup₃ (A B : U) : (A ⟶ A ⟶ A ⟶ B) ⟶ (A ⟶ B) := Λ F a => F a a a
#print testDup₃

variable [HasInternalProducts U]

def testProdSwap [HasLinearFunOp U] (A B : U) : A ⊓ B ⟶ B ⊓ A :=
HasInternalProducts.elimFun (Λ a b => HasProducts.intro b a)
#print testProdSwap

def testProdDistr [HasAffineFunOp U] (A B C : U) : (A ⟶ B ⊓ C) ⟶ (A ⟶ B) ⊓ (A ⟶ C) :=
Λ F => HasProducts.intro (Λ a => HasProducts.fst (F a)) (Λ a => HasProducts.snd (F a))
#print testProdDistr
