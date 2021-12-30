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



namespace Test

  open HasFunctors HasCongrFun

  variable {U : Universe.{u, v}} [HasIdentity.{u, iu, v, iuv} U] [HasInternalFunctors U] [HasFullFunOp U]
           (A B C D : U)

  def testRaw (F : A ⟶ B) : A ⟶ B := makeFunctor (apply F)
  #print testRaw
  def testRawEff (F : A ⟶ B) (a : A) : (testRaw A B F) a ≃ F a := byDef

  def testRawFunct (F : A ⟶ B) : A ⟶{apply F} B :=
  by functoriality
  #print testRawFunct

  def testConst (b : B) : A ⟶ B := Λ a => b
  #print testConst

  def testNamedConst (b : B) : A ⟶ B := makeFunctor (Function.const A b)
  #print testNamedConst

  def testConstFunct (b : B) : A ⟶{Function.const A b} B :=
  by functoriality
  #print testConstFunct

  def testTestConst : B ⟶ (A ⟶ B) := Λ b => testConst A B b
  #print testTestConst

  def testId : A ⟶ A := Λ a => a
  #print testId

  def testNamedId : A ⟶ A := makeFunctor id
  #print testNamedId

  def testTestId : B ⟶ (A ⟶ A) := Λ b => testId A
  #print testTestId

  def testFun (F : A ⟶ B) : A ⟶ B := Λ a => F a
  #print testFun

  def testAppFun (F : A ⟶ B) : A ⟶ B := Λ a => (appFun F) a
  #print testAppFun
  def testAppFunEff (F : A ⟶ B) (a : A) :
    (testAppFun A B F) a ≃ (appFun F) a :=
  byDef

  def app {A B : U} (F : A ⟶ B) (a : A) := F a
  def testIndirFun (F : A ⟶ B) : A ⟶ B := Λ a => app F a
  #print testIndirFun

  def testFromToDefFun : (A ⟶ B) ⟶ (A ⟶ B) :=
  Λ F => fromDefFun (toDefFun F)
  #print testFromToDefFun
  def testFromToDefPiEff (F : A ⟶ B) :
    testFromToDefFun A B F ≃ F :=
  byDef

  def testApp (a : A) : (A ⟶ B) ⟶ B := Λ F => F a
  #print testApp

  def testTestApp : A ⟶ (A ⟶ B) ⟶ B := Λ a => testApp A B a
  #print testTestApp

  def testIndirApp (a : A) : (A ⟶ B) ⟶ B := Λ F => app F a
  #print testIndirApp

  def testFixSnd (F : A ⟶ B ⟶ C) (b : B) : A ⟶ C := Λ a => F a b
  #print testFixSnd

  def testSwap : (A ⟶ B ⟶ C) ⟶ (B ⟶ A ⟶ C) := Λ F b => testFixSnd A B C F b
  #print testSwap

  def testRevSwap : B ⟶ (A ⟶ B ⟶ C) ⟶ (A ⟶ C) := Λ b F => testFixSnd A B C F b
  #print testRevSwap

  def testSwap₂₃ : (A ⟶ B ⟶ C ⟶ D) ⟶ (A ⟶ C ⟶ B ⟶ D) := Λ F a c b => F a b c
  #print testSwap₂₃

  def testComp (F : A ⟶ B) (G : B ⟶ C) : A ⟶ C := Λ a => G (F a)
  #print testComp
  def testCompEff (F : A ⟶ B) (G : B ⟶ C) (a : A) :
    (testComp A B C F G) a ≃ G (F a) :=
  byDef

  def testTestComp : (A ⟶ B) ⟶ (B ⟶ C) ⟶ (A ⟶ C) := Λ F G => testComp A B C F G
  #print testTestComp

  def testRevTestComp : (B ⟶ C) ⟶ (A ⟶ B) ⟶ (A ⟶ C) := Λ G F => testComp A B C F G
  #print testRevTestComp

  def comp {A B C : U} (F : A ⟶ B) (G : B ⟶ C) (a : A) := app G (app F a)
  def testIndirComp (F : A ⟶ B) (G : B ⟶ C) : A ⟶ C := Λ a => comp F G a
  #print testIndirComp

  def testCompComp (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) : A ⟶ D := Λ a => H (G (F a))
  #print testCompComp
  def testCompCompEff (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) (a : A) :
    (testCompComp A B C D F G H) a ≃ H (G (F a)) :=
  byDef

  def testCompCompFunct (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) : A ⟶{λ a => H (G (F a))} D :=
  by functoriality
  #print testCompCompFunct

  def testTestCompComp : (A ⟶ B) ⟶ (B ⟶ C) ⟶ (C ⟶ D) ⟶ (A ⟶ D) := Λ F G H => testCompComp A B C D F G H
  #print testTestCompComp
  def testTestCompCompEff (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) :
    (testTestCompComp A B C D) F G H ≃ testCompComp A B C D F G H :=
  byDef₃

  def testTestCompCompFunct (F : A ⟶ B) (H : C ⟶ D) : (B ⟶ C) ⟶{λ G => testCompComp A B C D F G H} (A ⟶ D) :=
  by functoriality
  #print testTestCompCompFunct

  def testComp₂ (F : A ⟶ B ⟶ C) (G : C ⟶ D) : A ⟶ B ⟶ D := Λ a b => G (F a b)
  #print testComp₂
  def testComp₂Eff (F : A ⟶ B ⟶ C) (G : C ⟶ D) (a : A) (b : B) :
    testComp₂ A B C D F G a b ≃ G (F a b) :=
  byDef₂

  def testTestComp₂ : (A ⟶ B ⟶ C) ⟶ (C ⟶ D) ⟶ (A ⟶ B ⟶ D) := Λ F G => testComp₂ A B C D F G
  #print testTestComp₂
  def testTestComp₂Eff (F : A ⟶ B ⟶ C) (G : C ⟶ D) :
    (testTestComp₂ A B C D) F G ≃ testComp₂ A B C D F G :=
  byDef₂

  def testRevTestComp₂ : (C ⟶ D) ⟶ (A ⟶ B ⟶ C) ⟶ (A ⟶ B ⟶ D) := Λ G F => testComp₂ A B C D F G
  #print testRevTestComp₂
  def testRevTestComp₂Eff (G : C ⟶ D) (F : A ⟶ B ⟶ C) :
    (testRevTestComp₂ A B C D) G F ≃ testComp₂ A B C D F G :=
  byDef₂

  def testRevTestComp₂Funct : (C ⟶ D) ⟶{λ G => Λ F => testComp₂ A B C D F G} ((A ⟶ B ⟶ C) ⟶ (A ⟶ B ⟶ D)) :=
  by functoriality
  #print testRevTestComp₂Funct

  def testRevAppApp : A ⟶ (A ⟶ B) ⟶ (B ⟶ C) ⟶ C := Λ a F G => G (F a)
  #print testRevAppApp
  def testRevAppAppEff (a : A) (F : A ⟶ B) (G : B ⟶ C) :
    (testRevAppApp A B C) a F G ≃ G (F a) :=
  byDef₃

  def testDup (F : A ⟶ A ⟶ B) : A ⟶ B := Λ a => F a a
  #print testDup

  def testTestDup : (A ⟶ A ⟶ B) ⟶ (A ⟶ B) := Λ F => testDup A B F
  #print testTestDup

  def testDupArg (F : A ⟶ C ⟶ A ⟶ B) (c : C) : A ⟶ B := Λ a => F a c a
  #print testDupArg

  def testTestDupArg : (A ⟶ C ⟶ A ⟶ B) ⟶ C ⟶ (A ⟶ B) := Λ F c => testDupArg A B C F c
  #print testTestDupArg

  def testSubst (F : A ⟶ B) (G : A ⟶ B ⟶ C) : A ⟶ C := Λ a => G a (F a)
  #print testSubst

  def testTestSubst : (A ⟶ B) ⟶ (A ⟶ B ⟶ C) ⟶ (A ⟶ C) := Λ F G => testSubst A B C F G
  #print testTestSubst

  def testRevTestSubst : (A ⟶ B ⟶ C) ⟶ (A ⟶ B) ⟶ (A ⟶ C) := Λ G F => testSubst A B C F G
  #print testRevTestSubst

  def testSubst₂ (F : A ⟶ B ⟶ C) (G : A ⟶ B ⟶ C ⟶ D) : A ⟶ B ⟶ D := Λ a b => G a b (F a b)
  #print testSubst₂

  def testDup₃ : (A ⟶ A ⟶ A ⟶ B) ⟶ (A ⟶ B) := Λ F a => F a a a
  #print testDup₃

  variable [HasInternalProducts U]

  def testProdSwap : A ⊓ B ⟶ B ⊓ A :=
  HasInternalProducts.elimFun (Λ a b => HasProducts.intro b a)
  #print testProdSwap

  def testProdAssocLR : (A ⊓ B) ⊓ C ⟶ A ⊓ (B ⊓ C) :=
  HasInternalProducts.elimFun (HasInternalProducts.elimFun (Λ a b c => HasProducts.intro a (HasProducts.intro b c)))
  #print testProdAssocLR

  def testProdAssocRL : A ⊓ (B ⊓ C) ⟶ (A ⊓ B) ⊓ C :=
  HasInternalProducts.elimFun (Λ a => HasInternalProducts.elimFun (Λ b c => HasProducts.intro (HasProducts.intro a b) c))
  #print testProdAssocRL

  def testProdDistr : (A ⟶ B ⊓ C) ⟶ (A ⟶ B) ⊓ (A ⟶ C) :=
  Λ F => HasProducts.intro (Λ a => HasProducts.fst (F a)) (Λ a => HasProducts.snd (F a))
  #print testProdDistr

end Test
