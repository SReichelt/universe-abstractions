import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors



namespace UniverseAbstractions.Layer1

set_option autoBoundImplicitLocal false



-- In contrast to `HasProducts`, `HasCoproducts` more or less requires full logic: `elimFun₃` takes
-- two functors but only uses one of them.

class HasCoproducts (U : Universe) [HasFunctors U] where
(Coprod                    : U → U → U)
(leftIntroFun  (A B   : U) : A ⟶ Coprod A B)
(rightIntroFun (A B   : U) : B ⟶ Coprod A B)
(elimFun₃      (A B C : U) : (A ⟶ C) ⟶ (B ⟶ C) ⟶ (Coprod A B ⟶ C))

namespace HasCoproducts

  infix:34 " ⊔ " => HasCoproducts.Coprod

  variable {U : Universe} [HasFunctors U] [HasCoproducts U]

  def leftIntro  {A : U} (a : A) (B : U) : A ⊔ B := (leftIntroFun  A B) a
  def rightIntro (A : U) {B : U} (b : B) : A ⊔ B := (rightIntroFun A B) b

  def elimFun {A B C : U} (F : A ⟶ C) (G : B ⟶ C) : A ⊔ B ⟶ C := (elimFun₃ A B C) F G
  def elim {A B C : U} (F : A ⟶ C) (G : B ⟶ C) (S : A ⊔ B) : C := (elimFun F G) S

end HasCoproducts
