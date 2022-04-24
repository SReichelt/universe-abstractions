import UniverseAbstractions.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors



namespace UniverseAbstractions.Layer1

set_option autoBoundImplicitLocal false

open HasFunctors



class HasProducts (U : Universe) where
(Prod            : U → U → U)
(intro {A B : U} : A → B → Prod A B)
(fst   {A B : U} : Prod A B → A)
(snd   {A B : U} : Prod A B → B)

namespace HasProducts

  infix:35 " ⊓ " => HasProducts.Prod

end HasProducts


class HasProductFun (U : Universe) [HasFunctors U] extends
  HasProducts U where
(defIntroFun₂ (A B   : U) : A ⟶ B ⟶{intro} Prod A B)
(defElimFun₂  (A B C : U) : (A ⟶ B ⟶ C) ⟶ Prod A B ⟶{λ F P => F (fst P) (snd P)} C)

namespace HasProductFun

  open HasProducts

  variable {U : Universe} [HasFunctors U] [HasProductFun U]

  @[reducible] def introFun₂ (A B : U) : A ⟶ B ⟶ A ⊓ B := (defIntroFun₂ A B).F

  instance intro.isFunApp₂ {A B : U} {a : A} {b : B} : IsFunApp₂ A B (intro a b) :=
  ⟨introFun₂ A B, a, b⟩

  @[reducible] def elimFun {A B C : U} (F : A ⟶ B ⟶ C) : A ⊓ B ⟶ C := ((defElimFun₂ A B C).app F).F
  @[reducible] def elimFun₂ (A B C : U) : (A ⟶ B ⟶ C) ⟶ (A ⊓ B ⟶ C) := (defElimFun₂ A B C).F

  instance elimFun.isFunApp {A B C : U} {F : A ⟶ B ⟶ C} : IsFunApp (A ⟶ B ⟶ C) (elimFun F) :=
  ⟨elimFun₂ A B C, F⟩

end HasProductFun
