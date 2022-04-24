import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors



namespace UniverseAbstractions.Layer1

set_option autoBoundImplicitLocal false

open HasFunctors



class HasProducts (U : Universe) [HasFunctors U] where
(Prod                  : U → U → U)
(introFun₂ (A B   : U) : A ⟶ B ⟶ Prod A B)
(elimFun₂  (A B C : U) : (A ⟶ B ⟶ C) ⟶ (Prod A B ⟶ C))

namespace HasProducts

  infix:35 " ⊓ " => HasProducts.Prod

  variable {U : Universe} [HasFunctors U] [HasProducts U]

  @[reducible] def intro {A B : U} (a : A) (b : B) := (introFun₂ A B) a b

  @[reducible] def elimFun {A B C : U} (F : A ⟶ B ⟶ C) : A ⊓ B ⟶ C := (elimFun₂ A B C) F
  @[reducible] def elim {A B C : U} (F : A ⟶ B ⟶ C) (P : A ⊓ B) : C := (elimFun F) P

end HasProducts
