import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedProductFunctors

import UniverseAbstractions.Universes.Layer2.Axioms.Functors
import UniverseAbstractions.Universes.Layer2.Axioms.FunctorialImplications



namespace UniverseAbstractions.Layer2

set_option autoImplicit false

open Universe



-- TODO define real properties
structure DefSigma {U : Universe} [HasFunctors U] {A : U} (φ : A → U.V) where
(S : U)
(intro (a : A) (p : φ a) : S)
(valElimFun : S ⟶ A)
(propElim (P : S) : φ (valElimFun P))
(valEq (a : A) (p : φ a) : valElimFun (intro a p) ≃ a)

namespace DefSigma

  variable {U : Universe} [HasFunctors U] [HasLinearLogic U]

  def defProdSigma {A : U} {φ ψ : A → U.V} (s : DefSigma φ) (t : DefSigma (λ P => ψ (s.valElimFun P))) :
    DefSigma (λ a => φ a ⊓ ψ a) :=
  { S          := t.S,
    intro      := λ a p => t.intro (s.intro a (Layer1.HasProducts.fst p)) _,
    valElimFun := s.valElimFun ⊙ t.valElimFun,
    propElim   := λ P => Layer1.HasProducts.intro _ _,
    valEq      := λ a p => _ }

end DefSigma



class HasPreimageSubtypes (U : Universe) [HasFunctors U] where
(defPreimageSigma {A B : U} (F : A ⟶ B) (b : B) : DefSigma (λ a => F a ≃ b))

-- TODO `DefPreimage`, axioms



class HasImplicationSubtypes (U : Universe) [HasFunctors U] [hFunImp : HasFunctorialImplication U]
                             where
(defImpSigma {A B C : U} (F : A ⟶ B) (G : A ⟶ C) :
   DefSigma (λ a => ((hFunImp.defFunImpPi F G).app a).p))

-- TODO uniqueness
-- TODO product as nested sigma
