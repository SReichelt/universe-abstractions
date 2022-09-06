import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations.AttachedRelations
import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations.NaturalTransformations



namespace UniverseAbstractions.Layer1

set_option autoImplicit false
set_option linter.unusedVariables false

open HasPiType HasLinearLogic HasPreorderRelation HasNaturalTransformations

universe u



-- The status of the Yoneda lemma in these generalized categories is a bit curious.
--
-- First of all, in layer 1 it is of course reduced to just the maps in both directions, without any
-- notion of naturality. But that is completely analogous to other parts of category theory. The
-- naturality of the Yoneda construction is part of layer 2.
--
-- The more interesting issue is that `HasNaturalTransformations ((homFun₂ α).app a) F` is not a
-- sufficient condition to be able to construct the reverse direction from `F a` to
-- `Nat ((homFun₂ α).app a) F`. On its own, it does not provide any mechanism to actually construct
-- a natural transformation, and the conditions required to enable such a construction would need to
-- be highly specific, making the formalization of Yoneda essentially useless.
--
-- But the reason why the Yoneda lemma exists in the first place is that preorder functors into `V`
-- (generalizing the category of sets) are really special, in particular their functoriality
-- condition `(a ⟶ b) ⥤ (F a ⟶ F b)` for `a b : α` is actually a family of bifunctors
-- `(a ⟶ b) ⥤ F a ⥤ F b`. And then hom-functors are even more special. Therefore, it is no surprise
-- that treating these functors as arbitrary preorder functors does not lead anywhere.
--
-- Instead, we employ a really simple solution here, which looks a bit like cheating but actually
-- fits well into some similar cases in layer 2: We _define_ `Nat ((homFun₂ α).app a) F` to be
-- `F a`. Although the Yoneda lemma itself becomes trivial under this definition, its proof is still
-- encoded in this formalization:
-- * In order to define the type of natural transformations in this way, we need to provide an
--   elimination functor from `F a` to `(a ⟶ b) ⥤ F b` for every `b : α`, which is exactly the
--   reverse direction of the Yoneda construction.
-- * The forward direction, in turn, is a genuinely nontrivial functor definition: Although it is
--   technically just a functor from `F a` to itself, it is not the identity functor: If we write
--   its type as `Nat ((homFun₂ α).app a) F ⥤ F a` and implement it as `Λ η => (η a) (idHom a)` as
--   in the proof of the Yoneda lemma, we get `swapFun (swapFun₂ (F.hφ.inst a a)) (idHom a)`.
--   (In layer 2, this is indeed equivalent to `(F.hφ.inst a a) (idHom a)`, which in turn is
--   equivalent to `idFun (F a)` if `F` is a layer 2 preorder functor. But this equivalence is not
--   `refl` aka `idIso` either, of course...)

namespace HasPreorderRelation

  variable {V : Universe} [HasLinearLogic V] {α : Sort u} [HasPreorderRelation V α]

  section

    variable (F : PreorderFunctor α V) (a : α)

    def covariantYonedaInv (x : F a) (b : α) : (a ⟶ b) ⥤ F b := Λ f => (F.hφ f) x
    def covariantYonedaInvFun (b : α) : F a ⥤ (a ⟶ b) ⥤ F b := Λ x => covariantYonedaInv F a x b

    instance hasCovariantYonedaPiType : HasPiType (λ b => (a ⟶ b) ⥤ F b) where
      defPiType := { A    := F a,
                     elim := covariantYonedaInv F a }

    instance hasCovariantYonedaPiAppFun : HasPiAppFun (λ b => (a ⟶ b) ⥤ F b) :=
      ⟨λ b => ⟨covariantYonedaInvFun F a b⟩⟩

    instance hasCovariantYoneda : HasNaturalTransformations ((homFun₂ α).app a) F where
      toHasPiType   := hasCovariantYonedaPiType   F a
      toHasPiAppFun := hasCovariantYonedaPiAppFun F a

    def covariantYonedaFun : Nat ((homFun₂ α).app a) F ⥤ F a := Λ η => (η a) (idHom a)

  end

  section

    variable (F : PreorderFunctor (opposite α) V) (b : α)

    def contravariantYonedaInv (y : F b) (a : α) : (a ⟶ b) ⥤ F a := Λ f => (F.hφ f) y
    def contravariantYonedaInvFun (a : α) : F b ⥤ (a ⟶ b) ⥤ F a :=
      Λ y => contravariantYonedaInv F b y a

    instance hasContravariantYonedaPiType : HasPiType (λ a => (a ⟶ b) ⥤ F a) where
      defPiType := { A    := F b,
                     elim := contravariantYonedaInv F b }

    instance hasContravariantYonedaPiAppFun : HasPiAppFun (λ a => (a ⟶ b) ⥤ F a) :=
      ⟨λ a => ⟨contravariantYonedaInvFun F b a⟩⟩

    instance hasContravariantYoneda : HasNaturalTransformations ((homFun₂ α).app₂ b) F where
      toHasPiType   := hasContravariantYonedaPiType   F b
      toHasPiAppFun := hasContravariantYonedaPiAppFun F b

    def contravariantYonedaFun : Nat ((homFun₂ α).app₂ b) F ⥤ F b := Λ η => (η b) (idHom b)

  end

  -- The Yoneda embedding is trivial when defining natural transformations as above.

  theorem covariant_yoneda_embedding (a b : α) :
      Nat ((homFun₂ α).app b) ((homFun₂ α).app a) = (a ⟶ b) :=
    rfl

  theorem contravariant_yoneda_embedding (a b : α) :
      Nat ((homFun₂ α).app₂ a) ((homFun₂ α).app₂ b) = (a ⟶ b) :=
    rfl

end HasPreorderRelation
