import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Axioms.Singletons
import UniverseAbstractions.Universes.Layer1.Axioms.Products
import UniverseAbstractions.Universes.Layer1.Axioms.Coproducts
import UniverseAbstractions.Universes.Layer1.Axioms.Equivalences
import UniverseAbstractions.Universes.Layer1.Instances.Utils.Trivial



namespace UniverseAbstractions.Layer1

set_option autoImplicit false

universe u

open HasPreorderRelation



-- A universe with exactly two types `true` and `false`. The function that maps a type to its
-- instances is exactly the same as the coercion from `Bool` to `Prop`. `bool` can be regarded as a
-- subuniverse of `prop` that is restricted to all decidable propositions.

def bool : Universe.{0, 1} where
  I := Bool
  h := ⟨λ b => cond b True False⟩

namespace bool

  def T : bool := true
  def F : bool := false

  def inst : T := trivial
  def elim {α : Sort u} (h : F) : α := False.elim h

  instance decidable (b : bool) : Decidable b := match b with
    | true  => isTrue  inst
    | false => isFalse elim

  instance hasFunType (b c : bool) : HasTypeWithIntro bool (b → c) where
    A      := cond b c true
    hElim  := ⟨λ f => match b with
                      | true  => λ _ => f
                      | false => elim⟩
    hIntro := ⟨λ f => match b with
                      | true  => f inst
                      | false => inst⟩

  instance hasFunctors (b : bool) : HasFunctorsWithIntro b bool := ⟨⟩

  instance hasUnivFunctors : HasUnivFunctorsWithIntro bool bool := ⟨⟩

  instance hasFullLogic : HasFullLogic bool := inferInstance

  instance hasTopType : HasTypeWithIntro bool PUnit.{0} where
    A      := T
    hElim  := ⟨λ _ => PUnit.unit⟩
    hIntro := ⟨λ _ => inst⟩

  instance hasTop : HasTop bool := inferInstance

  instance hasBotType : HasType bool PEmpty.{0} where
    A     := F
    hElim := ⟨elim⟩

  instance hasBot : HasBot bool := inferInstance

  instance hasClassicalLogic : HasClassicalLogic bool :=
    ⟨λ b => match b with
            | true  => inst
            | false => inst⟩

  instance hasProductType (b c : bool) : HasTypeWithIntro bool (PProd b c) where
    A      := b && c
    hElim  := ⟨λ h => match b, c with
                      | true,  true  => ⟨inst, inst⟩
                      | true,  false => elim h
                      | false, _     => elim h⟩
    hIntro := ⟨λ ⟨l, r⟩ => match b, c with
                           | true,  true  => inst
                           | true,  false => elim r
                           | false, _     => elim l⟩

  instance hasProducts : HasProducts bool := inferInstance

  instance hasCoproductType (b c : bool) : HasTypeWithIntro bool (PSum b c) where
    A      := b || c
    hElim  := ⟨λ h => match b, c with
                      | true,  _     => PSum.inl inst
                      | false, true  => PSum.inr inst
                      | false, false => elim h⟩
    hIntro := ⟨λ s => match b, c, s with
                      | false, _,     PSum.inl l => elim l
                      | _,     false, PSum.inr r => elim r
                      | false, true,  _          => inst
                      | true,  _,     _          => inst⟩

  instance hasCoproducts : HasCoproducts bool := inferInstance

  instance hasIsomorphisms (α : Sort u) [HasPreorderRelation bool α] : HasIsomorphismsWithIntro α :=
    HasProducts.hasIsomorphismsWithIntro α

  instance hasEquivalences : HasEquivalences bool := inferInstance

  instance hasFullPositiveEquivalences : HasFullPositiveEquivalences bool := inferInstance
  instance hasFullEquivalences : HasFullEquivalences bool := inferInstance
  instance hasPropEquivalences : HasPropEquivalences bool := inferInstance
  instance hasClassicalEquivalences : HasClassicalEquivalences bool := inferInstance

  instance isPositiveUniverse : IsPositiveUniverse bool := ⟨⟩
  instance isNegativeUniverse : IsNegativeUniverse bool := ⟨⟩
  instance isStandardUniverse : IsStandardUniverse bool := ⟨⟩

end bool
