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

open HasPreorderRelation HasTrivialDefInst HasTrivialDefPi



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

  def defFunType (b c : bool) : DefType bool (b → c) where
    A      := cond b c true
    elim f := match b with
              | true  => λ _ => f
              | false => elim

  instance hasFunctors (b c : bool) : HasFunctors b c where
    defPiType := defFunType b c

  instance hasTrivialDefFun (b c : bool) : HasTrivialDefFun b c where
    mkDefInst f := ⟨match b with
                    | true  => f inst
                    | false => inst⟩

  instance hasUnivFunctors : HasUnivFunctors bool bool := ⟨⟩

  instance hasTrivialFunctoriality : HasTrivialFunctoriality bool bool := ⟨⟩

  instance hasFullLogic : HasFullLogic bool := inferInstance

  instance hasTop : HasTop bool where
    defTopType   := ⟨⟨true, λ _ => PUnit.unit⟩, λ _ => ⟨inst⟩⟩
    defElimFun _ := defFun

  instance hasBot : HasBot bool where
    defBotType   := ⟨false, elim⟩
    defElimFun _ := defFun

  instance hasClassicalLogic : HasClassicalLogic bool :=
    ⟨λ b => match b with
            | true  => inst
            | false => inst⟩

  def defProdType (b c : bool) : DefTypeWithIntro bool (PProd b c) where
    A         := b && c
    elim    h := match b, c with
                 | true,  true  => ⟨inst, inst⟩
                 | true,  false => elim h
                 | false, _     => elim h
    defInst p := ⟨match b, c with
                  | true,  true  => inst
                  | true,  false => elim p.snd
                  | false, _     => elim p.fst⟩

  instance hasProducts (b c : bool) : HasProducts b c where
    defProdType    := defProdType b c
    defIntroFun₂   := defFun₂
    defElimFun₂  _ := defFun₂

  instance hasInnerProducts : HasInnerProducts bool := ⟨⟩

  def defCoprodType (b c : bool) : DefTypeWithIntro bool (PSum b c) where
    A         := b || c
    elim    h := match b, c with
                 | true,  _     => PSum.inl inst
                 | false, true  => PSum.inr inst
                 | false, false => elim h
    defInst s := ⟨match b, c, s with
                  | false, _,     PSum.inl l => elim l
                  | _,     false, PSum.inr r => elim r
                  | false, true,  _          => inst
                  | true,  _,     _          => inst⟩

  instance hasCoproducts (b c : bool) : HasCoproducts b c where
    defCoprodType      := defCoprodType b c
    defLeftIntroFun    := defFun
    defRightIntroFun   := defFun
    defElimFun₃      _ := defFun₃

  instance hasInnerCoproducts : HasInnerCoproducts bool := ⟨⟩

  instance hasIsomorphismsBase (α : Sort u) [HasPreorderRelation bool α] : HasIsomorphismsBase α :=
    HasInnerProducts.hasIsomorphismsBase α

  instance hasTrivialIsomorphismCondition (α : Sort u) [HasPreorderRelation bool α] :
      HasTrivialIsomorphismCondition α := ⟨⟩

  instance hasIsomorphisms (α : Sort u) [HasPreorderRelation bool α] : HasIsomorphisms α :=
    inferInstance

  instance hasEquivalences : HasEquivalences bool := inferInstance

  instance hasFullPositiveEquivalences : HasFullPositiveEquivalences bool := inferInstance
  instance hasFullEquivalences : HasFullEquivalences bool := inferInstance
  instance hasPropEquivalences : HasPropEquivalences bool := inferInstance
  instance hasClassicalEquivalences : HasClassicalEquivalences bool := inferInstance

  instance isPositiveUniverse : IsPositiveUniverse bool := ⟨⟩
  instance isNegativeUniverse : IsNegativeUniverse bool := ⟨⟩
  instance isStandardUniverse : IsStandardUniverse bool := ⟨⟩

end bool
