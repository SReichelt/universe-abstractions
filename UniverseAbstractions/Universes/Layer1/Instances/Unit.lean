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

open Universe HasPreorderRelation HasTrivialDefInst HasTrivialDefPi



def unit : Universe.{0, 0} where
  I := True
  h := ⟨λ _ => True⟩

namespace unit

  def Inst : unit := trivial
  def inst : Inst := trivial

  def defType {α : Sort u} (a : α) : DefType unit α where
    A      := Inst
    elim _ := a

  instance hasTrivialDefInst {α : Sort u} (a : α) : HasTrivialDefInst (defType a) where
    mkDefInst := λ _ => ⟨inst⟩

  def defTypeWithIntro {α : Sort u} (a : α) : DefTypeWithIntro unit α where
    toDefType := defType a
    defInst _ := defInst

  instance hasPiType {α : Sort u} (P : α → unit) : HasPiType P where
    defPiType := defType (λ _ => inst)

  instance hasTrivialDefPi {α : Sort u} (P : α → unit) : HasTrivialDefPi P where
    toHasTrivialDefInst := hasTrivialDefInst (λ _ => inst)

  instance hasFunctors (p : Prop) (Y : unit) : HasFunctors p Y := ⟨⟩

  instance hasTrivialDefFun (p : Prop) (Y : unit) : HasTrivialDefFun p Y := ⟨⟩

  instance hasUnivFunctors : HasUnivFunctors unit unit := ⟨⟩

  instance hasTrivialFunctoriality : HasTrivialFunctoriality unit unit := ⟨⟩

  instance hasExternalFullLogic (p : Prop) : HasExternalFullLogic p unit := inferInstance

  instance hasFullLogic : HasFullLogic unit := inferInstance

  instance hasTop : HasTop unit where
    defTopType   := defTypeWithIntro PUnit.unit
    defElimFun _ := defFun

  instance hasProducts (A B : unit) : HasProducts A B where
    defProdType    := defTypeWithIntro ⟨inst, inst⟩
    defIntroFun₂   := defFun₂
    defElimFun₂  _ := defFun₂

  instance hasInnerProducts : HasInnerProducts unit := ⟨⟩

  instance hasCoproducts (A B : unit) : HasCoproducts A B where
    defCoprodType      := defTypeWithIntro (PSum.inl inst)
    defLeftIntroFun    := defFun
    defRightIntroFun   := defFun
    defElimFun₃      _ := defFun₃

  instance hasInnerCoproducts : HasInnerCoproducts unit := ⟨⟩

  instance hasIsomorphismsBase (α : Sort u) [HasPreorderRelation unit α] : HasIsomorphismsBase α :=
    HasInnerProducts.hasIsomorphismsBase α

  instance hasTrivialIsomorphismCondition (α : Sort u) [HasPreorderRelation unit α] :
      HasTrivialIsomorphismCondition α := ⟨⟩

  instance hasIsomorphisms (α : Sort u) [HasPreorderRelation unit α] : HasIsomorphisms α :=
    inferInstance

  instance hasEquivalences : HasEquivalences unit := inferInstance

  instance hasFullPositiveEquivalences : HasFullPositiveEquivalences unit := inferInstance
  instance hasPropEquivalences : HasPropEquivalences unit := inferInstance

  instance isPositiveUniverse : IsPositiveUniverse unit := ⟨⟩

end unit
