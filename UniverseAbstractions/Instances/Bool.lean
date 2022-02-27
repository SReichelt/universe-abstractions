/-
A universe where types are instances of `Bool`.
This is equivalent to the subuniverse of `prop` that only contains decidable propositions.
The operations on types are the `Bool` equivalents of the corresponding operations on
propositions, and the universe axioms force us to prove that these operations really match.
-/



import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.FunctorExtensionality
import UniverseAbstractions.Axioms.Universe.Singletons
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences
import UniverseAbstractions.Axioms.Universe.DependentTypes.Properties
import UniverseAbstractions.Axioms.Universe.DependentTypes.DependentFunctors
import UniverseAbstractions.Axioms.Universe.DependentTypes.DependentProducts
import UniverseAbstractions.Instances.Utils.Trivial
import UniverseAbstractions.Instances.Unit



set_option autoBoundImplicitLocal false
--set_option pp.universes true



def boolean : Universe.{0, 1} := ⟨Bool⟩

namespace boolean

  open MetaRelation HasEquivOp HasEquivOpFun

  def True  : boolean := true
  def False : boolean := false

  def inst : True := trivial

  -- `boolean` has instance equivalences in `unit`.

  instance hasInstanceEquivalences : HasInstanceEquivalences boolean unit := unit.unitInstanceEquivalences boolean

  instance hasTrivialIdentity : HasTrivialIdentity boolean := ⟨λ _ _ => unit.inst⟩

  -- Internal functors in `boolean` are defined as implication.
  -- TODO: Generalize this to functors into an arbitrary universe.
  --       Then dependent types will start to make sense for `boolean` as well.

  instance hasFunctors : HasFunctors boolean boolean boolean :=
  { Fun   := λ a b => cond a b true,
    apply := λ {a b} hF ha => match a with
                              | true  => hF
                              | false => False.elim ha }

  instance hasTrivialFunctoriality : HasTrivialFunctoriality boolean boolean :=
  ⟨λ {a b} p => have h : a ⟶ b := match a with
                                  | true  => p inst
                                  | false => inst;
                HasTrivialIdentity.defFun h⟩

  instance hasInternalFunctors : HasInternalFunctors boolean := ⟨⟩

  -- `Top` is `true` and `Bot` is `false`.

  instance hasTop : HasTop boolean :=
  { T := True,
    t := inst }

  instance hasBot : HasBot boolean :=
  { B    := False,
    elim := False.elim }

  -- `boolean` has classical logic without assuming choice.

  instance hasClassicalLogic : HasClassicalLogic boolean :=
  { byContradictionFun := λ b => match b with
                                 | true  => inst
                                 | false => inst }

  -- Products are given by `and`.

  instance hasProducts : HasProducts boolean boolean boolean :=
  { Prod  := and,
    intro := λ {a b} ha hb => match a with
                              | false => ha
                              | true  => hb,
    fst   := λ {a b} h => match a with
                          | false => h
                          | true  => inst,
    snd   := λ {a b} h => match a with
                          | false => False.elim h
                          | true  => h }

  -- Equivalence is given by boolean equality.

  def Equiv (a b : Bool) : boolean := a == b

  def Equiv.toEq {a b : boolean} (h : Equiv a b) : a = b := match a, b with
  | true,  false => False.elim h
  | true,  true  => rfl
  | false, false => rfl
  | false, true  => False.elim h

  def Equiv.symm {a b : boolean} (h : Equiv a b) : Equiv b a := toEq h ▸ h

  def Equiv.toFun {a b : boolean} (h : Equiv a b) : a ⟶ b := match a, b with
  | true,  false => h
  | true,  true  => inst
  | false, _     => inst

  def Equiv.invFun {a b : boolean} (h : Equiv a b) : b ⟶ a := toFun (symm h)

  instance hasEquivalences : HasEquivalences boolean boolean boolean :=
  { Equiv := Equiv,
    desc  := λ h => HasTrivialIdentity.equivDesc (Equiv.toFun h) (Equiv.invFun h) }

  def Equiv.fromDesc {a b : boolean} (e : a ⮂ b) : a ⟷ b := match a, b with
  | false, false => inst
  | false, true  => False.elim e.invFun
  | true,  false => False.elim e.toFun
  | true,  true  => inst

  instance hasTrivialEquivalenceCondition : HasTrivialEquivalenceCondition boolean :=
  ⟨λ e => HasTrivialIdentity.defEquiv (Equiv.fromDesc e)⟩

end boolean
