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

import mathlib4_experiments.CoreExt
import mathlib4_experiments.Data.Equiv.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w



namespace unit

  open MetaRelation

  -- `unit` has instance equivalences in `unit`.

  def unitEq (α : Sort u) : EquivalenceRelation α unit :=
  { R := unitRelation α Inst,
    h := unitEquivalence α inst }

  def unitInstanceEquivalences (U : Universe) : HasInstanceEquivalences U unit :=
  ⟨λ A => unit.unitEq ⌈A⌉⟩

  instance hasInstanceEquivalences : HasInstanceEquivalences unit unit := unitInstanceEquivalences unit

  instance hasTrivialIdentity : HasTrivialIdentity unit := ⟨λ _ _ => inst⟩

  -- Functors into `unit` are trivial.

  instance (priority := high) hasInFunctors (U : Universe.{u}) : HasFunctors U unit unit :=
  { Fun   := λ _ _ => Inst,
    apply := λ _ _ => inst }

  instance hasTrivialInFunctoriality (U : Universe.{u}) : HasTrivialFunctoriality U unit :=
  ⟨λ _ => HasTrivialIdentity.defFun inst⟩

  -- Functors from `unit` to `V` are the same as instances of `V`.

  instance hasOutFunctors (V : Universe.{v}) : HasFunctors unit V V :=
  { Fun   := λ _ B => B,
    apply := λ b _ => b }

  instance hasTrivialOutFunctoriality (V : Universe.{v}) [HasIdentity V] :
    HasTrivialFunctoriality unit V :=
  ⟨λ f => { F   := f inst,
            eff := λ _ => HasRefl.refl (f inst) }⟩

  -- Internal functors are given by `hasInFunctors` due to its priority.

  instance hasInternalFunctors : HasInternalFunctors unit := ⟨⟩
  instance hasStandardFunctors : HasStandardFunctors unit := ⟨⟩

  -- `Inst` can serve as both top and bottom.

  instance hasTop : HasTop unit :=
  { T := Inst,
    t := inst }

  instance hasBot : HasBot unit :=
  { B    := Inst,
    elim := λ _ _ => inst }

  instance hasClassicalLogic : HasClassicalLogic unit :=
  { byContradictionFun := λ _ => inst }

  -- A product with `unit` is equivalent to the type itself.

  instance hasRightProducts (U : Universe.{u}) : HasProducts U unit U :=
  { Prod  := λ A _ => A,
    intro := λ a _ => a,
    fst   := id,
    snd   := λ _ => inst }

  instance hasLeftProducts (V : Universe.{v}) : HasProducts unit V V :=
  { Prod  := λ _ B => B,
    intro := λ _ b => b,
    fst   := λ _ => inst,
    snd   := id }

  -- Type equivalence is trivial.

  instance hasEquivalences : HasEquivalences unit unit unit :=
  { Equiv    := λ _ _ => Inst,
    toFun    := λ _   => inst,
    invFun   := λ _   => inst,
    leftInv  := λ _ _ => inst,
    rightInv := λ _ _ => inst }

  instance hasTrivialEquivalenceCondition : HasTrivialEquivalenceCondition unit :=
  ⟨λ _ => HasTrivialIdentity.defEquiv inst⟩

  -- Dependent functors to and from `unit` are not really dependent.

  instance hasTrivialTypeIdentity : HasTrivialIdentity {unit} := ⟨λ _ _ => inst⟩

  instance hasInProperties (U : Universe.{u}) : HasFunctors U {unit} unit :=
  { Fun   := λ _ _ => Inst,
    apply := λ _ _ => Inst }

  instance hasTrivialInPropertyCondition (U : Universe.{u}) : HasTrivialFunctoriality U {unit} :=
  ⟨λ _ => HasTrivialIdentity.defFun inst⟩

  instance (priority := high) hasDependentInFunctors (U : Universe.{u}) : HasDependentFunctors U unit unit :=
  { Pi    := λ _   => Inst,
    apply := λ _ _ => inst }

  instance hasTrivialDependentInFunctoriality (U : Universe.{u}) : HasTrivialDependentFunctoriality U unit :=
  ⟨λ _ => HasTrivialIdentity.defPi inst⟩

  instance hasDependentOutFunctors (V : Universe.{v}) : HasDependentFunctors unit V V :=
  { Pi    := λ φ   => φ inst,
    apply := λ b _ => b }

  instance hasTrivialDependentOutFunctoriality (V : Universe.{v}) [HasIdentity V] :
    HasTrivialDependentFunctoriality unit V :=
  ⟨λ f => { F   := f inst,
            eff := λ _ => HasRefl.refl (f inst) }⟩

--  def rightSigmaEquiv {U : Universe.{u}} {A : U} (φ : A ⟿ unit) : ⌈A⌉ ≃ (Σ' φ) :=
--  { toFun    := λ a => ⟨a, inst⟩,
--    invFun   := λ P => P.fst,
--    leftInv  := λ _ => rfl,
--    rightInv := λ ⟨_, _⟩ => rfl }
--
--  instance hasInternalDependentRightProductType {U : Universe.{u}} {A : U} (φ : A ⟿ unit) :
--    HasEmbeddedType U (Σ' φ) :=
--  ⟨rightSigmaEquiv φ⟩
--
--  instance hasDependentRightProducts (U : Universe.{u}) : HasDependentProducts U unit U := ⟨⟩
--
--  def leftSigmaEquiv {A : unit} {U : Universe.{u}} (φ : A ⟿ U) : ⌈φ inst⌉ ≃ (Σ' φ) :=
--  { toFun    := λ b => ⟨inst, b⟩,
--    invFun   := λ P => P.snd,
--    leftInv  := λ _ => rfl,
--    rightInv := λ ⟨_, _⟩ => rfl }
--
--  instance hasInternalDependentLeftProductType {A : unit} {U : Universe.{u}} (φ : A ⟿ U) :
--    HasEmbeddedType U (Σ' φ) :=
--  ⟨leftSigmaEquiv φ⟩
--
--  instance hasDependentLeftProducts (U : Universe.{u}) : HasDependentProducts unit U U := ⟨⟩

end unit



namespace boolean

  open MetaRelation

  -- `boolean` has instance equivalences in `unit`.

  instance hasInstanceEquivalences : HasInstanceEquivalences boolean unit := unit.unitInstanceEquivalences boolean

  instance hasTrivialIdentity : HasTrivialIdentity boolean := ⟨λ _ _ => unit.inst⟩

  -- Internal functors in `boolean` are defined as implication.

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
  instance hasStandardFunctors : HasStandardFunctors boolean := ⟨⟩

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

  instance hasEquivalences : HasEquivalences boolean boolean boolean :=
  { Equiv    := λ a b : Bool => a == b,
    toFun    := λ {a b} h => match a, b with
                             | true,  false => h
                             | true,  true  => h
                             | false, _     => inst,
    invFun   := λ {a b} h => match b, a with
                             | true,  false => h
                             | true,  true  => h
                             | false, _     => inst,
    leftInv  := λ _ _ => inst,
    rightInv := λ _ _ => inst }

  instance hasTrivialEquivalenceCondition : HasTrivialEquivalenceCondition boolean :=
  ⟨λ {a b} e => have h : a ⟷ b := match a, b with
                                  | false, false => inst
                                  | false, true  => False.elim e.invFun
                                  | true,  false => False.elim e.toFun
                                  | true,  true  => inst;
                HasTrivialIdentity.defEquiv h⟩

end boolean



namespace sort

  open MetaRelation HasFunctors HasDependentFunctors

  -- Functors from `sort` to any universe are just functions: Instance equivalence
  -- in `sort` is given by equality, so functors do not need to respect anything else
  -- besides equality.

  instance hasFunctors (V : Universe.{v}) : HasFunctors sort.{u} V sort.{imax u v} :=
  { Fun   := λ α B => α → B,
    apply := id }

  def defFun {A : sort.{u}} {V : Universe.{v}} [HasIdentity V] {B : V} (f : A → B) :
    DefFun A B f :=
  { F   := f,
    eff := λ a => HasRefl.refl (f a) }

  instance hasTrivialFunctoriality (V : Universe.{v}) [HasIdentity V] :
    HasTrivialFunctoriality sort.{u} V :=
  ⟨defFun⟩

  instance hasInstanceEquivalences : HasInstanceEquivalences sort.{u} prop :=
  ⟨λ α => @Eq.isEquivalence ⌈α⌉⟩

  instance hasCongrArg : HasCongrArg sort.{u} sort.{v} :=
  ⟨λ f => congrArg f⟩

  instance hasInternalFunctors : HasInternalFunctors sort.{u} := ⟨⟩

  instance hasTrivialExtensionality : HasTrivialExtensionality sort.{u} sort.{v} :=
  ⟨funext⟩

  instance hasStandardFunctors : HasStandardFunctors sort.{u} := ⟨⟩

  -- The same is true for dependent functors.

  instance hasDependentFunctors (V : Universe.{v}) :
    HasDependentFunctors sort.{u} V sort.{imax u v} :=
  { Pi    := HasFunctors.Pi,
    apply := id }

  def defPi {A : sort.{u}} {V : Universe.{v}} [HasIdentity V] {φ : ⌈A ⟶ ⌊V⌋⌉}
            (f : HasFunctors.Pi φ) :
    DefPi φ f :=
  { F   := f,
    eff := λ a => HasRefl.refl (f a) }

  instance hasTrivialDependentFunctoriality (V : Universe.{v}) [HasIdentity V] :
    HasTrivialDependentFunctoriality sort.{u} V :=
  ⟨defPi⟩

end sort

theorem Exists.Prop.fst {p : Prop} {q : p → Prop} : (∃ h, q h) → p
| ⟨h, _⟩ => h

theorem Exists.Prop.snd {p : Prop} {q : p → Prop} : (e : ∃ h, q h) → q (Exists.Prop.fst e)
| ⟨_, h⟩ => h

namespace prop

  instance hasTrivialIdentity : HasTrivialIdentity prop := ⟨proofIrrel⟩

  -- `Top` is `True`, `Bot` is `False`.

  instance hasTop : HasTop prop :=
  { T := True,
    t := trivial }

  instance hasBot : HasBot prop :=
  { B    := False,
    elim := False.elim }

  -- `prop` has classical logic if we want.

  instance hasClassicalLogic : HasClassicalLogic prop :=
  { byContradictionFun := @Classical.byContradiction }

  -- Products are given by `And`.

  instance hasProducts : HasProducts prop prop prop :=
  { Prod  := And,
    intro := And.intro,
    fst   := And.left,
    snd   := And.right }

  -- Equivalences are given by `Iff`.

  instance hasEquivalences : HasEquivalences prop prop prop :=
  { Equiv    := Iff,
    toFun    := Iff.mp,
    invFun   := Iff.mpr,
    leftInv  := λ _ _ => proofIrrel _ _,
    rightInv := λ _ _ => proofIrrel _ _ }

  instance hasTrivialEquivalenceCondition : HasTrivialEquivalenceCondition prop :=
  ⟨λ e => HasTrivialIdentity.defEquiv (U := prop) (Iff.intro e.toFun e.invFun)⟩

--  def sigmaEquiv {p : prop} (φ : p ⟿ prop) : (∃ a, φ a) ≃ (Σ' φ) :=
--  { toFun    := λ h => ⟨Exists.prop.fst h, Exists.prop.snd h⟩,
--    invFun   := λ P => ⟨P.fst, P.snd⟩,
--    leftInv  := λ _ => proofIrrel _ _,
--    rightInv := λ ⟨_, _⟩ => rfl }
--
--  instance hasInternalDependentProductType {p : prop} (φ : p ⟿ prop) :
--    HasEmbeddedType prop (Σ' φ) :=
--  ⟨sigmaEquiv φ⟩
--
--  instance hasDependentProducts : HasDependentProducts prop prop prop := ⟨⟩

end prop

namespace type

  instance hasTop : HasTop type.{u} :=
  { T := PUnit.{u + 1},
    t := PUnit.unit }
  
  instance hasTopEq : HasTop.HasTopEq type.{u} :=
  ⟨λ t' => by induction t'; rfl⟩

  -- TODO: Remove `noncomputable` if problem with `PEmpty.elim` can be solved.
  noncomputable instance hasBot : HasBot type.{u} :=
  { B    := PEmpty.{u + 1},
    elim := PEmpty.elim }

  noncomputable def byContradiction (α : type.{u}) (f : HasInternalBot.Not (HasInternalBot.Not α)) : α :=
  Classical.choice (Classical.byContradiction (λ h => PEmpty.elim (f (λ a => False.elim (h ⟨a⟩)))))

  noncomputable instance hasClassicalLogic : HasClassicalLogic type.{u} :=
  { byContradictionFun := byContradiction }

  instance hasProducts : HasProducts type.{u} type.{v} type.{max u v} :=
  { Prod  := PProd,
    intro := PProd.mk,
    fst   := PProd.fst,
    snd   := PProd.snd }

  instance hasProductEq : HasProducts.HasProductEq type.{u} type.{v} :=
  { introEq := λ p   => by induction p; rfl,
    fstEq   := λ a b => rfl,
    sndEq   := λ a b => rfl }

  instance hasEquivalences : HasEquivalences type.{u} type.{v} type.{max u v} :=
  { Equiv    := Equiv,
    toFun    := Equiv.toFun,
    invFun   := Equiv.invFun,
    leftInv  := Equiv.leftInv,
    rightInv := Equiv.rightInv }

  instance hasTrivialEquivalenceCondition : HasTrivialEquivalenceCondition type.{u} :=
  ⟨λ e => ⟨⟨e.toFun, e.invFun, e.equiv.left.inv, e.equiv.right.inv⟩, rfl, rfl⟩⟩

--  def sigmaEquiv {α : type.{u}} (φ : α ⟿ type.{u}) : (Σ a, φ a) ≃ (Σ' φ) :=
--  { toFun    := λ p => ⟨p.fst, p.snd⟩,
--    invFun   := λ P => ⟨P.fst, P.snd⟩,
--    leftInv  := λ ⟨_, _⟩ => rfl,
--    rightInv := λ ⟨_, _⟩ => rfl }
--
--  instance hasInternalDependentProductType {α : type.{u}} (φ : α ⟿ type.{u}) :
--    HasEmbeddedType type.{u} (Σ' φ) :=
--  ⟨sigmaEquiv φ⟩
--
--  instance hasDependentProducts : HasDependentProducts type.{u} type.{u} type.{u} := ⟨⟩
--
--  def subtypeEquiv {α : type.{u}} (φ : α ⟿ prop) : {a // φ a} ≃ (Σ' φ) :=
--  { toFun    := λ p => ⟨p.val, p.property⟩,
--    invFun   := λ P => ⟨P.fst, P.snd⟩,
--    leftInv  := λ ⟨_, _⟩ => rfl,
--    rightInv := λ ⟨_, _⟩ => rfl }
--
--  instance hasInternalSubtypeType {α : type.{u}} (φ : α ⟿ prop) :
--    HasEmbeddedType type.{u} (Σ' φ) :=
--  ⟨subtypeEquiv φ⟩
--
--  instance hasSubtypes : HasDependentProducts type.{u} prop type.{u} := ⟨⟩

end type
