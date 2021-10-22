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

universe u v w iu upv



namespace unit

  open MetaRelation HasFunctors HasInternalEquivalences

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

  instance hasOutCongrArg (V : Universe.{v}) [HasIdentity V] : HasCongrArg unit V :=
  ⟨λ {_ _} f {_ _} _ => HasRefl.refl (f inst)⟩

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

  instance hasRightProductEq (U : Universe.{u}) [HasIdentity U] :
    HasProducts.HasProductEq U unit :=
  { introEq := λ a   => HasRefl.refl a,
    fstEq   := λ a _ => HasRefl.refl a,
    sndEq   := λ _ _ => inst }

  instance hasLeftProducts (V : Universe.{v}) : HasProducts unit V V :=
  { Prod  := λ _ B => B,
    intro := λ _ b => b,
    fst   := λ _ => inst,
    snd   := id }

  instance hasLeftProductEq (V : Universe.{v}) [HasIdentity V] :
    HasProducts.HasProductEq unit V :=
  { introEq := λ b   => HasRefl.refl b,
    fstEq   := λ _ _ => inst,
    sndEq   := λ _ b => HasRefl.refl b }

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

  instance hasDependentOutCongrArg (V : Universe.{v}) [HasTypeIdentity V] : HasDependentCongrArg unit V :=
  ⟨λ {_ _} _ {_ _} _ => byDef • byToDef⟩

  -- Same for dependent products.

  instance hasRightDependentProducts (U : Universe.{u}) : HasDependentProducts U unit U :=
  { Sigma := λ {A} _ => A,
    intro := λ a _ => a,
    fst   := id,
    snd   := λ _ => inst }

  instance hasRightDependentProductEq (U : Universe.{u}) [HasIdentity U] :
    HasDependentProducts.HasDependentProductEq U unit :=
  { introEq := λ a   => HasRefl.refl a,
    fstEq   := λ a _ => HasRefl.refl a,
    sndEq   := λ _ _ => inst }

  instance hasLeftDependentProducts (V : Universe.{v}) : HasDependentProducts unit V V :=
  { Sigma := λ φ => φ inst,
    intro := λ _ b => b,
    fst   := λ _ => inst,
    snd   := id }

  instance hasLeftDependentProductEq (V : Universe.{v}) [HasTypeIdentity V] :
    HasDependentProducts.HasDependentProductEq unit V :=
  { introEq := λ b   => HasRefl.refl b,
    fstEq   := λ _ _ => inst,
    sndEq   := λ _ _ => byDef • byToDef }

end unit



namespace boolean

  open MetaRelation

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



-- We can define functors from any universe with propositional identities, i.e. a
-- universe where identities of identities are trivial (such as `sort`). Such functors
-- just need to map equivalent values to equivalent values. In general this captures
-- isomorphism invariance.

structure PropositionalFunctor {U : Universe.{u}} {V : Universe.{v}}
                                [HasIdentity.{u, iu} U] [HasIdentity.{v, 0} V]
                                (A : U) (B : V) :
  Sort (max 1 u v) where
(f                    : A → B)
(congrArg {a₁ a₂ : A} : a₁ ≃ a₂ → f a₁ ≃ f a₂)

namespace PropositionalFunctor

  variable (U : Universe.{u}) (V : Universe.{v}) [HasIdentity.{u, iu} U]
           [HasIdentity.{v, 0} V]

  instance (priority := low) hasPropositionalFunctors : HasFunctors U V sort.{max 1 u v} :=
  { Fun   := PropositionalFunctor,
    apply := PropositionalFunctor.f }

  instance (priority := low) hasPropositionalCongrArg : HasCongrArg U V :=
  ⟨PropositionalFunctor.congrArg⟩

end PropositionalFunctor

structure PropositionalDependentFunctor {U : Universe.{u}} {V : Universe.{v}}
                                        [HasIdentity.{u, iu} U] [HasTypeIdentity.{v, 0} V]
                                        {UpV : Universe.{upv}} [HasFunctors U {V} UpV]
                                        [HasCongrArg U {V}] {A : U} (φ : A ⟶ ⌊V⌋) :
  Sort (max 1 u v) where
(f                                  : HasFunctors.Pi φ)
(congrArg {a₁ a₂ : A} (e : a₁ ≃ a₂) : f a₁ ≃[HasCongrArg.propCongrArg φ e] f a₂)

namespace PropositionalDependentFunctor

  variable (U : Universe.{u}) (V : Universe.{v}) [HasIdentity.{u, iu} U] [HasTypeIdentity.{v, 0} V]
           {UpV : Universe.{upv}} [HasFunctors U {V} UpV] [HasCongrArg U {V}]

  instance (priority := low) hasPropositionalDependentFunctors : HasDependentFunctors U V sort.{max 1 u v} :=
  { Pi    := PropositionalDependentFunctor,
    apply := PropositionalDependentFunctor.f }

  instance (priority := low) hasPropositionalCongrArg : HasDependentCongrArg U V :=
  ⟨PropositionalDependentFunctor.congrArg⟩

end PropositionalDependentFunctor



namespace sort

  open MetaRelation HasFunctors HasInternalEquivalences HasDependentFunctors

  -- Instance equivalences of all `sort.{u}` are given by equality.
  -- For `prop`, we could define instance equivalences to be in `unit` instead of
  -- relying on proof irrelevance, but it's easier to generalize over `prop` and
  -- `type` if we have a single definition.

  instance hasInstanceEquivalences : HasInstanceEquivalences sort.{u} prop :=
  ⟨λ α => @Eq.isEquivalence ⌈α⌉⟩

  -- Functors from `sort` to any universe are just functions: Instance equivalence
  -- in `sort` is given by equality, so functors do not need to respect anything else
  -- besides equality.

  instance hasOutFunctors (V : Universe.{v}) : HasFunctors sort.{u} V sort.{imax u v} :=
  { Fun   := λ α B => α → B,
    apply := id }

  def defOutFun {α : sort.{u}} {V : Universe.{v}} [HasIdentity V] {B : V} (f : α → B) :
    DefFun α B f :=
  { F   := f,
    eff := λ a => HasRefl.refl (f a) }

  instance hasTrivialOutFunctoriality (V : Universe.{v}) [HasIdentity V] :
    HasTrivialFunctoriality sort.{u} V :=
  ⟨defOutFun⟩

  instance hasCongrArg : HasCongrArg sort.{u} sort.{v} :=
  ⟨λ f => congrArg f⟩

  instance (priority := low) hasOutCongrArg (V : Universe.{v}) [HasIdentity V] :
    HasCongrArg sort.{u} V :=
  ⟨λ {_ _} f {_ _} e => e ▸ HasRefl.refl _⟩

  instance hasInternalFunctors : HasInternalFunctors sort.{u} := ⟨⟩

  instance hasTrivialExtensionality : HasTrivialExtensionality sort.{u} sort.{v} :=
  ⟨funext⟩

  instance hasStandardFunctors : HasStandardFunctors sort.{u} := ⟨⟩

  -- There are top and bottom types that work generically for `sort`.

  instance hasTop : HasTop sort.{u} :=
  { T := PUnit,
    t := PUnit.unit }
  
  instance hasTopEq : HasTop.HasTopEq sort.{u} :=
  ⟨λ ⟨⟩ => rfl⟩

  -- TODO: Remove `noncomputable` if problem with `PEmpty.elim` can be solved.
  noncomputable instance hasBot : HasBot sort.{u} :=
  { B    := PEmpty,
    elim := PEmpty.elim }

  noncomputable def byContradiction (α : sort.{u}) (f : HasInternalBot.Not (HasInternalBot.Not α)) : α :=
  Classical.choice (Classical.byContradiction (λ h => PEmpty.elim (f (λ a => False.elim (h ⟨a⟩)))))

  noncomputable instance hasClassicalLogic : HasClassicalLogic sort.{u} :=
  { byContradictionFun := byContradiction }

  -- Same for products, but usually the specialized versions for `prop` and `type`
  -- should be used.

  instance (priority := low) hasProducts : HasProducts sort.{u} sort.{v} sort.{max 1 u v} :=
  { Prod  := PProd,
    intro := PProd.mk,
    fst   := PProd.fst,
    snd   := PProd.snd }

  instance (priority := low) hasProductEq : HasProducts.HasProductEq sort.{u} sort.{v} :=
  { introEq := λ ⟨_, _⟩ => rfl,
    fstEq   := λ _ _    => rfl,
    sndEq   := λ _ _    => rfl }

  -- `Equiv` also works for general `sort`, but is overridden for `prop`.

  instance hasEquivalences : HasEquivalences sort.{u} sort.{v} sort.{max 1 u v} :=
  { Equiv    := Equiv,
    toFun    := Equiv.toFun,
    invFun   := Equiv.invFun,
    leftInv  := Equiv.leftInv,
    rightInv := Equiv.rightInv }

  -- Dependent functors are analogous to independent functors.

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

namespace prop

  instance hasTrivialIdentity : HasTrivialIdentity prop := ⟨proofIrrel⟩

  -- In `prop`, `Top` is `True` and `Bot` is `False`.

  instance (priority := high) hasTop : HasTop prop :=
  { T := True,
    t := trivial }

  instance (priority := high) hasBot : HasBot prop :=
  { B    := False,
    elim := False.elim }

  -- `prop` has classical logic if we want.

  instance (priority := high) hasClassicalLogic : HasClassicalLogic prop :=
  { byContradictionFun := @Classical.byContradiction }

  -- Products are given by `And`.

  instance (priority := high) hasProducts : HasProducts prop prop prop :=
  { Prod  := And,
    intro := And.intro,
    fst   := And.left,
    snd   := And.right }

  -- Equivalences are given by `Iff`.

  instance (priority := high) hasEquivalences : HasEquivalences prop prop prop :=
  { Equiv    := Iff,
    toFun    := Iff.mp,
    invFun   := Iff.mpr,
    leftInv  := λ _ _ => proofIrrel _ _,
    rightInv := λ _ _ => proofIrrel _ _ }

  instance hasTrivialEquivalenceCondition : HasTrivialEquivalenceCondition prop :=
  ⟨λ e => HasTrivialIdentity.defEquiv (U := prop) (Iff.intro e.toFun e.invFun)⟩

  -- Dependent functors into `prop` are straightforward.

  instance hasDependentCongrArg : HasDependentCongrArg sort.{u} prop :=
  ⟨λ {_ _} f {_ _} e => proofIrrel _ _⟩

  -- Dependent products are given by `∃`, requiring choice to obtain a witness
  -- unless the witness is in `prop`.

  instance (priority := high) hasDependentProducts : HasDependentProducts prop prop prop :=
  { Sigma := λ φ => ∃ h₁, φ h₁,
    intro := λ h₁ h₂ => ⟨h₁, h₂⟩,
    fst   := λ ⟨h₁, _⟩ => h₁,
    snd   := λ ⟨_, h₂⟩ => h₂ }

  noncomputable instance (priority := low) hasClassicalDependentProducts
                                             (U : Universe.{u}) [HasIdentity U] :
    HasDependentProducts U prop prop :=
  { Sigma := λ φ => ∃ a, φ a,
    intro := λ a h => ⟨a, h⟩,
    fst   := Classical.choose,
    snd   := Classical.choose_spec }

end prop

namespace type

  -- Use specialized types for `type.{0}` if possible.

  instance (priority := high) hasTop : HasTop type.{0} :=
  { T := Unit,
    t := Unit.unit }
  
  instance (priority := high) hasTopEq : HasTop.HasTopEq type.{0} :=
  ⟨λ ⟨⟩ => rfl⟩

  instance (priority := high) hasBot : HasBot type.{0} :=
  { B    := Empty,
    elim := Empty.elim }

  noncomputable def byContradiction (α : type.{0}) (f : HasInternalBot.Not (HasInternalBot.Not α)) : α :=
  Classical.choice (Classical.byContradiction (λ h => Empty.elim (f (λ a => False.elim (h ⟨a⟩)))))

  noncomputable instance (priority := high) hasClassicalLogic : HasClassicalLogic type.{0} :=
  { byContradictionFun := byContradiction }

  -- Products are given by `Prod`.

  instance hasProducts : HasProducts type.{u} type.{v} type.{max u v} :=
  { Prod  := Prod,
    intro := Prod.mk,
    fst   := Prod.fst,
    snd   := Prod.snd }

  instance hasProductEq : HasProducts.HasProductEq type.{u} type.{v} :=
  { introEq := λ ⟨_, _⟩ => rfl,
    fstEq   := λ _ _    => rfl,
    sndEq   := λ _ _    => rfl }

  -- `type` has internal equivalences (but general `sort` does not, although each
  -- individual `sort.{u}` does). These equivalences can be constructed automatically.

  instance hasTrivialEquivalenceCondition : HasTrivialEquivalenceCondition type.{u} :=
  ⟨λ e => ⟨⟨e.toFun, e.invFun, e.equiv.left.inv, e.equiv.right.inv⟩, rfl, rfl⟩⟩

  -- The target equality of dependent functors contains a cast, but we can eliminate
  -- it easily.

  instance hasDependentCongrArg : HasDependentCongrArg sort.{u} type.{v} :=
  ⟨λ {_ _} _ {_ _} e => by subst e; rfl⟩

  -- Dependent products are given by either `Sigma`, `PSigma`, or `Subtype`,
  -- depending on the universe levels.

  instance hasDependentProducts : HasDependentProducts type.{u} type.{v} type.{max u v} :=
  { Sigma := Sigma,
    intro := Sigma.mk,
    fst   := Sigma.fst,
    snd   := Sigma.snd }

  instance hasDependentProductEq : HasDependentProducts.HasDependentProductEq type.{u} type.{v} :=
  { introEq := λ ⟨_, _⟩ => rfl,
    fstEq   := λ _ _    => rfl,
    sndEq   := λ _ _    => rfl }

  instance (priority := low) hasDependentProducts' :
    HasDependentProducts sort.{u} type.{v} sort.{max u (v + 1)} :=
  { Sigma := PSigma,
    intro := PSigma.mk,
    fst   := PSigma.fst,
    snd   := PSigma.snd }

  instance (priority := low) hasDependentProductEq' :
    HasDependentProducts.HasDependentProductEq sort.{u} type.{v} :=
  { introEq := λ ⟨_, _⟩ => rfl,
    fstEq   := λ _ _    => rfl,
    sndEq   := λ _ _    => rfl }

  instance hasSubtypes : HasDependentProducts type.{u} prop type.{u} :=
  { Sigma := Subtype,
    intro := Subtype.mk,
    fst   := Subtype.val,
    snd   := Subtype.property }

  instance hasSubtypeEq : HasDependentProducts.HasDependentProductEq type.{u} prop :=
  { introEq := λ ⟨_, _⟩ => rfl,
    fstEq   := λ _ _    => rfl,
    sndEq   := λ _ _    => proofIrrel _ _ }

end type
