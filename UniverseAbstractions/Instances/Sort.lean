/-
Instances of `Universe` that correspond to basic Lean types and universes, with structure such
as functors, products, ...

The actual universes are already defined in `Universes.lean` because they are occasionally
referenced without importing this file. They are:
* `sort.{u}  := ⟨Sort u⟩`
* `prop      := sort.{0}`
* `type.{u}  := sort.{u + 1}`
* `tsort.{u} := sort.{max 1 u}`

The structure on all of these universes is "trivial" to varying degrees, compared to what is
allowed in principle. Therefore, in this file there is often an instance of a class that is
defined in `Utils/Trivial.lean`, and which indirectly generates instances of classes in
`Axioms/Universe`.
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

import UniverseAbstractions.MathlibFragments.Init.CoreExt
import UniverseAbstractions.MathlibFragments.Data.Equiv.Basic



set_option autoBoundImplicitLocal false
-- TODO: It looks like there are bad instances.
set_option synthInstance.maxHeartbeats 100000
--set_option pp.universes true

universe u v w w'



-- Each Lean universe is also a universe according to our definition. Some definitions work
-- generically for `sort.{u}`, others need to be split between `prop` and `type.{u}`.

namespace sort

  open MetaRelation HasFunctors HasInternalEquivalences HasDependentFunctors

  -- Instance equivalences of all `sort.{u}` are given by equality.
  -- For `prop`, we could define instance equivalences to be in `unit` instead of relying on proof
  -- irrelevance, but it's easier to generalize over `prop` and `type` if we have a single
  -- definition.

  instance hasEquivalenceRelation (α : sort.{u}) : HasEquivalenceRelation α prop :=
  ⟨nativeRelation (@Eq α)⟩

  instance hasInstanceEquivalences : HasInstanceEquivalences sort.{u} prop :=
  ⟨hasEquivalenceRelation⟩

  -- Functors from `sort` to any universe are just functions: Instance equivalence in `sort` is
  -- given by equality, so functors do not need to respect anything else besides equality.

  instance hasOutFunctors (V : Universe.{v}) : HasFunctors sort.{u} V sort.{imax u v} :=
  { Fun   := λ α B => α → B,
    apply := id }

  def defOutFun {α : sort.{u}} {V : Universe.{v}} [HasIdentity V] {B : V} (f : ⌈α ⟶ B⌉) :
    α ⟶{f} B :=
  toDefFun f

  instance hasTrivialOutFunctoriality (V : Universe.{v}) [HasIdentity V] :
    HasTrivialFunctoriality sort.{u} V :=
  ⟨defOutFun⟩

  instance hasCongrArg : HasCongrArg sort.{u} sort.{v} := ⟨λ f => congrArg f⟩

  instance (priority := low) hasOutCongrArg (V : Universe.{v}) [HasIdentity V] :
    HasCongrArg sort.{u} V :=
  ⟨λ {_ _} f {_ _} e => e ▸ HasRefl.refl _⟩

  instance hasCongrFun : HasCongrFun sort.{u} sort.{v} := ⟨congrFun⟩

  instance (priority := low) hasOutCongrFun (V : Universe.{v}) [HasIdentity V] :
    HasCongrFun sort.{u} V :=
  ⟨λ e _ => e ▸ HasRefl.refl _⟩

  instance hasInternalFunctors : HasInternalFunctors sort.{u} := ⟨⟩

  instance hasTrivialExtensionality : HasTrivialExtensionality sort.{u} sort.{v} := ⟨funext⟩

  -- Functors into `sort` need to be well-defined.

  structure InFunctor {U : Universe.{u}} [HasIdentity U] (A : U) (B : sort.{v}) :
    Sort (max 1 u v) where
  (f                    : A → B)
  (congrArg {a₁ a₂ : A} : a₁ ≃ a₂ → f a₁ = f a₂)

  instance (priority := low) hasInFunctors (U : Universe.{u}) [HasIdentity U] :
    HasFunctors U sort.{v} sort.{max 1 u v} :=
  { Fun   := InFunctor,
    apply := InFunctor.f }

  instance (priority := low) hasInCongrArg (U : Universe.{u}) [HasIdentity U] :
    HasCongrArg U sort.{v} :=
  ⟨InFunctor.congrArg⟩

  def defInFun {U : Universe.{u}} [HasIdentity U] {A : U} {B : sort.{v}} (F : InFunctor A B) :
    A ⟶{F.f} B :=
  toDefFun' F (λ _ => by rfl)

  instance hasInCompFun (U : Universe.{u}) (V : Universe.{v}) {W : Universe.{w'}} [HasIdentity U]
                        [HasIdentity V] [HasFunctors U V W] [HasCongrArg U V] :
    HasCompFun U V sort.{w} :=
  ⟨λ F G => defInFun ⟨λ a => G.f (F a), λ e => G.congrArg (HasCongrArg.congrArg F e)⟩⟩

  -- There are top and bottom types that work generically for `sort`.

  instance (priority := low) hasTop : HasTop sort.{u} :=
  { T := PUnit,
    t := PUnit.unit }
  
  instance (priority := low) hasTopEq : HasTop.HasTopEq sort.{u} :=
  ⟨λ ⟨⟩ => rfl⟩

  instance (priority := low) hasBot : HasBot sort.{u} :=
  { B    := PEmpty,
    elim := PEmpty.elim }

  noncomputable def byContradiction (α : sort.{u}) (f : HasInternalBot.Not (HasInternalBot.Not α)) : α :=
  Classical.choice (Classical.byContradiction (λ h => PEmpty.elim (f (λ a => False.elim (h ⟨a⟩)))))

  noncomputable instance (priority := low) hasClassicalLogic : HasClassicalLogic sort.{u} :=
  { byContradictionFun := byContradiction }

  -- Same for products, but usually the specialized versions for `prop` and `type` should be used.

  instance (priority := low) hasProducts : HasProducts sort.{u} sort.{v} tsort.{max u v} :=
  { Prod  := PProd,
    intro := PProd.mk,
    fst   := PProd.fst,
    snd   := PProd.snd }

  instance (priority := low) hasProductEq :
    HasProducts.HasProductEq sort.{u} sort.{v} (UxV := tsort.{max u v}) :=
  { introEq := λ ⟨_, _⟩ => rfl,
    fstEq   := λ _ _    => rfl,
    sndEq   := λ _ _    => rfl }

  -- `Equiv` also works for general `sort`, but is overridden for `prop`.

  def equivDesc {α : sort.{u}} {β : sort.{v}} (e : Equiv α β) : α ⮂ β :=
  { toFun  := e.toFun,
    invFun := e.invFun,
    left   := ⟨e.leftInv⟩,
    right  := ⟨e.rightInv⟩ }

  instance (priority := low) hasEquivalences : HasEquivalences sort.{u} sort.{v} tsort.{max u v} :=
  { Equiv := Equiv,
    desc  := equivDesc }

  -- Dependent functors are analogous to independent functors.

  instance hasDependentOutFunctors (V : Universe.{v}) :
    HasDependentFunctors sort.{u} V sort.{imax u v} :=
  { Pi    := HasFunctors.Pi,
    apply := id }

  def defPi {α : sort.{u}} {V : Universe.{v}} [HasTypeIdentity V] {p : α → V} {φ : α ⟶{p} ⌊V⌋}
            (f : ∀ a, p a) :
    DefPi φ f :=
  { F   := λ a => HasEquivalences.inv      (φ.eff a) (f a),
    eff := λ a => HasEquivalences.rightInv (φ.eff a) (f a) }

  instance hasTrivialDependentOutFunctoriality (V : Universe.{v}) [HasTypeIdentity V] :
    HasTrivialDependentFunctoriality sort.{u} V :=
  ⟨defPi⟩

  instance hasDependentCongrFun : HasDependentCongrFun sort.{u} sort.{v} := ⟨congrFun⟩

  instance (priority := low) hasDependentOutCongrFun (V : Universe.{v}) [HasIdentity V] :
    HasDependentCongrFun sort.{u} V :=
  ⟨λ e _ => e ▸ HasRefl.refl _⟩

end sort

namespace prop

  open MetaRelation HasFunctors HasEquivOp HasEquivOpFun

  instance hasTrivialIdentity : HasTrivialIdentity prop := ⟨proofIrrel⟩

  -- Mapping into `prop` is expecially simple.

  instance hasInFunctors (U : Universe.{u}) : HasFunctors U prop prop :=
  { Fun   := λ A q => A → q,
    apply := id }

  def defInFun {U : Universe.{u}} {A : U} {q : prop} (f : ⌈A ⟶ q⌉) : A ⟶{f} q :=
  toDefFun f

  instance hasTrivialInFunctoriality (U : Universe.{u}) : HasTrivialFunctoriality U prop :=
  ⟨defInFun⟩

  -- Propositional trunction is functorial.

  def Truncated {U : Universe.{u}} (A : U) : prop := Nonempty A

  theorem trunc {U : Universe.{u}} {A : U} (a : A) : Truncated A := ⟨a⟩
  theorem truncFun {U : Universe.{u}} (A : U) : A ⟶ Truncated A := trunc

  instance trunc.isFunApp {U : Universe.{u}} {A : U} (a : A) : IsFunApp (V := prop) A (trunc a) :=
  { F := truncFun A,
    a := a,
    e := proofIrrel _ _ }

  theorem truncProj {U : Universe.{u}} [HasFunctors U U U] {A B : U} (F : A ⟶ B) :
    Truncated A ⟶ Truncated B :=
  λ ⟨a⟩ => ⟨F a⟩

  theorem truncProjFun {U : Universe.{u}} [HasFunctors U U U] (A B : U) :
    (A ⟶ B) ⟶ (Truncated A ⟶ Truncated B) :=
  truncProj

  instance truncProj.isFunApp {U : Universe.{u}} [HasFunctors U U U] {A B : U} (F : A ⟶ B) :
    IsFunApp (V := prop) (A ⟶ B) (truncProj F) :=
  { F := truncProjFun A B,
    a := F,
    e := proofIrrel _ _ }

  theorem truncProjFun' {U : Universe.{u}} [HasFunctors U U U] (A B : U) :
    Truncated (A ⟶ B) ⟶ (Truncated A ⟶ Truncated B) :=
  λ ⟨F⟩ => truncProj F

  -- In `prop`, `Top` is `True` and `Bot` is `False`.

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
  { Equiv := Iff,
    desc  := λ h => HasTrivialIdentity.equivDesc h.mp h.mpr }

  instance hasTrivialEquivalenceCondition : HasTrivialEquivalenceCondition prop :=
  ⟨λ e => HasTrivialIdentity.defEquiv (Iff.intro e.toFun e.invFun)⟩

  -- Dependent products are given by `∃`, requiring choice to obtain a witness unless the witness
  -- is in `prop`.

  instance hasDependentProducts : HasDependentProducts prop prop prop :=
  { Sigma := λ φ => ∃ h₁, φ h₁,
    intro := λ h₁ h₂ => ⟨h₁, h₂⟩,
    fst   := λ ⟨h₁, _⟩ => h₁,
    snd   := λ ⟨_, h₂⟩ => h₂ }

  noncomputable instance (priority := low) hasClassicalDependentProducts :
    HasDependentProducts sort.{u} prop prop :=
  { Sigma := λ φ => ∃ a, φ a,
    intro := λ a h => ⟨a, h⟩,
    fst   := Classical.choose,
    snd   := Classical.choose_spec }

end prop

namespace type

  open MetaRelation

  -- Use specialized types for `type.{0}`.

  instance hasTop : HasTop type.{0} :=
  { T := Unit,
    t := Unit.unit }
  
  instance hasTopEq : HasTop.HasTopEq type.{0} :=
  ⟨λ ⟨⟩ => rfl⟩

  instance hasBot : HasBot type.{0} :=
  { B    := Empty,
    elim := Empty.elim }

  noncomputable def byContradiction (α : type.{0}) (f : HasInternalBot.Not (HasInternalBot.Not α)) : α :=
  Classical.choice (Classical.byContradiction (λ h => Empty.elim (f (λ a => False.elim (h ⟨a⟩)))))

  noncomputable instance hasClassicalLogic : HasClassicalLogic type.{0} :=
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

  -- `type` has internal equivalences given by `Equiv`. An `Equiv` essentially matches our
  -- `EquivDesc`, so we can directly use the equivalence proofs from generic code.

  instance hasInternalEquivalences : HasInternalEquivalences type.{u} :=
  { defToFunFun := λ _ _ => HasTrivialFunctoriality.defFun,
    isExt       := λ E => HasTrivialExtensionality.equivDescExt type.{u} (HasEquivalences.desc E) }

  instance hasTrivialEquivalenceCondition : HasTrivialEquivalenceCondition type.{u} :=
  ⟨λ e => ⟨⟨e.toFun, e.invFun, e.left.inv, e.right.inv⟩, rfl, rfl⟩⟩

  -- The target equality of dependent functors contains a cast (from `sort.hasOutCongrArg`),
  -- but we can eliminate it easily.

  instance hasDependentCongrArg : HasDependentCongrArg sort.{u} type.{v} :=
  ⟨λ {_ _} _ {_ _} e => by subst e; rfl⟩

  -- Dependent products are given by either `Sigma`, `PSigma`, or `Subtype`, depending on the
  -- universe levels.

  instance hasDependentProducts : HasDependentProducts type.{u} type.{v} type.{max u v} :=
  { Sigma := Sigma,
    intro := Sigma.mk,
    fst   := Sigma.fst,
    snd   := Sigma.snd }

  instance hasDependentProductEq :
    HasDependentProducts.HasDependentProductEq type.{u} type.{v} (UxV := type.{max u v}) :=
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
    HasDependentProducts.HasDependentProductEq sort.{u} type.{v} (UxV := sort.{max u (v + 1)}) :=
  { introEq := λ ⟨_, _⟩ => rfl,
    fstEq   := λ _ _    => rfl,
    sndEq   := λ _ _    => rfl }

  instance (priority := low) hasSubtypes :
    HasDependentProducts sort.{u} prop tsort.{u} :=
  { Sigma := Subtype,
    intro := Subtype.mk,
    fst   := Subtype.val,
    snd   := Subtype.property }

  instance (priority := low) hasSubtypeEq :
    HasDependentProducts.HasDependentProductEq sort.{u} prop (UxV := tsort.{u}) :=
  { introEq := λ ⟨_, _⟩ => rfl,
    fstEq   := λ _ _    => rfl,
    sndEq   := λ _ _    => HasTrivialIdentity.eq }

end type
