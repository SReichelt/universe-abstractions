/-
A completely trivial universe with a single inhabited type.
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



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v



def unit : Universe.{0, 0} := ⟨True⟩

namespace unit

  open MetaRelation HasFunctors HasInternalEquivalences HasEquivOp HasEquivOpFun

  def Inst : unit := trivial

  def inst {A : unit} : A := trivial

  -- `unit` has instance equivalences in `unit`.

  def unitEq (α : Sort u) : HasEquivalenceRelation α unit :=
  { R := unitRelation α Inst,
    h := unitEquivalence α (B := Inst) inst }

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

  -- `Inst` can serve as both top and bottom.

  instance hasTop : HasTop unit :=
  { T := Inst,
    t := inst }

  instance hasBot : HasBot unit :=
  { B    := Inst,
    elim := λ _ _ => inst }

  instance hasClassicalLogic : HasClassicalLogic unit :=
  { byContradictionFun := λ _ => inst }

  -- A product with `Inst` is equivalent to the type itself.

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
  { Equiv := λ _ _ => Inst,
    desc  := λ _   => HasTrivialIdentity.equivDesc inst inst }

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

  instance hasTrivialDependentOutFunctoriality (V : Universe.{v}) [HasTypeIdentity V] :
    HasTrivialDependentFunctoriality unit V :=
  ⟨λ {_ _ φ} f => { F   := HasEquivalences.invFun (φ.eff inst) (f inst),
                    eff := λ _ => HasEquivalences.rightInv (φ.eff inst) (f inst) }⟩

  instance hasDependentOutCongrArg (V : Universe.{v}) [HasTypeIdentity V] : HasDependentCongrArg unit V :=
  ⟨λ {_ _} f {_ _} _ => DependentEquivalence.refl (f inst)⟩

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
    sndEq   := λ _ b => DependentEquivalence.refl b }

end unit
