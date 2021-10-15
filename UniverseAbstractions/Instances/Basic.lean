import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.FunctorExtensionality
import UniverseAbstractions.Axioms.Universe.Singletons
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences
import UniverseAbstractions.Axioms.Universe.Properties
import UniverseAbstractions.Axioms.Universe.DependentFunctors
import UniverseAbstractions.Axioms.Universe.DependentProducts
import UniverseAbstractions.Instances.Utils.Trivial

import mathlib4_experiments.CoreExt
import mathlib4_experiments.Data.Equiv.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v



namespace unit

  open MetaRelation

  def unitEq (α : Sort u) : EquivalenceRelation α unit :=
  { R := unitRelation α Inst,
    h := unitEquivalence α inst }

  -- `unit` has instance equivalences in `unit`.

  instance hasIdentity' : HasIdentity' unit unit :=
  ⟨λ A => unitEq ⌈A⌉⟩

  -- Functors into `unit` are trivial.

  instance (priority := high) hasInFunctors (U : Universe.{u}) : HasFunctors U unit unit :=
  { Fun   := λ _ _ => Inst,
    apply := λ _ _ => inst }

  instance hasTrivialInFunctoriality (U : Universe.{u}) : HasTrivialFunctoriality U unit :=
  ⟨λ _ => { F   := inst,
            eff := λ _ => inst }⟩

  instance hasInCongrArg (U : Universe.{u}) [HasIdentity U] : HasCongrArg U unit :=
  ⟨λ {_ _} _ {_ _} _ => inst⟩

  instance hasTrivialInExtensionality (U : Universe.{u}) : HasTrivialExtensionality U unit :=
  ⟨λ _ => inst⟩

  -- Functors from `unit` to `V` are the same as instances of `V`.

  instance hasOutFunctors (V : Universe.{v}) : HasFunctors unit V V :=
  { Fun   := λ _ A => A,
    apply := λ a _ => a }

  instance hasTrivialOutFunctoriality (V : Universe.{v}) [HasIdentity V] :
    HasTrivialFunctoriality unit V :=
  ⟨λ f => { F   := f inst,
            eff := λ _ => HasRefl.refl (f inst) }⟩

  instance hasOutCongrArg (V : Universe.{v}) [HasIdentity V] : HasCongrArg unit V :=
  ⟨λ {_ _} F {_ _} _ => HasRefl.refl F⟩

  instance hasTrivialOutExtensionality (V : Universe.{v}) [HasIdentity V] :
    HasTrivialExtensionality unit V :=
  ⟨λ e => e inst⟩

  -- Internal functors are given by `hasInFunctors` due to its priority.

  instance hasInternalFunctors : HasInternalFunctors unit := ⟨⟩
  instance hasStandardFunctors : HasStandardFunctors unit := ⟨⟩

--  instance hasInternalTopType : HasEmbeddedType unit True := ⟨Equiv.refl ⌈Inst⌉⟩
--
--  instance hasTop : HasTop unit := ⟨⟩
--
--  def rightProdEquiv {U : Universe.{u}} (A : U) (B : unit) : ⌈A⌉ ≃ (A ⊓' B) :=
--  { toFun    := λ a => ⟨a, inst⟩,
--    invFun   := λ P => P.fst,
--    leftInv  := λ _ => rfl,
--    rightInv := λ ⟨_, _⟩ => rfl }
--
--  instance hasInternalRightProductType {U : Universe.{u}} (A : U) (B : unit) : HasEmbeddedType U (A ⊓' B) :=
--  ⟨rightProdEquiv A B⟩
--
--  instance hasRightProducts (U : Universe.{u}) : HasProducts U unit U := ⟨⟩
--
--  def leftProdEquiv {U : Universe.{u}} (A : unit) (B : U) : ⌈B⌉ ≃ (A ⊓' B) :=
--  { toFun    := λ b => ⟨inst, b⟩,
--    invFun   := λ P => P.snd,
--    leftInv  := λ _ => rfl,
--    rightInv := λ ⟨_, _⟩ => rfl }
--
--  instance hasInternalLeftProductType {U : Universe.{u}} (A : unit) (B : U) : HasEmbeddedType U (A ⊓' B) :=
--  ⟨leftProdEquiv A B⟩
--
--  instance hasLeftProducts (U : Universe.{u}) : HasProducts unit U U := ⟨⟩
--
--  instance hasTrivialEquivalenceCondition : HasTrivialEquivalenceCondition unit unit := ⟨⟩
--
--  @[reducible] def unitEquivalence {A B : unit} : A ⟷' B := ⟨inst, inst, HasTrivialEquivalenceCondition.defEquiv⟩
--
--  @[simp] theorem unitEquivalence.unique {A B : unit} (E : A ⟷' B) : E = unitEquivalence :=
--  by induction E; simp
--
--  def equivEquiv (A B : unit) : ⌈Inst⌉ ≃ (A ⟷' B) :=
--  { toFun    := λ _ => unitEquivalence,
--    invFun   := λ _ => inst,
--    leftInv  := inst.unique,
--    rightInv := λ E => Eq.symm (unitEquivalence.unique E) }
--
--  instance hasInternalEquivType (A B : unit) : HasEmbeddedType unit (A ⟷' B) :=
--  ⟨equivEquiv A B⟩
--
--  instance hasTrivialEquivalences : HasTrivialEquivalenceCondition.HasTrivialEquivalences unit unit unit := ⟨⟩
--
--  instance hasTrivialInProperties  (U : Universe.{u}) : HasTrivialProperties U unit := ⟨⟩
--  instance hasTrivialOutProperties (U : Universe.{u}) : HasTrivialProperties unit U := ⟨⟩
--
--  instance hasTrivialDependentInFunctoriality (U : Universe.{u}) : HasTrivialDependentFunctoriality U unit := ⟨⟩
--
--  def dependentUnitFunctor {U : Universe.{u}} {A : U} {φ : A ⟿ unit} : Π' φ :=
--  ⟨λ _ => inst, HasTrivialDependentFunctoriality.defPi⟩
--
--  @[simp] theorem dependentUnitFunctor.unique {U : Universe.{u}} {A : U} {φ : A ⟿ unit} (F : Π' φ) :
--    F = dependentUnitFunctor :=
--  by induction F; rfl
--
--  def inPiEquiv {U : Universe.{u}} {A : U} (φ : A ⟿ unit) : ⌈Inst⌉ ≃ (Π' φ) :=
--  { toFun    := λ _ => dependentUnitFunctor,
--    invFun   := λ _ => inst,
--    leftInv  := inst.unique,
--    rightInv := λ F => Eq.symm (dependentUnitFunctor.unique F) }
--
--  instance hasInternalDependentInFunctorType {U : Universe.{u}} {A : U} (φ : A ⟿ unit) :
--    HasEmbeddedType unit (Π' φ) :=
--  ⟨inPiEquiv φ⟩
--
--  instance hasTrivialDependentInFunctors (U : Universe.{u}) :
--    HasTrivialDependentFunctoriality.HasTrivialDependentFunctors U unit unit :=
--  ⟨⟩
--
--  instance hasTrivialDependentOutFunctoriality (U : Universe.{u}) : HasTrivialDependentFunctoriality unit U := ⟨⟩
--
--  def outPiEquiv {A : unit} {U : Universe.{u}} (φ : A ⟿ U) : ⌈φ inst⌉ ≃ (Π' φ) :=
--  { toFun    := λ b => ⟨λ _ => b, HasTrivialDependentFunctoriality.defPi⟩,
--    invFun   := λ F => F inst,
--    leftInv  := λ _ => rfl,
--    rightInv := λ ⟨_, _⟩ => rfl }
--
--  instance hasInternalDependentOutFunctorType {A : unit} {U : Universe.{u}} (φ : A ⟿ U) :
--    HasEmbeddedType U (Π' φ) :=
--  ⟨outPiEquiv φ⟩
--
--  instance hasTrivialDependentOutFunctors (U : Universe.{u}) :
--    HasTrivialDependentFunctoriality.HasTrivialDependentFunctors unit U U :=
--  ⟨⟩
--
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

  -- `boolean` has instance equivalences in `unit`.

  instance hasIdentity' : HasIdentity' boolean unit :=
  ⟨λ A => unit.unitEq ⌈A⌉⟩

  -- Internal functors in `boolean` are defined as implication.

  instance hasFunctors : HasFunctors boolean boolean boolean :=
  { Fun   := λ a b => cond a b true,
    apply := λ {a b} hF ha => match a with
                              | true  => hF
                              | false => False.elim ha }

  instance hasTrivialFunctoriality : HasTrivialFunctoriality boolean boolean :=
  ⟨λ {a b} p => { F   := match a with
                         | true  => p inst
                         | false => inst,
                  eff := λ _ => inst }⟩

  instance hasCongrArg : HasCongrArg boolean boolean :=
  ⟨λ {_ _} _ {_ _} _ => inst⟩

  instance hasInternalFunctors : HasInternalFunctors boolean := ⟨⟩

  instance hasTrivialExtensionality : HasTrivialExtensionality boolean boolean :=
  ⟨λ _ => inst⟩

  instance hasStandardFunctors : HasStandardFunctors boolean := ⟨⟩

end boolean



namespace sort

  open MetaRelation

  -- Functors from `sort` to any other universe are just functions: Instance equivalence
  -- in `sort` is given by equality (or `unit` for `prop`), so functors do not need to
  -- respect anything else besides equality.

  instance hasFunctors (V : Universe.{v}) : HasFunctors sort.{u} V sort.{imax u v} :=
  { Fun   := λ α B => α → B,
    apply := id }

  instance hasTrivialFunctoriality (V : Universe.{v}) [HasIdentity V] :
    HasTrivialFunctoriality sort.{u} V :=
  ⟨λ f => { F   := f,
            eff := λ a => HasRefl.refl (f a) }⟩

--  instance hasTrivialProperties (V : Universe.{v}) : HasTrivialProperties sort V := ⟨⟩
--
--  instance hasTrivialDependentFunctoriality (V : Universe.{v}) : HasTrivialDependentFunctoriality sort V := ⟨⟩
--
--  def piEquiv {α : sort.{u}} {V : Universe.{v}} (φ : α ⟿ V) : HasProperties.Pi φ ≃ (Π' φ) :=
--  { toFun    := λ f => ⟨f, trivial⟩,
--    invFun   := λ F => F.f,
--    leftInv  := λ _ => rfl,
--    rightInv := λ ⟨_, _⟩ => rfl }
--
--  instance hasInternalDependentFunctorType {α : sort.{u}} {V : Universe.{v}} (φ : α ⟿ V) :
--    HasEmbeddedType sort.{imax u v} (Π' φ) :=
--  ⟨piEquiv φ⟩
--
--  instance hasTrivialDependentFunctors (V : Universe.{v}) :
--    HasTrivialDependentFunctoriality.HasTrivialDependentFunctors sort.{u} V sort.{imax u v} :=
--  ⟨⟩

end sort

-- TODO: Adapt
#exit

theorem Exists.prop.fst {p : Prop} {q : p → Prop} : (∃ h, q h) → p
| ⟨h, _⟩ => h

theorem Exists.prop.snd {p : Prop} {q : p → Prop} : (e : ∃ h, q h) → q (Exists.prop.fst e)
| ⟨_, h⟩ => h

namespace prop

  instance hasInternalTopType : HasEmbeddedType prop True := ⟨Equiv.refl True⟩

  instance hasTop : HasTop prop := ⟨⟩

  instance hasInternalBotType : HasEmbeddedType prop False := ⟨Equiv.refl False⟩

  instance hasBot : HasBot prop := ⟨⟩

  instance hasClassicalLogic : HasClassicalLogic prop :=
  { byContradictionFun := @Classical.byContradiction }

  def prodEquiv (p q : prop) : (p ∧ q) ≃ (p ⊓' q) :=
  { toFun    := λ h => ⟨h.left, h.right⟩,
    invFun   := λ P => ⟨P.fst, P.snd⟩,
    leftInv  := λ _ => proofIrrel _ _,
    rightInv := λ ⟨_, _⟩ => rfl }

  instance hasInternalProductType (p q : prop) : HasEmbeddedType prop (p ⊓' q) :=
  ⟨prodEquiv p q⟩

  instance hasProducts : HasProducts prop prop prop := ⟨⟩

  instance hasTrivialEquivalenceCondition : HasTrivialEquivalenceCondition prop prop := ⟨⟩

  def equivEquiv (p q : prop) : (p ↔ q) ≃ (p ⟷' q) :=
  { toFun    := λ h => ⟨h.mp, h.mpr, trivial⟩,
    invFun   := λ E => ⟨E.toFun, E.invFun⟩,
    leftInv  := λ _ => proofIrrel _ _,
    rightInv := λ ⟨_, _, _⟩ => by simp; exact HEq.rfl }

  instance hasInternalEquivType (p q : prop) : HasEmbeddedType prop (p ⟷' q) :=
  ⟨equivEquiv p q⟩

  instance hasTrivialEquivalences : HasTrivialEquivalenceCondition.HasTrivialEquivalences prop prop prop := ⟨⟩

  def sigmaEquiv {p : prop} (φ : p ⟿ prop) : (∃ a, φ a) ≃ (Σ' φ) :=
  { toFun    := λ h => ⟨Exists.prop.fst h, Exists.prop.snd h⟩,
    invFun   := λ P => ⟨P.fst, P.snd⟩,
    leftInv  := λ _ => proofIrrel _ _,
    rightInv := λ ⟨_, _⟩ => rfl }

  instance hasInternalDependentProductType {p : prop} (φ : p ⟿ prop) :
    HasEmbeddedType prop (Σ' φ) :=
  ⟨sigmaEquiv φ⟩

  instance hasDependentProducts : HasDependentProducts prop prop prop := ⟨⟩

end prop

theorem Equiv.trans_symm_trans {α : Sort u} {β : Sort v} {γ : Sort w} (e : α ≃ β) (f : α ≃ γ) :
  trans (trans e (symm e)) f = f :=
by simp

theorem Equiv.symm_trans_trans {α : Sort u} {β : Sort v} {γ : Sort w} (e : α ≃ β) (f : β ≃ γ) :
  trans (trans (symm e) e) f = f :=
by simp

namespace type

  def topEquiv : Unit ≃ True :=
  { toFun    := λ _  => trivial,
    invFun   := λ _  => (),
    leftInv  := λ () => rfl,
    rightInv := λ _  => proofIrrel _ _ }

  instance hasInternalTopType : HasEmbeddedType type True := ⟨topEquiv⟩

  instance hasTop : HasTop type := ⟨⟩

  def botEquiv : Empty ≃ False :=
  { toFun    := Empty.elim,
    invFun   := False.elim,
    leftInv  := λ e => Empty.elim e,
    rightInv := λ _ => proofIrrel _ _ }

  instance hasInternalBotType : HasEmbeddedType type False := ⟨botEquiv⟩

  instance hasBot : HasBot type := ⟨⟩

  noncomputable def byContradiction (α : type) (f : HasInternalBot.Not (HasInternalBot.Not α)) : α :=
  Classical.choice (Classical.byContradiction (λ h => Empty.elim (f (λ a => False.elim (h ⟨a⟩)))))

  noncomputable instance hasClassicalLogic : HasClassicalLogic type :=
  { byContradictionFun := byContradiction }

  def prodEquiv (α β : type) : Prod α β ≃ (α ⊓' β) :=
  { toFun    := λ p => ⟨p.fst, p.snd⟩,
    invFun   := λ P => ⟨P.fst, P.snd⟩,
    leftInv  := λ (_, _) => rfl,
    rightInv := λ ⟨_, _⟩ => rfl }

  instance hasInternalProductType (α β : type) : HasEmbeddedType type (α ⊓' β) :=
  ⟨prodEquiv α β⟩

  instance hasProducts : HasProducts type type type := ⟨⟩

  theorem prodExt {α β : type} {p q : Prod α β} (hFst : p.fst = q.fst) (hSnd : p.snd = q.snd) :
    p = q :=
  by induction p; induction q; simp [hFst, hSnd]

  class DefEquiv {α β : type} (toFun : α → β) (invFun : β → α) : Prop where
  (leftInv  : ∀ a, invFun (toFun a) = a)
  (rightInv : ∀ b, toFun (invFun b) = b)

  instance hasEquivalenceCondition : HasEquivalenceCondition type type := ⟨DefEquiv⟩

  @[reducible] def DefEquiv.fromEquiv {α β : type} (e : ⌈α⌉ ≃ ⌈β⌉) : α ⟷[sort.toFunctor e.toFun, sort.toFunctor e.invFun] β :=
  ⟨e.leftInv, e.rightInv⟩

  @[reducible] def DefEquiv.inv {α β : type} {toFun : α → β} {invFun : β → α}
                                (h : α ⟷[sort.toFunctor toFun, sort.toFunctor invFun] β) :
    β ⟷[sort.toFunctor invFun, sort.toFunctor toFun] α :=
  ⟨h.rightInv, h.leftInv⟩

  def equivEquiv (α β : type) : Equiv α β ≃ (α ⟷' β) :=
  { toFun    := λ e => ⟨e.toFun, e.invFun, DefEquiv.fromEquiv e⟩,
    invFun   := λ E => ⟨E.toFun, E.invFun, E.E.leftInv, E.E.rightInv⟩,
    leftInv  := λ ⟨_, _, _, _⟩ => rfl,
    rightInv := λ ⟨_, _, _⟩ => rfl }

  instance hasInternalEquivType (α β : type) : HasEmbeddedType type (α ⟷' β) :=
  ⟨equivEquiv α β⟩

  instance hasEquivalences : HasEquivalences type type type := ⟨⟩

  instance hasEquivOp : HasEquivOp type :=
  { defIdEquiv         := λ α     => DefEquiv.fromEquiv (Equiv.refl α),
    defCompEquiv       := λ e f   => DefEquiv.fromEquiv (Equiv.trans e f),
    defCompEquivFun    := λ _ _   => HasTrivialFunctoriality.defFun,
    defCompEquivFunFun := λ _ _ _ => HasTrivialFunctoriality.defFun,
    defInvEquiv        := λ e     => DefEquiv.fromEquiv (Equiv.symm e),
    defInvEquivFun     := λ _ _   => HasTrivialFunctoriality.defFun }

  instance hasIdEquiv : HasIdEquiv type type := HasEquivOp.hasIdEquiv
  instance hasInvEquiv : HasInvEquiv type type type := HasEquivOp.hasInvEquiv
  instance hasCompEquiv : HasCompEquiv type type type := HasEquivOp.hasCompEquiv

  instance hasEquivOpEq : HasEquivOpEq type := HasEquivOpEq.std type

  instance hasLinearCommonEquivalences : HasLinearCommonEquivalences type :=
  { defFunDomainEquiv      := λ e _   => ⟨λ f => funext λ b => congrArg f (e.rightInv b),
                                          λ f => funext λ a => congrArg f (e.leftInv  a)⟩,
    defFunDomainEquivFun   := λ _ _ _ => HasTrivialFunctoriality.defFun,
    defFunCodomainEquiv    := λ e _   => ⟨λ f => funext λ c => e.leftInv  (f c),
                                          λ f => funext λ c => e.rightInv (f c)⟩,
    defFunCodomainEquivFun := λ _ _ _ => HasTrivialFunctoriality.defFun,
    defSwapFunFunEquiv     := λ _ _ _ => ⟨λ _ => funext λ _ => funext λ _ => rfl,
                                          λ _ => funext λ _ => funext λ _ => rfl⟩,
    defTopElimEquiv        := λ _     => ⟨λ _ => rfl, λ f => funext λ () => rfl⟩,
    defProdElimFunEquiv    := λ _ _ _ => ⟨λ _ => funext λ _ => funext λ _ => rfl,
                                          λ _ => funext λ (_, _) => rfl⟩,
    defProdFstEquiv        := λ e _   => ⟨λ p => prodExt (e.leftInv  p.fst) rfl,
                                          λ p => prodExt (e.rightInv p.fst) rfl⟩,
    defProdFstEquivFun     := λ _ _ _ => HasTrivialFunctoriality.defFun,
    defProdSndEquiv        := λ e _   => ⟨λ p => prodExt rfl (e.leftInv  p.snd),
                                          λ p => prodExt rfl (e.rightInv p.snd)⟩,
    defProdSndEquivFun     := λ _ _ _ => HasTrivialFunctoriality.defFun,
    defProdCommEquiv       := λ _ _   => ⟨λ (_, _) => rfl, λ (_, _) => rfl⟩,
    defProdAssocEquiv      := λ _ _ _ => ⟨λ ((_, _), _) => rfl, λ (_, (_, _)) => rfl⟩,
    defProdTopEquiv        := λ _     => ⟨λ _ => rfl, λ ((), _) => rfl⟩,
    defCompEquivEquiv      := λ e _   => ⟨Equiv.symm_trans_trans e, Equiv.trans_symm_trans e⟩,
    defCompEquivEquivFun   := λ _ _ _ => HasTrivialFunctoriality.defFun,
    defInvEquivEquiv       := λ _ _   => ⟨Equiv.symm_symm, Equiv.symm_symm⟩ }

  instance hasNonLinearCommonEquivalences : HasNonLinearCommonEquivalences type :=
  { defProdDistrEquiv := λ _ _ _ => ⟨λ _ => funext λ _ => prodExt rfl rfl,
                                     λ _ => prodExt (funext λ _ => rfl) (funext λ _ => rfl)⟩ }

  instance hasBotEquivalences : HasBotEquivalences type :=
  { defBotNotTopEquiv := ⟨λ e => Empty.elim e, λ f => Empty.elim (f ())⟩,
    defProdBotEquiv   := λ _ => ⟨λ e => Empty.elim e, λ p => Empty.elim p.fst⟩,
    defBotContraEquiv := λ _ => ⟨λ e => Empty.elim e, λ p => Empty.elim (p.snd p.fst)⟩ }

  def sigmaEquiv {α : type} (φ : α ⟿ type) : (Σ a, φ a) ≃ (Σ' φ) :=
  { toFun    := λ p => ⟨p.fst, p.snd⟩,
    invFun   := λ P => ⟨P.fst, P.snd⟩,
    leftInv  := λ ⟨_, _⟩ => rfl,
    rightInv := λ ⟨_, _⟩ => rfl }

  instance hasInternalDependentProductType {α : type} (φ : α ⟿ type) :
    HasEmbeddedType type (Σ' φ) :=
  ⟨sigmaEquiv φ⟩

  instance hasDependentProducts : HasDependentProducts type type type := ⟨⟩

  def subtypeEquiv {α : type} (φ : α ⟿ prop) : {a // φ a} ≃ (Σ' φ) :=
  { toFun    := λ p => ⟨p.val, p.property⟩,
    invFun   := λ P => ⟨P.fst, P.snd⟩,
    leftInv  := λ ⟨_, _⟩ => rfl,
    rightInv := λ ⟨_, _⟩ => rfl }

  instance hasInternalSubtypeType {α : type} (φ : α ⟿ prop) :
    HasEmbeddedType type (Σ' φ) :=
  ⟨subtypeEquiv φ⟩

  instance hasSubtypes : HasDependentProducts type prop type := ⟨⟩

end type
