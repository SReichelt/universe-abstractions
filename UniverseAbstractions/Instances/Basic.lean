import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Equivalences

import mathlib4_experiments.CoreExt
import mathlib4_experiments.Data.Equiv.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w



instance unitHasInstances : HasInstances.{0, 1} Unit := ⟨λ _ => True⟩

def unit : Universe.{0} := ⟨Unit⟩

namespace unit

  instance hasExternalFunctor {U : Universe.{u}} (α : U) (β : unit) : HasExternalFunctor.{u, 0, 0} α β :=
  ⟨λ _ => True⟩

  def unitFunctor {U : Universe.{u}} {α : U} {β : unit} : α ⟶' β := ⟨λ _ => trivial, trivial⟩

  @[simp] theorem unitFunctor.unique {U : Universe.{u}} {α : U} {β : unit} (F : α ⟶' β) :
    F = unitFunctor := match F with
  | ⟨_, _⟩ => rfl

  def funEquiv (α β : unit) : True ≃ (α ⟶' β) :=
  { toFun    := λ _ => unitFunctor,
    invFun   := λ _ => trivial,
    leftInv  := λ _ => proofIrrel _ _,
    rightInv := λ _ => by simp }

  instance hasEmbeddedFunctorType (α β : unit) : HasEmbeddedType unit (α ⟶' β) :=
  { α := (),
    h := funEquiv α β }

  instance hasEmbeddedFunctor (α β : unit) : HasEmbeddedFunctor α β := ⟨⟩
  instance hasEmbeddedFunctors : HasEmbeddedFunctors unit := ⟨⟩

  instance hasLinearFunOp : HasLinearFunOp unit :=
  { defIdFun         := λ _     => trivial,
    defAppFun        := λ _ _   => trivial,
    defAppFunFun     := λ _ _   => trivial,
    defCompFun       := λ _ _   => trivial,
    defCompFunFun    := λ _ _   => trivial,
    defCompFunFunFun := λ _ _ _ => trivial }

  instance hasAffineFunOp : HasAffineFunOp unit :=
  { defConstFun    := λ _ _ _ => trivial,
    defConstFunFun := λ _ _   => trivial }

  instance hasFullFunOp : HasFullFunOp unit :=
  { defDupFun    := λ _   => trivial,
    defDupFunFun := λ _ _ => trivial }

  instance hasFunOp : HasFunOp unit := ⟨⟩

  instance hasExternalEquivalence (α β : unit) : HasExternalEquivalence.{0, 0, 0, 0} α β := ⟨λ _ _ => True⟩

  @[reducible] def unitEquivalence {α β : unit} : α ⟷' β :=
  ⟨unitFunctor, unitFunctor, trivial⟩

  @[simp] theorem unitEquivalence.unique {α β : unit} {E : α ⟷' β} :
    E = unitEquivalence := match E with
  | ⟨_, _, _⟩ => by simp; exact HEq.rfl

  def equivEquiv (α β : unit) : True ≃ (α ⟷' β) :=
  { toFun    := λ _ => unitEquivalence,
    invFun   := λ _ => trivial,
    leftInv  := λ _ => proofIrrel _ _,
    rightInv := λ _ => by simp }

  instance hasEmbeddedEquivType (α β : unit) : HasEmbeddedType unit (α ⟷' β) :=
  { α := (),
    h := equivEquiv α β }

  instance hasEmbeddedEquivalence (α β : unit) : HasEmbeddedEquivalence α β := ⟨⟩
  instance hasEmbeddedEquivalences : HasEmbeddedEquivalences unit := ⟨⟩

  instance hasFunctorialEquivalences : HasFunctorialEquivalences unit :=
  { defToFunFun  := λ _ _ => trivial,
    defInvFunFun := λ _ _ => trivial }

  instance hasEquivOp : HasEquivOp unit :=
  { defIdEquiv         := λ _     => trivial,
    defCompEquiv       := λ _ _   => trivial,
    defCompEquivFun    := λ _ _   => trivial,
    defCompEquivFunFun := λ _ _ _ => trivial,
    defInvEquiv        := λ _     => trivial,
    defInvEquivFun     := λ _ _   => trivial,
    defInvEquivEquiv   := λ _ _   => trivial }

--  @[reducible] def unitProduct (α : unit) (β : unit) : α ⊓'' β :=
--  ⟨trivial, trivial⟩
--
--  @[simp] theorem unitProductIsUnique {α : unit} {β : unit} (P : α ⊓'' β) :
--    P = unitProduct α β := match P with
--  | ⟨_, _⟩ => rfl
--
--  def prodEquiv (α β : unit) : True ≃ (α ⊓'' β) :=
--  { toFun    := λ _ => unitProduct α β,
--    invFun   := λ _ => trivial,
--    leftInv  := λ _ => proofIrrel _ _,
--    rightInv := λ _ => by simp }
--
--  def prodEmbed (φ : HasExternalProducts.productUniverse unit unit) : TypeEmbedding unit φ :=
--  { α     := UnitType,
--    equiv := prodEquiv φ.α φ.β }
--
--  instance : HasEmbeddedUniverse unit (HasExternalProducts.productUniverse unit unit) :=
--  { embed := prodEmbed }
--
--  instance hasFunctorialExternalProducts : HasFunctorialExternalProducts unit unit :=
--  { fstIsFun         := λ _ _     => trivial,
--    sndIsFun         := λ _ _     => trivial,
--    introFstIsFun    := λ _ {_} _ => trivial,
--    introSndIsFun    := λ {_} _ _ => trivial }
--
--  instance hasInternalProducts : HasInternalProducts unit :=
--  { introFstFunIsFun := λ _ _ => trivial,
--    introSndFunIsFun := λ _ _ => trivial }
--
--  instance hasExternalUnitType : HasExternalUnitType unit :=
--  { unitIntroIsFun := λ _ => trivial }
--
--  def unitEmbed (φ : unit) : TypeEmbedding unit φ :=
--  { α     := UnitType,
--    equiv := Equiv.refl True }
--
--  instance hasInternalUnitType : HasInternalUnitType unit :=
--  { embed := unitEmbed }
--
--  def Rel (α : Sort u) : GeneralizedRelation α unit := λ _ _ => UnitType
--
--  instance Rel.isEquivalence (α : Sort u) : IsEquivalence (Rel α) :=
--  { refl  := λ _ => unitInstance,
--    trans := unitInstance,
--    symm  := unitInstance }
--
--  class HasUnitEquivalences (U : Universe.{u}) where
--  (Equiv (α : U)              : GeneralizedRelation ⌈α⌉ unit)
--  [equivIsEquivalence (α : U) : IsEquivalence (Equiv α)]
--
--  instance hasUnitInstanceEquivalences (U : Universe.{u}) [HasUnitEquivalences U] :
--    HasInstanceEquivalences U :=
--  ⟨unit, λ α => unit.Rel ⌈α⌉⟩
--
--  instance hasUnitEquivalence : HasUnitEquivalences unit := ⟨λ _ => unit.Rel True⟩
--
--  instance hasEquivCongr : HasEquivCongr unit :=
--  { equivCongrArg := λ _ => unitFunctor UnitType UnitType,
--    equivCongrFun := λ _ => unitFunctor UnitType UnitType }
--
--  instance hasNaturalEquivalences : HasNaturalEquivalences unit :=
--  { equivHasInstEquivs := hasUnitInstanceEquivalences unit,
--    isNat              := λ _ _ _ _ => trivial }
--
--  section Morphisms
--
--    variable {α : Sort u} {V : Universe.{v}} [HasEmbeddedFunctors V] [HasUnitEquivalences V] (R : GeneralizedRelation α V)
--
--    variable [HasLinearFunOp V] [HasTrans R]
--
--    instance isCompositionRelation : IsCompositionRelation R :=
--    { assoc := trivial }
--
--    variable [HasRefl R]
--
--    instance isMorphismRelation [IsPreorder R] : IsMorphismRelation R :=
--    { leftId  := trivial,
--      rightId := trivial }
--
--    variable [HasSubLinearFunOp V] [HasNonLinearFunOp V] [HasInternalEquivalences V] [HasSymm R]
--
--    instance isIsomorphismRelation [IsEquivalence R] : IsIsomorphismRelation R :=
--    { leftInv  := trivial,
--      rightInv := trivial }
--
--  end Morphisms
--
--  section Functors
--
--    variable {α : Sort u} {V : Universe.{v}} {W : Universe.{w}}
--             [HasEmbeddedFunctors V] [HasInternalEquivalences V] [HasEmbeddedFunctors W] [HasInternalEquivalences W]
--             [HasUnitEquivalences W] [HasExternalFunctor V W]
--             (R : GeneralizedRelation α V) (S : GeneralizedRelation α W)
--             [IsEquivalence R] [IsEquivalence S]
--             (F : BaseFunctor R S)
--
--    instance isReflFunctor  : IsReflFunctor  R S F := ⟨λ _   => trivial⟩
--    instance isSymmFunctor  : IsSymmFunctor  R S F := ⟨λ _   => trivial⟩
--    instance isTransFunctor : IsTransFunctor R S F := ⟨λ _ _ => trivial⟩
--
--    instance isPreorderFunctor    : IsPreorderFunctor    R S F := ⟨⟩
--    instance isEquivalenceFunctor : IsEquivalenceFunctor R S F := ⟨⟩
--
--  end Functors

end unit



def sort : Universe.{u} := ⟨Sort u⟩
@[reducible] def prop := sort.{0}
@[reducible] def type := sort.{1}

namespace sort

  instance hasExternalFunctor {U : Universe.{u}} (α : U) (β : sort.{v}) : HasExternalFunctor.{u, v, 0} α β :=
  ⟨λ _ => True⟩

  def toExtFun   {U : Universe.{u}} {α : U} {β : sort.{v}} (f : α →  β) : α ⟶' β := ⟨f, trivial⟩
  def fromExtFun {U : Universe.{u}} {α : U} {β : sort.{v}} (F : α ⟶' β) : α →  β := F.f

  @[simp] theorem fromToExtFun {U : Universe.{u}} {α : U} {β : sort.{v}} (f : α → β) :
    fromExtFun (toExtFun f) = f :=
  rfl

  @[simp] theorem toFromExtFun {U : Universe.{u}} {α : U} {β : sort.{v}} (F : α ⟶' β) :
    toExtFun (fromExtFun F) = F := match F with
  | ⟨_, _⟩ => rfl

  def funEquiv (α β : sort.{u}) : (α → β) ≃ (α ⟶' β) :=
  { toFun    := toExtFun     (U := sort.{u}),
    invFun   := fromExtFun   (U := sort.{u}),
    leftInv  := fromToExtFun (U := sort.{u}),
    rightInv := toFromExtFun (U := sort.{u}) }

  instance hasEmbeddedFunctorType (α β : sort.{u}) : HasEmbeddedType sort.{u} (α ⟶' β) :=
  { α := α → β,
    h := funEquiv α β }

  instance hasEmbeddedFunctor (α β : sort.{u}) : HasEmbeddedFunctor α β := ⟨⟩
  instance hasEmbeddedFunctors : HasEmbeddedFunctors sort.{u} := ⟨⟩

  instance hasLinearFunOp : HasLinearFunOp sort.{u} :=
  { defIdFun         := λ _     => trivial,
    defAppFun        := λ _ _   => trivial,
    defAppFunFun     := λ _ _   => trivial,
    defCompFun       := λ _ _   => trivial,
    defCompFunFun    := λ _ _   => trivial,
    defCompFunFunFun := λ _ _ _ => trivial }

  instance hasAffineFunOp : HasAffineFunOp sort.{u} :=
  { defConstFun    := λ _ _ _ => trivial,
    defConstFunFun := λ _ _   => trivial }

  instance hasFullFunOp : HasFullFunOp sort.{u} :=
  { defDupFun    := λ _   => trivial,
    defDupFunFun := λ _ _ => trivial }

  instance hasFunOp : HasFunOp sort.{u} := ⟨⟩

end sort

namespace prop

  instance hasExternalEquivalence (p q : prop) : HasExternalEquivalence p q := ⟨λ _ _ => True⟩

  @[reducible] def toExtEquiv {p q : prop} (h : p ↔ q) : p ⟷' q :=
  ⟨sort.toExtFun h.mp, sort.toExtFun h.mpr, trivial⟩

  @[reducible] def fromExtEquiv {p q : prop} (E : p ⟷' q) : p ↔ q :=
  ⟨E.toFun.f, E.invFun.f⟩

  @[simp] theorem fromToExtEquiv {p q : prop} (h : p ↔ q) :
    fromExtEquiv (toExtEquiv h) = h :=
  rfl

  @[simp] theorem toFromExtEquiv {p q : prop} (E : p ⟷' q) :
    toExtEquiv (fromExtEquiv E) = E := match E with
  | ⟨toFun, invFun, _⟩ => by simp; exact ⟨sort.toFromExtFun toFun, sort.toFromExtFun invFun, HEq.rfl⟩

  def equivEquiv (p q : prop) : (p ↔ q) ≃ (p ⟷' q) :=
  { toFun    := toExtEquiv,
    invFun   := fromExtEquiv,
    leftInv  := fromToExtEquiv,
    rightInv := toFromExtEquiv }

  instance hasEmbeddedEquivType (p q : prop) : HasEmbeddedType prop (p ⟷' q) :=
  { α := p ↔ q,
    h := equivEquiv p q }

  instance hasEmbeddedEquivalence (p q : prop) : HasEmbeddedEquivalence p q := ⟨⟩
  instance hasEmbeddedEquivalences : HasEmbeddedEquivalences prop := ⟨⟩

  instance hasFunctorialEquivalences : HasFunctorialEquivalences prop :=
  { defToFunFun  := λ _ _ => trivial,
    defInvFunFun := λ _ _ => trivial }

  instance hasEquivOp : HasEquivOp prop :=
  { defIdEquiv         := λ _     => trivial,
    defCompEquiv       := λ _ _   => trivial,
    defCompEquivFun    := λ _ _   => trivial,
    defCompEquivFunFun := λ _ _ _ => trivial,
    defInvEquiv        := λ _     => trivial,
    defInvEquivFun     := λ _ _   => trivial,
    defInvEquivEquiv   := λ _ _   => trivial }

--  def prodEquiv (p q : prop) : (p ∧ q) ≃ (p ⊓'' q) :=
--  { toFun    := λ h => ⟨h.left, h.right⟩,
--    invFun   := λ P => ⟨P.fst, P.snd⟩,
--    leftInv  := λ _ => rfl,
--    rightInv := λ ⟨_, _⟩ => rfl }
--
--  def prodEmbed (PU : HasExternalProducts.productUniverse prop prop) : TypeEmbedding prop PU :=
--  { α     := PU.α ∧ PU.β,
--    equiv := prodEquiv PU.α PU.β }
--
--  instance : HasEmbeddedUniverse prop (HasExternalProducts.productUniverse prop prop) :=
--  { embed := prodEmbed }
--
--  instance hasFunctorialExternalProducts : HasFunctorialExternalProducts prop prop :=
--  { fstIsFun         := λ _ _     => trivial,
--    sndIsFun         := λ _ _     => trivial,
--    introFstIsFun    := λ _ {_} _ => trivial,
--    introSndIsFun    := λ {_} _ _ => trivial }
--
--  instance hasInternalProducts : HasInternalProducts prop :=
--  { introFstFunIsFun := λ _ _ => trivial,
--    introSndFunIsFun := λ _ _ => trivial }
--
--  instance hasExternalEmptyType : HasExternalEmptyType prop :=
--  { emptyElimIsFun := λ _ => trivial }
--
--  def emptyEmbed (φ : emptyTypeUniverse) : TypeEmbedding prop φ :=
--  { α     := False,
--    equiv := Equiv.refl False }
--
--  instance : HasEmbeddedUniverse prop emptyTypeUniverse :=
--  { embed := emptyEmbed }
--
--  instance hasInternalEmptyType : HasInternalEmptyType prop := ⟨⟩
--
--  instance hasClassicalLogic : HasClassicalLogic prop :=
--  { byContradiction := @Classical.byContradiction }
--
--  instance hasExternalUnitType : HasExternalUnitType prop :=
--  { unitIntroIsFun := λ _ => trivial }
--
--  def unitEmbed (φ : unit) : TypeEmbedding prop φ :=
--  { α     := True,
--    equiv := Equiv.refl True }
--
--  instance : HasEmbeddedUniverse prop unit :=
--  { embed := unitEmbed }
--
--  instance hasInternalUnitType : HasInternalUnitType prop := ⟨⟩
--
--  -- Every equivalence relation can trivially be converted to an instance of `IsEquivalence`.
--  instance relEquiv {α : Sort u} {R : GeneralizedRelation α prop} (e : Equivalence R) : IsEquivalence R :=
--  { refl  := e.refl,
--    trans := e.trans,
--    symm  := ⟨e.symm, e.symm⟩ }
--
--  namespace relEquiv
--
--    instance eq     (α : Sort u)                : IsEquivalence (V := prop) (@Eq α) := relEquiv Eq.isEquivalence
--    instance setoid (α : Sort u) [s : Setoid α] : IsEquivalence (V := prop) s.r     := relEquiv s.iseqv
--
--  end relEquiv
--
--  instance hasUnitEquivalences : unit.HasUnitEquivalences prop := ⟨unit.Rel⟩
--
--  instance hasEquivCongr : HasEquivCongr prop :=
--  { equivCongrArg := λ _ => unit.unitFunctor (U := unit) ⟨⟩ ⟨⟩,
--    equivCongrFun := λ _ => unit.unitFunctor (U := unit) ⟨⟩ ⟨⟩ }
--
--  instance hasNaturalEquivalences : HasNaturalEquivalences prop :=
--  { equivHasInstEquivs := unit.hasUnitInstanceEquivalences unit,
--    isNat              := λ _ _ _ _ => trivial }
--
--  section NaturalTransformations
--
--    variable {α : Sort u} {β : Sort v} {V : Universe.{v}}
--             [HasEmbeddedFunctors V] [HasExternalFunctor V prop]
--             (R : GeneralizedRelation α V) (S : GeneralizedRelation β prop) [HasTrans S]
--             {mF mG : α → β} (F : MappedBaseFunctor R S mF) (G : MappedBaseFunctor R S mG)
--
--    instance isNatural (n : ∀ a, S (mF a) (mG a)) : IsNatural R S F G n := ⟨λ _ => trivial⟩
--
--    def natEquiv : (∀ a, S (mF a) (mG a)) ≃ NaturalQuantification R S F G :=
--    { toFun    := λ n => ⟨n⟩,
--      invFun   := λ N => N.n,
--      leftInv  := λ _ => rfl,
--      rightInv := λ { n := _, isNatural := ⟨_⟩ } => rfl }
--
--    --instance hasIntNat : HasInternalNaturalQuantification R S F G :=
--    --{ Nat      := ∀ a, S (mF a) (mG a),
--    --  natEquiv := natEquiv R S F G }
--
--  end NaturalTransformations
--
--  --instance hasNat {U₁ U₂ V : Universe} [HasExternalFunctor U₁ U₂] [HasExternalFunctor V prop] :
--  --  HasNaturalQuantification U₁ U₂ V prop :=
--  --{ hasNat := λ {α β} R S {h mF mG} F G => hasIntNat R S F G }
--
--  instance hasInstanceIsomorphisms : HasInstanceIsomorphisms prop :=
--  { equivIsIso := λ p => unit.isIsomorphismRelation (unit.Rel p) }

end prop

namespace type

  class DefEquiv {α β : type} (toFun : α ⟶' β) (invFun : β ⟶' α) : Prop where
  (leftInv  : ∀ a, invFun (toFun a) = a)
  (rightInv : ∀ b, toFun (invFun b) = b)

  instance hasExternalEquivalence (α β : type) : HasExternalEquivalence α β := ⟨DefEquiv⟩

  @[reducible] def toDefEquiv {α β : type} (e : ⌈α⌉ ≃ ⌈β⌉) : α ⟷'[sort.toExtFun e.toFun, sort.toExtFun e.invFun] β :=
  ⟨e.leftInv, e.rightInv⟩

  theorem defEquiv.unique {α β : type} {toFun : α ⟶' β} {invFun : β ⟶' α} (h₁ h₂ : α ⟷'[toFun,invFun] β) :
    h₁ = h₂ :=
  proofIrrel _ _

  theorem defEquiv.unique' {α β : type} {toFun₁ toFun₂ : α ⟶' β} {invFun₁ invFun₂ : β ⟶' α}
                           (hToFun : toFun₁ = toFun₂) (hInvFun : invFun₁ = invFun₂)
                           (h₁ : α ⟷'[toFun₁,invFun₁] β) (h₂ : α ⟷'[toFun₂,invFun₂] β) :
    h₁ ≅ h₂ :=
  heq_of_eqRec_eq (hToFun ▸ hInvFun ▸ rfl) (proofIrrel _ _)

  @[reducible] def invDefEquiv {α β : type} {toFun : α ⟶' β} {invFun : β ⟶' α} (h : α ⟷'[toFun,invFun] β) :
    β ⟷'[invFun,toFun] α :=
  ⟨h.rightInv, h.leftInv⟩

  @[reducible] def toExtEquiv {α β : type} (e : Equiv α β) : α ⟷' β :=
  ⟨sort.toExtFun e.toFun, sort.toExtFun e.invFun, toDefEquiv e⟩

  @[reducible] def fromExtEquiv {α β : type} (E : α ⟷' β) : Equiv α β :=
  ⟨E.toFun.f, E.invFun.f, E.E.leftInv, E.E.rightInv⟩

  @[simp] theorem fromToExtEquiv {α β : type} (e : Equiv α β) :
    fromExtEquiv (toExtEquiv e) = e := match e with
  | ⟨_, _, _, _⟩ => rfl

  @[simp] theorem toFromExtEquiv {α β : type} (E : α ⟷' β) :
    toExtEquiv (fromExtEquiv E) = E := match E with
  | ⟨toFun, invFun, _⟩ => by simp; exact ⟨sort.toFromExtFun toFun, sort.toFromExtFun invFun,
                                          defEquiv.unique' (sort.toFromExtFun toFun) (sort.toFromExtFun invFun) _ _⟩

  def equivEquiv (α β : type) : Equiv α β ≃ (α ⟷' β) :=
  { toFun    := toExtEquiv,
    invFun   := fromExtEquiv,
    leftInv  := fromToExtEquiv,
    rightInv := toFromExtEquiv }

  instance hasEmbeddedEquivType (α β : type) : HasEmbeddedType type (α ⟷' β) :=
  { α := Equiv α β,
    h := equivEquiv α β }

  instance hasEmbeddedEquivalence (α β : type) : HasEmbeddedEquivalence α β := ⟨⟩
  instance hasEmbeddedEquivalences : HasEmbeddedEquivalences type := ⟨⟩

  instance hasFunctorialEquivalences : HasFunctorialEquivalences type :=
  { defToFunFun  := λ _ _ => trivial,
    defInvFunFun := λ _ _ => trivial }

  instance hasEquivOp : HasEquivOp type :=
  { defIdEquiv         := λ α     => toDefEquiv (Equiv.refl α),
    defCompEquiv       := λ E F   => toDefEquiv (Equiv.trans E F),
    defCompEquivFun    := λ _ _   => trivial,
    defCompEquivFunFun := λ _ _ _ => trivial,
    defInvEquiv        := λ E     => toDefEquiv (Equiv.symm E),
    defInvEquivFun     := λ _ _   => trivial,
    defInvEquivEquiv   := λ _ _   => ⟨Equiv.symm_symm, Equiv.symm_symm⟩ }

--  def prodEquiv (α β : type) : Prod α β ≃ (α ⊓'' β) :=
--  { toFun    := λ p => ⟨p.fst, p.snd⟩,
--    invFun   := λ P => ⟨P.fst, P.snd⟩,
--    leftInv  := λ ⟨_, _⟩ => rfl,
--    rightInv := λ ⟨_, _⟩ => rfl }
--
--  def prodEmbed (φ : HasExternalProducts.productUniverse type type) : TypeEmbedding type φ :=
--  { α     := Prod φ.α φ.β,
--    equiv := prodEquiv φ.α φ.β }
--
--  instance : HasEmbeddedUniverse type (HasExternalProducts.productUniverse type type) :=
--  { embed := prodEmbed }
--
--  instance hasFunctorialExternalProducts : HasFunctorialExternalProducts type type :=
--  { fstIsFun         := λ _ _     => trivial,
--    sndIsFun         := λ _ _     => trivial,
--    introFstIsFun    := λ _ {_} _ => trivial,
--    introSndIsFun    := λ {_} _ _ => trivial }
--
--  instance hasInternalProducts : HasInternalProducts type :=
--  { introFstFunIsFun := λ _ _ => trivial,
--    introSndFunIsFun := λ _ _ => trivial }
--
--  instance hasExternalEmptyType : HasExternalEmptyType type :=
--  { emptyElimIsFun := λ _ => trivial }
--
--  def emptyEquiv : Empty ≃ False :=
--  { toFun    := λ e => (by induction e),
--    invFun   := False.elim,
--    leftInv  := λ e => (by induction e),
--    rightInv := λ _ => proofIrrel _ _ }
--
--  def emptyEmbed (φ : emptyTypeUniverse) : TypeEmbedding type φ :=
--  { α     := Empty,
--    equiv := emptyEquiv }
--
--  instance : HasEmbeddedUniverse type emptyTypeUniverse :=
--  { embed := emptyEmbed }
--
--  instance hasInternalEmptyType : HasInternalEmptyType type := ⟨⟩
--
--  instance hasExternalUnitType : HasExternalUnitType type :=
--  { unitIntroIsFun := λ _ => trivial }
--
--  def unitEquiv : Unit ≃ True :=
--  { toFun    := λ _  => trivial,
--    invFun   := λ _  => Unit.unit,
--    leftInv  := λ ⟨⟩ => rfl,
--    rightInv := λ _  => proofIrrel _ _ }
--
--  def unitEmbed (φ : unit) : TypeEmbedding type φ :=
--  { α     := Unit,
--    equiv := unitEquiv }
--
--  instance : HasEmbeddedUniverse type unit :=
--  { embed := unitEmbed }
--
--  instance hasInternalUnitType : HasInternalUnitType type := ⟨⟩
--
--  instance hasGeneralizedProperties : HasGeneralizedProperties.{u, 0, 0} sort.{u} prop :=
--  { IsProp      := λ _   => True,
--    constIsProp := λ _ _ => trivial }
--
--  instance hasExternalSubtypes : HasExternalSubtypes.{1, 0, 0} type := ⟨prop⟩
--
--  def subtypeEquiv (S : HasExternalSubtypes.BundledSet type) : Subtype S.P.P ≃ HasExternalSubtypes.Subtype S :=
--  { toFun    := λ a => ⟨a.val, a.property⟩,
--    invFun   := λ a => ⟨a.val, a.property⟩,
--    leftInv  := λ ⟨_, _⟩ => rfl,
--    rightInv := λ ⟨_, _⟩ => rfl }
--
--  def subtypeEmbed (φ : HasExternalSubtypes.subtypeUniverse type) : TypeEmbedding type φ :=
--  { α     := Subtype φ.P.P,
--    equiv := subtypeEquiv φ }
--
--  instance : HasEmbeddedUniverse type (HasExternalSubtypes.subtypeUniverse type) :=
--  { embed := subtypeEmbed }
--
--  instance hasFunctorialExternalSubtypes : HasFunctorialExternalSubtypes type :=
--  { valIsFun := λ _ => trivial }
--
--  instance hasInternalSubtypes : HasInternalSubtypes type := ⟨⟩
--
--  instance hasInstanceEquivalences : HasInstanceEquivalences type := ⟨prop, @Eq⟩
--
--  instance hasEquivCongr : HasEquivCongr type :=
--  { equivCongrArg := λ F => sort.toBundledFunctor (congrArg F.f),
--    equivCongrFun := λ a => sort.toBundledFunctor (λ h => congrFun h a) }
--
--  instance hasNaturalEquivalences : HasNaturalEquivalences type :=
--  { equivHasInstEquivs := unit.hasUnitInstanceEquivalences prop,
--    isNat              := λ _ _ _ _ => trivial }
--
--  instance hasInstanceIsomorphisms : HasInstanceIsomorphisms type :=
--  { equivIsIso := λ α => unit.isIsomorphismRelation (V := prop) (@Eq α) }

end type
