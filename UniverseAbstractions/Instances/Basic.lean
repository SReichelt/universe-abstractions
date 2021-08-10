import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors

import mathlib4_experiments.CoreExt
import mathlib4_experiments.Data.Equiv.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w



instance unitHasInstances : HasInstances.{0, 1} Unit := ⟨λ _ => True⟩

def unit : Universe.{0} := ⟨Unit⟩

namespace unit

  instance hasFunctoriality {U : Universe.{u}} (α : U) (β : unit) : HasFunctoriality.{u, 0, 0} α β :=
  ⟨λ _ => True⟩

  def funEquiv (α β : unit) : True ≃ (α ⟶' β) :=
  { toFun    := λ _ => ⟨λ _ => trivial, trivial⟩,
    invFun   := λ _ => trivial,
    leftInv  := λ _ => proofIrrel _ _,
    rightInv := λ ⟨_, _⟩ => rfl }

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

--  instance hasExternalEquivalences : HasExternalEquivalences.{0, 0, 0, 0} unit unit := ⟨λ _ _ => True⟩
--
--  @[reducible] def unitEquivalence (α : unit) (β : unit) : α ⟷'' β :=
--  ⟨unitFunctor α β, unitFunctor β α, trivial⟩
--
--  @[simp] theorem unitEquivalenceIsUnique {α : unit} {β : unit} (E : α ⟷'' β) :
--    E = unitEquivalence α β := match E with
--  | ⟨_, _, _⟩ => by simp; exact ⟨rfl, rfl, HEq.rfl⟩
--
--  instance hasIdEquiv   : HasIdEquiv   unit           := ⟨λ _   => trivial⟩
--  instance hasCompEquiv : HasCompEquiv unit unit unit := ⟨λ _ _ => trivial⟩
--  instance hasInvEquiv  : HasInvEquiv  unit unit      := ⟨λ _   => trivial⟩
--
--  def equivEquiv (α β : unit) : True ≃ (α ⟷'' β) :=
--  { toFun    := λ _ => unitEquivalence α β,
--    invFun   := λ _ => trivial,
--    leftInv  := λ _ => proofIrrel _ _,
--    rightInv := λ _ => by simp }
--
--  def equivEmbed (φ : HasExternalEquivalences.equivalenceUniverse unit unit) : TypeEmbedding unit φ :=
--  { α     := UnitType,
--    equiv := equivEquiv φ.α φ.β }
--
--  instance : HasEmbeddedUniverse unit (HasExternalEquivalences.equivalenceUniverse unit unit) :=
--  { embed := equivEmbed }
--
--  instance hasFunctorialExternalEquivalences : HasFunctorialExternalEquivalences unit unit :=
--  { toFunIsFun  := λ _ _ => trivial,
--    invFunIsFun := λ _ _ => trivial }
--
--  instance hasInternalEquivalences : HasInternalEquivalences unit := ⟨⟩
--
--  instance hasEquivOp : HasEquivOp unit :=
--  { compEquivIsFun    := λ _ _   => trivial,
--    compEquivFunIsFun := λ _ _ _ => trivial,
--    invEquivIsFun     := λ _ _   => trivial,
--    invEquivIsEquiv   := λ _ _   => trivial }
--
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
--             [HasUnitEquivalences W] [HasExternalFunctors V W]
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

  instance hasFunctoriality {U : Universe.{u}} (α : U) (β : sort.{v}) : HasFunctoriality.{u, v, 0} α β :=
  ⟨λ _ => True⟩

  def funEquiv (α β : sort.{u}) : (α → β) ≃ (α ⟶' β) :=
  { toFun    := λ f => ⟨f, trivial⟩,
    invFun   := λ F => F.f,
    leftInv  := λ f => rfl,
    rightInv := λ ⟨_, _⟩ => rfl }

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

--namespace prop
--
--  instance hasExternalEquivalences : HasExternalEquivalences prop prop := ⟨λ _ _ => True⟩
--
--  @[reducible] def toBundledEquivalence {p q : prop} (h : p ↔ q) : p ⟷'' q :=
--  ⟨sort.toBundledFunctor h.mp, sort.toBundledFunctor h.mpr, trivial⟩
--
--  @[reducible] def fromBundledEquivalence {p q : prop} (E : p ⟷'' q) : p ↔ q :=
--  ⟨E.toFun.f, E.invFun.f⟩
--
--  theorem fromToBundledEquivalence {p q : prop} (h : p ↔ q) :
--    fromBundledEquivalence (toBundledEquivalence h) = h :=
--  rfl
--
--  theorem toFromBundledEquivalence {p q : prop} (E : p ⟷'' q) :
--    toBundledEquivalence (fromBundledEquivalence E) = E := match E with
--  | ⟨toFun, invFun, _⟩ => by simp; exact ⟨sort.toFromBundledFunctor toFun, sort.toFromBundledFunctor invFun, HEq.rfl⟩
--
--  instance hasIdEquiv   : HasIdEquiv   prop           := ⟨λ _   => trivial⟩
--  instance hasCompEquiv : HasCompEquiv prop prop prop := ⟨λ _ _ => trivial⟩
--  instance hasInvEquiv  : HasInvEquiv  prop prop      := ⟨λ _   => trivial⟩
--
--  def equivEquiv (p q : prop) : (p ↔ q) ≃ (p ⟷'' q) :=
--  { toFun    := toBundledEquivalence,
--    invFun   := fromBundledEquivalence,
--    leftInv  := fromToBundledEquivalence,
--    rightInv := toFromBundledEquivalence }
--
--  def equivEmbed (φ : HasExternalEquivalences.equivalenceUniverse prop prop) : TypeEmbedding prop φ :=
--  { α     := φ.α ↔ φ.β,
--    equiv := equivEquiv φ.α φ.β }
--
--  instance : HasEmbeddedUniverse prop (HasExternalEquivalences.equivalenceUniverse prop prop) :=
--  { embed := equivEmbed }
--
--  instance hasFunctorialExternalEquivalences : HasFunctorialExternalEquivalences prop prop :=
--  { toFunIsFun  := λ _ _ => trivial,
--    invFunIsFun := λ _ _ => trivial }
--
--  instance hasInternalEquivalences : HasInternalEquivalences prop := ⟨⟩
--
--  instance hasEquivOp : HasEquivOp prop :=
--  { compEquivIsFun    := λ _ _   => trivial,
--    compEquivFunIsFun := λ _ _ _ => trivial,
--    invEquivIsFun     := λ _ _   => trivial,
--    invEquivIsEquiv   := λ _ _   => trivial }
--
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
--             [HasEmbeddedFunctors V] [HasExternalFunctors V prop]
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
--  --instance hasNat {U₁ U₂ V : Universe} [HasExternalFunctors U₁ U₂] [HasExternalFunctors V prop] :
--  --  HasNaturalQuantification U₁ U₂ V prop :=
--  --{ hasNat := λ {α β} R S {h mF mG} F G => hasIntNat R S F G }
--
--  instance hasInstanceIsomorphisms : HasInstanceIsomorphisms prop :=
--  { equivIsIso := λ p => unit.isIsomorphismRelation (unit.Rel p) }
--
--end prop
--
--namespace type
--
--  class IsEquiv {α β : type} (toFun : α ⟶'' β) (invFun : β ⟶'' α) where
--  (leftInv  : ∀ a, invFun (toFun a) = a)
--  (rightInv : ∀ b, toFun (invFun b) = b)
--
--  instance hasExternalEquivalences : HasExternalEquivalences type type := ⟨IsEquiv⟩
--
--  @[reducible] def isEquivalence {α β : type} (e : Equiv α β) :
--    IsEquiv (sort.toBundledFunctor e.toFun) (sort.toBundledFunctor e.invFun) :=
--  ⟨e.leftInv, e.rightInv⟩
--
--  theorem isEquivalenceIsUnique {α β : type} {e : Equiv α β} (h : IsEquiv (sort.toBundledFunctor e.toFun) (sort.toBundledFunctor e.invFun)) :
--    h = isEquivalence e := match h with
--  | ⟨_, _⟩ => sorry -- by proof irrelevance
--
--  @[reducible] def invIsEquivalence {α β : type} {toFun : α ⟶'' β} {invFun : β ⟶'' α} (h : IsEquiv toFun invFun) :
--    IsEquiv invFun toFun :=
--  ⟨h.rightInv, h.leftInv⟩
--
--  @[reducible] def toBundledEquivalence {α β : type} (e : Equiv α β) : α ⟷'' β :=
--  ⟨sort.toBundledFunctor e.toFun, sort.toBundledFunctor e.invFun, isEquivalence e⟩
--
--  @[reducible] def fromBundledEquivalence {α β : type} (E : α ⟷'' β) : Equiv α β :=
--  ⟨E.toFun.f, E.invFun.f, E.isEquiv.leftInv, E.isEquiv.rightInv⟩
--
--  theorem fromToBundledEquivalence {α β : type} (e : Equiv α β) :
--    fromBundledEquivalence (toBundledEquivalence e) = e := match e with
--  | ⟨_, _, _, _⟩ => rfl
--
--  theorem toFromBundledEquivalence {α β : type} (E : α ⟷'' β) :
--    toBundledEquivalence (fromBundledEquivalence E) = E := match E with
--  | ⟨toFun, invFun, _⟩ => by simp; exact ⟨sort.toFromBundledFunctor toFun, sort.toFromBundledFunctor invFun,
--                                          sorry⟩ -- by `isEquivalenceIsUnique`
--
--  instance hasIdEquiv   : HasIdEquiv   type           := ⟨λ α   => isEquivalence (Equiv.refl α)⟩
--  instance hasCompEquiv : HasCompEquiv type type type := ⟨λ E F => isEquivalence (Equiv.trans (fromBundledEquivalence E) (fromBundledEquivalence F))⟩
--  instance hasInvEquiv  : HasInvEquiv  type type      := ⟨λ E   => invIsEquivalence E.isEquiv⟩
--
--  def equivEquiv (α β : type) : Equiv α β ≃ (α ⟷'' β) :=
--  { toFun    := toBundledEquivalence,
--    invFun   := fromBundledEquivalence,
--    leftInv  := fromToBundledEquivalence,
--    rightInv := toFromBundledEquivalence }
--
--  def equivEmbed (φ : HasExternalEquivalences.equivalenceUniverse type type) : TypeEmbedding type φ :=
--  { α     := Equiv φ.α φ.β,
--    equiv := equivEquiv φ.α φ.β }
--
--  instance : HasEmbeddedUniverse type (HasExternalEquivalences.equivalenceUniverse type type) :=
--  { embed := equivEmbed }
--
--  instance hasFunctorialExternalEquivalences : HasFunctorialExternalEquivalences type type :=
--  { toFunIsFun  := λ _ _ => trivial,
--    invFunIsFun := λ _ _ => trivial }
--
--  instance hasInternalEquivalences : HasInternalEquivalences type := ⟨⟩
--
--  instance hasEquivOp : HasEquivOp type :=
--  { compEquivIsFun    := λ _ _   => ⟨⟩,
--    compEquivFunIsFun := λ _ _ _ => ⟨⟩,
--    invEquivIsFun     := λ _ _   => ⟨⟩,
--    invEquivIsEquiv   := λ α β   => ⟨@Equiv.symm_symm α β, @Equiv.symm_symm β α⟩ }
--
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
--
--end type
