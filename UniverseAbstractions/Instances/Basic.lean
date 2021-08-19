import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Singletons
import UniverseAbstractions.Axioms.Universe.Products
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
    F = unitFunctor :=
  by induction F; rfl

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

  instance hasEmbeddedTopType : HasEmbeddedType unit True :=
  { α := (),
    h := Equiv.refl True }

  instance hasEmbeddedTop : HasEmbeddedTop unit := ⟨⟩

  instance hasFunctorialTop : HasFunctorialTop unit :=
  { defElimFun    := λ _ => trivial,
    defElimFunFun := λ _ => trivial }

  @[reducible] def unitProduct {α β : unit} : α ⊓' β :=
  ⟨trivial, trivial⟩

  @[simp] theorem unitProductIsUnique {α β : unit} (P : α ⊓' β) :
    P = unitProduct :=
  by induction P; rfl

  def prodEquiv (α β : unit) : True ≃ (α ⊓' β) :=
  { toFun    := λ _ => unitProduct,
    invFun   := λ _ => trivial,
    leftInv  := λ _ => proofIrrel _ _,
    rightInv := λ _ => by simp }

  instance hasEmbeddedProductType (α β : unit) : HasEmbeddedType unit (α ⊓' β) :=
  { α := (),
    h := prodEquiv α β }

  instance hasEmbeddedProduct (α β : unit) : HasEmbeddedProduct α β := ⟨⟩
  instance hasEmbeddedProducts : HasEmbeddedProducts unit := ⟨⟩

  instance hasFunctorialProducts : HasFunctorialProducts unit :=
  { defIntroFun    := λ _ _   => trivial,
    defIntroFunFun := λ _ _   => trivial,
    defElimFun     := λ _     => trivial,
    defElimFunFun  := λ _ _ _ => trivial }

  instance hasExternalEquivalence (α β : unit) : HasExternalEquivalence.{0, 0, 0, 0} α β := ⟨λ _ _ => True⟩

  @[reducible] def unitEquivalence {α β : unit} : α ⟷' β :=
  ⟨unitFunctor, unitFunctor, trivial⟩

  @[simp] theorem unitEquivalence.unique {α β : unit} {E : α ⟷' β} :
    E = unitEquivalence :=
  by induction E; simp; exact HEq.rfl

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
  { defElimFun  := λ _ _ => trivial }

  instance hasEquivOp : HasEquivOp unit :=
  { defIdEquiv         := λ _     => trivial,
    defCompEquiv       := λ _ _   => trivial,
    defCompEquivFun    := λ _ _   => trivial,
    defCompEquivFunFun := λ _ _ _ => trivial,
    defInvEquiv        := λ _     => trivial,
    defInvEquivFun     := λ _ _   => trivial }

  instance hasLinearCommonEquivalences : HasLinearCommonEquivalences unit :=
  { defFunDomainEquiv      := λ _ _   => trivial,
    defFunDomainEquivFun   := λ _ _ _ => trivial,
    defFunCodomainEquiv    := λ _ _   => trivial,
    defFunCodomainEquivFun := λ _ _ _ => trivial,
    defSwapFunFunEquiv     := λ _ _ _ => trivial,
    defTopElimEquiv        := λ _     => trivial,
    defProdElimFunEquiv    := λ _ _ _ => trivial,
    defProdFstEquiv        := λ _ _   => trivial,
    defProdFstEquivFun     := λ _ _ _ => trivial,
    defProdSndEquiv        := λ _ _   => trivial,
    defProdSndEquivFun     := λ _ _ _ => trivial,
    defProdCommEquiv       := λ _ _   => trivial,
    defProdAssocEquiv      := λ _ _ _ => trivial,
    defProdTopEquiv        := λ _     => trivial,
    defCompEquivEquiv      := λ _ _   => trivial,
    defCompEquivEquivFun   := λ _ _ _ => trivial,
    defInvEquivEquiv       := λ _ _   => trivial }

  instance hasNonLinearCommonEquivalences : HasNonLinearCommonEquivalences unit :=
  { defProdDistrEquiv := λ _ _ _ => trivial }

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
    toExtFun (fromExtFun F) = F :=
  by induction F; rfl

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

  instance hasEmbeddedTopType : HasEmbeddedType prop True :=
  { α := True,
    h := Equiv.refl True }

  instance hasEmbeddedTop : HasEmbeddedTop prop := ⟨⟩

  instance hasFunctorialTop : HasFunctorialTop prop :=
  { defElimFun    := λ _ => trivial,
    defElimFunFun := λ _ => trivial }

  instance hasEmbeddedBotType : HasEmbeddedType prop False :=
  { α := False,
    h := Equiv.refl False }

  instance hasEmbeddedBot : HasEmbeddedBot prop := ⟨⟩

  instance hasFunctorialBot : HasFunctorialBot prop :=
  { defElimFun := λ _ => trivial }

  instance hasClassicalLogic : HasClassicalLogic prop :=
  { byContradictionFun := @Classical.byContradiction }

  def prodEquiv (p q : prop) : (p ∧ q) ≃ (p ⊓' q) :=
  { toFun    := λ h => ⟨h.left, h.right⟩,
    invFun   := λ P => ⟨P.fst, P.snd⟩,
    leftInv  := λ _ => rfl,
    rightInv := λ ⟨_, _⟩ => rfl }

  instance hasEmbeddedProductType (p q : prop) : HasEmbeddedType prop (p ⊓' q) :=
  { α := p ∧ q,
    h := prodEquiv p q }

  instance hasEmbeddedProduct (p q : prop) : HasEmbeddedProduct p q := ⟨⟩
  instance hasEmbeddedProducts : HasEmbeddedProducts prop := ⟨⟩

  instance hasFunctorialProducts : HasFunctorialProducts prop :=
  { defIntroFun    := λ _ _   => trivial,
    defIntroFunFun := λ _ _   => trivial,
    defElimFun     := λ _     => trivial,
    defElimFunFun  := λ _ _ _ => trivial }

  instance hasExternalEquivalence (p q : prop) : HasExternalEquivalence p q := ⟨λ _ _ => True⟩

  @[reducible] def toExtEquiv {p q : prop} (h : p ↔ q) : p ⟷' q :=
  ⟨sort.toExtFun h.mp, sort.toExtFun h.mpr, trivial⟩

  @[reducible] def fromExtEquiv {p q : prop} (E : p ⟷' q) : p ↔ q :=
  ⟨E.toFun.f, E.invFun.f⟩

  @[simp] theorem fromToExtEquiv {p q : prop} (h : p ↔ q) :
    fromExtEquiv (toExtEquiv h) = h :=
  rfl

  @[simp] theorem toFromExtEquiv {p q : prop} (E : p ⟷' q) :
    toExtEquiv (fromExtEquiv E) = E :=
  by match E with
     | ⟨toFun, invFun, _⟩ => simp; exact ⟨sort.toFromExtFun toFun, sort.toFromExtFun invFun, HEq.rfl⟩

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
  { defElimFun := λ _ _ => trivial }

  instance hasEquivOp : HasEquivOp prop :=
  { defIdEquiv         := λ _     => trivial,
    defCompEquiv       := λ _ _   => trivial,
    defCompEquivFun    := λ _ _   => trivial,
    defCompEquivFunFun := λ _ _ _ => trivial,
    defInvEquiv        := λ _     => trivial,
    defInvEquivFun     := λ _ _   => trivial }

  instance hasLinearCommonEquivalences : HasLinearCommonEquivalences prop :=
  { defFunDomainEquiv      := λ _ _   => trivial,
    defFunDomainEquivFun   := λ _ _ _ => trivial,
    defFunCodomainEquiv    := λ _ _   => trivial,
    defFunCodomainEquivFun := λ _ _ _ => trivial,
    defSwapFunFunEquiv     := λ _ _ _ => trivial,
    defTopElimEquiv        := λ _     => trivial,
    defProdElimFunEquiv    := λ _ _ _ => trivial,
    defProdFstEquiv        := λ _ _   => trivial,
    defProdFstEquivFun     := λ _ _ _ => trivial,
    defProdSndEquiv        := λ _ _   => trivial,
    defProdSndEquivFun     := λ _ _ _ => trivial,
    defProdCommEquiv       := λ _ _   => trivial,
    defProdAssocEquiv      := λ _ _ _ => trivial,
    defProdTopEquiv        := λ _     => trivial,
    defCompEquivEquiv      := λ _ _   => trivial,
    defCompEquivEquivFun   := λ _ _ _ => trivial,
    defInvEquivEquiv       := λ _ _   => trivial }

  instance hasNonLinearCommonEquivalences : HasNonLinearCommonEquivalences prop :=
  { defProdDistrEquiv := λ _ _ _ => trivial }

  instance hasBotEquivalences : HasBotEquivalences prop :=
  { defBotNotTopEquiv := trivial,
    defProdBotEquiv   := λ _ => trivial,
    defBotContraEquiv := λ _ => trivial }

  instance hasClassicalEquivalences : HasClassicalEquivalences prop :=
  { defByContradictionEquiv := λ _ => trivial }

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

theorem Equiv.trans_symm_trans {α : Sort u} {β : Sort v} {γ : Sort w} (e : α ≃ β) (f : α ≃ γ) :
  trans (trans e (symm e)) f = f :=
by simp

theorem Equiv.symm_trans_trans {α : Sort u} {β : Sort v} {γ : Sort w} (e : α ≃ β) (f : β ≃ γ) :
  trans (trans (symm e) e) f = f :=
by simp

theorem Empty.elim {C : Sort u} (e : Empty) : C := by induction e

namespace type

  def topEquiv : Unit ≃ True :=
  { toFun    := λ _  => trivial,
    invFun   := λ _  => (),
    leftInv  := λ () => rfl,
    rightInv := λ _  => proofIrrel _ _ }

  instance hasEmbeddedTopType : HasEmbeddedType type True :=
  { α := Unit,
    h := topEquiv }

  def botEquiv : Empty ≃ False :=
  { toFun    := Empty.elim,
    invFun   := False.elim,
    leftInv  := λ e => Empty.elim e,
    rightInv := λ _ => proofIrrel _ _ }

  instance hasEmbeddedTop : HasEmbeddedTop type := ⟨⟩

  instance hasFunctorialTop : HasFunctorialTop type :=
  { defElimFun    := λ _ => trivial,
    defElimFunFun := λ _ => trivial }

  instance hasEmbeddedBotType : HasEmbeddedType type False :=
  { α := Empty,
    h := botEquiv }

  instance hasEmbeddedBot : HasEmbeddedBot type := ⟨⟩

  instance hasFunctorialBot : HasFunctorialBot type :=
  { defElimFun := λ _ => trivial }

  def prodEquiv (α β : type) : Prod α β ≃ (α ⊓' β) :=
  { toFun    := λ p => ⟨p.fst, p.snd⟩,
    invFun   := λ P => ⟨P.fst, P.snd⟩,
    leftInv  := λ (_, _) => rfl,
    rightInv := λ ⟨_, _⟩ => rfl }

  instance hasEmbeddedProductType (α β : type) : HasEmbeddedType type (α ⊓' β) :=
  { α := Prod α β,
    h := prodEquiv α β }

  instance hasEmbeddedProduct (α β : type) : HasEmbeddedProduct α β := ⟨⟩
  instance hasEmbeddedProducts : HasEmbeddedProducts type := ⟨⟩

  instance hasFunctorialProducts : HasFunctorialProducts type :=
  { defIntroFun    := λ _ _   => trivial,
    defIntroFunFun := λ _ _   => trivial,
    defElimFun     := λ _     => trivial,
    defElimFunFun  := λ _ _ _ => trivial }

  theorem prodExt {α β : type} {p q : Prod α β} (hFst : p.fst = q.fst) (hSnd : p.snd = q.snd) :
    p = q :=
  by induction p; induction q; simp [hFst, hSnd]

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
    fromExtEquiv (toExtEquiv e) = e :=
  by induction e; rfl

  @[simp] theorem toFromExtEquiv {α β : type} (E : α ⟷' β) :
    toExtEquiv (fromExtEquiv E) = E :=
  by match E with
     | ⟨toFun, invFun, _⟩ => simp; exact ⟨sort.toFromExtFun toFun, sort.toFromExtFun invFun,
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
  { defElimFun := λ _ _ => trivial }

  instance hasEquivOp : HasEquivOp type :=
  { defIdEquiv         := λ α     => toDefEquiv (Equiv.refl α),
    defCompEquiv       := λ e f   => toDefEquiv (Equiv.trans e f),
    defCompEquivFun    := λ _ _   => trivial,
    defCompEquivFunFun := λ _ _ _ => trivial,
    defInvEquiv        := λ e     => toDefEquiv (Equiv.symm e),
    defInvEquivFun     := λ _ _   => trivial }

  instance hasLinearCommonEquivalences : HasLinearCommonEquivalences type :=
  { defFunDomainEquiv      := λ e _   => ⟨λ f => funext (λ b => congrArg f (e.rightInv b)),
                                          λ f => funext (λ a => congrArg f (e.leftInv  a))⟩,
    defFunDomainEquivFun   := λ _ _ _ => trivial,
    defFunCodomainEquiv    := λ e _   => ⟨λ f => funext (λ c => e.leftInv  (f c)),
                                          λ f => funext (λ c => e.rightInv (f c))⟩,
    defFunCodomainEquivFun := λ _ _ _ => trivial,
    defSwapFunFunEquiv     := λ _ _ _ => ⟨λ _ => funext (λ _ => funext (λ _ => rfl)),
                                          λ _ => funext (λ _ => funext (λ _ => rfl))⟩,
    defTopElimEquiv        := λ _     => ⟨λ _ => rfl, λ f => funext (λ () => rfl)⟩,
    defProdElimFunEquiv    := λ _ _ _ => ⟨λ _ => funext (λ _ => funext (λ _ => rfl)),
                                          λ _ => funext (λ (_, _) => rfl)⟩,
    defProdFstEquiv        := λ e _   => ⟨λ p => prodExt (e.leftInv  p.fst) rfl,
                                          λ p => prodExt (e.rightInv p.fst) rfl⟩,
    defProdFstEquivFun     := λ _ _ _ => trivial,
    defProdSndEquiv        := λ e _   => ⟨λ p => prodExt rfl (e.leftInv  p.snd),
                                          λ p => prodExt rfl (e.rightInv p.snd)⟩,
    defProdSndEquivFun     := λ _ _ _ => trivial,
    defProdCommEquiv       := λ _ _   => ⟨λ (_, _) => rfl, λ (_, _) => rfl⟩,
    defProdAssocEquiv      := λ _ _ _ => ⟨λ ((_, _), _) => rfl, λ (_, (_, _)) => rfl⟩,
    defProdTopEquiv        := λ _     => ⟨λ _ => rfl, λ ((), _) => rfl⟩,
    defCompEquivEquiv      := λ e _   => ⟨Equiv.symm_trans_trans e, Equiv.trans_symm_trans e⟩,
    defCompEquivEquivFun   := λ _ _ _ => trivial,
    defInvEquivEquiv       := λ _ _   => ⟨Equiv.symm_symm, Equiv.symm_symm⟩ }

  instance hasNonLinearCommonEquivalences : HasNonLinearCommonEquivalences type :=
  { defProdDistrEquiv := λ _ _ _ => ⟨λ _ => funext (λ _ => prodExt rfl rfl),
                                     λ _ => prodExt (funext (λ _ => rfl)) (funext (λ _ => rfl))⟩, }

  instance hasBotEquivalences : HasBotEquivalences type :=
  { defBotNotTopEquiv := ⟨λ e => Empty.elim e, λ f => Empty.elim (f ())⟩,
    defProdBotEquiv   := λ _ => ⟨λ e => Empty.elim e, λ p => Empty.elim p.fst⟩,
    defBotContraEquiv := λ _ => ⟨λ e => Empty.elim e, λ p => Empty.elim (p.snd p.fst)⟩ }

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
