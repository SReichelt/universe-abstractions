import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Singletons
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences
import UniverseAbstractions.Axioms.Universe.Properties
import UniverseAbstractions.Axioms.Universe.Quantifiers

import mathlib4_experiments.CoreExt
import mathlib4_experiments.Data.Equiv.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w



instance unitHasInstances : HasInstances.{0, 1} Unit := ⟨λ _ => True⟩

def unit : Universe.{0} := ⟨Unit⟩

namespace unit

  instance hasFunctoriality (U : Universe.{u}) : HasFunctoriality.{u, 0, 0} U unit :=
  ⟨λ _ => True⟩

  def unitFunctor {U : Universe.{u}} {α : U} {β : unit} : α ⟶' β := ⟨λ _ => trivial, trivial⟩

  @[simp] theorem unitFunctor.unique {U : Universe.{u}} {α : U} {β : unit} (F : α ⟶' β) :
    F = unitFunctor :=
  by induction F; rfl

  def funEquiv {U : Universe.{u}} (α : U) (β : unit) : True ≃ (α ⟶' β) :=
  { toFun    := λ _ => unitFunctor,
    invFun   := λ _ => trivial,
    leftInv  := λ _ => proofIrrel _ _,
    rightInv := λ _ => by simp }

  instance hasEmbeddedFunctorType {U : Universe.{u}} (α : U) (β : unit) : HasEmbeddedType unit (α ⟶' β) :=
  { α := (),
    h := funEquiv α β }

  instance hasFunctors (U : Universe.{u}) : HasFunctors U unit unit := ⟨⟩

  instance hasEmbeddedFunctors : HasEmbeddedFunctors unit := ⟨⟩

  instance hasLinearFunOp : HasLinearFunOp unit :=
  { defIdFun         := λ _     => trivial,
    defAppFun        := λ _ _   => trivial,
    defAppFunFun     := λ _ _   => trivial,
    defCompFun       := λ _ _   => trivial,
    defCompFunFun    := λ _ _   => trivial,
    defCompFunFunFun := λ _ _ _ => trivial }

  instance hasAffineFunOp : HasAffineFunOp unit :=
  { defConstFun    := λ _ {_} _ => trivial,
    defConstFunFun := λ _ _     => trivial }

  instance hasFullFunOp : HasFullFunOp unit :=
  { defDupFun    := λ _   => trivial,
    defDupFunFun := λ _ _ => trivial }

  instance hasFunOp : HasFunOp unit := ⟨⟩

  instance hasEmbeddedTopType : HasEmbeddedType unit True :=
  { α := (),
    h := Equiv.refl True }

  instance hasTop : HasTop unit := ⟨⟩

  instance hasEmbeddedTop : HasEmbeddedTop unit :=
  { defElimFun    := λ _ => trivial,
    defElimFunFun := λ _ => trivial }

  def prodEquiv {U : Universe.{u}} (α : U) (β : unit) : ⌈α⌉ ≃ (α ⊓' β) :=
  { toFun    := λ a => ⟨a, trivial⟩,
    invFun   := λ P => P.fst,
    leftInv  := λ _ => rfl,
    rightInv := λ ⟨_, _⟩ => rfl }

  instance hasEmbeddedProductType {U : Universe.{u}} (α : U) (β : unit) : HasEmbeddedType U (α ⊓' β) :=
  { α := α,
    h := prodEquiv α β }

  instance hasProducts (U : Universe.{u}) : HasProducts U unit U := ⟨⟩

  instance hasEmbeddedProducts : HasEmbeddedProducts unit :=
  { defIntroFun    := λ _ _   => trivial,
    defIntroFunFun := λ _ _   => trivial,
    defElimFun     := λ _     => trivial,
    defElimFunFun  := λ _ _ _ => trivial }

  instance hasEquivalenceCondition : HasEquivalenceCondition.{0, 0, 0, 0} unit unit := ⟨λ _ _ => True⟩

  @[reducible] def unitEquivalence {α β : unit} : α ⟷' β := ⟨trivial, trivial, trivial⟩

  @[simp] theorem unitEquivalence.unique {α β : unit} {E : α ⟷' β} : E = unitEquivalence :=
  by induction E; simp; exact ⟨proofIrrel _ _, proofIrrel _ _, HEq.rfl⟩

  def equivEquiv (α β : unit) : True ≃ (α ⟷' β) :=
  { toFun    := λ _ => unitEquivalence,
    invFun   := λ _ => trivial,
    leftInv  := λ _ => proofIrrel _ _,
    rightInv := λ _ => by simp }

  instance hasEmbeddedEquivType (α β : unit) : HasEmbeddedType unit (α ⟷' β) :=
  { α := (),
    h := equivEquiv α β }

  instance hasEquivalences : HasEquivalences unit unit unit := ⟨⟩

  instance hasEmbeddedEquivalences : HasEmbeddedEquivalences unit :=
  { defElimFun  := λ _ _ => trivial }

  instance hasEquivOp : HasEquivOp unit :=
  { defIdEquiv         := λ _     => trivial,
    defInvEquiv        := λ _     => trivial,
    defInvEquivFun     := λ _ _   => trivial,
    defCompEquiv       := λ _ _   => trivial,
    defCompEquivFun    := λ _ _   => trivial,
    defCompEquivFunFun := λ _ _ _ => trivial }

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

  instance hasUnivFunctoriality : HasFunctoriality.{0, v + 1, 0} unit univ.{v} := ⟨λ _ => True⟩
  instance hasUnivConstFun : HasConstFun unit univ.{v} := ⟨λ _ {_} _ => trivial⟩

  instance hasGeneralizedProperties : HasGeneralizedProperties unit := ⟨⟩

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

  instance hasFunctoriality (U : Universe.{u}) : HasFunctoriality.{u, v, 0} U sort.{v} :=
  ⟨λ _ => True⟩

  def funEquiv {U : Universe.{u}} (α : U) (β : sort.{v}) : (α → β) ≃ (α ⟶' β) :=
  { toFun    := λ f => ⟨f, trivial⟩,
    invFun   := λ F => F.f,
    leftInv  := λ _ => rfl,
    rightInv := λ ⟨_, _⟩ => rfl }

  instance hasEmbeddedFunctorType {U : Universe.{u}} (α : U) (β : sort.{v}) : HasEmbeddedType sort.{imax u v} (α ⟶' β) :=
  { α := α → β,
    h := funEquiv α β }

  instance hasFunctors (U : Universe.{u}) : HasFunctors U sort.{v} sort.{imax u v} := ⟨⟩

  -- This shouldn't be necessary, but sometimes we have to help Lean a bit.
  @[reducible] def toFunctor {U : Universe.{u}} {α : U} {β : sort.{v}} (f : α → β) : ⌈α ⟶ β⌉ := f

  instance hasEmbeddedFunctors : HasEmbeddedFunctors sort.{u} := ⟨⟩

  instance hasLinearFunOp : HasLinearFunOp sort.{u} :=
  { defIdFun         := λ _     => trivial,
    defAppFun        := λ _ _   => trivial,
    defAppFunFun     := λ _ _   => trivial,
    defCompFun       := λ _ _   => trivial,
    defCompFunFun    := λ _ _   => trivial,
    defCompFunFunFun := λ _ _ _ => trivial }

  instance hasAffineFunOp : HasAffineFunOp sort.{u} :=
  { defConstFun    := λ _ {_} _ => trivial,
    defConstFunFun := λ _ _     => trivial }

  instance hasFullFunOp : HasFullFunOp sort.{u} :=
  { defDupFun    := λ _   => trivial,
    defDupFunFun := λ _ _ => trivial }

  instance hasFunOp : HasFunOp sort.{u} := ⟨⟩

  instance hasUnivFunctoriality : HasFunctoriality.{u, v + 1, 0} sort.{u} univ.{v} := ⟨λ _ => True⟩
  instance hasUnivConstFun : HasConstFun sort.{u} univ.{v} := ⟨λ _ {_} _ => trivial⟩

  instance hasGeneralizedProperties : HasGeneralizedProperties sort.{u} := ⟨⟩

  instance hasUniversality : HasUniversality.{u, v, 0} sort.{u} sort.{v} := ⟨λ _ => True⟩

  def piEquiv {α : sort.{u}} (P : HasGeneralizedProperties.Property sort.{v} α) :
    HasGeneralizedProperties.Pi P ≃ HasUniversality.Pi P :=
  { toFun    := λ f => ⟨f, trivial⟩,
    invFun   := λ F => F.f,
    leftInv  := λ _ => rfl,
    rightInv := λ ⟨_, _⟩ => rfl }

  instance hasEmbeddedPiType {α : sort.{u}} (P : HasGeneralizedProperties.Property sort.{v} α) :
    HasEmbeddedType sort.{imax u v} (HasUniversality.Pi P) :=
  { α := HasGeneralizedProperties.Pi P,
    h := piEquiv P }

  instance hasPiTypes : HasPiTypes sort.{u} sort.{u} sort.{u} := ⟨⟩
  instance hasEmbeddedPiTypes : HasEmbeddedPiTypes sort.{u} sort.{u} := ⟨⟩

end sort

namespace prop

  instance hasPiTypes : HasPiTypes sort.{u} prop prop := ⟨⟩
  instance hasEmbeddedPiTypes : HasEmbeddedPiTypes sort.{u} prop := ⟨⟩

  instance hasEmbeddedTopType : HasEmbeddedType prop True :=
  { α := True,
    h := Equiv.refl True }

  instance hasTop : HasTop prop := ⟨⟩

  instance hasEmbeddedTop : HasEmbeddedTop prop :=
  { defElimFun    := λ _ => trivial,
    defElimFunFun := λ _ => trivial }

  instance hasEmbeddedBotType : HasEmbeddedType prop False :=
  { α := False,
    h := Equiv.refl False }

  instance hasBot : HasBot prop := ⟨⟩

  instance hasEmbeddedBot : HasEmbeddedBot prop :=
  { defElimFun := λ _ => trivial }

  instance hasClassicalLogic : HasClassicalLogic prop :=
  { byContradictionFun := @Classical.byContradiction }

  def prodEquiv (p q : prop) : (p ∧ q) ≃ (p ⊓' q) :=
  { toFun    := λ h => ⟨h.left, h.right⟩,
    invFun   := λ P => ⟨P.fst, P.snd⟩,
    leftInv  := λ _ => proofIrrel _ _,
    rightInv := λ ⟨_, _⟩ => rfl }

  instance hasEmbeddedProductType (p q : prop) : HasEmbeddedType prop (p ⊓' q) :=
  { α := p ∧ q,
    h := prodEquiv p q }

  instance hasProducts : HasProducts prop prop prop := ⟨⟩

  instance hasEmbeddedProducts : HasEmbeddedProducts prop :=
  { defIntroFun    := λ _ _   => trivial,
    defIntroFunFun := λ _ _   => trivial,
    defElimFun     := λ _     => trivial,
    defElimFunFun  := λ _ _ _ => trivial }

  instance hasEquivalenceCondition : HasEquivalenceCondition prop prop := ⟨λ _ _ => True⟩

  def equivEquiv (p q : prop) : (p ↔ q) ≃ (p ⟷' q) :=
  { toFun    := λ h => ⟨h.mp, h.mpr, trivial⟩,
    invFun   := λ E => ⟨E.toFun, E.invFun⟩,
    leftInv  := λ _ => rfl,
    rightInv := λ ⟨_, _, _⟩ => by simp; exact HEq.rfl }

  instance hasEmbeddedEquivType (p q : prop) : HasEmbeddedType prop (p ⟷' q) :=
  { α := p ↔ q,
    h := equivEquiv p q }

  instance hasEquivalences : HasEquivalences prop prop prop := ⟨⟩

  instance hasEmbeddedEquivalences : HasEmbeddedEquivalences prop :=
  { defElimFun := λ _ _ => trivial }

  instance hasEquivOp : HasEquivOp prop :=
  { defIdEquiv         := λ _     => trivial,
    defInvEquiv        := λ _     => trivial,
    defInvEquivFun     := λ _ _   => trivial,
    defCompEquiv       := λ _ _   => trivial,
    defCompEquivFun    := λ _ _   => trivial,
    defCompEquivFunFun := λ _ _ _ => trivial }

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

def Empty.elim {C : Sort u} (e : Empty) : C := by induction e

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

  instance hasTop : HasTop type := ⟨⟩

  instance hasEmbeddedTop : HasEmbeddedTop type :=
  { defElimFun    := λ _ => trivial,
    defElimFunFun := λ _ => trivial }

  instance hasEmbeddedBotType : HasEmbeddedType type False :=
  { α := Empty,
    h := botEquiv }

  instance hasBot : HasBot type := ⟨⟩

  instance hasEmbeddedBot : HasEmbeddedBot type :=
  { defElimFun := λ _ => trivial }

  def prodEquiv (α β : type) : Prod α β ≃ (α ⊓' β) :=
  { toFun    := λ p => ⟨p.fst, p.snd⟩,
    invFun   := λ P => ⟨P.fst, P.snd⟩,
    leftInv  := λ (_, _) => rfl,
    rightInv := λ ⟨_, _⟩ => rfl }

  instance hasEmbeddedProductType (α β : type) : HasEmbeddedType type (α ⊓' β) :=
  { α := Prod α β,
    h := prodEquiv α β }

  instance hasProducts : HasProducts type type type := ⟨⟩

  instance hasEmbeddedProducts : HasEmbeddedProducts type :=
  { defIntroFun    := λ _ _   => trivial,
    defIntroFunFun := λ _ _   => trivial,
    defElimFun     := λ _     => trivial,
    defElimFunFun  := λ _ _ _ => trivial }

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

  instance hasEmbeddedEquivType (α β : type) : HasEmbeddedType type (α ⟷' β) :=
  { α := Equiv α β,
    h := equivEquiv α β }

  instance hasEquivalences : HasEquivalences type type type := ⟨⟩

  instance hasEmbeddedEquivalences : HasEmbeddedEquivalences type :=
  { defElimFun := λ _ _ => trivial }

  instance hasEquivOp : HasEquivOp type :=
  { defIdEquiv         := λ α     => DefEquiv.fromEquiv (Equiv.refl α),
    defCompEquiv       := λ e f   => DefEquiv.fromEquiv (Equiv.trans e f),
    defCompEquivFun    := λ _ _   => trivial,
    defCompEquivFunFun := λ _ _ _ => trivial,
    defInvEquiv        := λ e     => DefEquiv.fromEquiv (Equiv.symm e),
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
