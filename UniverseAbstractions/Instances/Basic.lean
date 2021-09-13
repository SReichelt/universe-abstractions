import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Singletons
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences
import UniverseAbstractions.Axioms.Universe.Properties
import UniverseAbstractions.Axioms.Universe.DependentFunctors
import UniverseAbstractions.Axioms.Universe.DependentProducts

import mathlib4_experiments.CoreExt
import mathlib4_experiments.Data.Equiv.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w



class HasTrivialFunctoriality (U : Universe.{u}) (V : Universe.{v})

namespace HasTrivialFunctoriality

  instance hasFunctoriality (U : Universe.{u}) (V : Universe.{v}) [HasTrivialFunctoriality U V] :
    HasFunctoriality.{u, v, 0} U V :=
  ⟨λ _ => True⟩

  def defFun {U V : Universe} [HasTrivialFunctoriality U V] {A : U} {B : V} {f : A → B} :
    A ⟶[f] B :=
  trivial

  theorem defFunEq {U V : Universe} [HasTrivialFunctoriality U V] {A : U} {B : V} {f : A → B}
                   {F₁ F₂ : A ⟶[f] B} :
    F₁ = F₂ :=
  proofIrrel F₁ F₂

  class HasTrivialFunctors (U : Universe.{u}) (V : Universe.{v}) (UV : outParam Universe.{w}) extends
    HasTrivialFunctoriality U V where
  [embedFun (A : U) (B : V) : HasEmbeddedType UV (A ⟶' B)]

  instance hasFunctors (U V UV : Universe) [h : HasTrivialFunctors U V UV] : HasFunctors U V UV :=
  { embed := h.embedFun }

  instance hasIdFun (U : Universe) [HasTrivialFunctoriality U U] : HasIdFun U := ⟨λ _ => defFun⟩
  instance hasConstFun (U V : Universe) [HasTrivialFunctoriality U V] : HasConstFun U V := ⟨λ _ {_} _ => defFun⟩

  instance hasCompFun' (U V W : Universe) [HasFunctoriality U V] [HasFunctoriality V W] [HasTrivialFunctoriality U W] :
    HasCompFun' U V W :=
  ⟨λ _ _ => defFun⟩

  instance hasCompFun (U V W UV VW : Universe) [HasFunctors U V UV] [HasFunctors V W VW] [HasTrivialFunctoriality U W] :
    HasCompFun U V W UV VW :=
  ⟨λ _ _ => defFun⟩

  variable (U : Universe) [HasTrivialFunctors U U U]

  instance hasEmbeddedFunctors : HasEmbeddedFunctors U := ⟨⟩

  instance hasLinearFunOp : HasLinearFunOp U :=
  { defIdFun         := λ _     => defFun,
    defAppFun        := λ _ _   => defFun,
    defAppFunFun     := λ _ _   => defFun,
    defCompFun       := λ _ _   => defFun,
    defCompFunFun    := λ _ _   => defFun,
    defCompFunFunFun := λ _ _ _ => defFun }

  instance hasLinearFunOpEq : HasLinearFunOpEq U :=
  { defIdFunEq   := λ _   => defFunEq,
    defCompFunEq := λ _ _ => defFunEq }

  instance hasAffineFunOp : HasAffineFunOp U :=
  { defConstFun    := λ _ {_} _ => defFun,
    defConstFunFun := λ _ _     => defFun }

  instance hasSubLinearFunOpEq : HasSubLinearFunOpEq U :=
  { defConstFunEq := λ _ {_} _ => defFunEq }

  instance hasFullFunOp : HasFullFunOp U :=
  { defDupFun    := λ _   => defFun,
    defDupFunFun := λ _ _ => defFun }

  instance hasFunOp : HasFunOp U := ⟨⟩

  instance hasEmbeddedTop [HasTop U] : HasEmbeddedTop U :=
  { defElimFun    := λ _ => defFun,
    defElimFunFun := λ _ => defFun }

  instance hasEmbeddedBot [HasBot U] : HasEmbeddedBot U :=
  { defElimFun := λ _ => defFun }

  instance hasEmbeddedProducts [HasProducts U U U] : HasEmbeddedProducts U :=
  { defIntroFun    := λ _ _   => defFun,
    defIntroFunFun := λ _ _   => defFun,
    defElimFun     := λ _     => defFun,
    defElimFunFun  := λ _ _ _ => defFun }

  instance hasEmbeddedEquivalences [HasEquivalences U U U] [HasEmbeddedProducts U] : HasEmbeddedEquivalences U :=
  { defElimFun  := λ _ _ => defFun }

end HasTrivialFunctoriality



class HasTrivialEquivalenceCondition (U : Universe.{u}) (UU : Universe.{v}) extends
  HasTrivialFunctoriality.HasTrivialFunctors U U UU

namespace HasTrivialEquivalenceCondition

  open HasTrivialFunctoriality

  instance hasEquivalenceCondition (U : Universe.{u}) (UU : Universe.{v}) [HasTrivialEquivalenceCondition U UU] :
    HasEquivalenceCondition.{u, v, 0} U UU :=
  ⟨λ _ _ => True⟩

  def defEquiv {U UU : Universe} [HasTrivialEquivalenceCondition U UU] {A B : U} {toFun : A ⟶ B} {invFun : B ⟶ A} :
    A ⟷[toFun,invFun] B :=
  trivial

  theorem defEquivEq {U UU : Universe} [HasTrivialEquivalenceCondition U UU] {A B : U}
                     {toFun : A ⟶ B} {invFun : B ⟶ A} {E₁ E₂ : A ⟷[toFun,invFun] B} :
    E₁ = E₂ :=
  proofIrrel E₁ E₂

  class HasTrivialEquivalences (U : Universe.{u}) (UU : Universe.{v}) (U_U : outParam Universe.{w}) extends
    HasTrivialEquivalenceCondition U UU where
  [embedEquiv (A B : U) : HasEmbeddedType U_U (A ⟷' B)]

  instance hasEquivalences (U UU U_U : Universe) [h : HasTrivialEquivalences U UU U_U] : HasEquivalences U UU U_U :=
  { embed := h.embedEquiv }

  instance hasIdEquiv (U UU : Universe) [HasTrivialEquivalenceCondition U UU] : HasIdEquiv U UU := ⟨λ _ => defEquiv⟩
  instance hasInvEquiv' (U UU : Universe) [HasTrivialEquivalenceCondition U UU] : HasInvEquiv' U UU := ⟨λ _ => defEquiv⟩
  instance hasInvEquiv (U UU U_U : Universe) [HasTrivialEquivalences U UU U_U] : HasInvEquiv U UU U_U := ⟨λ _ => defEquiv⟩
  instance hasCompEquiv' (U UU : Universe) [HasTrivialEquivalenceCondition U UU] : HasCompEquiv' U UU := ⟨λ _ _ => defEquiv⟩
  instance hasCompEquiv (U UU U_U : Universe) [HasTrivialEquivalences U UU U_U] : HasCompEquiv U UU U_U := ⟨λ _ _ => defEquiv⟩

  variable (U : Universe) [HasProducts U U U] [HasTrivialEquivalences U U U]

  instance hasEquivOp : HasEquivOp U :=
  { defIdEquiv         := λ _     => defEquiv,
    defInvEquiv        := λ _     => defEquiv,
    defInvEquivFun     := λ _ _   => defFun,
    defCompEquiv       := λ _ _   => defEquiv,
    defCompEquivFun    := λ _ _   => defFun,
    defCompEquivFunFun := λ _ _ _ => defFun }

  instance hasEquivOpEq : HasEquivOpEq U :=
  { defIdEquivEq   := λ _   => defEquivEq,
    defInvEquivEq  := λ _   => defEquivEq,
    defCompEquivEq := λ _ _ => defEquivEq }

  instance hasLinearCommonEquivalences [HasEmbeddedTop U] : HasLinearCommonEquivalences U :=
  { defFunDomainEquiv      := λ _ _   => defEquiv,
    defFunDomainEquivFun   := λ _ _ _ => defFun,
    defFunCodomainEquiv    := λ _ _   => defEquiv,
    defFunCodomainEquivFun := λ _ _ _ => defFun,
    defSwapFunFunEquiv     := λ _ _ _ => defEquiv,
    defTopElimEquiv        := λ _     => defEquiv,
    defProdElimFunEquiv    := λ _ _ _ => defEquiv,
    defProdFstEquiv        := λ _ _   => defEquiv,
    defProdFstEquivFun     := λ _ _ _ => defFun,
    defProdSndEquiv        := λ _ _   => defEquiv,
    defProdSndEquivFun     := λ _ _ _ => defFun,
    defProdCommEquiv       := λ _ _   => defEquiv,
    defProdAssocEquiv      := λ _ _ _ => defEquiv,
    defProdTopEquiv        := λ _     => defEquiv,
    defCompEquivEquiv      := λ _ _   => defEquiv,
    defCompEquivEquivFun   := λ _ _ _ => defFun,
    defInvEquivEquiv       := λ _ _   => defEquiv }

  instance hasNonLinearCommonEquivalences [HasEmbeddedTop U] : HasNonLinearCommonEquivalences U :=
  { defProdDistrEquiv := λ _ _ _ => defEquiv }

  instance hasBotEquivalences [HasEmbeddedTop U] [HasEmbeddedBot U] : HasBotEquivalences U :=
  { defBotNotTopEquiv := defEquiv,
    defProdBotEquiv   := λ _ => defEquiv,
    defBotContraEquiv := λ _ => defEquiv }

  instance hasClassicalEquivalences [HasEmbeddedBot U] [HasClassicalLogic U] : HasClassicalEquivalences U :=
  { defByContradictionEquiv := λ _ => defEquiv }

  instance hasSigmaProdEquiv (U V UxV UxVUxV : Universe) [HasProperties U V] [HasDependentProducts U V UxV]
                             [HasProducts U V UxV] [HasTrivialEquivalenceCondition UxV UxVUxV] :
    HasSigmaProdEquiv U V UxV UxVUxV :=
  { defSigmaProdFun   := λ _ _ => defFun,
    defProdSigmaFun   := λ _ _ => defFun,
    defSigmaProdEquiv := λ _ _ => defEquiv }

end HasTrivialEquivalenceCondition



class HasTrivialProperties (U : Universe.{u}) (V : Universe.{v})

namespace HasTrivialProperties

  instance hasProperties (U : Universe.{u}) (V : Universe.{v}) [HasTrivialProperties U V] : HasProperties.{u, v, 0} U V :=
  { IsProp       := λ _   => True,
    defConstProp := λ _ _ => trivial }

  def defProp {U V : Universe} [HasTrivialProperties U V] {A : U} {p : A → V} : A ⟿[p] V := trivial

  theorem defPropEq {U V : Universe} [HasTrivialProperties U V] {A : U} {p : A → V} {P₁ P₂ : A ⟿[p] V} :
    P₁ = P₂ :=
  proofIrrel P₁ P₂

  instance hasCompFunProp' (U V W : Universe) [HasFunctoriality U V] [HasProperties V W] [HasTrivialProperties U W] :
    HasCompFunProp' U V W :=
  { defCompProp    := λ _ _ => defProp,
    defCompConstEq := λ _ _ => defPropEq }

  instance hasCompFunProp (U V W UV : Universe) [HasFunctors U V UV] [HasProperties V W] [HasTrivialProperties U W] :
    HasCompFunProp U V W UV :=
  { defCompProp    := λ _ _ => defProp,
    defCompConstEq := λ _ _ => defPropEq }

  instance hasFunProp (U V W VW : Universe) [HasProperties U V] [HasProperties U W] [HasFunctors V W VW]
                      [HasTrivialProperties U VW] :
    HasFunProp U V W VW :=
  { defFunProp    := λ _ _   => defProp,
    defFunConstEq := λ _ _ _ => defPropEq }

  instance hasProdProp (U V W VxW : Universe) [HasProperties U V] [HasProperties U W] [HasProducts V W VxW]
                       [HasTrivialProperties U VxW] :
    HasProdProp U V W VxW :=
  { defProdProp    := λ _ _   => defProp,
    defProdConstEq := λ _ _ _ => defPropEq }

  instance hasEquivProp (U V V_V : Universe) [HasProperties U V] [HasEmbeddedFunctors V] [HasEquivalences V V V_V]
                        [HasTrivialProperties U V_V] :
    HasEquivProp U V V_V :=
  { defEquivProp    := λ _ _   => defProp,
    defEquivConstEq := λ _ _ _ => defPropEq }

end HasTrivialProperties



class HasTrivialDependentFunctoriality (U : Universe.{u}) (V : Universe.{v}) extends
  HasTrivialProperties U V

namespace HasTrivialDependentFunctoriality

  open HasTrivialFunctoriality HasTrivialEquivalenceCondition HasTrivialProperties

  instance hasDependentFunctoriality (U : Universe.{u}) (V : Universe.{v}) [HasTrivialDependentFunctoriality U V] :
    HasDependentFunctoriality.{u, v, 0, 0} U V :=
  ⟨λ _ => True⟩

  def defPi {U V : Universe} [HasTrivialDependentFunctoriality U V] {A : U}
            {φ : A ⟿ V} {f : HasProperties.Pi φ} :
    Π[f] φ :=
  trivial

  theorem defPiEq {U V : Universe} [HasTrivialDependentFunctoriality U V] {A : U}
                  {φ : A ⟿ V} {f : HasProperties.Pi φ} {F₁ F₂ : Π[f] φ} :
    F₁ = F₂ :=
  proofIrrel F₁ F₂

  class HasTrivialDependentFunctors (U : Universe.{u}) (V : Universe.{v}) (UV : outParam Universe.{w}) extends
    HasTrivialDependentFunctoriality U V where
  [embedPi {A : U} (φ : A ⟿ V) : HasEmbeddedType UV (Π' φ)]

  instance hasDependentFunctors (U V UV : Universe) [h : HasTrivialDependentFunctors U V UV] : HasDependentFunctors U V UV :=
  { embed := h.embedPi }

  instance hasPiFunEquiv (U V UV UVUV : Universe) [HasTrivialDependentFunctors U V UV] [HasTrivialFunctors U V UV]
                         [HasTrivialEquivalenceCondition UV UVUV] :
    HasPiFunEquiv U V UV UVUV :=
  { defPiFun      := λ _   => defFun,
    defPiFunFun   := λ _ _ => defFun,
    defFunPi      := λ _   => defPi,
    defFunPiFun   := λ _ _ => defFun,
    defPiFunEquiv := λ _ _ => defEquiv }

  instance hasPiCompFunProp (U V W UV UW : Universe) [HasFunctors U V UV] [HasProperties V W]
                            [HasTrivialDependentFunctors U W UW] [HasTrivialProperties UV UW] :
    HasPiCompFunProp U V W UV UW :=
  { defPiCompPropProp    := λ _ _ _ => defProp,
    defPiCompPropConstEq := λ _ _ _ => defPropEq }

  instance hasCompFunPi' (U V W : Universe) [HasFunctoriality U V] [HasDependentFunctoriality V W]
                         [HasTrivialDependentFunctoriality U W] :
    HasCompFunPi' U V W :=
  ⟨λ _ _ => defPi⟩

  instance hasCompFunPi (U V W UV VW : Universe) [HasFunctors U V UV] [HasDependentFunctors V W VW]
                        [HasTrivialDependentFunctoriality U W] :
    HasCompFunPi U V W UV VW :=
  ⟨λ _ _ => defPi⟩

  instance hasCompFunPiPi (U : Universe) [HasTrivialFunctors U U U] [HasTrivialDependentFunctors U U U] :
    HasCompFunPiPi U :=
  { defRevCompFunPiPi    := λ _ {_ _} _ => defPi,
    defRevCompFunPiPiFun := λ _ _ _     => defFun }

  instance hasConstFunPi (U V UV : Universe) [HasFunctors U V UV] [HasConstFun U V] [HasProperties V U]
                         [HasProperties V V] [HasTrivialDependentFunctoriality V UV] :
    HasConstFunPi U V UV :=
  { defConstFunPi := λ _ => defPi }

  instance hasPiAppFun (U V UV UVV : Universe) [HasDependentFunctors U V UV] [HasTrivialFunctors UV V UVV]
                       [HasProperties U UV] [HasTrivialDependentFunctoriality U UVV] :
    HasPiAppFun U V UV UVV :=
  { defAppFun   := λ _ _ => defFun,
    defAppFunPi := λ _   => defPi }

  instance hasDupPi (U V UV UUV : Universe) [HasTrivialDependentFunctors U V UV] [HasFunctors U UV UUV]
                    [HasTrivialFunctoriality UUV UV] :
    HasDupPi U V UV UUV :=
  { defDupPi    := λ _ => defPi,
    defDupPiFun := λ _ => defFun }

  instance hasEmbeddedDependentProducts (U V : Universe) [HasTrivialFunctors V V V] [HasTrivialDependentFunctors U V V]
                                        [HasDependentProducts U V V] :
    HasEmbeddedDependentProducts U V :=
  { defIntroFun   := λ _ _ => defFun,
    defIntroFunPi := λ _   => defPi,
    defElimFun    := λ _   => defFun,
    defElimFunFun := λ _ _ => defFun }

end HasTrivialDependentFunctoriality



instance unitHasInstances : HasInstances.{0, 1} Unit := ⟨λ _ => True⟩

def unit : Universe.{0} := ⟨Unit⟩

namespace unit

  def Inst : unit := ()
  def inst {A : unit} : A := trivial

  @[simp] theorem inst.unique {A : unit} (a : A) : a = inst := proofIrrel a inst

  instance hasTrivialInFunctoriality (U : Universe.{u}) : HasTrivialFunctoriality U unit := ⟨⟩

  def unitFunctor {U : Universe.{u}} {A : U} {B : unit} : A ⟶' B :=
  ⟨λ _ => inst, HasTrivialFunctoriality.defFun⟩

  @[simp] theorem unitFunctor.unique {U : Universe.{u}} {A : U} {B : unit} (F : A ⟶' B) :
    F = unitFunctor :=
  by induction F; rfl

  def inFunEquiv {U : Universe.{u}} (A : U) (B : unit) : ⌈Inst⌉ ≃ (A ⟶' B) :=
  { toFun    := λ _ => unitFunctor,
    invFun   := λ _ => inst,
    leftInv  := inst.unique,
    rightInv := λ F => Eq.symm (unitFunctor.unique F) }

  instance hasEmbeddedInFunctorType {U : Universe.{u}} (A : U) (B : unit) :
    HasEmbeddedType unit (A ⟶' B) :=
  ⟨inFunEquiv A B⟩

  instance hasTrivialInFunctors (U : Universe.{u}) : HasTrivialFunctoriality.HasTrivialFunctors U unit unit := ⟨⟩

  instance hasTrivialOutFunctoriality (U : Universe.{u}) : HasTrivialFunctoriality unit U := ⟨⟩

  def outFunEquiv {U : Universe.{u}} (A : unit) (B : U) : ⌈B⌉ ≃ (A ⟶' B) :=
  { toFun    := λ b => ⟨λ _ => b, HasTrivialFunctoriality.defFun⟩,
    invFun   := λ F => F inst,
    leftInv  := λ _ => rfl,
    rightInv := λ ⟨_, _⟩ => rfl }

  instance hasEmbeddedOutFunctorType {U : Universe.{u}} (A : unit) (B : U) :
    HasEmbeddedType U (A ⟶' B) :=
  ⟨outFunEquiv A B⟩

  instance hasTrivialOutFunctors (U : Universe.{u}) : HasTrivialFunctoriality.HasTrivialFunctors unit U U := ⟨⟩

  instance hasEmbeddedTopType : HasEmbeddedType unit True := ⟨Equiv.refl ⌈Inst⌉⟩

  instance hasTop : HasTop unit := ⟨⟩

  def rightProdEquiv {U : Universe.{u}} (A : U) (B : unit) : ⌈A⌉ ≃ (A ⊓' B) :=
  { toFun    := λ a => ⟨a, inst⟩,
    invFun   := λ P => P.fst,
    leftInv  := λ _ => rfl,
    rightInv := λ ⟨_, _⟩ => rfl }

  instance hasEmbeddedRightProductType {U : Universe.{u}} (A : U) (B : unit) : HasEmbeddedType U (A ⊓' B) :=
  ⟨rightProdEquiv A B⟩

  instance hasRightProducts (U : Universe.{u}) : HasProducts U unit U := ⟨⟩

  def leftProdEquiv {U : Universe.{u}} (A : unit) (B : U) : ⌈B⌉ ≃ (A ⊓' B) :=
  { toFun    := λ b => ⟨inst, b⟩,
    invFun   := λ P => P.snd,
    leftInv  := λ _ => rfl,
    rightInv := λ ⟨_, _⟩ => rfl }

  instance hasEmbeddedLeftProductType {U : Universe.{u}} (A : unit) (B : U) : HasEmbeddedType U (A ⊓' B) :=
  ⟨leftProdEquiv A B⟩

  instance hasLeftProducts (U : Universe.{u}) : HasProducts unit U U := ⟨⟩

  instance hasTrivialEquivalenceCondition : HasTrivialEquivalenceCondition unit unit := ⟨⟩

  @[reducible] def unitEquivalence {A B : unit} : A ⟷' B := ⟨inst, inst, HasTrivialEquivalenceCondition.defEquiv⟩

  @[simp] theorem unitEquivalence.unique {A B : unit} (E : A ⟷' B) : E = unitEquivalence :=
  by induction E; simp

  def equivEquiv (A B : unit) : ⌈Inst⌉ ≃ (A ⟷' B) :=
  { toFun    := λ _ => unitEquivalence,
    invFun   := λ _ => inst,
    leftInv  := inst.unique,
    rightInv := λ E => Eq.symm (unitEquivalence.unique E) }

  instance hasEmbeddedEquivType (A B : unit) : HasEmbeddedType unit (A ⟷' B) :=
  ⟨equivEquiv A B⟩

  instance hasTrivialEquivalences : HasTrivialEquivalenceCondition.HasTrivialEquivalences unit unit unit := ⟨⟩

  instance hasTrivialInProperties  (U : Universe.{u}) : HasTrivialProperties U unit := ⟨⟩
  instance hasTrivialOutProperties (U : Universe.{u}) : HasTrivialProperties unit U := ⟨⟩

  instance hasTrivialDependentInFunctoriality (U : Universe.{u}) : HasTrivialDependentFunctoriality U unit := ⟨⟩

  def dependentUnitFunctor {U : Universe.{u}} {A : U} {φ : A ⟿ unit} : Π' φ :=
  ⟨λ _ => inst, HasTrivialDependentFunctoriality.defPi⟩

  @[simp] theorem dependentUnitFunctor.unique {U : Universe.{u}} {A : U} {φ : A ⟿ unit} (F : Π' φ) :
    F = dependentUnitFunctor :=
  by induction F; rfl

  def inPiEquiv {U : Universe.{u}} {A : U} (φ : A ⟿ unit) : ⌈Inst⌉ ≃ (Π' φ) :=
  { toFun    := λ _ => dependentUnitFunctor,
    invFun   := λ _ => inst,
    leftInv  := inst.unique,
    rightInv := λ F => Eq.symm (dependentUnitFunctor.unique F) }

  instance hasEmbeddedDependentInFunctorType {U : Universe.{u}} {A : U} (φ : A ⟿ unit) :
    HasEmbeddedType unit (Π' φ) :=
  ⟨inPiEquiv φ⟩

  instance hasTrivialDependentInFunctors (U : Universe.{u}) :
    HasTrivialDependentFunctoriality.HasTrivialDependentFunctors U unit unit :=
  ⟨⟩

  instance hasTrivialDependentOutFunctoriality (U : Universe.{u}) : HasTrivialDependentFunctoriality unit U := ⟨⟩

  def outPiEquiv {A : unit} {U : Universe.{u}} (φ : A ⟿ U) : ⌈φ inst⌉ ≃ (Π' φ) :=
  { toFun    := λ b => ⟨λ _ => b, HasTrivialDependentFunctoriality.defPi⟩,
    invFun   := λ F => F inst,
    leftInv  := λ _ => rfl,
    rightInv := λ ⟨_, _⟩ => rfl }

  instance hasEmbeddedDependentOutFunctorType {A : unit} {U : Universe.{u}} (φ : A ⟿ U) :
    HasEmbeddedType U (Π' φ) :=
  ⟨outPiEquiv φ⟩

  instance hasTrivialDependentOutFunctors (U : Universe.{u}) :
    HasTrivialDependentFunctoriality.HasTrivialDependentFunctors unit U U :=
  ⟨⟩

  def rightSigmaEquiv {U : Universe.{u}} {A : U} (φ : A ⟿ unit) : ⌈A⌉ ≃ (Σ' φ) :=
  { toFun    := λ a => ⟨a, inst⟩,
    invFun   := λ P => P.fst,
    leftInv  := λ _ => rfl,
    rightInv := λ ⟨_, _⟩ => rfl }

  instance hasEmbeddedDependentRightProductType {U : Universe.{u}} {A : U} (φ : A ⟿ unit) :
    HasEmbeddedType U (Σ' φ) :=
  ⟨rightSigmaEquiv φ⟩

  instance hasDependentRightProducts (U : Universe.{u}) : HasDependentProducts U unit U := ⟨⟩

  def leftSigmaEquiv {A : unit} {U : Universe.{u}} (φ : A ⟿ U) : ⌈φ inst⌉ ≃ (Σ' φ) :=
  { toFun    := λ b => ⟨inst, b⟩,
    invFun   := λ P => P.snd,
    leftInv  := λ _ => rfl,
    rightInv := λ ⟨_, _⟩ => rfl }

  instance hasEmbeddedDependentLeftProductType {A : unit} {U : Universe.{u}} (φ : A ⟿ U) :
    HasEmbeddedType U (Σ' φ) :=
  ⟨leftSigmaEquiv φ⟩

  instance hasDependentLeftProducts (U : Universe.{u}) : HasDependentProducts unit U U := ⟨⟩

end unit



namespace sort

  -- One special property of the `sort` universe is that we can map out of a type in `sort` into
  -- any universe, even dependently. We assume that such functors are always well-defined,
  -- therefore we define functoriality of all functions out of `sort` to be trivial.

  instance hasTrivialFunctoriality (V : Universe.{v}) : HasTrivialFunctoriality sort V := ⟨⟩

  def funEquiv (α : sort.{u}) {V : Universe.{v}} (β : V) : (α → β) ≃ (α ⟶' β) :=
  { toFun    := λ f => ⟨f, trivial⟩,
    invFun   := λ F => F.f,
    leftInv  := λ _ => rfl,
    rightInv := λ ⟨_, _⟩ => rfl }

  instance hasEmbeddedFunctorType (α : sort.{u}) {V : Universe.{v}} (β : V) :
    HasEmbeddedType sort.{imax u v} (α ⟶' β) :=
  ⟨funEquiv α β⟩

  instance hasTrivialFunctors (V : Universe.{v}) :
    HasTrivialFunctoriality.HasTrivialFunctors sort.{u} V sort.{imax u v} :=
  ⟨⟩

  -- This shouldn't be necessary, but sometimes we have to help Lean a bit.
  @[reducible] def toFunctor {α β : sort.{u}} (f : α → β) : ⌈α ⟶ β⌉ := f

  instance hasTrivialProperties (V : Universe.{v}) : HasTrivialProperties sort V := ⟨⟩

  instance hasTrivialDependentFunctoriality (V : Universe.{v}) : HasTrivialDependentFunctoriality sort V := ⟨⟩

  def piEquiv {α : sort.{u}} {V : Universe.{v}} (φ : α ⟿ V) : HasProperties.Pi φ ≃ (Π' φ) :=
  { toFun    := λ f => ⟨f, trivial⟩,
    invFun   := λ F => F.f,
    leftInv  := λ _ => rfl,
    rightInv := λ ⟨_, _⟩ => rfl }

  instance hasEmbeddedDependentFunctorType {α : sort.{u}} {V : Universe.{v}} (φ : α ⟿ V) :
    HasEmbeddedType sort.{imax u v} (Π' φ) :=
  ⟨piEquiv φ⟩

  instance hasTrivialDependentFunctors (V : Universe.{v}) :
    HasTrivialDependentFunctoriality.HasTrivialDependentFunctors sort.{u} V sort.{imax u v} :=
  ⟨⟩

end sort

theorem Exists.prop.fst {p : Prop} {q : p → Prop} : (∃ h, q h) → p
| ⟨h, _⟩ => h

theorem Exists.prop.snd {p : Prop} {q : p → Prop} : (e : ∃ h, q h) → q (Exists.prop.fst e)
| ⟨_, h⟩ => h

namespace prop

  instance hasEmbeddedTopType : HasEmbeddedType prop True := ⟨Equiv.refl True⟩

  instance hasTop : HasTop prop := ⟨⟩

  instance hasEmbeddedBotType : HasEmbeddedType prop False := ⟨Equiv.refl False⟩

  instance hasBot : HasBot prop := ⟨⟩

  instance hasClassicalLogic : HasClassicalLogic prop :=
  { byContradictionFun := @Classical.byContradiction }

  def prodEquiv (p q : prop) : (p ∧ q) ≃ (p ⊓' q) :=
  { toFun    := λ h => ⟨h.left, h.right⟩,
    invFun   := λ P => ⟨P.fst, P.snd⟩,
    leftInv  := λ _ => proofIrrel _ _,
    rightInv := λ ⟨_, _⟩ => rfl }

  instance hasEmbeddedProductType (p q : prop) : HasEmbeddedType prop (p ⊓' q) :=
  ⟨prodEquiv p q⟩

  instance hasProducts : HasProducts prop prop prop := ⟨⟩

  instance hasTrivialEquivalenceCondition : HasTrivialEquivalenceCondition prop prop := ⟨⟩

  def equivEquiv (p q : prop) : (p ↔ q) ≃ (p ⟷' q) :=
  { toFun    := λ h => ⟨h.mp, h.mpr, trivial⟩,
    invFun   := λ E => ⟨E.toFun, E.invFun⟩,
    leftInv  := λ _ => proofIrrel _ _,
    rightInv := λ ⟨_, _, _⟩ => by simp; exact HEq.rfl }

  instance hasEmbeddedEquivType (p q : prop) : HasEmbeddedType prop (p ⟷' q) :=
  ⟨equivEquiv p q⟩

  instance hasTrivialEquivalences : HasTrivialEquivalenceCondition.HasTrivialEquivalences prop prop prop := ⟨⟩

  def sigmaEquiv {p : prop} (φ : p ⟿ prop) : (∃ a, φ a) ≃ (Σ' φ) :=
  { toFun    := λ h => ⟨Exists.prop.fst h, Exists.prop.snd h⟩,
    invFun   := λ P => ⟨P.fst, P.snd⟩,
    leftInv  := λ _ => proofIrrel _ _,
    rightInv := λ ⟨_, _⟩ => rfl }

  instance hasEmbeddedDependentProductType {p : prop} (φ : p ⟿ prop) :
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

def Empty.elim {C : Sort u} (e : Empty) : C := by induction e

namespace type

  def topEquiv : Unit ≃ True :=
  { toFun    := λ _  => trivial,
    invFun   := λ _  => (),
    leftInv  := λ () => rfl,
    rightInv := λ _  => proofIrrel _ _ }

  instance hasEmbeddedTopType : HasEmbeddedType type True := ⟨topEquiv⟩

  instance hasTop : HasTop type := ⟨⟩

  def botEquiv : Empty ≃ False :=
  { toFun    := Empty.elim,
    invFun   := False.elim,
    leftInv  := λ e => Empty.elim e,
    rightInv := λ _ => proofIrrel _ _ }

  instance hasEmbeddedBotType : HasEmbeddedType type False := ⟨botEquiv⟩

  instance hasBot : HasBot type := ⟨⟩

  noncomputable def byContradiction (α : type) (f : HasEmbeddedBot.Not (HasEmbeddedBot.Not α)) : α :=
  Classical.choice (Classical.byContradiction (λ h => Empty.elim (f (λ a => False.elim (h ⟨a⟩)))))

  noncomputable instance hasClassicalLogic : HasClassicalLogic type :=
  { byContradictionFun := byContradiction }

  def prodEquiv (α β : type) : Prod α β ≃ (α ⊓' β) :=
  { toFun    := λ p => ⟨p.fst, p.snd⟩,
    invFun   := λ P => ⟨P.fst, P.snd⟩,
    leftInv  := λ (_, _) => rfl,
    rightInv := λ ⟨_, _⟩ => rfl }

  instance hasEmbeddedProductType (α β : type) : HasEmbeddedType type (α ⊓' β) :=
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

  instance hasEmbeddedEquivType (α β : type) : HasEmbeddedType type (α ⟷' β) :=
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

  instance hasEmbeddedDependentProductType {α : type} (φ : α ⟿ type) :
    HasEmbeddedType type (Σ' φ) :=
  ⟨sigmaEquiv φ⟩

  instance hasDependentProducts : HasDependentProducts type type type := ⟨⟩

  def subtypeEquiv {α : type} (φ : α ⟿ prop) : {a // φ a} ≃ (Σ' φ) :=
  { toFun    := λ p => ⟨p.val, p.property⟩,
    invFun   := λ P => ⟨P.fst, P.snd⟩,
    leftInv  := λ ⟨_, _⟩ => rfl,
    rightInv := λ ⟨_, _⟩ => rfl }

  instance hasEmbeddedSubtypeType {α : type} (φ : α ⟿ prop) :
    HasEmbeddedType type (Σ' φ) :=
  ⟨subtypeEquiv φ⟩

  instance hasSubtypes : HasDependentProducts type prop type := ⟨⟩

end type
