import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.FunctorExtensionality
import UniverseAbstractions.Axioms.CategoryTheory.Meta
import UniverseAbstractions.Axioms.CategoryTheory.Basic
import UniverseAbstractions.Axioms.CategoryTheory.Extended
import UniverseAbstractions.Instances.Utils.Bundled



set_option autoBoundImplicitLocal false
--set_option pp.universes true
set_option synthInstance.maxHeartbeats 10000

universe u w ww iw



namespace CategoryTheory.IsCategory

  open Bundled MetaRelation HasFunctors HasCongrArg HasLinearFunOp IsAssociative IsCategoricalPreorder

  def typeClass (W : Universe.{w, ww}) [HasIdentity.{w, iw} W] [HasStandardFunctors W] :
    SimpleTypeClass.{max 1 u w, max 1 u w ww iw} := IsCategory.{max 1 u w, w, ww, iw} W
  def univ (W : Universe.{w, ww}) [HasIdentity.{w, iw} W] [HasStandardFunctors W] :
    Universe.{max 1 u w, max ((max 1 u w) + 1) ww iw} := Bundled.univ (typeClass.{u} W)

  variable {W : Universe.{w, ww}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]

  instance inst (A : univ.{u} W) : IsCategory.{max 1 u w, w, ww, iw} W A := Bundled.inst A

  -- Instance equivalences

  variable [hIsoUniv : IsIsoUniverse W]

  instance hasEquivalenceRelation (A : univ.{u} W) : HasEquivalenceRelation A W :=
  ⟨(hIsoUniv.hasIsomorphisms A).hasIsoRel.Iso⟩

  instance hasInstanceEquivalences : HasInstanceEquivalences (univ.{u} W) W :=
  ⟨hasEquivalenceRelation⟩

  -- Functors

  variable [hFunUniv : IsFunUniverse W]

  instance hasFunctoriality : HasFunctoriality (univ.{u} W) (univ.{u} W) W :=
  ⟨λ {A B : univ W} => (hFunUniv.hasFunProp A B).Fun⟩

  variable [hNatUniv : IsNatUniverse W]

  instance hasFunctorialityInstances :
    HasFunctorialityInstances.{max 1 u w, max 1 u w, w} (univ.{u} W) (univ.{u} W) (typeClass.{u} W) :=
  ⟨λ A B => HasNaturalityRelation.funIsCategory A B⟩

  def toDefFun {A B : univ.{u} W} (F : A ⟶' B) : A ⟶{F.f} B :=
  Bundled.HasFunctorialityInstances.toDefFun F

  instance hasCongrArg : HasCongrArg (univ.{u} W) (univ.{u} W) :=
  ⟨λ {_ _} F {_ _} e => (IsIsoFunctor.preFunctor F.f) e⟩

  instance hasInternalFunctors : HasInternalFunctors (univ.{u} W) := ⟨⟩

  instance hasIdFun : HasIdFun (univ.{u} W) := ⟨λ A => toDefFun (IsFunUniverse.idFun A)⟩

  instance hasConstFun : HasConstFun (univ.{u} W) (univ.{u} W) :=
  ⟨λ A {B} b => toDefFun (IsFunUniverse.constFun A b)⟩

  instance hasCompFun : HasCompFun (univ.{u} W) (univ.{u} W) (univ.{u} W) :=
  ⟨λ F G => toDefFun (IsFunUniverse.compFun F G)⟩

  instance hasLinearFunOp : HasLinearFunOp (univ.{u} W) := sorry

end CategoryTheory.IsCategory
