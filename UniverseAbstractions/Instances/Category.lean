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
    Universe.{max 1 u w, max ((max 1 u w) + 1) iw ww} := Bundled.univ (typeClass.{u} W)

  variable {W : Universe.{w, ww}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]

  instance inst (A : univ.{u} W) : IsCategory.{max 1 u w, w, ww, iw} W A := A.inst
  instance (A : univ.{u} W) : IsCategory.{max 1 u w, w, ww, iw} W A.a := A.inst

  -- Instance equivalences

  variable [hIsoUniv : IsIsoUniverse.{u} W]

  instance hasEquivalenceRelation (A : univ.{u} W) : HasEquivalenceRelation A W :=
  ⟨(hIsoUniv.hasIsomorphisms A).hasIsoRel.Iso⟩

  instance hasInstanceEquivalences : HasInstanceEquivalences (univ.{u} W) W :=
  ⟨hasEquivalenceRelation⟩

  -- Functors

  variable [hFunUniv : IsFunUniverse.{u} W] [hNatUniv : IsNatUniverse.{u} W]

  instance hasFunctorInstances :
    HasFunctorInstances (univ.{u} W) (univ.{u} W) (typeClass.{u} W) :=
  { Fun     := λ A B => HasFunctorialityProperty.Functor A B,
    apply   := HasFunctorialityProperty.Functor.φ,
    funInst := λ A B => HasNaturality.funIsCategory.{u, w, iw} A B }

  def toDefFun {A B : univ.{u} W} (F : A ⟶ B) : A ⟶{F.φ} B :=
  HasFunctors.toDefFun F

  instance hasCongrArg : HasCongrArg (univ.{u} W) (univ.{u} W) := ⟨IsFunUniverse.mapIso⟩

  instance hasInternalFunctors : HasInternalFunctors (univ.{u} W) := ⟨⟩

  instance hasLinearFunOp : HasLinearFunOp (univ.{u} W) :=
  { defIdFun         := λ A => toDefFun (IsFunUniverse.idFun.{u} A.a),
                                 -- TODO: Why doesn't `toDefFun` work here?
    defRevAppFun     := λ a B => { F   := IsNatUniverse.revAppFun.{u} a B.a,
                                   eff := λ F => HasInstanceEquivalences.refl (F a) },
    defRevAppFunFun  := λ A B => { F   := IsNatUniverse.revAppFunFun.{u} A.a B.a,
                                   eff := λ a => HasInstanceEquivalences.refl (IsNatUniverse.revAppFun.{u} a B.a) },
    defCompFun       := λ F G => toDefFun (IsFunUniverse.compFun.{u} F G),
    defCompFunFun    := sorry,
    defCompFunFunFun := sorry }

  instance hasAffineFunOp : HasAffineFunOp (univ.{u} W) :=
  { defConstFun    := λ A {B} b => toDefFun (IsFunUniverse.constFun.{u} A.a b),
    defConstFunFun := sorry }

  instance hasFullFunOp : HasFullFunOp (univ.{u} W) :=
  { defDupFun    := sorry,
    defDupFunFun := sorry }

end CategoryTheory.IsCategory
