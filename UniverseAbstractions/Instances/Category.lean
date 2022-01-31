import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.FunctorExtensionality
import UniverseAbstractions.Axioms.CategoryTheory.Meta
import UniverseAbstractions.Axioms.CategoryTheory.Basic
import UniverseAbstractions.Axioms.CategoryTheory.Extended
import UniverseAbstractions.Axioms.CategoryTheory.Isomorphisms
import UniverseAbstractions.Instances.Utils.Bundled



set_option autoBoundImplicitLocal false
set_option synthInstance.maxHeartbeats 10000
--set_option pp.universes true

universe u w ww iw iww



namespace CategoryTheory.IsCategory

  open Bundled MetaRelation HasFunctors HasCongrArg HasLinearFunOp IsAssociative IsCategoricalPreorder
       HasFunProp HasFunProp.Functor HasNatRel HasIsoFunctoriality HasIsoNaturality

  def typeClass (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw, iww} W] :
    SimpleTypeClass.{max 1 u w, max 1 u w ww iw} := IsCategory.{max 1 u w, w, ww, iw} W
  def univ (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw, iww} W] :
    Universe.{max 1 u w, max ((max 1 u w) + 1) iw ww} := Bundled.univ (typeClass.{u} W)

  variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]

  instance inst (A : univ.{u} W) : IsCategory.{max 1 u w, w, ww, iw} W A := A.inst
  instance (A : univ.{u} W) : IsCategory.{max 1 u w, w, ww, iw} W A.a := A.inst
  @[reducible] def CatHom (A : univ.{u} W) := (inst A).Hom

  -- Instance equivalences

  variable [hFunUniv : IsFunUniverse.{u} W] [hNatUniv : IsNatUniverse.{u} W] [hIsoUniv : IsIsoUniverse.{u} W]

  @[reducible] def CatIso (A : univ.{u} W) := (hIsoUniv.hasIso A).Iso

  instance hasEquivalenceRelation (A : univ.{u} W) : HasEquivalenceRelation A W :=
  ⟨CatIso A⟩

  instance hasInstanceEquivalences : HasInstanceEquivalences (univ.{u} W) W :=
  ⟨hasEquivalenceRelation⟩

  -- Functors

  instance hasFunctorInstances :
    HasFunctorInstances (univ.{u} W) (univ.{u} W) (typeClass.{u} W) :=
  { Fun     := λ A B => A ⮕ B,
    apply   := HasFunProp.Functor.φ,
    funInst := λ A B => HasNaturality.funIsCategory A B }

  instance hasFunctors : HasFunctors (univ.{u} W) (univ.{u} W) (univ.{u} W) :=
  Bundled.hasFunctors (univ.{u} W) (univ.{u} W)

  def mkFun {A B : univ.{u} W} {φ : A → B} (F : HasFunProp.Fun φ) : A ⟶ B :=
  HasFunProp.Functor.mk F

  def toDefFun {A B : univ.{u} W} (F : A ⟶ B) : A ⟶{F.φ} B :=
  HasFunctors.toDefFun F

  instance hasCongrArg : HasCongrArg (univ.{u} W) (univ.{u} W) := ⟨mapIso⟩
  instance hasCongrFun : HasCongrFun (univ.{u} W) (univ.{u} W) := ⟨natIso⟩

  instance hasInternalFunctors : HasInternalFunctors (univ.{u} W) := ⟨⟩

  instance hasLinearFunOp [IsFunUniverse.HasLinearFunctors W] [IsNatUniverse.HasLinearFunctors W] :
    HasLinearFunOp (univ.{u} W) :=
  { defIdFun         := λ A => toDefFun (IsFunUniverse.HasLinearFunctors.idFun.{u} A.a),
                                 -- TODO: Why doesn't `toDefFun` work here?
    defRevAppFun     := λ a B => { F   := IsNatUniverse.HasLinearFunctors.revAppFun.{u} a B.a,
                                   eff := λ F => HasInstanceEquivalences.refl (F a) },
    defRevAppFunFun  := λ A B => { F   := IsNatUniverse.HasLinearFunctors.revAppFunFun.{u} A.a B.a,
                                   eff := λ a => HasInstanceEquivalences.refl (IsNatUniverse.HasLinearFunctors.revAppFun.{u} a B.a) },
    defCompFun       := λ F G => toDefFun (IsFunUniverse.HasLinearFunctors.compFun.{u} F G),
    defCompFunFun    := λ F C => { F   := IsNatUniverse.HasLinearFunctors.compFunFun.{u} F C.a,
                                   eff := λ G => HasInstanceEquivalences.refl (IsFunUniverse.HasLinearFunctors.compFun.{u} F G) },
    defCompFunFunFun := λ A B C => { F   := IsNatUniverse.HasLinearFunctors.compFunFunFun.{u} A.a B.a C.a,
                                     eff := λ F => HasInstanceEquivalences.refl (IsNatUniverse.HasLinearFunctors.compFunFun.{u} F C.a) } }

  instance hasAffineFunOp [HasSubLinearFunOp W] [IsFunUniverse.HasAffineFunctors W]
                          [IsNatUniverse.HasAffineFunctors W] :
    HasAffineFunOp (univ.{u} W) :=
  { defConstFun    := λ A {B} b => toDefFun (IsFunUniverse.HasAffineFunctors.constFun.{u} A.a b),
    defConstFunFun := λ A B => { F   := IsNatUniverse.HasAffineFunctors.constFunFun.{u} A.a B.a,
                                 eff := λ b => HasInstanceEquivalences.refl (IsFunUniverse.HasAffineFunctors.constFun.{u} A.a b) } }

  instance hasFullFunOp [HasSubLinearFunOp W] [HasNonLinearFunOp W] [IsFunUniverse.HasAffineFunctors W]
                        [IsNatUniverse.HasFullFunctors W] :
    HasFullFunOp (univ.{u} W) :=
  { defDupFun    := λ F => toDefFun (IsNatUniverse.HasFullFunctors.dupFun.{u} F),
    defDupFunFun := λ A B => { F   := IsNatUniverse.HasFullFunctors.dupFunFun.{u} A.a B.a,
                               eff := λ F => HasInstanceEquivalences.refl (IsNatUniverse.HasFullFunctors.dupFun.{u} F) } }

  def funReflEq {A B : univ.{u} W} {φ : A → B} {F₁ F₂ : HasFunProp.Fun φ}
                (hEq : ∀ {a b : A} (f : a ⇾ b), (HasFunProp.desc F₁).F f ≃ (HasFunProp.desc F₂).F f) :
    mkFun F₁ ≃ mkFun F₂ :=
  sorry

  instance hasLinearFunExt [IsFunUniverse.HasLinearFunctors W] [IsNatUniverse.HasLinearFunctors W]
                           [h : HasLinearFunExt W] :
    HasLinearFunOp.HasLinearFunExt (univ.{u} W) :=
  { rightId              := λ F => funReflEq (λ f => congrArg _ (DefFun.byMapHomDef byDef) • DefFun.byMapHomDef byDef),
    leftId               := λ F => funReflEq (λ f => DefFun.byMapHomDef byDef • DefFun.byMapHomDef byDef),
    rightIdExt           := sorry,
    leftIdExt            := sorry,
    swapRevApp           := λ F => funReflEq (λ f => byNatDef F • DefFun.byMapHomDef byDef • congrArg _ (DefFun.byMapHomDef byDef) • DefFun.byMapHomDef byDef),
    swapRevAppExt        := sorry,
    swapCompFun          := sorry,
    swapCompFunExt       := sorry,
    swapCompFunExtExt    := sorry,
    swapRevCompFun       := sorry,
    swapRevCompFunExt    := sorry,
    swapRevCompFunExtExt := sorry,
    compAssoc            := sorry,
    compAssocExt         := sorry,
    compAssocExtExt      := sorry,
    compAssocExtExtExt   := sorry }

end CategoryTheory.IsCategory
