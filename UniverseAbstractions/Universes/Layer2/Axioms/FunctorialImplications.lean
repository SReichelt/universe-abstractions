import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations.FunctorialImplications
import UniverseAbstractions.Universes.Layer2.Axioms.Functors



namespace UniverseAbstractions.Layer2

set_option autoImplicit false

universe u

open Layer1 Layer1.HasPiType Layer1.HasFunctors Layer1.HasLinearLogic
     Layer1.HasSubLinearLogic Layer1.HasNonLinearLogic Layer1.HasPreorderRelation
     HasPiTypeBase HasFunctors



class HasFunctorialImplications (α : Sort u) {U : Universe.{u}} [HasEquivalenceRelationBase U.V α]
                                (B C : U) [HasFunctors α B] [HasFunctors α C] where
  [hFunImp (F : α ⥤ B) (G : α ⥤ C) :
     HasFunctorialImplication (equivalenceFunctor F) (equivalenceFunctor G)]

namespace HasFunctorialImplications

  variable {α : Sort u} {U : Universe.{u}} [HasEquivalenceRelationBase U.V α] {B C : U}
           [HasFunctors α B] [HasFunctors α C] [h : HasFunctorialImplications α B C]

  instance (F : α ⥤ B) (G : α ⥤ C) :
      HasFunctorialImplication (equivalenceFunctor F) (equivalenceFunctor G) :=
    h.hFunImp F G

  @[reducible] def FunImp (F : α ⥤ B) (G : α ⥤ C) : U.V :=
    HasFunctorialImplication.FunImp (equivalenceFunctor F) (equivalenceFunctor G)
  infixr:20 " ≃⥤ " => HasFunctorialImplications.FunImp

  @[reducible] def DefFunImp (F : α ⥤ B) (G : α ⥤ C) (eFG : ∀ a b, F a ≃ F b ⥤ G a ≃ G b) :=
    HasFunctorialImplication.DefFunImp (equivalenceFunctor F) (equivalenceFunctor G) eFG
  notation:20 F:21 " ≃⥤{" eFG:0 "} " G:21 => HasFunctorialImplications.DefFunImp F G eFG

end HasFunctorialImplications

open HasFunctorialImplications


class HasUnivFunImp (U : Layer1.Universe.{u}) (V : Universe.{u}) [HasPropositions V.V U]
                    [HasUnivFunctors U V] where
  [hFunImp (A : U) (B C : V) : HasFunctorialImplications A B C]

namespace HasUnivFunImp

  section

    variable (U : Layer1.Universe.{u}) (V : Universe.{u}) [HasPropositions V.V U]
             [HasUnivFunctors U V] [h : HasUnivFunImp U V]

    instance (A : U) (B C : V) : HasFunctorialImplications A B C := h.hFunImp A B C

  end

  section

    variable (U : Universe.{u}) [HasUnivFunctors U U] [h : HasUnivFunImp U U]

    instance (A B C : U) : HasFunctorialImplications A B C := h.hFunImp A B C

  end

end HasUnivFunImp

instance  (U : Universe) [HasLinearLogic U] (A B : U) (b : A) : @Prerelation.HasTrans ⌈Function.const ⌈A⌉ B b⌉ U.V Layer1.HasAffineLogic.toHasLinearLogic
  HasEquivalenceRelation.toHasEquivalenceRelationBase.Iso := inferInstance

class HasLinearFunImp (U : Universe) [HasLinearLogic U] extends
    HasUnivFunImp U U where
  defEqFunImp {A B : U} {F G : A ⥤ B} (e : F ≃ G) :
    F ≃⥤{λ a b => Λ f => (congrFun e b • f • congrFun e⁻¹ a : G a ≃ G b)} G

#exit

class HasLinearFunImp (U : Universe) [HasLinearLogic U] extends
    HasUnivFunImp U U where
  defEqFunImp {A B : U} {F G : A ⥤ B} (e : F ≃ G) :
    F ≃⥤{λ a b => Λ f => congrFun e b • f • congrFun e⁻¹ a} G
  defEqFunImpFun {A B : U} (F G : A ⥤ B) :
    F ≃ G ⥤{λ e => (defEqFunImp e).i} (F ≃⥤ G)
  defCompFunImp {A B C D : U} {F : A ⥤ B} {G : A ⥤ C} {H : A ⥤ D} (iFG : F ≃⥤ G) (iGH : G ≃⥤ H) :
    F ≃⥤{λ a b => elimFun iGH a b ⊙ elimFun iFG a b} H
  defCompFunImpFun₂ {A B C D : U} (F : A ⥤ B) (G : A ⥤ C) (H : A ⥤ D) :
    (F ≃⥤ G) ⥤ (G ≃⥤ H) ⥤{λ iFG iGH => (defCompFunImp iFG iGH).i} (F ≃⥤ H)
  defRightCompFunImp {A B C : U} (F : A ⥤ B) (G : B ⥤ C) :
    F ≃⥤{λ a b => Λ e => DefFun.byDef⁻¹ • congrArg G e • DefFun.byDef} G ⊙ F
  defLeftCompFunImp {A B C D : U} {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ D} (i : G ⊙ F ≃⥤ H) :
    F ≃⥤{λ a b => Λ e => elim i (DefFun.byDef⁻¹ • congrArg G e • DefFun.byDef)} H
  defLeftCompFunImpFun {A B C D : U} (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ D) :
    (G ⊙ F ≃⥤ H) ⥤{λ i => (defLeftCompFunImp i).i} (F ≃⥤ H)

namespace HasLinearFunImp

  variable {U : Universe} [HasLinearLogic U] [HasLinearFunImp U]

  @[reducible] def eqFunImp {A B : U} {F G : A ⥤ B} (e : F ≃ G) : F ≃⥤ G := (defEqFunImp e).i
  @[reducible] def eqFunImpFun {A B : U} (F G : A ⥤ B) : F ≃ G ⥤ (F ≃⥤ G) := (defEqFunImpFun F G).F

  instance eqFunImp.isFunApp {A B : U} {F G : A ⥤ B} (e : F ≃ G) : IsFunApp (F ≃ G) (eqFunImp e) :=
  ⟨eqFunImpFun F G, e⟩

  @[reducible] def idFunImp {A B : U} (F : A ⥤ B) : F ≃⥤ F := eqFunImp (InstEq.refl F)

  @[reducible] def compFunImp {A B C D : U} {F : A ⥤ B} {G : A ⥤ C} {H : A ⥤ D} (iFG : F ≃⥤ G)
                              (iGH : G ≃⥤ H) :
    F ≃⥤ H :=
  (defCompFunImp iFG iGH).i

  @[reducible] def compFunImpFun₂ {A B C D : U} (F : A ⥤ B) (G : A ⥤ C) (H : A ⥤ D) :
    (F ≃⥤ G) ⥤ (G ≃⥤ H) ⥤ (F ≃⥤ H) :=
  (defCompFunImpFun₂ F G H).F

  instance compFunImp.isFunApp₂ {A B C D : U} {F : A ⥤ B} {G : A ⥤ C} {H : A ⥤ D} (iFG : F ≃⥤ G)
                                (iGH : G ≃⥤ H) :
    IsFunApp₂ (F ≃⥤ G) (G ≃⥤ H) (compFunImp iFG iGH) :=
  ⟨compFunImpFun₂ F G H, iFG, iGH⟩

  structure OutFun (A : U) where
  {B : U}
  (F : A ⥤ B)

  def funImpRel (A : U) : Prerelation (OutFun A) U.V := λ F G => F.F ≃⥤ G.F

  instance funImpRel.isPreorder (A : U) : IsPreorder (funImpRel A) :=
  { refl      := λ F     => idFunImp F.F,
    transFun₂ := λ F G H => compFunImpFun₂ F.F G.F H.F }

  @[reducible] def rightCompFunImp {A B C : U} (F : A ⥤ B) (G : B ⥤ C) : F ≃⥤ G ⊙ F :=
  (defRightCompFunImp F G).i

  @[reducible] def leftCompFunImp {A B C D : U} {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ D}
                                  (i : G ⊙ F ≃⥤ H) :
    F ≃⥤ H :=
  (defLeftCompFunImp i).i

  @[reducible] def leftCompFunImpFun {A B C D : U} (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ D) :
    (G ⊙ F ≃⥤ H) ⥤ (F ≃⥤ H) :=
  (defLeftCompFunImpFun F G H).F

  instance leftCompFunImp.isFunApp {A B C D : U} {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ D}
                                   (i : G ⊙ F ≃⥤ H) :
    IsFunApp (G ⊙ F ≃⥤ H) (leftCompFunImp i) :=
  ⟨leftCompFunImpFun F G H, i⟩

end HasLinearFunImp

#exit

class HasSubLinearFunImp (U : Universe) [HasFunctors U] [HasFunctorialImplications U]
                         [HasSubLinearLogic U] where
(defConstFunImp {A B C : U} (F : A ⥤ B) (c : C) :
   F ≃⥤{λ a b => constFun (F a ≃ F b) (DefFun.byDef⁻¹ • DefFun.byDef)} constFun A c)

namespace HasSubLinearFunImp

  variable {U : Universe} [HasFunctors U] [HasFunctorialImplications U]
           [HasSubLinearLogic U] [HasSubLinearFunImp U]

  @[reducible] def constFunImp {A B C : U} (F : A ⥤ B) (c : C) : F ≃⥤ constFun A c :=
  (defConstFunImp F c).i

end HasSubLinearFunImp

class HasAffineFunImp (U : Universe) [HasFunctors U] [HasFunctorialImplications U]
                      [HasAffineLogic U] extends
  HasLinearFunImp U, HasSubLinearFunImp U


class HasNonLinearFunImp (U : Universe) [HasFunctors U] [HasFunctorialImplications U]
                         [HasLinearLogic U] [HasNonLinearLogic U] where
(defRightSubstFunImp {A B C : U} {F : A ⥤ B} {G : A ⥤ B ⥤ C} (i : F ≃⥤ G) :
   F ≃⥤{λ a b => Λ e => DefFun.byDef⁻¹ • congr (elim i e) e • DefFun.byDef} substFun F G)
(defRightSubstFunImpFun {A B C : U} (F : A ⥤ B) (G : A ⥤ B ⥤ C) :
   (F ≃⥤ G) ⥤{λ i => (defRightSubstFunImp i).i} (F ≃⥤ substFun F G))
(defLeftSubstFunImp {A B C D : U} {F : A ⥤ B} {G : A ⥤ B ⥤ C} {H : A ⥤ D}
                    (iFGH : substFun F G ≃⥤ H) (iFG : F ≃⥤ G) :
   F ≃⥤{λ a b => Λ e => elim iFGH (DefFun.byDef⁻¹ • congr (elim iFG e) e • DefFun.byDef)} H)
(defLeftSubstFunImpFun₂ {A B C D : U} (F : A ⥤ B) (G : A ⥤ B ⥤ C) (H : A ⥤ D) :
   (substFun F G ≃⥤ H) ⥤ (F ≃⥤ G) ⥤{λ iFGH iFG => (defLeftSubstFunImp iFGH iFG).i} (F ≃⥤ H))

namespace HasNonLinearFunImp

  variable {U : Universe} [HasFunctors U] [HasFunctorialImplications U] [HasLinearLogic U]
           [HasNonLinearLogic U] [HasNonLinearFunImp U]

  @[reducible] def rightSubstFunImp {A B C : U} {F : A ⥤ B} {G : A ⥤ B ⥤ C} (i : F ≃⥤ G) :
    F ≃⥤ substFun F G :=
  (defRightSubstFunImp i).i

  @[reducible] def rightSubstFunImpFun {A B C : U} (F : A ⥤ B) (G : A ⥤ B ⥤ C) :
    (F ≃⥤ G) ⥤ (F ≃⥤ substFun F G) :=
  (defRightSubstFunImpFun F G).F

  @[reducible] def leftSubstFunImp {A B C D : U} {F : A ⥤ B} {G : A ⥤ B ⥤ C} {H : A ⥤ D}
                                   (iFGH : substFun F G ≃⥤ H) (iFG : F ≃⥤ G) :
    F ≃⥤ H :=
  (defLeftSubstFunImp iFGH iFG).i

  @[reducible] def leftSubstFunImpFun {A B C D : U} {F : A ⥤ B} {G : A ⥤ B ⥤ C} {H : A ⥤ D}
                                      (iFGH : substFun F G ≃⥤ H) :
    (F ≃⥤ G) ⥤ (F ≃⥤ H) :=
  ((defLeftSubstFunImpFun₂ F G H).app iFGH).F

  @[reducible] def leftSubstFunImpFun₂ {A B C D : U} (F : A ⥤ B) (G : A ⥤ B ⥤ C) (H : A ⥤ D) :
    (substFun F G ≃⥤ H) ⥤ (F ≃⥤ G) ⥤ (F ≃⥤ H) :=
  (defLeftSubstFunImpFun₂ F G H).F

  instance leftSubstFunImp.isFunApp {A B C D : U} {F : A ⥤ B} {G : A ⥤ B ⥤ C} {H : A ⥤ D}
                                    (iFGH : substFun F G ≃⥤ H) (iFG : F ≃⥤ G) :
    IsFunApp (F ≃⥤ G) (leftSubstFunImp iFGH iFG) :=
  ⟨leftSubstFunImpFun iFGH, iFG⟩

  instance leftSubstFunImpFun.isFunApp {A B C D : U} {F : A ⥤ B} {G : A ⥤ B ⥤ C} {H : A ⥤ D}
                                       (iFGH : substFun F G ≃⥤ H) :
    IsFunApp (substFun F G ≃⥤ H) (leftSubstFunImpFun iFGH) :=
  ⟨leftSubstFunImpFun₂ F G H, iFGH⟩

end HasNonLinearFunImp

class HasFullFunImp (U : Universe) [HasFunctors U] [HasFunctorialImplications U] [HasFullLogic U]
                    extends
  HasAffineFunImp U, HasNonLinearFunImp U
