import UniverseAbstractions.Universes.Layer2.Axioms.Functors
import UniverseAbstractions.Universes.Layer2.Lemmas.DerivedFunctors



namespace UniverseAbstractions.Layer2

set_option autoBoundImplicitLocal false

open Universe Layer1 Layer1.HasFunctors Layer1.HasLinearLogic Layer1.HasSubLinearLogic
     Layer1.HasNonLinearLogic Layer1.Prerelation HasFunctors



class HasFunctorialImplication (U : Universe) [HasFunctors U] where
(defFunImpPi {A B C : U} (F : A ⟶ B) (G : A ⟶ C) : DefPi₂ (λ a b => F a ≃ F b ⟶ G a ≃ G b))

namespace HasFunctorialImplication

  variable {U : Universe} [HasFunctors U] [h : HasFunctorialImplication U]

  @[reducible] def FunImp {A B C : U} (F : A ⟶ B) (G : A ⟶ C) : U.V := (h.defFunImpPi F G).toDefPi.p

  infixr:20 " −≃→ " => HasFunctorialImplication.FunImp

  @[reducible] def elimFun₂ {A B C : U} (F : A ⟶ B) (G : A ⟶ C) (a b : A) :
    (F −≃→ G) ⟶ (F a ≃ F b ⟶ G a ≃ G b) :=
  DefPi₂.appFun (h.defFunImpPi F G) a b

  @[reducible] def elimFun {A B C : U} {F : A ⟶ B} {G : A ⟶ C} (i : F −≃→ G) (a b : A) :
    F a ≃ F b ⟶ G a ≃ G b :=
  (elimFun₂ F G a b) i

  @[reducible] def elim {A B C : U} {F : A ⟶ B} {G : A ⟶ C} (i : F −≃→ G) {a b : A} (e : F a ≃ F b) :
    G a ≃ G b :=
  (elimFun i a b) e

  @[reducible] def DefFunImp {A B C : U} (F : A ⟶ B) (G : A ⟶ C) :=
  DefPi₂.DefLambda (h.defFunImpPi F G)

  notation:20 F:21 " −≃→{" congr:0 "} " G:21 => HasFunctorialImplication.DefFunImp F G congr

end HasFunctorialImplication

open HasFunctorialImplication



class HasLinearFunImp (U : Universe) [HasFunctors U] [HasFunctorialImplication U] [HasLinearLogic U]
                      where
(defEqFunImp {A B : U} {F G : A ⟶ B} (e : F ≃ G) :
   F −≃→{λ a b => Λ f => congrFun e b • f • congrFun e⁻¹ a} G)
(defEqFunImpFun {A B : U} (F G : A ⟶ B) :
   F ≃ G ⟶{λ e => (defEqFunImp e).i} (F −≃→ G))
(defCompFunImp {A B C D : U} {F : A ⟶ B} {G : A ⟶ C} {H : A ⟶ D} (iFG : F −≃→ G) (iGH : G −≃→ H) :
   F −≃→{λ a b => elimFun iGH a b ⊙ elimFun iFG a b} H)
(defCompFunImpFun₂ {A B C D : U} (F : A ⟶ B) (G : A ⟶ C) (H : A ⟶ D) :
   (F −≃→ G) ⟶ (G −≃→ H) ⟶{λ iFG iGH => (defCompFunImp iFG iGH).i} (F −≃→ H))
(defRightCompFunImp {A B C : U} (F : A ⟶ B) (G : B ⟶ C) :
   F −≃→{λ a b => Λ e => DefFun.byDef⁻¹ • congrArg G e • DefFun.byDef} G ⊙ F)
(defLeftCompFunImp {A B C D : U} {F : A ⟶ B} {G : B ⟶ C} {H : A ⟶ D} (i : G ⊙ F −≃→ H) :
   F −≃→{λ a b => Λ e => elim i (DefFun.byDef⁻¹ • congrArg G e • DefFun.byDef)} H)
(defLeftCompFunImpFun {A B C D : U} (F : A ⟶ B) (G : B ⟶ C) (H : A ⟶ D) :
   (G ⊙ F −≃→ H) ⟶{λ i => (defLeftCompFunImp i).i} (F −≃→ H))

namespace HasLinearFunImp

  variable {U : Universe} [HasFunctors U] [HasFunctorialImplication U] [HasLinearLogic U]
           [HasLinearFunImp U]

  @[reducible] def eqFunImp {A B : U} {F G : A ⟶ B} (e : F ≃ G) : F −≃→ G := (defEqFunImp e).i
  @[reducible] def eqFunImpFun {A B : U} (F G : A ⟶ B) : F ≃ G ⟶ (F −≃→ G) := (defEqFunImpFun F G).F

  instance eqFunImp.isFunApp {A B : U} {F G : A ⟶ B} (e : F ≃ G) : IsFunApp (F ≃ G) (eqFunImp e) :=
  ⟨eqFunImpFun F G, e⟩

  @[reducible] def idFunImp {A B : U} (F : A ⟶ B) : F −≃→ F := eqFunImp (InstEq.refl F)

  @[reducible] def compFunImp {A B C D : U} {F : A ⟶ B} {G : A ⟶ C} {H : A ⟶ D} (iFG : F −≃→ G)
                              (iGH : G −≃→ H) :
    F −≃→ H :=
  (defCompFunImp iFG iGH).i

  @[reducible] def compFunImpFun₂ {A B C D : U} (F : A ⟶ B) (G : A ⟶ C) (H : A ⟶ D) :
    (F −≃→ G) ⟶ (G −≃→ H) ⟶ (F −≃→ H) :=
  (defCompFunImpFun₂ F G H).F

  instance compFunImp.isFunApp₂ {A B C D : U} {F : A ⟶ B} {G : A ⟶ C} {H : A ⟶ D} (iFG : F −≃→ G)
                                (iGH : G −≃→ H) :
    IsFunApp₂ (F −≃→ G) (G −≃→ H) (compFunImp iFG iGH) :=
  ⟨compFunImpFun₂ F G H, iFG, iGH⟩

  structure OutFun (A : U) where
  {B : U}
  (F : A ⟶ B)

  def funImpRel (A : U) : Prerelation (OutFun A) U.V := λ F G => F.F −≃→ G.F

  instance funImpRel.isPreorder (A : U) : IsPreorder (funImpRel A) :=
  { refl      := λ F     => idFunImp F.F,
    transFun₂ := λ F G H => compFunImpFun₂ F.F G.F H.F }

  @[reducible] def rightCompFunImp {A B C : U} (F : A ⟶ B) (G : B ⟶ C) : F −≃→ G ⊙ F :=
  (defRightCompFunImp F G).i

  @[reducible] def leftCompFunImp {A B C D : U} {F : A ⟶ B} {G : B ⟶ C} {H : A ⟶ D}
                                  (i : G ⊙ F −≃→ H) :
    F −≃→ H :=
  (defLeftCompFunImp i).i

  @[reducible] def leftCompFunImpFun {A B C D : U} (F : A ⟶ B) (G : B ⟶ C) (H : A ⟶ D) :
    (G ⊙ F −≃→ H) ⟶ (F −≃→ H) :=
  (defLeftCompFunImpFun F G H).F

  instance leftCompFunImp.isFunApp {A B C D : U} {F : A ⟶ B} {G : B ⟶ C} {H : A ⟶ D}
                                   (i : G ⊙ F −≃→ H) :
    IsFunApp (G ⊙ F −≃→ H) (leftCompFunImp i) :=
  ⟨leftCompFunImpFun F G H, i⟩

end HasLinearFunImp


class HasSubLinearFunImp (U : Universe) [HasFunctors U] [HasFunctorialImplication U]
                         [Layer1.HasSubLinearLogic U.V] [HasSubLinearLogic U] where
(defConstFunImp {A B C : U} (F : A ⟶ B) (c : C) :
   F −≃→{λ a b => constFun (F a ≃ F b) (DefFun.byDef⁻¹ • DefFun.byDef)} constFun A c)

namespace HasSubLinearFunImp

  variable {U : Universe} [HasFunctors U] [HasFunctorialImplication U]
           [Layer1.HasSubLinearLogic U.V] [HasSubLinearLogic U] [HasSubLinearFunImp U]

  @[reducible] def constFunImp {A B C : U} (F : A ⟶ B) (c : C) : F −≃→ constFun A c :=
  (defConstFunImp F c).i

end HasSubLinearFunImp

class HasAffineFunImp (U : Universe) [HasFunctors U] [HasFunctorialImplication U]
                      [Layer1.HasSubLinearLogic U.V] [HasAffineLogic U] extends
  HasLinearFunImp U, HasSubLinearFunImp U


class HasNonLinearFunImp (U : Universe) [HasFunctors U] [HasFunctorialImplication U]
                         [Layer1.HasNonLinearLogic U.V] [HasLinearLogic U] [HasNonLinearLogic U]
                         where
(defRightSubstFunImp {A B C : U} {F : A ⟶ B} {G : A ⟶ B ⟶ C} (i : F −≃→ G) :
   F −≃→{λ a b => Λ e => DefFun.byDef⁻¹ • congr (elim i e) e • DefFun.byDef} substFun F G)
(defRightSubstFunImpFun {A B C : U} (F : A ⟶ B) (G : A ⟶ B ⟶ C) :
   (F −≃→ G) ⟶{λ i => (defRightSubstFunImp i).i} (F −≃→ substFun F G))
(defLeftSubstFunImp {A B C D : U} {F : A ⟶ B} {G : A ⟶ B ⟶ C} {H : A ⟶ D}
                    (iFGH : substFun F G −≃→ H) (iFG : F −≃→ G) :
   F −≃→{λ a b => Λ e => elim iFGH (DefFun.byDef⁻¹ • congr (elim iFG e) e • DefFun.byDef)} H)
(defLeftSubstFunImpFun₂ {A B C D : U} (F : A ⟶ B) (G : A ⟶ B ⟶ C) (H : A ⟶ D) :
   (substFun F G −≃→ H) ⟶ (F −≃→ G) ⟶{λ iFGH iFG => (defLeftSubstFunImp iFGH iFG).i} (F −≃→ H))

namespace HasNonLinearFunImp

  variable {U : Universe} [HasFunctors U] [HasFunctorialImplication U]
           [Layer1.HasNonLinearLogic U.V] [HasLinearLogic U] [HasNonLinearLogic U]
           [HasNonLinearFunImp U]

  @[reducible] def rightSubstFunImp {A B C : U} {F : A ⟶ B} {G : A ⟶ B ⟶ C} (i : F −≃→ G) :
    F −≃→ substFun F G :=
  (defRightSubstFunImp i).i

  @[reducible] def rightSubstFunImpFun {A B C : U} (F : A ⟶ B) (G : A ⟶ B ⟶ C) :
    (F −≃→ G) ⟶ (F −≃→ substFun F G) :=
  (defRightSubstFunImpFun F G).F

  @[reducible] def leftSubstFunImp {A B C D : U} {F : A ⟶ B} {G : A ⟶ B ⟶ C} {H : A ⟶ D}
                                   (iFGH : substFun F G −≃→ H) (iFG : F −≃→ G) :
    F −≃→ H :=
  (defLeftSubstFunImp iFGH iFG).i

  @[reducible] def leftSubstFunImpFun {A B C D : U} {F : A ⟶ B} {G : A ⟶ B ⟶ C} {H : A ⟶ D}
                                      (iFGH : substFun F G −≃→ H) :
    (F −≃→ G) ⟶ (F −≃→ H) :=
  ((defLeftSubstFunImpFun₂ F G H).app iFGH).F

  @[reducible] def leftSubstFunImpFun₂ {A B C D : U} (F : A ⟶ B) (G : A ⟶ B ⟶ C) (H : A ⟶ D) :
    (substFun F G −≃→ H) ⟶ (F −≃→ G) ⟶ (F −≃→ H) :=
  (defLeftSubstFunImpFun₂ F G H).F

  instance leftSubstFunImp.isFunApp {A B C D : U} {F : A ⟶ B} {G : A ⟶ B ⟶ C} {H : A ⟶ D}
                                    (iFGH : substFun F G −≃→ H) (iFG : F −≃→ G) :
    IsFunApp (F −≃→ G) (leftSubstFunImp iFGH iFG) :=
  ⟨leftSubstFunImpFun iFGH, iFG⟩

  instance leftSubstFunImpFun.isFunApp {A B C D : U} {F : A ⟶ B} {G : A ⟶ B ⟶ C} {H : A ⟶ D}
                                       (iFGH : substFun F G −≃→ H) :
    IsFunApp (substFun F G −≃→ H) (leftSubstFunImpFun iFGH) :=
  ⟨leftSubstFunImpFun₂ F G H, iFGH⟩

end HasNonLinearFunImp

class HasFullFunImp (U : Universe) [HasFunctors U] [HasFunctorialImplication U]
                    [Layer1.HasSubLinearLogic U.V] [Layer1.HasNonLinearLogic U.V] [HasFullLogic U]
                    extends
  HasAffineFunImp U, HasNonLinearFunImp U
