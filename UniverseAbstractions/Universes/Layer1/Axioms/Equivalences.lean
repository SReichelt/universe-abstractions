import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors



namespace UniverseAbstractions.Layer1

set_option autoBoundImplicitLocal false

open HasFunctors HasLinearLogic



class HasEquivalences (U : Universe) [HasFunctors U] where
(Equiv             : U → U → U)
(toFun₂  (A B : U) : Equiv A B ⟶ (A ⟶ B))
(invFun₂ (A B : U) : Equiv A B ⟶ (B ⟶ A))

namespace HasEquivalences

  infix:20 " ⟷ " => HasEquivalences.Equiv

  variable {U : Universe} [HasFunctors U] [HasEquivalences U]

  @[reducible] def toFun  {A B : U} (E : A ⟷ B) : A ⟶ B := (toFun₂  A B) E
  @[reducible] def invFun {A B : U} (E : A ⟷ B) : B ⟶ A := (invFun₂ A B) E

  @[reducible] def to  {A B : U} (E : A ⟷ B) (a : A) : B := (toFun  E) a
  @[reducible] def inv {A B : U} (E : A ⟷ B) (b : B) : A := (invFun E) b

  -- An equivalence that incorporates concrete functors in both directions, which in layer 1 are
  -- just proofs.
  structure DefEquiv (A B : U) (toFun : A ⟶ B) (invFun : B ⟶ A) where
  (E : A ⟷ B)

  notation:20 A:21 " ⟷{" toFun:0 "," invFun:0 "} " B:21 => HasEquivalences.DefEquiv A B toFun invFun

end HasEquivalences

open HasEquivalences


class HasEquivOp (U : Universe) [HasFunctors U] [HasLinearLogic U] extends
  HasEquivalences U where
(defRefl  (A     : U)                         : A ⟷{idFun A, idFun A} A)
(defSymm  {A B   : U} (E : A ⟷ B)             : B ⟷{invFun E, toFun E} A)
(defTrans {A B C : U} (E : A ⟷ B) (F : B ⟷ C) : A ⟷{toFun F ⊙ toFun E, invFun E ⊙ invFun F} C)

namespace HasEquivOp

  variable {U : Universe} [HasFunctors U] [HasLinearLogic U] [HasEquivOp U]

  @[reducible] def refl (A : U) : A ⟷ A := (defRefl A).E
  @[reducible] def symm {A B : U} (E : A ⟷ B) : B ⟷ A := (defSymm E).E
  @[reducible] def trans {A B C : U} (E : A ⟷ B) (F : B ⟷ C) : A ⟷ C := (defTrans E F).E

end HasEquivOp


class HasEquivOpFun (U : Universe) [HasFunctors U] [HasLinearLogic U] extends
  HasEquivOp U where
(defSymmFun   (A B   : U) : (A ⟷ B) ⟶{HasEquivOp.symm} (B ⟷ A))
(defTransFun₂ (A B C : U) : (A ⟷ B) ⟶ (B ⟷ C) ⟶{HasEquivOp.trans} (A ⟷ C))

namespace HasEquivOpFun

  variable {U : Universe} [HasFunctors U] [HasLinearLogic U] [HasEquivOpFun U]

  @[reducible] def symmFun (A B : U) : (A ⟷ B) ⟶ (B ⟷ A) := (defSymmFun A B).F

  instance symm.isFunApp {A B : U} {E : A ⟷ B} : IsFunApp (A ⟷ B) (HasEquivOp.symm E) :=
  ⟨symmFun A B, E⟩

  @[reducible] def transFun {A B : U} (E : A ⟷ B) (C : U) : (B ⟷ C) ⟶ (A ⟷ C) :=
  ((defTransFun₂ A B C).app E).F

  @[reducible] def transFun₂ (A B C : U) : (A ⟷ B) ⟶ (B ⟷ C) ⟶ (A ⟷ C) :=
  (defTransFun₂ A B C).F

  instance trans.isFunApp {A B C : U} {E : A ⟷ B} {F : B ⟷ C} :
    IsFunApp (B ⟷ C) (HasEquivOp.trans E F) :=
  ⟨transFun E C, F⟩

  instance transFun.isFunApp {A B C : U} {E : A ⟷ B} : IsFunApp (A ⟷ B) (transFun E C) :=
  ⟨transFun₂ A B C, E⟩

end HasEquivOpFun


-- TODO: Standard equivalences
