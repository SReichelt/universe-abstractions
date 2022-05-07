import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors

import UniverseAbstractions.Universes.Layer1.Meta.Tactics.Functoriality



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
(defRefl      (A     : U)                         : A ⟷{idFun A, idFun A} A)
(defSymm      {A B   : U} (E : A ⟷ B)             : B ⟷{invFun E, toFun E} A)
(defSymmFun   (A B   : U)                         : (A ⟷ B) ⟶{λ E => (defSymm E).E} (B ⟷ A))
(defTrans     {A B C : U} (E : A ⟷ B) (F : B ⟷ C) : A ⟷{toFun F ⊙ toFun E, invFun E ⊙ invFun F} C)
(defTransFun₂ (A B C : U)                         : (A ⟷ B) ⟶ (B ⟷ C) ⟶{λ E F => (defTrans E F).E} (A ⟷ C))

namespace HasEquivOp

  variable {U : Universe} [HasFunctors U] [HasLinearLogic U] [HasEquivOp U]

  @[reducible] def refl (A : U) : A ⟷ A := (defRefl A).E

  @[reducible] def symm {A B : U} (E : A ⟷ B) : B ⟷ A := (defSymm E).E
  @[reducible] def symmFun (A B : U) : (A ⟷ B) ⟶ (B ⟷ A) := (defSymmFun A B).F

  instance symm.isFunApp {A B : U} {E : A ⟷ B} : IsFunApp (A ⟷ B) (HasEquivOp.symm E) :=
  ⟨symmFun A B, E⟩

  @[reducible] def trans {A B C : U} (E : A ⟷ B) (F : B ⟷ C) : A ⟷ C := (defTrans E F).E
  @[reducible] def transFun {A B : U} (E : A ⟷ B) (C : U) : (B ⟷ C) ⟶ (A ⟷ C) :=
  ((defTransFun₂ A B C).app E).F
  @[reducible] def transFun₂ (A B C : U) : (A ⟷ B) ⟶ (B ⟷ C) ⟶ (A ⟷ C) := (defTransFun₂ A B C).F

  instance trans.isFunApp {A B C : U} {E : A ⟷ B} {F : B ⟷ C} :
    IsFunApp (B ⟷ C) (HasEquivOp.trans E F) :=
  ⟨transFun E C, F⟩

  instance transFun.isFunApp {A B C : U} {E : A ⟷ B} : IsFunApp (A ⟷ B) (transFun E C) :=
  ⟨transFun₂ A B C, E⟩

  structure TypeFunProof (φ : U → U) where
  (transport {A₁ A₂ : U} (E : A₁ ⟷ A₂) : φ A₁ ⟶ φ A₂)

  structure DefTypeFun (φ : U → U) (hφ : TypeFunProof φ) where
  (defEquiv {A₁ A₂ : U} (E : A₁ ⟷ A₂) : φ A₁ ⟷{hφ.transport E, hφ.transport (symm E)} φ A₂)
  (defEquivFun (A₁ A₂ : U) : (A₁ ⟷ A₂) ⟶{λ E => (defEquiv E).E} (φ A₁ ⟷ φ A₂))

  namespace DefTypeFun

    variable {φ : U → U} {hφ : TypeFunProof φ} (Φ : DefTypeFun φ hφ)

    @[reducible] def equiv {A₁ A₂ : U} (E : A₁ ⟷ A₂) : φ A₁ ⟷ φ A₂ := (Φ.defEquiv E).E
    @[reducible] def equivFun (A₁ A₂ : U) : (A₁ ⟷ A₂) ⟶ (φ A₁ ⟷ φ A₂) := (Φ.defEquivFun A₁ A₂).F

    instance equiv.isFunApp {A₁ A₂ : U} {E : A₁ ⟷ A₂} : IsFunApp (A₁ ⟷ A₂) (equiv Φ E) :=
    ⟨equivFun Φ A₁ A₂, E⟩

  end DefTypeFun

  structure TypeFunProof₂ (φ : U → U → U) where
  (app  (A : U) : TypeFunProof (φ A))
  (app₂ (B : U) : TypeFunProof (λ A => φ A B))

  structure DefTypeFun₂ (φ : U → U → U) (hφ : TypeFunProof₂ φ) where
  (app  (A : U) : DefTypeFun (φ A) (hφ.app A))
  (app₂ (B : U) : DefTypeFun (λ A => φ A B) (hφ.app₂ B))

  namespace DefTypeFun₂

    variable {φ : U → U → U} {hφ : TypeFunProof₂ φ} (Φ : DefTypeFun₂ φ hφ) (A₁ A₂ B₁ B₂ : U)

    def defEquivFun₂ :
      (A₁ ⟷ A₂) ⟶ (B₁ ⟷ B₂) ⟶{λ E F => trans (DefTypeFun.equiv (Φ.app₂ B₁) E)
                                             (DefTypeFun.equiv (Φ.app A₂) F)} (φ A₁ B₁ ⟷ φ A₂ B₂) :=
    by functoriality

    @[reducible] def equivFun₂ : (A₁ ⟷ A₂) ⟶ (B₁ ⟷ B₂) ⟶ (φ A₁ B₁ ⟷ φ A₂ B₂) :=
    (defEquivFun₂ Φ A₁ A₂ B₁ B₂).F

    def defEquivFun₂' :
      (A₁ ⟷ A₂) ⟶ (B₁ ⟷ B₂) ⟶{λ E F => trans (DefTypeFun.equiv (Φ.app A₁) F)
                                             (DefTypeFun.equiv (Φ.app₂ B₂) E)} (φ A₁ B₁ ⟷ φ A₂ B₂) :=
    by functoriality

    @[reducible] def equivFun₂' : (A₁ ⟷ A₂) ⟶ (B₁ ⟷ B₂) ⟶ (φ A₁ B₁ ⟷ φ A₂ B₂) :=
    (defEquivFun₂' Φ A₁ A₂ B₁ B₂).F

  end DefTypeFun₂

end HasEquivOp
