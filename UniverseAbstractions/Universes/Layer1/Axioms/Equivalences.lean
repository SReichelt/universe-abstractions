import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations.Isomorphisms



namespace UniverseAbstractions.Layer1

set_option autoImplicit false

universe u

open Universe HasFunctors HasLinearLogic Prerelation HasPreorderRelation HasIsomorphisms
     HasEquivalenceRelationBase



class HasEquivalences (U : Universe) [HasLinearLogic U] extends HasIsomorphisms U

namespace HasEquivalences

  @[reducible] def equivRel (U : Universe) [HasLinearLogic U] [h : HasEquivalences U] :
      Prerelation U U :=
    isoRel U

  variable {U : Universe} [HasLinearLogic U] [h : HasEquivalences U]

  @[reducible] def toFun₂  (A B : U) : A ≃ B ⟶ (A ⟶ B) := toHomFun  A B
  @[reducible] def invFun₂ (A B : U) : A ≃ B ⟶ (B ⟶ A) := invHomFun A B

  @[reducible] def toFun  {A B : U} (E : A ≃ B) : A ⟶ B := toHom  E
  @[reducible] def invFun {A B : U} (E : A ≃ B) : B ⟶ A := invHom E

  instance toFun.isFunApp  {A B : U} {E : A ≃ B} : IsFunApp (A ≃ B) (toFun  E) := ⟨toFun₂  A B, E⟩
  instance invFun.isFunApp {A B : U} {E : A ≃ B} : IsFunApp (A ≃ B) (invFun E) := ⟨invFun₂ A B, E⟩

  @[reducible] def to  {A B : U} (E : A ≃ B) (a : A) : B := (toFun  E) a
  @[reducible] def inv {A B : U} (E : A ≃ B) (b : B) : A := (invFun E) b

end HasEquivalences



class HasHomEquivalences {V : Universe} [HasLinearLogic V] [HasEquivalences V] (α : Sort u)
                         [HasPreorderRelation V α] [HasIsomorphisms α] where
  [hHomCtor₂ : IsIsoFunctor₂ (homFun₂ α)]

namespace HasHomEquivalences

  variable {V : Universe} [HasLinearLogic V] [HasEquivalences V] {α : Sort u}
           [HasPreorderRelation V α] [HasIsomorphisms α] [h : HasHomEquivalences α]

  instance : IsIsoFunctor₂ (homFun₂ α) := h.hHomCtor₂

  @[reducible] def outIsoEquiv {a₁ a₂ : α} (e : a₂ ≃ a₁) (b : α) : (a₁ ⟶ b) ≃ (a₂ ⟶ b) :=
    IsIsoFunctor.iso.opposite ((homFun₂ α).app₂ b) e

  @[reducible] def inIsoEquiv (a : α) {b₁ b₂ : α} (e : b₁ ≃ b₂) : (a ⟶ b₁) ≃ (a ⟶ b₂) :=
    IsIsoFunctor.iso ((homFun₂ α).app a) e

end HasHomEquivalences


class HasEquivRelEquivalences {V : Universe} [HasLinearLogic V] [HasEquivalences V] (α : Sort u)
                              [HasEquivalenceRelationBase V α] where
  [hEquivEquiv : HasHomEquivalences (asPreorder α)]
  defEquivRelSymmEquiv (a b : α) : (a ≃ b) ≃{symmFun a b, symmFun b a} (b ≃ a)

namespace HasEquivRelEquivalences

  variable {V : Universe} [HasLinearLogic V] [HasEquivalences V] {α : Sort u}
           [HasEquivalenceRelationBase V α] [h : HasEquivRelEquivalences α]

  instance : HasHomEquivalences (asPreorder α) := h.hEquivEquiv

  @[reducible] def equivRelSymmEquiv (a b : α) : (a ≃ b) ≃ (b ≃ a) := h.defEquivRelSymmEquiv a b

end HasEquivRelEquivalences


class HasHomIsoEquivalences {V : Universe} [HasLinearLogic V] [HasEquivalences V] (α : Sort u)
                            [HasPreorderRelation V α] [HasIsomorphisms α] extends
  HasHomEquivalences α, HasEquivRelEquivalences α
