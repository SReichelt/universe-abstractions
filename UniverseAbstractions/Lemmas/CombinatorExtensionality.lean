import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.MetaRelations
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.FunctorExtensionality
import UniverseAbstractions.Lemmas.DerivedFunctors
import UniverseAbstractions.Lemmas.DerivedFunctorExtensionality
import UniverseAbstractions.Meta.Tactics.Functoriality



set_option autoBoundImplicitLocal false
--set_option pp.universes true



namespace HasLinearFunOp.HasLinearFunExt

  open MetaRelation

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasLinearFunOp U]
           [HasLinearFunExt U]

  def idFunDefExt₁ (A : U) :
    (Λ a => (idFun A) a) ≃⦃A ▻⟶ A⦄ (Λ a => a) :=
  HasRefl.refl (idFun A)

  def idFunDefExt₂ {X A : U} (F : X ⟶ A) :
    (Λ x => (idFun A) (F x)) ≃⦃X ▻⟶ A⦄ (Λ x => F x) :=
  leftId F

  def revAppFunDefExt₁ {A : U} (a : A) (B : U) :
    (Λ F => (revAppFun a B) F) ≃⦃(A ⟶ B) ▻⟶ B⦄ (Λ F => F a) :=
  HasRefl.refl (revAppFun a B)

  def revAppFunDefExt₂ {X A B : U} (a : A) (F : X ⟶ (A ⟶ B)) :
    (Λ x => (revAppFun a B) (F x)) ≃⦃X ▻⟶ B⦄ (Λ x => (F x) a) :=
  HasRefl.refl (swapFun F a)

  def revAppFunDefExt₃ {A B : U} (F : A ⟶ B) :
    (Λ a => (revAppFun a B) F) ≃⦃A ▻⟶ B⦄ (Λ a => F a) :=
  swapRevApp F

  def revAppFunDefExt₄ {X A B : U} (F : A ⟶ B) (H : X ⟶ A) :
    (Λ x => (revAppFun (H x) B) F) ≃⦃X ▻⟶ B⦄ (Λ x => F (H x)) :=
  swapCompRevApp H F

  def revAppFunFunDefExt₁ (A B : U) :
    (Λ a => (revAppFunFun A B) a) ≃⦃A ▻⟶ ((A ⟶ B) ⟶ B)⦄ (Λ a => revAppFun a B) :=
  HasRefl.refl (revAppFunFun A B)

  def revAppFunFunDefExt₂ {X A : U} (F : X ⟶ A) (B : U) :
    (Λ x => (revAppFunFun A B) (F x)) ≃⦃X ▻⟶ ((A ⟶ B) ⟶ B)⦄ (Λ x => revAppFun (F x) B) :=
  HasRefl.refl (revAppFunFun A B • F)

  def compFunDefExt₁ {A B C : U} (F : A ⟶ B) (G : B ⟶ C) :
    (Λ a => (G • F) a) ≃⦃A ▻⟶ C⦄ (Λ a => G (F a)) :=
  HasRefl.refl (G • F)

  def compFunDefExt₂ {X A B C : U} (F : A ⟶ B) (G : B ⟶ C) (H : X ⟶ A) :
    (Λ x => (G • F) (H x)) ≃⦃X ▻⟶ C⦄ (Λ x => G (F (H x))) :=
  compAssoc H F G

  def compFunDefExt₃ {A B C : U} (F : A ⟶ B) (a : A) :
    (Λ G => (G • F) a) ≃⦃(B ⟶ C) ▻⟶ C⦄ (Λ G => G (F a)) :=
  swapCompFun F a C

  def compFunDefExt₄ {X A B C : U} (F : A ⟶ B) (G : X ⟶ (B ⟶ C)) (a : A) :
    (Λ x => (G x • F) a) ≃⦃X ▻⟶ C⦄ (Λ x => (G x) (F a)) :=
  swapCompCompFun G F a

  def compFunDefExt₅ {A B C : U} (G : B ⟶ C) (a : A) :
    (Λ F => (G • F) a) ≃⦃(A ⟶ B) ▻⟶ C⦄ (Λ F => G (F a)) :=
  swapRevCompFun G a

  def compFunDefExt₆ {X A B C : U} (F : X ⟶ (A ⟶ B)) (G : B ⟶ C) (a : A) :
    (Λ x => (G • F x) a) ≃⦃X ▻⟶ C⦄ (Λ x => G ((F x) a)) :=
  swapCompRevCompFun F G a

  def compFunFunDefExt₁ {A B : U} (F : A ⟶ B) (C : U) :
    (Λ G => (compFunFun F C) G) ≃⦃(B ⟶ C) ▻⟶ (A ⟶ C)⦄ (Λ G => G • F) :=
  HasRefl.refl (compFunFun F C)

  def compFunFunDefExt₂ {X A B C : U} (F : A ⟶ B) (G : X ⟶ (B ⟶ C)) :
    (Λ x => (compFunFun F C) (G x)) ≃⦃X ▻⟶ (A ⟶ C)⦄ (Λ x => G x • F) :=
  HasRefl.refl (compFunFun F C • G)

  def compFunFunDefExt₃ (A : U) {B C : U} (G : B ⟶ C) :
    (Λ F => (compFunFun F C) G) ≃⦃(A ⟶ B) ▻⟶ (A ⟶ C)⦄ (Λ F => G • F) :=
  HasRefl.refl (revCompFunFun A G)

  def compFunFunDefExt₄ {X A B C : U} (F : X ⟶ (A ⟶ B)) (G : B ⟶ C) :
    (Λ x => (compFunFun (F x) C) G) ≃⦃X ▻⟶ (A ⟶ C)⦄ (Λ x => G • F x) :=
  swapComp F (compFunFunFun A B C) G

  def compFunFunFunDefExt₁ (A B C : U) :
    (Λ F => (compFunFunFun A B C) F) ≃⦃(A ⟶ B) ▻⟶ ((B ⟶ C) ⟶ (A ⟶ C))⦄ (Λ F => compFunFun F C) :=
  HasRefl.refl (compFunFunFun A B C)

  def compFunFunFunDefExt₂ {X A B : U} (F : X ⟶ (A ⟶ B)) (C : U) :
    (Λ x => (compFunFunFun A B C) (F x)) ≃⦃X ▻⟶ ((B ⟶ C) ⟶ (A ⟶ C))⦄ (Λ x => compFunFun (F x) C) :=
  HasRefl.refl (compFunFunFun A B C • F)

end HasLinearFunOp.HasLinearFunExt



namespace HasAffineFunOp.HasAffineFunExt

  open MetaRelation HasSubLinearFunOp

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasAffineFunOp U] [HasAffineFunExt U]

  def constFunDefExt₁ (A : U) {B : U} (b : B) :
    (Λ a => (constFun A b) a) ≃⦃A ▻⟶ B⦄ (Λ a => b) :=
  HasRefl.refl (constFun A b)

  def constFunDefExt₂ {X A B : U} (F : X ⟶ A) (b : B) :
    (Λ x => (constFun A b) (F x)) ≃⦃X ▻⟶ B⦄ (Λ x => b) :=
  leftConst F b

  def constFunDefExt₃ {A : U} (a : A) (B : U) :
    (Λ b => (constFun A b) a) ≃⦃B ▻⟶ B⦄ (Λ b => b) :=
  swapConstFun a B

  def constFunDefExt₄ {X A B : U} (a : A) (G : X ⟶ B) :
    (Λ x => (constFun A (G x)) a) ≃⦃X ▻⟶ B⦄ (Λ x => G x) :=
  swapCompConstFun a G

  def constFunFunDef₁ (A B : U) :
    (Λ b => (constFunFun A B) b) ≃⦃B ▻⟶ (A ⟶ B)⦄ (Λ b => constFun A b) :=
  HasRefl.refl (constFunFun A B)

  def constFunFunDef₂ {X : U} (A : U) {B : U} (F : X ⟶ B) :
    (Λ x => (constFunFun A B) (F x)) ≃⦃X ▻⟶ (A ⟶ B)⦄ (Λ x => constFun A (F x)) :=
  HasRefl.refl (constFunFun A B • F)

end HasAffineFunOp.HasAffineFunExt



namespace HasFullFunOp.HasFullFunExt

  open MetaRelation HasFunctors HasCongrArg HasLinearFunOp HasLinearFunExt HasSubLinearFunOp
       HasAffineFunOp HasAffineFunExt HasNonLinearFunOp

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasFullFunOp U] [HasFullFunExt U]

  def revAppFunDefExt₅ {A B : U} (F : (A ⟶ B) ⟶ A) :
    (Λ G => (revAppFun (F G) B) G) ≃⦃(A ⟶ B) ▻⟶ B⦄ (Λ G => G (F G)) :=
  defCongrArg (defDupFunFun (A ⟶ B) B) (rightId (compFunFun F B))⁻¹ •
  dupCompRevApp F

  def revAppFunDefExt₆ {X A B : U} (F : X ⟶ A) (G : X ⟶ (A ⟶ B)) :
    (Λ x => (revAppFun (F x) B) (G x)) ≃⦃X ▻⟶ B⦄ (Λ x => (G x) (F x)) :=
  substCompRevApp F G

  def compFunDefExt₇ {A B C : U} (F : A ⟶ B) (G : A ⟶ (B ⟶ C)) :
    (Λ a => (G a • F) a) ≃⦃A ▻⟶ C⦄ (Λ a => (G a) (F a)) :=
  HasRefl.refl (substFun F G)

  def compFunDefExt₈ {X A B C : U} (F : A ⟶ B) (G : X ⟶ (B ⟶ C)) (H : X ⟶ A) :
    (Λ x => (G x • F) (H x)) ≃⦃X ▻⟶ C⦄ (Λ x => (G x) (F (H x))) :=
  substComp H F G

  def compFunDefExt₉ {A B C : U} (F : A ⟶ (A ⟶ B)) (G : B ⟶ C) :
    (Λ a => (G • F a) a) ≃⦃A ▻⟶ C⦄ (Λ a => G ((F a) a)) :=
  rightDup F G

  def compFunDefExt₁₀ {X A B C : U} (F : X ⟶ (A ⟶ B)) (G : B ⟶ C) (H : X ⟶ A) :
    (Λ x => (G • F x) (H x)) ≃⦃X ▻⟶ C⦄ (Λ x => G ((F x) (H x))) :=
  substRevComp H G F

  def compFunDefExt₁₁ {A B C : U} (F : A ⟶ (A ⟶ B)) (G : A ⟶ (B ⟶ C)) :
    (Λ a => (G a • F a) a) ≃⦃A ▻⟶ C⦄ (Λ a => (G a) ((F a) a)) :=
  dupSubstAssoc F G

  def compFunDefExt₁₂ {X A B C : U} (F : X ⟶ (A ⟶ B)) (G : X ⟶ (B ⟶ C)) (H : X ⟶ A) :
    (Λ x => (G x • F x) (H x)) ≃⦃X ▻⟶ C⦄ (Λ x => (G x) ((F x) (H x))) :=
  substAssoc H F G

  def compFunFunDefExt₅ {A B C : U} (F : (B ⟶ C) ⟶ (A ⟶ B)) :
    (Λ G => (compFunFun (F G) C) G) ≃⦃(B ⟶ C) ▻⟶ (A ⟶ C)⦄ (Λ G => G • F G) :=
  substAltDef F (revCompFunFunFun A B C) •
  defCongrArg (defDupFunFun (B ⟶ C) (A ⟶ C))
              (defCongrArg (HasCompFunFun.defCompFunFun F ((B ⟶ C) ⟶ (A ⟶ C)))
                           (swapSwapExt (compFunFunFun A B C))⁻¹)

  def compFunFunDefExt₆ {X A B C : U} (F : X ⟶ (A ⟶ B)) (G : X ⟶ (B ⟶ C)) :
    (Λ x => (compFunFun (F x) C) (G x)) ≃⦃X ▻⟶ (A ⟶ C)⦄ (Λ x => G x • F x) :=
  substCompFun F G

  def constFunDefExt₄ {A B : U} (F : A ⟶ B) :
    (Λ a => (constFun A (F a)) a) ≃⦃A ▻⟶ B⦄ (Λ a => F a) :=
  dupCompConst F

  def constFunDefExt₅ {X A B : U} (F : X ⟶ A) (G : X ⟶ B) :
    (Λ x => (constFun A (G x)) (F x)) ≃⦃X ▻⟶ B⦄ (Λ x => G x) :=
  substCompConst F G

  def dupFunDefExt₁ {A B : U} (F : A ⟶ A ⟶ B) :
    (Λ a => (dupFun F) a) ≃⦃A ▻⟶ B⦄ (Λ a => F a a) :=
  HasRefl.refl (dupFun F)

  def dupFunDefExt₂ {X A B : U} (F : A ⟶ A ⟶ B) (G : X ⟶ A) :
    (Λ x => (dupFun F) (G x)) ≃⦃X ▻⟶ B⦄ (Λ x => F (G x) (G x)) :=
  leftDup G F

  def dupFunDefExt₃ {A : U} (a : A) (B : U) :
    (Λ F => (dupFun F) a) ≃⦃(A ⟶ A ⟶ B) ▻⟶ B⦄ (Λ F => F a a) :=
  swapDup a B

  def dupFunDefExt₄ {X A B : U} (F : X ⟶ (A ⟶ A ⟶ B)) (a : A) :
    (Λ x => (dupFun (F x)) a) ≃⦃X ▻⟶ B⦄ (Λ x => (F x) a a) :=
  swapCompDup F a

  def dupFunDefExt₅ {A B : U} (F : A ⟶ (A ⟶ A ⟶ B)) :
    (Λ a => (dupFun (F a)) a) ≃⦃A ▻⟶ B⦄ (Λ a => (F a) a a) :=
  dupDup F

  def dupFunDefExt₆ {X A B : U} (F : X ⟶ (A ⟶ A ⟶ B)) (G : X ⟶ A) :
    (Λ x => (dupFun (F x)) (G x)) ≃⦃X ▻⟶ B⦄ (Λ x => (F x) (G x) (G x)) :=
  substDup G F

  def dupFunFunDefExt₁ (A B : U) :
    (Λ F => (dupFunFun A B) F) ≃⦃(A ⟶ A ⟶ B) ▻⟶ (A ⟶ B)⦄ (Λ F => dupFun F) :=
  HasRefl.refl (dupFunFun A B)

  def dupFunFunDefExt₂ {X A B : U} (F : X ⟶ (A ⟶ A ⟶ B)) :
    (Λ x => (dupFunFun A B) (F x)) ≃⦃X ▻⟶ (A ⟶ B)⦄ (Λ x => dupFun (F x)) :=
  HasRefl.refl (dupFunFun A B • F)

end HasFullFunOp.HasFullFunExt
