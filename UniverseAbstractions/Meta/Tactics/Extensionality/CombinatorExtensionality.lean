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

  open MetaRelation HasCongrArg

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasLinearFunOp U]
           [HasLinearFunExt U]

  -- `idFun`

  @[reducible] def idFunDefExt_a_id (A : U) :
    (Λ a => (idFun A) a) ≃⦃A ▻ λ a => (HasIdFun.defIdFun A).eff a ◅ A⦄ (Λ a => a) :=
  HasRefl.refl (idFun A)

  @[reducible] def idFunDefExt_a_fun {X A : U} (F : X ⟶ A) :
    (Λ x => (idFun A) (F x)) ≃⦃X ▻ λ x => (HasIdFun.defIdFun A).eff (F x) ◅ A⦄ (Λ x => F x) :=
  leftId F

  -- `revAppFun`

  @[reducible] def revAppFunDefExt_F_id {A : U} (a : A) (B : U) :
    (Λ F => (revAppFun a B) F) ≃⦃A ⟶ B ▻ λ F => (HasRevAppFun.defRevAppFun a B).eff F ◅ B⦄ (Λ F => F a) :=
  HasRefl.refl (revAppFun a B)

  @[reducible] def revAppFunDefExt_F_fun {X A B : U} (a : A) (F : X ⟶ (A ⟶ B)) :
    (Λ x => (revAppFun a B) (F x)) ≃⦃X ▻ λ x => (HasRevAppFun.defRevAppFun a B).eff (F x) ◅ B⦄ (Λ x => (F x) a) :=
  HasRefl.refl (swapFun F a)

  @[reducible] def revAppFunDefExt_a_id {A B : U} (F : A ⟶ B) :
    (Λ a => (revAppFun a B) F) ≃⦃A ▻ λ a => (HasRevAppFun.defRevAppFun a B).eff F ◅ B⦄ (Λ a => F a) :=
  swapRevApp F

  @[reducible] def revAppFunDefExt_a_fun {X A B : U} (H : X ⟶ A) (F : A ⟶ B) :
    (Λ x => (revAppFun (H x) B) F) ≃⦃X ▻ λ x => (HasRevAppFun.defRevAppFun (H x) B).eff F ◅ B⦄ (Λ x => F (H x)) :=
  swapCompRevApp H F

  -- `revAppFunFun`

  @[reducible] def revAppFunFunDefExt_a_id (A B : U) :
    (Λ a => (revAppFunFun A B) a) ≃⦃A ▻ λ a => (defRevAppFunFun A B).eff a ◅ (A ⟶ B) ⟶ B⦄ (Λ a => revAppFun a B) :=
  HasRefl.refl (revAppFunFun A B)

  @[reducible] def revAppFunFunDefExt_a_fun {X A : U} (F : X ⟶ A) (B : U) :
    (Λ x => (revAppFunFun A B) (F x)) ≃⦃X ▻ λ x => (defRevAppFunFun A B).eff (F x) ◅ (A ⟶ B) ⟶ B⦄ (Λ x => revAppFun (F x) B) :=
  HasRefl.refl (revAppFunFun A B • F)

  -- `compFun`

  @[reducible] def compFunDefExt_a_id {A B C : U} (F : A ⟶ B) (G : B ⟶ C) :
    (Λ a => (G • F) a) ≃⦃A ▻ λ a => (HasCompFun.defCompFun F G).eff a ◅ C⦄ (Λ a => G (F a)) :=
  HasRefl.refl (G • F)

  @[reducible] def compFunDefExt_a_fun {X A B C : U} (F : A ⟶ B) (G : B ⟶ C) (H : X ⟶ A) :
    (Λ x => (G • F) (H x)) ≃⦃X ▻ λ x => (HasCompFun.defCompFun F G).eff (H x) ◅ C⦄ (Λ x => G (F (H x))) :=
  compAssoc H F G

  @[reducible] def compFunDefExt_G_id {A B : U} (F : A ⟶ B) (C : U) (a : A) :
    (Λ G => (G • F) a) ≃⦃B ⟶ C ▻ λ G => (HasCompFun.defCompFun F G).eff a ◅ C⦄ (Λ G => G (F a)) :=
  swapCompFun F a C

  @[reducible] def compFunDefExt_G_fun {X A B C : U} (F : A ⟶ B) (G : X ⟶ (B ⟶ C)) (a : A) :
    (Λ x => (G x • F) a) ≃⦃X ▻ λ x => (HasCompFun.defCompFun F (G x)).eff a ◅ C⦄ (Λ x => (G x) (F a)) :=
  swapCompCompFun G F a

  @[reducible] def compFunDefExt_F_id {A B C : U} (G : B ⟶ C) (a : A) :
    (Λ F => (G • F) a) ≃⦃A ⟶ B ▻ λ F => (HasCompFun.defCompFun F G).eff a ◅ C⦄ (Λ F => G (F a)) :=
  swapRevCompFun G a

  @[reducible] def compFunDefExt_F_fun {X A B C : U} (F : X ⟶ (A ⟶ B)) (G : B ⟶ C) (a : A) :
    (Λ x => (G • F x) a) ≃⦃X ▻ λ x => (HasCompFun.defCompFun (F x) G).eff a ◅ C⦄ (Λ x => G ((F x) a)) :=
  swapCompRevCompFun F G a

  -- `compFunFun`

  @[reducible] def compFunFunDefExt_G_id {A B : U} (F : A ⟶ B) (C : U) :
    (Λ G => (compFunFun F C) G) ≃⦃B ⟶ C ▻ λ G => (HasCompFunFun.defCompFunFun F C).eff G ◅ A ⟶ C⦄ (Λ G => G • F) :=
  HasRefl.refl (compFunFun F C)

  @[reducible] def compFunFunDefExt_G_fun {X A B C : U} (F : A ⟶ B) (G : X ⟶ (B ⟶ C)) :
    (Λ x => (compFunFun F C) (G x)) ≃⦃X ▻ λ x => (HasCompFunFun.defCompFunFun F C).eff (G x) ◅ A ⟶ C⦄ (Λ x => G x • F) :=
  HasRefl.refl (compFunFun F C • G)

  @[reducible] def compFunFunDefExt_F_id (A : U) {B C : U} (G : B ⟶ C) :
    (Λ F => (compFunFun F C) G) ≃⦃A ⟶ B ▻ λ F => (HasCompFunFun.defCompFunFun F C).eff G ◅ A ⟶ C⦄ (Λ F => G • F) :=
  HasRefl.refl (revCompFunFun A G)

  @[reducible] def compFunFunDefExt_F_fun {X A B C : U} (F : X ⟶ (A ⟶ B)) (G : B ⟶ C) :
    (Λ x => (compFunFun (F x) C) G) ≃⦃X ▻ λ x => (HasCompFunFun.defCompFunFun (F x) C).eff G ◅ A ⟶ C⦄ (Λ x => G • F x) :=
  swapComp F (compFunFunFun A B C) G

  -- `compFunFunFun`

  @[reducible] def compFunFunFunDefExt_F_id (A B C : U) :
    (Λ F => (compFunFunFun A B C) F) ≃⦃A ⟶ B ▻ λ F => (defCompFunFunFun A B C).eff F ◅ (B ⟶ C) ⟶ (A ⟶ C)⦄ (Λ F => compFunFun F C) :=
  HasRefl.refl (compFunFunFun A B C)

  @[reducible] def compFunFunFunDefExt_F_fun {X A B : U} (F : X ⟶ (A ⟶ B)) (C : U) :
    (Λ x => (compFunFunFun A B C) (F x)) ≃⦃X ▻ λ x => (defCompFunFunFun A B C).eff (F x) ◅ (B ⟶ C) ⟶ (A ⟶ C)⦄ (Λ x => compFunFun (F x) C) :=
  HasRefl.refl (compFunFunFun A B C • F)

end HasLinearFunOp.HasLinearFunExt



namespace HasAffineFunOp.HasAffineFunExt

  open MetaRelation HasSubLinearFunOp

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasAffineFunOp U] [HasAffineFunExt U]

  -- `constFun`

  @[reducible] def constFunDefExt_a_id (A : U) {B : U} (b : B) :
    (Λ a => (constFun A b) a) ≃⦃A ▻ λ a => (HasConstFun.defConstFun A b).eff a ◅ B⦄ (Λ a => b) :=
  HasRefl.refl (constFun A b)

  @[reducible] def constFunDefExt_a_fun {X A B : U} (F : X ⟶ A) (b : B) :
    (Λ x => (constFun A b) (F x)) ≃⦃X ▻ λ x => (HasConstFun.defConstFun A b).eff (F x) ◅ B⦄ (Λ x => b) :=
  leftConst F b

  @[reducible] def constFunDefExt_b_id {A : U} (a : A) (B : U) :
    (Λ b => (constFun A b) a) ≃⦃B ▻ λ b => (HasConstFun.defConstFun A b).eff a ◅ B⦄ (Λ b => b) :=
  swapConstFun a B

  @[reducible] def constFunDefExt_b_fun {X A B : U} (a : A) (G : X ⟶ B) :
    (Λ x => (constFun A (G x)) a) ≃⦃X ▻ λ x => (HasConstFun.defConstFun A (G x)).eff a ◅ B⦄ (Λ x => G x) :=
  swapCompConstFun a G

  -- `constFunFun`

  @[reducible] def constFunFunDef_b_id (A B : U) :
    (Λ b => (constFunFun A B) b) ≃⦃B ▻ λ b => (defConstFunFun A B).eff b ◅ A ⟶ B⦄ (Λ b => constFun A b) :=
  HasRefl.refl (constFunFun A B)

  @[reducible] def constFunFunDef_b_fun {X : U} (A : U) {B : U} (F : X ⟶ B) :
    (Λ x => (constFunFun A B) (F x)) ≃⦃X ▻ λ x => (defConstFunFun A B).eff (F x) ◅ A ⟶ B⦄ (Λ x => constFun A (F x)) :=
  HasRefl.refl (constFunFun A B • F)

end HasAffineFunOp.HasAffineFunExt



namespace HasFullFunOp.HasFullFunExt

  open MetaRelation HasFunctors HasCongrArg HasLinearFunOp HasLinearFunExt HasSubLinearFunOp
       HasAffineFunOp HasAffineFunExt HasNonLinearFunOp

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasFullFunOp U] [HasFullFunExt U]

  -- `revAppFun`

  @[reducible] def revAppFunDefExt_G_id_F_fun {A B : U} (F : (A ⟶ B) ⟶ A) :
    (Λ G => (revAppFun (F G) B) G) ≃⦃A ⟶ B ▻ λ G => (HasRevAppFun.defRevAppFun (F G) B).eff G ◅ B⦄ (Λ G => G (F G)) :=
  defCongrArg (defDupFunFun (A ⟶ B) B) (rightId (compFunFun F B))⁻¹ •
  dupCompRevApp F

  @[reducible] def revAppFunDefExt_G_fun_F_fun {X A B : U} (F : X ⟶ A) (G : X ⟶ (A ⟶ B)) :
    (Λ x => (revAppFun (F x) B) (G x)) ≃⦃X ▻ λ x => (HasRevAppFun.defRevAppFun (F x) B).eff (G x) ◅ B⦄ (Λ x => (G x) (F x)) :=
  substCompRevApp F G

  -- `compFun`

  @[reducible] def compFunDefExt_a_id_G_fun {A B C : U} (F : A ⟶ B) (G : A ⟶ (B ⟶ C)) :
    (Λ a => (G a • F) a) ≃⦃A ▻ λ a => (HasCompFun.defCompFun F (G a)).eff a ◅ C⦄ (Λ a => (G a) (F a)) :=
  HasRefl.refl (substFun F G)

  @[reducible] def compFunDefExt_a_fun_G_fun {X A B C : U} (F : A ⟶ B) (G : X ⟶ (B ⟶ C)) (H : X ⟶ A) :
    (Λ x => (G x • F) (H x)) ≃⦃X ▻ λ x => (HasCompFun.defCompFun F (G x)).eff (H x) ◅ C⦄ (Λ x => (G x) (F (H x))) :=
  substComp H F G

  @[reducible] def compFunDefExt_a_id_F_fun {A B C : U} (F : A ⟶ (A ⟶ B)) (G : B ⟶ C) :
    (Λ a => (G • F a) a) ≃⦃A ▻ λ a => (HasCompFun.defCompFun (F a) G).eff a ◅ C⦄ (Λ a => G ((F a) a)) :=
  rightDup F G

  @[reducible] def compFunDefExt_a_fun_F_fun {X A B C : U} (F : X ⟶ (A ⟶ B)) (G : B ⟶ C) (H : X ⟶ A) :
    (Λ x => (G • F x) (H x)) ≃⦃X ▻ λ x => (HasCompFun.defCompFun (F x) G).eff (H x) ◅ C⦄ (Λ x => G ((F x) (H x))) :=
  substRevComp H G F

  @[reducible] def compFunDefExt_a_id_F_fun_G_fun {A B C : U} (F : A ⟶ (A ⟶ B)) (G : A ⟶ (B ⟶ C)) :
    (Λ a => (G a • F a) a) ≃⦃A ▻ λ a => (HasCompFun.defCompFun (F a) (G a)).eff a ◅ C⦄ (Λ a => (G a) ((F a) a)) :=
  dupSubstAssoc' F G

  @[reducible] def compFunDefExt_a_fun_F_fun_G_fun {X A B C : U} (F : X ⟶ (A ⟶ B)) (G : X ⟶ (B ⟶ C)) (H : X ⟶ A) :
    (Λ x => (G x • F x) (H x)) ≃⦃X ▻ λ x => (HasCompFun.defCompFun (F x) (G x)).eff (H x) ◅ C⦄ (Λ x => (G x) ((F x) (H x))) :=
  substAssoc' H F G

  -- `compFunFun`

  @[reducible] def compFunFunDefExt_G_id_F_fun {A B C : U} (F : (B ⟶ C) ⟶ (A ⟶ B)) :
    (Λ G => (compFunFun (F G) C) G) ≃⦃B ⟶ C ▻ λ G => (HasCompFunFun.defCompFunFun (F G) C).eff G ◅ A ⟶ C⦄ (Λ G => G • F G) :=
  HasRefl.refl (dupFun (compFunFunFun A B C • F))

  @[reducible] def compFunFunDefExt_G_fun_F_fun {X A B C : U} (F : X ⟶ (A ⟶ B)) (G : X ⟶ (B ⟶ C)) :
    (Λ x => (compFunFun (F x) C) (G x)) ≃⦃X ▻ λ x => (HasCompFunFun.defCompFunFun (F x) C).eff (G x) ◅ A ⟶ C⦄ (Λ x => G x • F x) :=
  HasRefl.refl (substFun G (compFunFunFun A B C • F))

  -- `constFun`

  @[reducible] def constFunDefExt_a_id_F_fun {A B : U} (F : A ⟶ B) :
    (Λ a => (constFun A (F a)) a) ≃⦃A ▻ λ a => (HasConstFun.defConstFun A (F a)).eff a ◅ B⦄ (Λ a => F a) :=
  dupCompConst F

  @[reducible] def constFunDefExt_a_fun_F_fun {X A B : U} (F : X ⟶ A) (G : X ⟶ B) :
    (Λ x => (constFun A (G x)) (F x)) ≃⦃X ▻ λ x => (HasConstFun.defConstFun A (G x)).eff (F x) ◅ B⦄ (Λ x => G x) :=
  substCompConst F G

  -- `dupFun`

  @[reducible] def dupFunDefExt_a_id {A B : U} (F : A ⟶ A ⟶ B) :
    (Λ a => (dupFun F) a) ≃⦃A ▻ λ a => (HasDupFun.defDupFun F).eff a ◅ B⦄ (Λ a => F a a) :=
  HasRefl.refl (dupFun F)

  @[reducible] def dupFunDefExt_a_fun {X A B : U} (F : A ⟶ A ⟶ B) (G : X ⟶ A) :
    (Λ x => (dupFun F) (G x)) ≃⦃X ▻ λ x => (HasDupFun.defDupFun F).eff (G x) ◅ B⦄ (Λ x => F (G x) (G x)) :=
  leftDup G F

  @[reducible] def dupFunDefExt_F_id {A : U} (a : A) (B : U) :
    (Λ F => (dupFun F) a) ≃⦃A ⟶ A ⟶ B ▻ λ F => (HasDupFun.defDupFun F).eff a ◅ B⦄ (Λ F => F a a) :=
  swapDup a B

  @[reducible] def dupFunDefExt_F_fun {X A B : U} (F : X ⟶ (A ⟶ A ⟶ B)) (a : A) :
    (Λ x => (dupFun (F x)) a) ≃⦃X ▻ λ x => (HasDupFun.defDupFun (F x)).eff a ◅ B⦄ (Λ x => (F x) a a) :=
  swapCompDup F a

  @[reducible] def dupFunDefExt_a_id_F_fun {A B : U} (F : A ⟶ (A ⟶ A ⟶ B)) :
    (Λ a => (dupFun (F a)) a) ≃⦃A ▻ λ a => (HasDupFun.defDupFun (F a)).eff a ◅ B⦄ (Λ a => (F a) a a) :=
  dupDup F

  @[reducible] def dupFunDefExt_a_fun_F_fun {X A B : U} (F : X ⟶ (A ⟶ A ⟶ B)) (G : X ⟶ A) :
    (Λ x => (dupFun (F x)) (G x)) ≃⦃X ▻ λ x => (HasDupFun.defDupFun (F x)).eff (G x) ◅ B⦄ (Λ x => (F x) (G x) (G x)) :=
  substDup G F

  -- `dupFunFun`

  @[reducible] def dupFunFunDefExt_F_id (A B : U) :
    (Λ F => (dupFunFun A B) F) ≃⦃A ⟶ A ⟶ B ▻ λ F => (defDupFunFun A B).eff F ◅ A ⟶ B⦄ (Λ F => dupFun F) :=
  HasRefl.refl (dupFunFun A B)

  @[reducible] def dupFunFunDefExt_F_fun {X A B : U} (F : X ⟶ (A ⟶ A ⟶ B)) :
    (Λ x => (dupFunFun A B) (F x)) ≃⦃X ▻ λ x => (defDupFunFun A B).eff (F x) ◅ A ⟶ B⦄ (Λ x => dupFun (F x)) :=
  HasRefl.refl (dupFunFun A B • F)

end HasFullFunOp.HasFullFunExt
