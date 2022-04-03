import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.MetaRelations
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.FunctorExtensionality
import UniverseAbstractions.Lemmas.DerivedFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u



namespace HasLinearFunOp.HasLinearFunExt

  open HasFunctors HasCongrArg

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasLinearFunOp U]
           [HasLinearFunExt U]

  def idId (A : U) :
    idFun A • idFun A ≃{byDefDef ▻-◅} idFun A :=
  rightId (idFun A)

  def swapApp {A : U} (a : A) (B : U) :
    swapFun (appFunFun A B) a ≃{byFunDef ▻-◅} revAppFun a B :=
  rightId (revAppFun a B)

  def swapAppExt (A B : U) :
    swapFunFun (appFunFun A B) ≃{▻ λ a => swapApp a B ◅} revAppFunFun A B :=
  leftId (revAppFunFun A B) •
  compFun.congrArg (revAppFunFun A B) (rightIdExt (A ⟶ B) B)

  def swapComp {A B C D : U} (F : A ⟶ B) (G : B ⟶ C ⟶ D) (c : C) :
    swapFun (G • F) c ≃{byFunDef ▻-◅ byDef} swapFun G c • F :=
  (compAssoc F G (revAppFun c D))⁻¹

  def swapCompExt {A B C D : U} (F : A ⟶ B) (G : B ⟶ C ⟶ D) :
    swapFunFun (G • F)
    ≃{▻ λ c => swapComp F G c ◅ byDefDef}
    compFunFun F D • swapFunFun G :=
  compAssoc (revAppFunFun C D) (compFunFun G D) (compFunFun F D) •
  compFun.congrArg (revAppFunFun C D) (compAssocExt F G D)⁻¹

  def swapCompRevApp {A B C : U} (F : A ⟶ B) (G : B ⟶ C) :
    swapFun (revAppFunFun B C • F) G ≃{byDef₂ • byFunDef ▻-◅} G • F :=
  compFun.congrArg F (swapRevApp G) •
  swapComp F (revAppFunFun B C) G

  def swapCompCompFun {A B C D : U} (F : A ⟶ C ⟶ D) (G : B ⟶ C) (b : B) :
    swapFun (compFunFun G D • F) b ≃{byDef₂ • byFunDef ▻-◅} swapFun F (G b) :=
  compFun.congrArg F (swapCompFun G b D) •
  swapComp F (compFunFun G D) b

  def swapCompRevCompFun {A B C D : U} (F : A ⟶ B ⟶ C) (G : C ⟶ D) (b : B) :
    swapFun (revCompFunFun B G • F) b ≃{byDef₂ • byFunDef ▻-◅ byArgDef} G • swapFun F b :=
  compAssoc F (revAppFun b C) G •
  compFun.congrArg F (swapRevCompFun G b) •
  swapComp F (revCompFunFun B G) b

  def swapSwap {A B C : U} (F : A ⟶ B ⟶ C) (a : A) :
    swapFun (swapFunFun F) a ≃{byDef₂ ▻|} F a :=
  swapRevApp (F a) •
  swapCompCompFun (revAppFunFun B C) F a

  def swapSwapExt {A B C : U} (F : A ⟶ B ⟶ C) :
    swapFunFun (swapFunFun F) ≃{▻ λ a => swapSwap F a} F :=
  leftId F •
  compFun.congrArg F (swapRevAppExt B C) •
  (compAssoc F (revAppFunFun (B ⟶ C) C) (compFunFun (revAppFunFun B C) C))⁻¹ •
  revCompFun.congrArg (compFunFun (revAppFunFun B C) C) (swapCompFunExt F C) •
  swapCompExt (revAppFunFun B C) (compFunFun F C)

  def reverseSwap {A B C : U} {F : A ⟶ B ⟶ C} {G : B ⟶ A ⟶ C} : swapFunFun F ≃ G → swapFunFun G ≃ F :=
  λ e => swapSwapExt F • (swapFunFun.congrArg e)⁻¹

  def bySwap {A B C : U} {F : A ⟶ B ⟶ C} {G : A ⟶ B ⟶ C} : swapFunFun F ≃ swapFunFun G → G ≃ F :=
  λ e => reverseSwap e • (swapSwapExt G)⁻¹

  def compAssocRightExtLemma (A : U) {B C : U} (G : B ⟶ C) (D : U) :
    compFunFun (compFunFun G D) (A ⟶ D) • compFunFunFun A B D ≃
    compFunFunFun A C D • revCompFunFun A G :=
  compAssoc (compFunFunFun A B C) (revAppFun G (A ⟶ C)) (compFunFunFun A C D) •
  compFun.congrArg (compFunFunFun A B C) (swapRevCompFun (compFunFunFun A C D) G) •
  swapComp (compFunFunFun A B C) (revCompFunFun (B ⟶ C) (compFunFunFun A C D)) G •
  revSwapFun.congrArg G (compAssocExtExtExt A B C D) •
  (compFun.congrArg (compFunFunFun A B D)
                    (byDef • swapSwap (compFunFunFun (C ⟶ D) (B ⟶ D) (A ⟶ D)) (compFunFun G D)) •
   swapComp (compFunFunFun A B D) (revCompFunFunFun (C ⟶ D) (B ⟶ D) (A ⟶ D)) (compFunFun G D) •
   compFun.congrArg (revCompFunFunFun (C ⟶ D) (B ⟶ D) (A ⟶ D) • compFunFunFun A B D)
                    (revAppFun.congrArg byDef ((C ⟶ D) ⟶ (A ⟶ D)) •
                     swapCompFun (compFunFunFun B C D) G ((C ⟶ D) ⟶ (A ⟶ D))) •
   swapComp (revCompFunFunFun (C ⟶ D) (B ⟶ D) (A ⟶ D) • compFunFunFun A B D)
            (compFunFun (compFunFunFun B C D) ((C ⟶ D) ⟶ (A ⟶ D)))
            G)⁻¹

  def compAssocRightExt (A : U) {B C D : U} (G : B ⟶ C) (H : C ⟶ D) :
    revCompFunFun A (H • G)
    ≃{▻ λ F => compAssoc F G H ◅ byDefDef}
    revCompFunFun A H • revCompFunFun A G :=
  swapComp (revCompFunFun A G) (compFunFunFun A C D) H •
  revSwapFun.congrArg H (compAssocRightExtLemma A G D) •
  (compFun.congrArg (compFunFunFun A B D)
                    (revAppFun.congrArg byDef (A ⟶ D) •
                     swapCompFun (compFunFun G D) H (A ⟶ D)) •
   swapComp (compFunFunFun A B D) (compFunFun (compFunFun G D) (A ⟶ D)) H)⁻¹

  def compAssocMidExt {A B C D : U} (F : A ⟶ B) (H : C ⟶ D) :
    compFunFun F D • revCompFunFun B H
    ≃{byDefDef ▻ λ G => compAssoc F G H ◅ byDefDef}
    revCompFunFun A H • compFunFun F C :=
  swapComp (compFunFun F C) (compFunFunFun A C D) H •
  revSwapFun.congrArg H (compAssocExtExt F C D) •
  (compAssoc (compFunFunFun B C D) (revAppFun H (B ⟶ D)) (compFunFun F D) •
   compFun.congrArg (compFunFunFun B C D) (swapRevCompFun (compFunFun F D) H) •
   swapComp (compFunFunFun B C D) (revCompFunFun (C ⟶ D) (compFunFun F D)) H)⁻¹

  def compAssocMidExtExt {A B : U} (F : A ⟶ B) (C D : U) :
    revCompFunFun (B ⟶ C) (compFunFun F D) • revCompFunFunFun B C D
    ≃{byDefDef ▻ λ H => compAssocMidExt F H ◅ byDefDef}
    compFunFun (compFunFun F C) (A ⟶ D) • revCompFunFunFun A C D :=
  swapCompExt (compFunFun F C) (compFunFunFun A C D) •
  swapFunFun.congrArg (compAssocExtExt F C D) •
  (swapCompExt (compFunFunFun B C D) (revCompFunFun (C ⟶ D) (compFunFun F D)))⁻¹ •
  revCompFun.congrArg (compFunFun (compFunFunFun B C D) (A ⟶ D))
                      (swapRevCompFunExt (C ⟶ D) (compFunFun F D))⁻¹ •
  compAssoc (revAppFunFun (C ⟶ D) (B ⟶ D))
            (revCompFunFun ((C ⟶ D) ⟶ B ⟶ D) (compFunFun F D))
            (compFunFun (compFunFunFun B C D) (A ⟶ D)) •
  compFun.congrArg (revAppFunFun (C ⟶ D) (B ⟶ D))
                   (compAssocMidExt (compFunFunFun B C D) (compFunFun F D))⁻¹ •
  (compAssoc (revAppFunFun (C ⟶ D) (B ⟶ D))
             (compFunFun (compFunFunFun B C D) (B ⟶ D))
             (revCompFunFun (B ⟶ C) (compFunFun F D)))⁻¹

  def compAssoc₄ {A B C D E : U} (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) (I : D ⟶ E) :
    ((I • H) • G) • F ≃{byDef • byDef ▻-◅ congrArg I (byArgDef • byDef)} I • (H • (G • F)) :=
  compAssoc (G • F) H I • compAssoc F G (I • H)

end HasLinearFunOp.HasLinearFunExt



namespace HasAffineFunOp.HasAffineFunExt

  open MetaRelation HasFunctors HasCongrFun HasLinearFunOp HasLinearFunOp.HasLinearFunExt HasSubLinearFunOp

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasAffineFunOp U] [HasAffineFunExt U]

  def swapConst (A : U) {B C : U} (F : B ⟶ C) (b : B) :
    swapFun (constFun A F) b ≃{byFunDef ▻-◅} constFun A (F b) :=
  constFun.congrArg A byDef • rightConst A F (revAppFun b C)

  def swapConstExt (A : U) {B C : U} (F : B ⟶ C) :
    swapFunFun (constFun A F)
    ≃{▻ λ b => swapConst A F b ◅ byDef}
    constFunFun A C • F :=
  revCompFun.congrArg (constFunFun A C) (swapRevApp F) •
  compAssoc (revAppFunFun B C) (revAppFun F C) (constFunFun A C) •
  compFun.congrArg (revAppFunFun B C) (rightConstExt A F C)

  def swapConstFunExt' (A B : U) : swapFunFun (constFunFun A B) ≃ constFun A (idFun B) :=
  reverseSwap (rightId (constFunFun A B) • swapConstExt A (idFun B))

  def swapConstFun {A : U} (a : A) (B : U) :
    swapFun (constFunFun A B) a ≃{byDef₂ ▻-◅} idFun B :=
  defCongrFun (swapConstFunExt' A B) a

  def swapConstFunExt (A B : U) :
    swapFunFun (constFunFun A B) ≃{▻ λ a => swapConstFun a B ◅} constFun A (idFun B) :=
  swapConstFunExt' A B

  def swapCompConstFun {A B C : U} (a : A) (F : B ⟶ C) :
    swapFun (constFunFun A C • F) a ≃{byDef₂ • byFunDef ▻|} F :=
  leftId F •
  compFun.congrArg F (swapConstFun a C) •
  swapComp F (constFunFun A C) a

  def swapConstConst (A B : U) {C : U} (c : C) :
    swapFunFun (constFun A (constFun B c))
    ≃{▻ λ b => constFun.congrArg A byDef • swapConst A (constFun B c) b ◅}
    constFun B (constFun A c) :=
  constFun.congrArg B byDef •
  rightConst B c (constFunFun A C) •
  swapConstExt A (constFun B c)

  def leftConstFunExt (A B : U) {C : U} (c : C) :
    revCompFunFun A (constFun B c)
    ≃{▻ λ F => leftConst F c ◅}
    constFun (A ⟶ B) (constFun A c) :=
  constFun.congrArg (A ⟶ B) byDef •
  swapConst (A ⟶ B) (constFunFun A C) c •
  revSwapFun.congrArg c (leftConstExtExt A B C) •
  (compFun.congrArg (compFunFunFun A B C)
                    (revAppFun.congrArg byDef (A ⟶ C) •
                     swapCompFun (constFunFun B C) c (A ⟶ C)) •
   swapComp (compFunFunFun A B C) (compFunFun (constFunFun B C) (A ⟶ C)) c)⁻¹

  def rightConstArgExt (A : U) {B C : U} (G : B ⟶ C) :
    revCompFunFun A G • constFunFun A B
    ≃{byDefDef ▻ λ b => rightConst A b G ◅ byDef}
    constFunFun A C • G :=
  revCompFun.congrArg (constFunFun A C) (swapRevApp G) •
  compAssoc (revAppFunFun B C) (revAppFun G C) (constFunFun A C) •
  compFun.congrArg (revAppFunFun B C) (swapRevCompFun (constFunFun A C) G) •
  swapComp (revAppFunFun B C) (revCompFunFun (B ⟶ C) (constFunFun A C)) G •
  revSwapFun.congrArg G (rightConstExtExt A B C) •
  (swapComp (constFunFun A B) (compFunFunFun A B C) G)⁻¹

end HasAffineFunOp.HasAffineFunExt



namespace HasFullFunOp.HasFullFunExt

  open HasFunctors HasLinearFunOp HasLinearFunOp.HasLinearFunExt
       HasSubLinearFunOp HasAffineFunOp.HasAffineFunExt HasNonLinearFunOp

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasFullFunOp U] [HasFullFunExt U]

  def dupCompRevApp {A B : U} (F : (A ⟶ B) ⟶ A) :
    dupFun (revAppFunFun A B • F) ≃{byDef₂ • byFunDef ▻-◅ byDef₂} dupFun (compFunFun F B) :=
  dupSwap (compFunFun F B) •
  dupFun.congrArg (swapCompFunExt F B)⁻¹

  def dupCompConst {A B : U} (F : A ⟶ B) :
    dupFun (constFunFun A B • F) ≃{byDef₂ • byFunDef ▻|} F :=
  dupConst F •
  dupSwap (constFun A F) •
  dupFun.congrArg (swapConstExt A F)⁻¹

  def substCompConst {A B C : U} (F : A ⟶ B) (G : A ⟶ C) :
    substFun F (constFunFun B C • G) ≃{byDef₂ • byFunDef ▻|} G :=
  dupCompConst G •
  dupFun.congrArg (compFun.congrArg G (leftConstExt F C) •
                   (compAssoc G (constFunFun B C) (compFunFun F C))⁻¹)

  def substId {A B : U} (F : A ⟶ A ⟶ B) :
    substFun (idFun A) F ≃{byArgDef ▻-◅} dupFun F :=
  dupFun.congrArg (leftId F • compFun.congrArg F (rightIdExt A B))

  def substIdExt (A B : U) :
    substFunFun (idFun A) B ≃{▻ λ F => substId F ◅} dupFunFun A B :=
  rightId (dupFunFun A B) •
  revCompFun.congrArg (dupFunFun A B)
                      (leftIdExt A (A ⟶ B) • revCompFunFun.congrArg A (rightIdExt A B))

  def dupDup {A B : U} (F : A ⟶ A ⟶ A ⟶ B) :
    dupFun (dupFunFun A B • F) ≃{byDef₂ • byFunDef ▻-◅ byFunDef} dupFun (dupFun F) :=
  substId (dupFun F) •
  substFun.congrArg (idFun A) (substId F) •
  substDup (idFun A) F •
  (substId (dupFunFun A B • F))⁻¹

  def dupDupExt (A B : U) :
    dupFunFun A B • revCompFunFun A (dupFunFun A B)
    ≃{byDefDef ▻ λ F => dupDup F ◅ byDefDef}
    dupFunFun A B • dupFunFun A (A ⟶ B) :=
  compFun.congrArg (dupFunFun A (A ⟶ B)) (substIdExt A B) •
  revCompFun.congrArg (substFunFun (idFun A) B) (substIdExt A (A ⟶ B)) •
  substDupExt (idFun A) B •
  compFun.congrArg (revCompFunFun A (dupFunFun A B)) (substIdExt A B)⁻¹

  def substAltDef {A B C : U} (F : A ⟶ B) (G : A ⟶ B ⟶ C) :
    dupFun (swapFunFun G • F) ≃{byDef₂ • byFunDef ▻-◅} substFun F G :=
  dupFun.congrArg (revCompFun.congrArg (compFunFun F C) (swapSwapExt G) •
                   swapCompExt F (swapFunFun G)) •
  (dupSwap (swapFunFun G • F))⁻¹

  def substConstFun {A B C : U} (F : A ⟶ B) (G : B ⟶ C) :
    substFun F (constFun A G) ≃{byFunDef ▻-◅} G • F :=
  dupConst (G • F) •
  dupFun.congrArg (constFun.congrArg A byDef •
                   rightConst A G (compFunFun F C))

  def substConstArg {A B C : U} (b : B) (G : A ⟶ B ⟶ C) :
    substFun (constFun A b) G ≃{byArgDef ▻-◅} swapFun G b :=
  byDef •
  dupConst ((swapFunFun G) b) •
  dupFun.congrArg (rightConst A b (swapFunFun G)) •
  (substAltDef (constFun A b) G)⁻¹

  def substConst (A : U) {B C : U} (b : B) (G : B ⟶ C) :
    substFun (constFun A b) (constFun A G) ≃{byArgDef • byFunDef ▻-◅} constFun A (G b) :=
  rightConst A b G • substConstFun (constFun A b) G

  def substCompRevApp {A B C : U} (F : A ⟶ B) (G : A ⟶ B ⟶ C) :
    substFun G (revAppFunFun B C • F) ≃{byDef₂ • byFunDef ▻-◅} substFun F G :=
  substAltDef F G •
  dupFun.congrArg (compAssoc F (revAppFunFun B C) (compFunFun G C))⁻¹

  def substComp {A B C D : U} (F : A ⟶ B) (G : B ⟶ C) (H : A ⟶ C ⟶ D) :
    substFun F (compFunFun G D • H) ≃{byDef₂ • byFunDef ▻-◅ byArgDef} substFun (G • F) H :=
  dupFun.congrArg (compFun.congrArg H (compAssocExt F G D) •
                   (compAssoc H (compFunFun G D) (compFunFun F D))⁻¹)

  def substRevComp {A B C D : U} (F : A ⟶ B) (G : C ⟶ D) (H : A ⟶ B ⟶ C) :
    substFun F (revCompFunFun B G • H) ≃{byDef₂ • byFunDef ▻-◅ byArgDef} G • substFun F H :=
  rightDup (compFunFun F C • H) G •
  dupFun.congrArg (compAssoc H (compFunFun F C) (revCompFunFun A G) •
                   compFun.congrArg H (compAssocMidExt F G) •
                   (compAssoc H (revCompFunFun B G) (compFunFun F D))⁻¹)

  def substCompFun {A B C D : U} (F : A ⟶ B ⟶ C) (G : A ⟶ C ⟶ D) :
    substFun G (compFunFunFun B C D • F)
    ≃{byDef₂ • byFunDef ▻-◅ byDef₂ • byFunDef}
    substFun F (revCompFunFunFun B C D • G) :=
  dupFun.congrArg (compAssoc G (revCompFunFunFun B C D) (compFunFun F (B ⟶ D)) •
                   compFun.congrArg G (swapCompExt F (compFunFunFun B C D))) •
  (substAltDef G (compFunFunFun B C D • F))⁻¹

  def swapCompDup {A B C : U} (F : A ⟶ B ⟶ B ⟶ C) (b : B) :
    swapFun (dupFunFun B C • F) b
    ≃{byDef₂ • byFunDef ▻-◅ byFunDef}
    swapFun (swapFun F b) b :=
  revSwapFun.congrArg b (substConstArg b F) •
  substConstArg b (substFun (constFun A b) F) •
  substDup (constFun A b) F •
  (substConstArg b (dupFunFun B C • F))⁻¹

  def swapDup {A : U} (a : A) (B : U) :
    swapFun (dupFunFun A B) a
    ≃{byDef₂ ▻-◅ byFunDef}
    swapFun (revAppFun a (A ⟶ B)) a :=
  revSwapFun.congrArg a (swapApp a (A ⟶ B)) •
  swapCompDup (idFun (A ⟶ A ⟶ B)) a •
  revSwapFun.congrArg a (rightId (dupFunFun A B))⁻¹

  def leftDup {A B C : U} (F : A ⟶ B) (G : B ⟶ B ⟶ C) :
    dupFun G • F ≃{byDef ▻-◅} biCompFun F F G :=
  substFun.congrArg F (substConstFun F G) •
  substDup F (constFun A G) •
  (substConstFun F (dupFun G) •
   substFun.congrArg F (constFun.congrArg A byDef •
                        rightConst A G (dupFunFun B C)))⁻¹

  def dupSubstAssoc {A B C : U} (F : A ⟶ A ⟶ B) (G : A ⟶ B ⟶ C) :
    dupFun (substFun F (revCompFunFunFun A B C • G))
    ≃{byDef₃ • byFunDef₂ • byFunDef ▻-◅ byArgDef}
    substFun (dupFun F) G :=
  dupFun.congrArg (compFun.congrArg G (rightDupExt F C) •
                   (revCompFun.congrArg (dupFunFun A C)
                                        (compAssoc G (revCompFunFunFun A B C) (compFunFun F (A ⟶ C))) •
                    compAssoc G (compFunFun F (A ⟶ C) • revCompFunFunFun A B C) (dupFunFun A C))⁻¹) •
  (dupDup (compFunFun F (A ⟶ C) • revCompFunFunFun A B C • G))⁻¹

  def dupSubstAssoc' {A B C : U} (F : A ⟶ A ⟶ B) (G : A ⟶ B ⟶ C) :
    dupFun (substFun G (compFunFunFun A B C • F))
    ≃{byDef₃ • byFunDef₂ • byFunDef ▻-◅ byArgDef}
    substFun (dupFun F) G :=
  dupSubstAssoc F G •
  dupFun.congrArg (substCompFun F G)

  def substAssocLemma {A A' B C : U} (F : A ⟶ B) (G : A' ⟶ B ⟶ C) (D : U) :
    (revCompFunFun A' (compFunFun F D) • compFunFun G (B ⟶ D)) • revCompFunFunFun B C D
    ≃{byDefDef • byDefDef ▻
      λ H => compAssoc G (compFunFun F C) (revCompFunFun A H) •
             compFun.congrArg G (compAssocMidExt F H) •
             (compAssoc G (revCompFunFun B H) (compFunFun F D))⁻¹
      ◅ byDefDef}
    compFunFun (compFunFun F C • G) (A ⟶ D) • revCompFunFunFun A C D :=
  compFun.congrArg (revCompFunFunFun A C D) (compAssocExt G (compFunFun F C) (A ⟶ D)) •
  (compAssoc (revCompFunFunFun A C D) (compFunFun (compFunFun F C) (A ⟶ D)) (compFunFun G (A ⟶ D)))⁻¹ •
  revCompFun.congrArg (compFunFun G (A ⟶ D)) (compAssocMidExtExt F C D) •
  compAssoc (revCompFunFunFun B C D) (revCompFunFun (B ⟶ C) (compFunFun F D)) (compFunFun G (A ⟶ D)) •
  compFun.congrArg (revCompFunFunFun B C D) (compAssocMidExt G (compFunFun F D))⁻¹

  def substAssoc {A B C D : U} (F : A ⟶ B) (G : A ⟶ B ⟶ C) (H : A ⟶ C ⟶ D) :
    substFun F (substFun G (revCompFunFunFun B C D • H))
    ≃{byDef₃ • byFunDef₂ • byFunDef ▻-◅ byArgDef}
    substFun (substFun F G) H :=
  dupSubstAssoc (compFunFun F C • G) H •
  dupFun.congrArg (dupFun.congrArg (compAssoc H
                                              (revCompFunFunFun A C D)
                                              (compFunFun (compFunFun F C • G) (A ⟶ D)) •
                                    compFun.congrArg H (substAssocLemma F G D) •
                                    (compAssoc₄ H
                                                (revCompFunFunFun B C D)
                                                (compFunFun G (B ⟶ D))
                                                (revCompFunFun A (compFunFun F D)))⁻¹) •
                   (rightDup (compFunFun G (B ⟶ D) • revCompFunFunFun B C D • H) (compFunFun F D))⁻¹)

  def substAssoc' {A B C D : U} (F : A ⟶ B) (G : A ⟶ B ⟶ C) (H : A ⟶ C ⟶ D) :
    substFun F (substFun H (compFunFunFun B C D • G))
    ≃{byDef₃ • byFunDef₂ • byFunDef ▻-◅ byArgDef}
    substFun (substFun F G) H :=
  substAssoc F G H •
  substFun.congrArg F (substCompFun G H)

end HasFullFunOp.HasFullFunExt



namespace MetaRelation

  open HasFunctors HasLinearFunOp HasLinearFunExt HasTransFun

  variable {α : Sort u} {V : Universe} [HasIdentity V] [HasInternalFunctors V] [HasLinearFunOp V]
           [HasLinearFunExt V] (R : MetaRelation α V)

  namespace opposite

    def revTransFunEq [HasTrans R] [HasTransFun R] (a : α) {b c : α} (f : R c b) :
      revTransFun (opposite R) a f ≃{▻-◅} transFun R f a :=
    byDef • swapSwap (transFunFun R c b a) f

    def revTransFunFunEq [HasTrans R] [HasTransFun R] (a b c : α) :
      revTransFunFun (opposite R) a b c ≃{▻ λ f => revTransFunEq R a f ◅} transFunFun R c b a :=
    swapSwapExt (transFunFun R c b a)

  end opposite

end MetaRelation
