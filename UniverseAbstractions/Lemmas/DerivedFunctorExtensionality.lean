import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Relations
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.FunctorExtensionality
import UniverseAbstractions.Lemmas.DerivedFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true



namespace HasLinearFunOp.HasLinearFunExt

  open MetaRelation HasFunctors HasCongrArg HasCongrFun

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasLinearFunOp U] [HasLinearFunExt U]

  def swapApp {A : U} (a : A) (B : U) :
    swapFun (appFunFun A B) a ≃{byFunDef ▻-◅} revAppFun a B :=
  rightId (revAppFun a B)

  def swapAppExt (A B : U) :
    swapFunFun (appFunFun A B) ≃{▻ λ a => swapApp a B ◅} revAppFunFun A B :=
  leftId (revAppFunFun A B) •
  defCongrArg (defCompFunFun (revAppFunFun A B) ((A ⟶ B) ⟶ B)) (rightIdExt (A ⟶ B) B)

  def swapComp {A B C D : U} (F : A ⟶ B) (G : B ⟶ C ⟶ D) (c : C) :
    swapFun (G • F) c ≃{byFunDef ▻-◅ byDef} swapFun G c • F :=
  (compAssoc F G (revAppFun c D))⁻¹

  def swapCompExt {A B C D : U} (F : A ⟶ B) (G : B ⟶ C ⟶ D) :
    swapFunFun (G • F)
    ≃{▻ λ c => swapComp F G c ◅ byDef • byArgDef}
    compFunFun F D • swapFunFun G :=
  compAssoc (revAppFunFun C D) (compFunFun G D) (compFunFun F D) •
  defCongrArg (defCompFunFun (revAppFunFun C D) (A ⟶ D)) (compAssocExt F G D)⁻¹

  def swapSwap {A B C : U} (F : A ⟶ B ⟶ C) (a : A) :
    swapFun (swapFunFun F) a ≃{byDef₂ ▻|} F a :=
  swapRevApp (F a) •
  defCongrArg (defCompFunFun (revAppFunFun B C) C) (swapCompFun F a C) •
  swapComp (revAppFunFun B C) (compFunFun F C) a

  def swapSwapExt {A B C : U} (F : A ⟶ B ⟶ C) :
    swapFunFun (swapFunFun F) ≃{▻ λ a => swapSwap F a} F :=
  leftId F •
  defCongrArg (defCompFunFun F (B ⟶ C)) (swapRevAppExt B C) •
  (compAssoc F (revAppFunFun (B ⟶ C) C) (compFunFun (revAppFunFun B C) C))⁻¹ •
  defCongrArg (defRevCompFunFun A (compFunFun (revAppFunFun B C) C)) (swapCompFunExt F C) •
  swapCompExt (revAppFunFun B C) (compFunFun F C)

  def reverseSwap {A B C : U} {F : A ⟶ B ⟶ C} {G : B ⟶ A ⟶ C} : swapFunFun F ≃ G → swapFunFun G ≃ F :=
  λ e => swapSwapExt F • (defCongrArg (defSwapFunFunFun B A C) e)⁻¹

  def bySwap {A B C : U} {F : A ⟶ B ⟶ C} {G : A ⟶ B ⟶ C} : swapFunFun F ≃ swapFunFun G → G ≃ F :=
  λ e => reverseSwap e • (swapSwapExt G)⁻¹

  def compAssocMidExt {A B C D : U} (F : A ⟶ B) (H : C ⟶ D) :
    compFunFun F D • revCompFunFun B H
    ≃{byDef • byArgDef ▻ λ G => compAssoc F G H ◅ byDef • byArgDef}
    revCompFunFun A H • compFunFun F C :=
  (compAssoc (compFunFun F C) (compFunFunFun A C D) (revAppFun H (A ⟶ D)))⁻¹ •
  defCongrArg (defRevSwapFunFun (B ⟶ C) H (A ⟶ D)) (compAssocExtExt F C D) •
  (compAssoc (compFunFunFun B C D) (revAppFun H (B ⟶ D)) (compFunFun F D) •
   defCongrArg (defCompFunFun (compFunFunFun B C D) (A ⟶ D)) (swapRevCompFun (compFunFun F D) H) •
   swapComp (compFunFunFun B C D) (revCompFunFun (C ⟶ D) (compFunFun F D)) H)⁻¹

  def compAssocMidExtExt {A B : U} (F : A ⟶ B) (C D : U) :
    revCompFunFun (B ⟶ C) (compFunFun F D) • revCompFunFunFun B C D
    ≃{byDef • byArgDef ▻ λ H => compAssocMidExt F H ◅ byDef • byArgDef}
    compFunFun (compFunFun F C) (A ⟶ D) • revCompFunFunFun A C D :=
  swapCompExt (compFunFun F C) (compFunFunFun A C D) •
  defCongrArg (defSwapFunFunFun (B ⟶ C) (C ⟶ D) (A ⟶ D)) (compAssocExtExt F C D) •
  (swapCompExt (compFunFunFun B C D) (revCompFunFun (C ⟶ D) (compFunFun F D)))⁻¹ •
  defCongrArg (defRevCompFunFun (C ⟶ D) (compFunFun (compFunFunFun B C D) (A ⟶ D)))
              (swapRevCompFunExt (C ⟶ D) (compFunFun F D))⁻¹ •
  compAssoc (revAppFunFun (C ⟶ D) (B ⟶ D))
            (revCompFunFun ((C ⟶ D) ⟶ B ⟶ D) (compFunFun F D))
            (compFunFun (compFunFunFun B C D) (A ⟶ D)) •
  defCongrArg (defCompFunFun (revAppFunFun (C ⟶ D) (B ⟶ D)) ((B ⟶ C) ⟶ (A ⟶ D)))
              (compAssocMidExt (compFunFunFun B C D) (compFunFun F D))⁻¹ •
  (compAssoc (revAppFunFun (C ⟶ D) (B ⟶ D))
             (compFunFun (compFunFunFun B C D) (B ⟶ D))
             (revCompFunFun (B ⟶ C) (compFunFun F D)))⁻¹

  def compAssoc₄ {A B C D E : U} (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) (I : D ⟶ E) :
    ((I • H) • G) • F ≃{byDef • byDef ▻-◅ byArgDef₂ • byArgDef} I • (H • (G • F)) :=
  compAssoc (G • F) H I • compAssoc F G (I • H)

end HasLinearFunOp.HasLinearFunExt



namespace HasAffineFunOp.HasAffineFunExt

  open MetaRelation HasFunctors HasCongrArg HasCongrFun HasLinearFunOp HasLinearFunOp.HasLinearFunExt HasSubLinearFunOp

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasAffineFunOp U] [HasAffineFunExt U]

  def swapConst (A : U) {B C : U} (F : B ⟶ C) (b : B) :
    swapFun (constFun A F) b ≃{byFunDef ▻-◅} constFun A (F b) :=
  defCongrArg (defConstFunFun A C) byDef • rightConst A F (revAppFun b C)

  def swapConstExt (A : U) {B C : U} (F : B ⟶ C) :
    swapFunFun (constFun A F)
    ≃{▻ λ b => swapConst A F b ◅ byDef}
    constFunFun A C • F :=
  defCongrArg (defRevCompFunFun B (constFunFun A C)) (swapRevApp F) •
  compAssoc (revAppFunFun B C) (revAppFun F C) (constFunFun A C) •
  defCongrArg (defCompFunFun (revAppFunFun B C) (A ⟶ C)) (rightConstExt A F C)

  def swapConstFunExt' (A B : U) : swapFunFun (constFunFun A B) ≃ constFun A (idFun B) :=
  reverseSwap (rightId (constFunFun A B) • swapConstExt A (idFun B))

  def swapConstFun {A : U} (a : A) (B : U) :
    swapFun (constFunFun A B) a ≃{byDef₂ ▻-◅} idFun B :=
  byDef • congrFun (swapConstFunExt' A B) a • byDef⁻¹

  def swapConstFunExt (A B : U) :
    swapFunFun (constFunFun A B) ≃{▻ λ a => swapConstFun a B ◅} constFun A (idFun B) :=
  swapConstFunExt' A B

  def swapConstConst (A B : U) {C : U} (c : C) :
    swapFunFun (constFun A (constFun B c))
    ≃{▻ λ b => defCongrArg (defConstFunFun A C) byDef • swapConst A (constFun B c) b ◅}
    constFun B (constFun A c) :=
  defCongrArg (defConstFunFun B (A ⟶ C)) byDef • rightConst B c (constFunFun A C) • swapConstExt A (constFun B c)

end HasAffineFunOp.HasAffineFunExt



namespace HasFullFunOp.HasFullFunExt

  open HasFunctors HasCongrArg HasCongrFun HasLinearFunOp HasLinearFunOp.HasLinearFunExt
       HasSubLinearFunOp HasAffineFunOp.HasAffineFunExt HasNonLinearFunOp

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasFullFunOp U] [HasFullFunExt U]

  def substAltDef {A B C : U} (F : A ⟶ B) (G : A ⟶ B ⟶ C) :
    dupFun (swapFunFun G • F) ≃{byDef₂ • byFunDef ▻-◅} substFun F G :=
  defCongrArg (defDupFunFun A C)
              (defCongrArg (defRevCompFunFun A (compFunFun F C)) (swapSwapExt G) •
               swapCompExt F (swapFunFun G)) •
  (dupSwap (swapFunFun G • F))⁻¹

  def substConstFun {A B C : U} (F : A ⟶ B) (G : B ⟶ C) :
    substFun F (constFun A G) ≃{byFunDef ▻-◅} G • F :=
  dupConst (G • F) •
  defCongrArg (defDupFunFun A C) (defCongrArg (defConstFunFun A (A ⟶ C)) byDef •
                                  rightConst A G (compFunFun F C))

  def substConstArg {A B C : U} (b : B) (G : A ⟶ B ⟶ C) :
    substFun (constFun A b) G ≃{byArgDef ▻-◅} swapFun G b :=
  byDef •
  dupConst ((swapFunFun G) b) •
  defCongrArg (defDupFunFun A C) (rightConst A b (swapFunFun G)) •
  (substAltDef (constFun A b) G)⁻¹

  def substConst (A : U) {B C : U} (b : B) (G : B ⟶ C) :
    substFun (constFun A b) (constFun A G) ≃{byArgDef • byFunDef ▻-◅} constFun A (G b) :=
  rightConst A b G • substConstFun (constFun A b) G

  def substApp {A B C : U} (F : A ⟶ B) (G : A ⟶ B ⟶ C) :
    substFun G (revAppFunFun B C • F) ≃{byDef₂ • byFunDef ▻-◅} substFun F G :=
  substAltDef F G •
  defCongrArg (defDupFunFun A C) (compAssoc F (revAppFunFun B C) (compFunFun G C))⁻¹

  def substComp {A B C D : U} (F : A ⟶ B) (G : B ⟶ C) (H : A ⟶ C ⟶ D) :
    substFun F (compFunFun G D • H) ≃{byDef₂ • byFunDef ▻-◅ byArgDef} substFun (G • F) H :=
  defCongrArg (defDupFunFun A D) (defCongrArg (defCompFunFun H (A ⟶ D)) (compAssocExt F G D) •
                                  (compAssoc H (compFunFun G D) (compFunFun F D))⁻¹)

  def substAssocLemma {A A' B C : U} (F : A ⟶ B) (G : A' ⟶ B ⟶ C) (D : U) :
    (revCompFunFun A' (compFunFun F D) • compFunFun G (B ⟶ D)) • revCompFunFunFun B C D
    ≃{byDef • byArgDef • byDef • byArgDef ▻
      λ H => compAssoc G (compFunFun F C) (revCompFunFun A H) •
             defCongrArg (defCompFunFun G (A ⟶ D)) (compAssocMidExt F H) •
             (compAssoc G (revCompFunFun B H) (compFunFun F D))⁻¹
      ◅ byDef • byArgDef}
    compFunFun (compFunFun F C • G) (A ⟶ D) • revCompFunFunFun A C D :=
  defCongrArg (defCompFunFun (revCompFunFunFun A C D) (A' ⟶ A ⟶ D))
              (compAssocExt G (compFunFun F C) (A ⟶ D)) •
  (compAssoc (revCompFunFunFun A C D) (compFunFun (compFunFun F C) (A ⟶ D)) (compFunFun G (A ⟶ D)))⁻¹ •
  defCongrArg (defRevCompFunFun (C ⟶ D) (compFunFun G (A ⟶ D)))
              (compAssocMidExtExt F C D) •
  compAssoc (revCompFunFunFun B C D) (revCompFunFun (B ⟶ C) (compFunFun F D)) (compFunFun G (A ⟶ D)) •
  defCongrArg (defCompFunFun (revCompFunFunFun B C D) (A' ⟶ A ⟶ D))
              (compAssocMidExt G (compFunFun F D))⁻¹

  def substAssoc {A B C D : U} (F : A ⟶ B) (G : A ⟶ B ⟶ C) (H : A ⟶ C ⟶ D) :
    substFun F (substFun G (revCompFunFunFun B C D • H))
    ≃{byDef₃ • byFunDef₂ • byFunDef ▻-◅ byArgDef}
    substFun (substFun F G) H :=
  defCongrArg (defDupFunFun A D)
              (compAssoc H
                         (compFunFun (compFunFun F C • G) (A ⟶ D) • revCompFunFunFun A C D)
                         (dupFunFun A D) •
               defCongrArg (defCompFunFun H (A ⟶ D)) (rightDupExt (compFunFun F C • G) D))⁻¹ •
  dupDup ((compFunFun (compFunFun F C • G) (A ⟶ D) • revCompFunFunFun A C D) • H) •
  defCongrArg (defDupFunFun A D)
              (defCongrArg (defDupFunFun A (A ⟶ D))
                           (defCongrArg (defCompFunFun H (A ⟶ A ⟶ D)) (substAssocLemma F G D) •
                            (compAssoc₄ H
                                        (revCompFunFunFun B C D)
                                        (compFunFun G (B ⟶ D))
                                        (revCompFunFun A (compFunFun F D)))⁻¹) •
               rightDup (compFunFun G (B ⟶ D) • revCompFunFunFun B C D • H) (compFunFun F D))

  def leftDup {A B C : U} (F : A ⟶ B) (G : B ⟶ B ⟶ C) :
    dupFun G • F ≃{byDef ▻-◅} biCompFun F F G :=
  defCongrArg (defSubstFunFun F C) (substConstFun F G) •
  substDup F (constFun A G) •
  defCongrArg (defSubstFunFun F C) (defCongrArg (defConstFunFun A (B ⟶ C)) byDef •
                                    rightConst A G (dupFunFun B C))⁻¹ •
  (substConstFun F (dupFun G))⁻¹

end HasFullFunOp.HasFullFunExt
