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

  def swapId {A : U} (a : A) (B : U) :
    swapFun (idFun (A ⟶ B)) a
    ≃[λ _ => byDef⁻¹ • (byFunDef • byDef)]
    appFun a B :=
  rightId (appFun a B)

  def swapIdExt (A B : U) :
    swapFunFun (idFun (A ⟶ B))
    ≃[λ a => byDef⁻¹ • swapId a B • byDef]
    appFunFun A B :=
  leftId (appFunFun A B) • defCongrArg (defCompFunFun (appFunFun A B) ((A ⟶ B) ⟶ B)) (rightIdExt (A ⟶ B) B)

  def swapComp {A B C D : U} (F : A ⟶ B) (G : B ⟶ C ⟶ D) (c : C) :
    swapFun (G • F) c
    ≃[λ _ => (byDef • byDef)⁻¹ • (byFunDef • byDef)]
    swapFun G c • F :=
  (compAssoc F G (appFun c D))⁻¹

  def swapCompExt {A B C D : U} (F : A ⟶ B) (G : B ⟶ C ⟶ D) :
    swapFunFun (G • F)
    ≃[λ c => (byDef • byArgDef • byDef)⁻¹ • swapComp F G c • byDef]
    compFunFun F D • swapFunFun G :=
  compAssoc (appFunFun C D) (compFunFun G D) (compFunFun F D) •
  defCongrArg (defCompFunFun (appFunFun C D) (A ⟶ D)) (compAssocExt F G D)⁻¹

  --def swapCompExtExt {A B : U} (F : A ⟶ B) (C D : U) :
  --  swapFunFunFun A C D • compFunFun F (C ⟶ D)
  --  ≃[λ G => (byDef • byArgDef • byDef)⁻¹ • swapCompExt F G • (byDef • byArgDef • byDef)]
  --  revCompFunFun C (compFunFun F D) • swapFunFunFun B C D :=
  --sorry

  --def swapCompExtExtExt (A B C D : U) :
  --  revCompFunFun (B ⟶ C ⟶ D) (swapFunFunFun A C D) • compFunFunFun A B (C ⟶ D)
  --  ≃[λ F => (byDef • byArgDef • byArgDef₂ • byArgDef • byDef)⁻¹ • swapCompExtExt F C D • (byDef • byArgDef • byDef)]
  --  compFunFun (swapFunFunFun B C D) (C ⟶ A ⟶ D) • revCompFunFunFun C (B ⟶ D) (A ⟶ D) • compFunFunFun A B D :=
  --sorry

  def swapSwap {A B C : U} (F : A ⟶ B ⟶ C) (a : A) :
    swapFun (swapFunFun F) a
    ≃[λ _ => byDef₂ • byDef]
    F a :=
  swapApp (F a) •
  defCongrArg (defCompFunFun (appFunFun B C) C) (swapCompFun F a C) •
  swapComp (appFunFun B C) (compFunFun F C) a

  def swapSwapExt {A B C : U} (F : A ⟶ B ⟶ C) :
    swapFunFun (swapFunFun F)
    ≃[λ a => swapSwap F a • byDef]
    F :=
  leftId F •
  defCongrArg (defCompFunFun F (B ⟶ C)) (swapAppExt B C) •
  (compAssoc F (appFunFun (B ⟶ C) C) (compFunFun (appFunFun B C) C))⁻¹ •
  defCongrArg (defRevCompFunFun A (compFunFun (appFunFun B C) C)) (swapCompFunExt F C) •
  swapCompExt (appFunFun B C) (compFunFun F C)

  --def swapSwapExtExt (A B C : U) :
  --  swapFunFunFun B A C • swapFunFunFun A B C
  --  ≃[λ F => byDef⁻¹ • swapSwapExt F • (byDef • byArgDef • byDef)]
  --  idFun (A ⟶ B ⟶ C) :=
  --sorry

  def reverseSwap {A B C : U} {F : A ⟶ B ⟶ C} {G : B ⟶ A ⟶ C} : swapFunFun F ≃ G → swapFunFun G ≃ F :=
  λ e => swapSwapExt F • (defCongrArg (defSwapFunFunFun B A C) e)⁻¹

  def bySwap {A B C : U} {F : A ⟶ B ⟶ C} {G : A ⟶ B ⟶ C} : swapFunFun F ≃ swapFunFun G → G ≃ F :=
  λ e => reverseSwap e • (swapSwapExt G)⁻¹

  def compAssocMidExt {A B C D : U} (F : A ⟶ B) (H : C ⟶ D) :
    compFunFun F D • revCompFunFun B H
    ≃[λ G => (byDef • byArgDef • byDef)⁻¹ • compAssoc F G H • (byDef • byArgDef • byDef)]
    revCompFunFun A H • compFunFun F C :=
  (compAssoc (compFunFun F C) (compFunFunFun A C D) (appFun H (A ⟶ D)))⁻¹ •
  defCongrArg (defRevSwapFunFun (B ⟶ C) H (A ⟶ D)) (compAssocExtExt F C D) •
  (compAssoc (compFunFunFun B C D) (appFun H (B ⟶ D)) (compFunFun F D) •
   defCongrArg (defCompFunFun (compFunFunFun B C D) (A ⟶ D)) (swapRevCompFun (compFunFun F D) H) •
   swapComp (compFunFunFun B C D) (revCompFunFun (C ⟶ D) (compFunFun F D)) H)⁻¹

  def compAssocMidExtExt {A B : U} (F : A ⟶ B) (C D : U) :
    revCompFunFun (B ⟶ C) (compFunFun F D) • revCompFunFunFun B C D
    ≃[λ H => (byDef • byArgDef • byDef)⁻¹ • compAssocMidExt F H • (byDef • byArgDef • byDef)]
    compFunFun (compFunFun F C) (A ⟶ D) • revCompFunFunFun A C D :=
  swapCompExt (compFunFun F C) (compFunFunFun A C D) •
  defCongrArg (defSwapFunFunFun (B ⟶ C) (C ⟶ D) (A ⟶ D)) (compAssocExtExt F C D) •
  (swapCompExt (compFunFunFun B C D) (revCompFunFun (C ⟶ D) (compFunFun F D)))⁻¹ •
  defCongrArg (defRevCompFunFun (C ⟶ D) (compFunFun (compFunFunFun B C D) (A ⟶ D)))
              (swapRevCompFunExt (C ⟶ D) (compFunFun F D))⁻¹ •
  compAssoc (appFunFun (C ⟶ D) (B ⟶ D))
            (revCompFunFun ((C ⟶ D) ⟶ B ⟶ D) (compFunFun F D))
            (compFunFun (compFunFunFun B C D) (A ⟶ D)) •
  defCongrArg (defCompFunFun (appFunFun (C ⟶ D) (B ⟶ D)) ((B ⟶ C) ⟶ (A ⟶ D)))
              (compAssocMidExt (compFunFunFun B C D) (compFunFun F D))⁻¹ •
  (compAssoc (appFunFun (C ⟶ D) (B ⟶ D))
             (compFunFun (compFunFunFun B C D) (B ⟶ D))
             (revCompFunFun (B ⟶ C) (compFunFun F D)))⁻¹

  def compAssoc₄ {A B C D E : U} (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) (I : D ⟶ E) :
    ((I • H) • G) • F
    ≃[λ _ => (byArgDef₂ • byArgDef • byDef)⁻¹ • (byDef • byDef • byDef)]
    I • (H • (G • F)) :=
  compAssoc (G • F) H I • compAssoc F G (I • H)

end HasLinearFunOp.HasLinearFunExt



namespace HasAffineFunOp.HasAffineFunExt

  open MetaRelation HasFunctors HasCongrArg HasCongrFun HasLinearFunOp HasLinearFunOp.HasLinearFunExt HasSubLinearFunOp

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasAffineFunOp U] [HasAffineFunExt U]

  def swapConst (A : U) {B C : U} (F : B ⟶ C) (b : B) :
    swapFun (constFun A F) b
    ≃[λ _ => byDef⁻¹ • (byFunDef • byDef)]
    constFun A (F b) :=
  defCongrArg (defConstFunFun A C) byDef • rightConst A F (appFun b C)

  def swapConstExt (A : U) {B C : U} (F : B ⟶ C) :
    swapFunFun (constFun A F)
    ≃[λ b => (byDef • byDef)⁻¹ • swapConst A F b • byDef]
    constFunFun A C • F :=
  defCongrArg (defRevCompFunFun B (constFunFun A C)) (swapApp F) •
  compAssoc (appFunFun B C) (appFun F C) (constFunFun A C) •
  defCongrArg (defCompFunFun (appFunFun B C) (A ⟶ C)) (rightConstExt A F C)

  --def swapConstExtExt (A B C : U) :
  --  swapFunFunFun A B C • constFunFun A (B ⟶ C)
  --  ≃[λ F => byDef⁻¹ • swapConstExt A F • (byDef • byArgDef • byDef)]
  --  revCompFunFun B (constFunFun A C) :=
  --sorry

  def swapConstFunExt' (A B : U) : swapFunFun (constFunFun A B) ≃ constFun A (idFun B) :=
  reverseSwap (rightId (constFunFun A B) • swapConstExt A (idFun B))

  def swapConstFun {A : U} (a : A) (B : U) :
    swapFun (constFunFun A B) a
    ≃[λ _ => byDef⁻¹ • (byDef₂ • byDef)]
    idFun B :=
  byDef • congrFun (swapConstFunExt' A B) a • byDef⁻¹

  def swapConstFunExt (A B : U) :
    swapFunFun (constFunFun A B)
    ≃[λ a => byDef⁻¹ • swapConstFun a B • byDef]
    constFun A (idFun B) :=
  swapConstFunExt' A B

  def constConst (A B : U) {C : U} (c : C) :
    swapFunFun (constFun A (constFun B c))
    ≃[λ b => byDef⁻¹ • (defCongrArg (defConstFunFun A C) byDef • swapConst A (constFun B c) b • byDef)]
    constFun B (constFun A c) :=
  defCongrArg (defConstFunFun B (A ⟶ C)) byDef • rightConst B c (constFunFun A C) • swapConstExt A (constFun B c)

  --def constConstExt (A B C : U) :
  --  swapFunFunFun A B C • constFunFun A (B ⟶ C) • constFunFun B C
  --  ≃[λ c => (byDef • byArgDef • byDef)⁻¹ • constConst A B c • (byDef • byArgDef • byArgDef₂ • byArgDef • byDef)]
  --  constFunFun B (A ⟶ C) • constFunFun A C :=
  --sorry

end HasAffineFunOp.HasAffineFunExt



namespace HasFullFunOp.HasFullFunExt

  open HasFunctors HasCongrArg HasCongrFun HasLinearFunOp HasLinearFunOp.HasLinearFunExt
       HasSubLinearFunOp HasAffineFunOp.HasAffineFunExt HasNonLinearFunOp

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasFullFunOp U] [HasFullFunExt U]

  def substAltDef {A B C : U} (F : A ⟶ B) (G : A ⟶ B ⟶ C) :
    dupFun (swapFunFun G • F)
    ≃[λ _ => byDef⁻¹ • (byDef₂ • byFunDef • byDef)]
    substFun F G :=
  defCongrArg (defDupFunFun A C)
              (defCongrArg (defRevCompFunFun A (compFunFun F C)) (swapSwapExt G) •
               swapCompExt F (swapFunFun G)) •
  (dupSwap (swapFunFun G • F))⁻¹

  def substConstFun {A B C : U} (F : A ⟶ B) (G : B ⟶ C) :
    substFun F (constFun A G)
    ≃[λ _ => byDef⁻¹ • (byFunDef • byDef)]
    G • F :=
  dupConst (G • F) •
  defCongrArg (defDupFunFun A C) (defCongrArg (defConstFunFun A (A ⟶ C)) byDef •
                                  rightConst A G (compFunFun F C))

  --def substConstFunExt {A B : U} (F : A ⟶ B) (C : U) :
  --  substFunFun F C • constFunFun A (B ⟶ C)
  --  ≃[λ G => byDef⁻¹ • substConstFun F G • (byDef • byArgDef • byDef)]
  --  compFunFun F C :=
  --sorry

  --def substConstFunExtExt (A B C : U) :
  --  compFunFun (constFunFun A (B ⟶ C)) (A ⟶ C) • substFunFunFun A B C
  --  ≃[λ F => byDef⁻¹ • substConstFunExt F C • (byDef • byArgDef • byDef)]
  --  compFunFunFun A B C :=
  --sorry

  def substConstArg {A B C : U} (b : B) (G : A ⟶ B ⟶ C) :
    substFun (constFun A b) G
    ≃[λ _ => byDef⁻¹ • (byArgDef • byDef)]
    swapFun G b :=
  byDef •
  dupConst ((swapFunFun G) b) •
  defCongrArg (defDupFunFun A C) (rightConst A b (swapFunFun G)) •
  (substAltDef (constFun A b) G)⁻¹

  --def substConstArgExt (A : U) {B : U} (b : B) (C : U) :
  --  substFunFun (constFun A b) C
  --  ≃[λ G => byDef⁻¹ • substConstArg b G • byDef]
  --  revSwapFunFun A b C :=
  --sorry

  --def substConstArgExtExt (A B C : U) :
  --  substFunFunFun A B C • constFunFun A B
  --  ≃[λ b => byDef⁻¹ • substConstArgExt A b C • (byDef • byArgDef • byDef)]
  --  revSwapFunFunFun A B C :=
  --sorry

  def substConst (A : U) {B C : U} (b : B) (G : B ⟶ C) :
    substFun (constFun A b) (constFun A G)
    ≃[λ _ => byDef⁻¹ • (byArgDef • byFunDef • byDef)]
    constFun A (G b) :=
  rightConst A b G • substConstFun (constFun A b) G

  --def substConstExt (A : U) {B : U} (b : B) (C : U) :
  --  substFunFun (constFun A b) C • constFunFun A (B ⟶ C)
  --  ≃[λ G => (byDef • byArgDef • byDef)⁻¹ • substConst A b G • (byDef • byArgDef • byDef)]
  --  constFunFun A C • appFun b C :=
  --sorry

  --def substConstExtExt (A B C : U) :
  --  compFunFun (constFunFun A (B ⟶ C)) (A ⟶ C) • substFunFunFun A B C • constFunFun A B
  --  ≃[λ b => (byDef • byArgDef • byDef)⁻¹ • substConstExt A b C • (byDef • byArgDef • byArgDef₂ • byArgDef • byDef)]
  --  revCompFunFun (B ⟶ C) (constFunFun A C) • appFunFun B C :=
  --sorry

  def substApp {A B C : U} (F : A ⟶ B) (G : A ⟶ B ⟶ C) :
    substFun G (appFunFun B C • F)
    ≃[λ _ => byDef⁻¹ • (byDef₂ • byFunDef • byDef)]
    substFun F G :=
  substAltDef F G •
  defCongrArg (defDupFunFun A C) (compAssoc F (appFunFun B C) (compFunFun G C))⁻¹

  --def substAppExt {A B : U} (F : A ⟶ B) (C : U) :
  --  revSubstFunFun (appFunFun B C • F)
  --  ≃[λ G => byDef⁻¹ • substApp F G • byDef]
  --  substFunFun F C :=
  --sorry

  --def substAppExtExt (A B C : U) :
  --  revSubstFunFunFun A (B ⟶ C) C • revCompFunFun A (appFunFun B C)
  --  ≃[λ F => byDef⁻¹ • substAppExt F C • (byDef • byArgDef • byDef)]
  --  substFunFunFun A B C :=
  --sorry

  def substComp {A B C D : U} (F : A ⟶ B) (G : B ⟶ C) (H : A ⟶ C ⟶ D) :
    substFun F (compFunFun G D • H)
    ≃[λ _ => (byArgDef • byDef)⁻¹ • (byDef₂ • byFunDef • byDef)]
    substFun (G • F) H :=
  defCongrArg (defDupFunFun A D) (defCongrArg (defCompFunFun H (A ⟶ D)) (compAssocExt F G D) •
                                  (compAssoc H (compFunFun G D) (compFunFun F D))⁻¹)

  def substAssocLemma {A A' B C : U} (F : A ⟶ B) (G : A' ⟶ B ⟶ C) (D : U) :
    (revCompFunFun A' (compFunFun F D) • compFunFun G (B ⟶ D)) • revCompFunFunFun B C D
    ≃[λ H => (byDef • byArgDef • byDef)⁻¹ •
             compAssoc G (compFunFun F C) (revCompFunFun A H) •
             defCongrArg (defCompFunFun G (A ⟶ D)) (compAssocMidExt F H) •
             (compAssoc G (revCompFunFun B H) (compFunFun F D))⁻¹ •
             (byDef • byArgDef • byDef • byArgDef • byDef)]
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
    ≃[λ _ => (byArgDef • byDef)⁻¹ • (byDef₃ • byFunDef₂ • byFunDef • byDef)]
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

  --def substAssocExt {A B C : U} (F : A ⟶ B) (G : A ⟶ B ⟶ C) (D : U) :
  --  substFunFun F D • substFunFun G (B ⟶ D) • revCompFunFun A (revCompFunFunFun B C D)
  --  ≃[λ H => byDef⁻¹ • substAssoc F G H • (byDef • byArgDef • byArgDef₂ • byArgDef • byDef)]
  --  substFunFun (substFun F G) D :=
  --sorry

  --def substAssocExtExt {A B : U} (F : A ⟶ B) (C D : U) :
  --  revCompFunFun (A ⟶ C ⟶ D) (substFunFun F D) •
  --  compFunFun (revCompFunFun A (revCompFunFunFun B C D)) (A ⟶ B ⟶ D) •
  --  substFunFunFun A (B ⟶ C) (B ⟶ D)
  --  ≃[λ G => sorry]
  --  substFunFunFun A C D • substFunFun F C :=
  --sorry

  --def substAssocExtExtExt (A B C D : U) :
  --  compFunFun (compFunFun (revCompFunFun A (revCompFunFunFun B C D)) (A ⟶ B ⟶ D) •
  --              substFunFunFun A (B ⟶ C) (B ⟶ D))
  --             ((A ⟶ C ⟶ D) ⟶ A ⟶ D) •
  --  revCompFunFunFun (A ⟶ C ⟶ D) (A ⟶ B ⟶ D) (A ⟶ D) •
  --  substFunFunFun A B D
  --  ≃[λ F => sorry]
  --  revCompFunFun (A ⟶ B ⟶ C) (substFunFunFun A C D) • substFunFunFun A B C :=
  --sorry

  def leftDup {A B C : U} (F : A ⟶ B) (G : B ⟶ B ⟶ C) :
    dupFun G • F
    ≃[λ _ => (byFunDef • byDef)⁻¹ • (byDef • byDef)]
    substFun F (G • F) :=
  defCongrArg (defSubstFunFun F C) (substConstFun F G) •
  substDup F (constFun A G) •
  defCongrArg (defSubstFunFun F C) (defCongrArg (defConstFunFun A (B ⟶ C)) byDef •
                                    rightConst A G (dupFunFun B C))⁻¹ •
  (substConstFun F (dupFun G))⁻¹

  --def leftDupExt {A B : U} (F : A ⟶ B) (C : U) :
  --  compFunFun F C • dupFunFun B C
  --  ≃[λ G => (byDef • byArgDef • byDef)⁻¹ • leftDup F G • (byDef • byArgDef • byDef)]
  --  substFunFun F C • compFunFun F (B ⟶ C) :=
  --sorry

end HasFullFunOp.HasFullFunExt
