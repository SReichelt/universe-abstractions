import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.FunctorExtensionality
import UniverseAbstractions.Lemmas.DerivedFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true



variable (U : Universe) [HasIdentity U] [HasInternalFunctors U]



namespace HasLinearFunOp

  open HasFunctors HasCongrArg HasCongrFun HasCompFun

  variable [HasLinearFunOp U]

  class HasDirectLinearFunExt where
  (rightId (A B : U) : compFunFun (idFun A) B ≃ idFun (A ⟶ B))
  (leftId  (A B : U) : revCompFunFun A (idFun B) ≃ idFun (A ⟶ B))
  (swapRevApp (A B : U) : swapFunFun (revAppFunFun A B) ≃ appFunFun A B)
  (swapCompFun (A B C : U) :
     swapFunFunFun (B ⟶ C) A C • compFunFunFun A B C ≃
     revCompFunFun A (revAppFunFun B C))
  (swapRevCompFun (A B C : U) :
     swapFunFunFun (A ⟶ B) A C • revCompFunFunFun A B C ≃
     compFunFun (revAppFunFun A B) ((A ⟶ B) ⟶ C) • revCompFunFunFun (A ⟶ B) B C)
  (compAssoc (A B C D : U) :
     compFunFun (compFunFunFun B C D) ((C ⟶ D) ⟶ (A ⟶ D)) •
     revCompFunFunFun (C ⟶ D) (B ⟶ D) (A ⟶ D) •
     compFunFunFun A B D ≃
     revCompFunFun (B ⟶ C) (compFunFunFun A C D) • compFunFunFun A B C)

  namespace HasDirectLinearFunExt

    def fromLinearFunExt [HasLinearFunExt U] : HasDirectLinearFunExt U :=
    { rightId        := HasLinearFunExt.rightIdExt,
      leftId         := HasLinearFunExt.leftIdExt,
      swapRevApp     := HasLinearFunExt.swapRevAppExt,
      swapCompFun    := HasLinearFunExt.swapCompFunExtExt,
      swapRevCompFun := HasLinearFunExt.swapRevCompFunExtExt,
      compAssoc      := HasLinearFunExt.compAssocExtExtExt }

    variable [HasDirectLinearFunExt U]

    def rightIdCongr {A B : U} (F : A ⟶ B) :
      F • idFun A ≃ F :=
    applyCongrFun (rightId A B) F byDef byDef

    def leftIdCongr {A B : U} (F : A ⟶ B) :
      idFun B • F ≃ F :=
    applyCongrFun (leftId A B) F byDef byDef

    def swapRevAppCongr {A B : U} (F : A ⟶ B) :
      swapFun (revAppFunFun A B) F ≃ F :=
    applyCongrFun (swapRevApp A B) F byDef byDef

    def swapCompFunCongr {A B : U} (F : A ⟶ B) (C : U) :
      swapFunFun (compFunFun F C) ≃ revAppFunFun B C • F :=
    applyCongrFun (swapCompFun A B C) F (byDefDef • byDef) byDef

    def swapCompFunCongrCongr {A B : U} (F : A ⟶ B) (a : A) (C : U) :
      swapFun (compFunFun F C) a ≃ revAppFun (F a) C :=
    applyCongrFun (swapCompFunCongr U F C) a byDef (byDef • byDef)

    def swapRevCompFunCongr (A : U) {B C : U} (G : B ⟶ C) :
      swapFunFun (revCompFunFun A G) ≃ revCompFunFun (A ⟶ B) G • revAppFunFun A B :=
    applyCongrFun (swapRevCompFun A B C) G (byDefDef • byDef) (byDefDef • byDef)

    def swapRevCompFunCongrCongr {A B C : U} (G : B ⟶ C) (a : A) :
      swapFun (revCompFunFun A G) a ≃ G • revAppFun a B :=
    applyCongrFun (swapRevCompFunCongr U A G) a byDef (byDefDef • byDef)

    def compAssocCongr {A B : U} (F : A ⟶ B) (C D : U) :
      revCompFunFun (C ⟶ D) (compFunFun F D) • compFunFunFun B C D ≃ compFunFunFun A C D • compFunFun F C :=
    applyCongrFun (compAssoc A B C D) F
                  (byDefDefDef • byArgDef • byDef) (byDefDef • byDef)

    def compAssocCongrCongr {A B C : U} (F : A ⟶ B) (G : B ⟶ C) (D : U) :
      compFunFun F D • compFunFun G D ≃ compFunFun (G • F) D :=
    applyCongrFun (compAssocCongr U F C D) G (byDefDef • byDef) (byDefDef • byDef)

    def compAssocCongrCongrCongr {A B C D : U} (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) :
      (H • G) • F ≃ H • (G • F) :=
    applyCongrFun (compAssocCongrCongr U F G D) H (byDefDef • byDef) byDef

    instance hasLinearFunExt : HasLinearFunExt U :=
    { rightId              := rightIdCongr U,
      rightIdExt           := rightId,
      leftId               := leftIdCongr U,
      leftIdExt            := leftId,
      swapRevApp           := swapRevAppCongr U,
      swapRevAppExt        := swapRevApp,
      swapCompFun          := swapCompFunCongrCongr U,
      swapCompFunExt       := swapCompFunCongr U,
      swapCompFunExtExt    := swapCompFun,
      swapRevCompFun       := swapRevCompFunCongrCongr U,
      swapRevCompFunExt    := swapRevCompFunCongr U,
      swapRevCompFunExtExt := swapRevCompFun,
      compAssoc            := compAssocCongrCongrCongr U,
      compAssocExt         := compAssocCongrCongr U,
      compAssocExtExt      := compAssocCongr U,
      compAssocExtExtExt   := compAssoc }

  end HasDirectLinearFunExt

end HasLinearFunOp

namespace HasAffineFunOp

  open HasFunctors HasCongrArg HasCongrFun HasCompFun HasLinearFunOp HasSubLinearFunOp

  variable [HasAffineFunOp U]

  class HasDirectSubLinearFunExt where
  (rightConst (A B C : U) :
     compFunFunFun A B C • constFunFun A B ≃
     revCompFunFun (B ⟶ C) (constFunFun A C) • revAppFunFun B C)
  (leftConst (A B C : U) :
     compFunFun (constFunFun B C) (A ⟶ C) • compFunFunFun A B C ≃
     constFun (A ⟶ B) (constFunFun A C))

  namespace HasDirectSubLinearFunExt

    def fromAffineFunExt [HasAffineFunExt U] : HasDirectSubLinearFunExt U :=
    { rightConst := HasAffineFunExt.rightConstExtExt,
      leftConst  := HasAffineFunExt.leftConstExtExt }

    variable [HasLinearFunExt U] [HasDirectSubLinearFunExt U]

    def rightConstCongr (A : U) {B : U} (b : B) (C : U) :
      compFunFun (constFun A b) C ≃ constFunFun A C • revAppFun b C :=
    applyCongrFun (rightConst A B C) b (byDefDef • byDef) (byDefDef • byDef)

    def rightConstCongrCongr (A : U) {B C : U} (b : B) (G : B ⟶ C) :
      G • constFun A b ≃ constFun A (G b) :=
    applyCongrFun (rightConstCongr U A b C) G byDef (byDefDef • byDef)

    def leftConstCongr {A B : U} (F : A ⟶ B) (C : U) :
      compFunFun F C • constFunFun B C ≃ constFunFun A C :=
    applyCongrFun (leftConst A B C) F (byDefDef • byDef) byDef

    def leftConstCongrCongr {A B C : U} (F : A ⟶ B) (c : C) :
      constFun B c • F ≃ constFun A c :=
    applyCongrFun (leftConstCongr U F C) c (byDefDef • byDef) byDef

    instance hasAffineFunExt : HasAffineFunExt U :=
    { rightConst       := rightConstCongrCongr U,
      rightConstExt    := rightConstCongr U,
      rightConstExtExt := rightConst,
      leftConst        := leftConstCongrCongr U,
      leftConstExt     := leftConstCongr U,
      leftConstExtExt  := leftConst }

  end HasDirectSubLinearFunExt

end HasAffineFunOp

namespace HasFullFunOp

  open HasFunctors HasCongrArg HasCongrFun HasCompFun HasLinearFunOp HasSubLinearFunOp HasAffineFunOp HasNonLinearFunOp

  variable [HasFullFunOp U]

  class HasDirectNonLinearFunExt where
  (dupSwap (A B : U) : dupFunFun A B • swapFunFunFun A A B ≃ dupFunFun A B)
  (dupConst (A B : U) : dupFunFun A B • constFunFun A (A ⟶ B) ≃ idFun (A ⟶ B))
  (rightDup (A B C : U) :
     revCompFunFun (B ⟶ C) (dupFunFun A C) •
     compFunFun (revCompFunFunFun A B C) (A ⟶ A ⟶ C) •
     compFunFunFun A (A ⟶ B) (A ⟶ C) ≃
     compFunFunFun A B C • dupFunFun A B)
  (substDup (A B C : U) :
     compFunFun (revCompFunFun A (dupFunFun B C)) (A ⟶ C) •
     substFunFunFun A B C ≃
     substFun (substFunFunFun A B C) (compFunFunFun (A ⟶ B ⟶ B ⟶ C) (A ⟶ B ⟶ C) (A ⟶ C) •
     substFunFunFun A B (B ⟶ C)))

  namespace HasDirectNonLinearFunExt

    def fromFullFunExt [HasFullFunExt U] : HasDirectNonLinearFunExt U :=
    { dupSwap  := HasFullFunExt.dupSwapExt,
      dupConst := HasFullFunExt.dupConstExt,
      rightDup := HasFullFunExt.rightDupExtExt,
      substDup := HasFullFunExt.substDupExtExt }

    variable [HasAffineFunExt U] [HasDirectNonLinearFunExt U]

    def dupSwapCongr {A B : U} (F : A ⟶ A ⟶ B) :
      dupFun (swapFunFun F) ≃ dupFun F :=
    applyCongrFun (dupSwap A B) F (byDefDef • byDef) byDef

    def dupConstCongr {A B : U} (F : A ⟶ B) :
      dupFun (constFun A F) ≃ F :=
    applyCongrFun (dupConst A B) F (byDefDef • byDef) byDef

    def rightDupCongr {A B : U} (F : A ⟶ A ⟶ B) (C : U) :
      dupFunFun A C • compFunFun F (A ⟶ C) • revCompFunFunFun A B C ≃ compFunFun (dupFun F) C :=
    applyCongrFun (rightDup A B C) F
                  (byDefDefDef • byArgDef • byDef) (byDefDef • byDef)

    def rightDupCongrCongr {A B C : U} (F : A ⟶ A ⟶ B) (G : B ⟶ C) :
      dupFun (revCompFunFun A G • F) ≃ G • dupFun F :=
    applyCongrFun (rightDupCongr U F C) G
                  (byDefDefDef • byArgDef • byDef) byDef

    def substDupCongr {A B : U} (F : A ⟶ B) (C : U) :
      substFunFun F C • revCompFunFun A (dupFunFun B C) ≃ substFunFun F C • substFunFun F (B ⟶ C) :=
    applyCongrFun (substDup A B C) F
                  (byDefDef • byDef)
                  (byDef • congrFun byDefDef (substFunFun F C) • byFunDef • byArgDef • byDef)

    def substDupCongrCongr {A B C : U} (F : A ⟶ B) (G : A ⟶ B ⟶ B ⟶ C) :
      substFun F (dupFunFun B C • G) ≃ substFun F (substFun F G) :=
    applyCongrFun (substDupCongr U F C) G (byDefDef • byDef) (byDefDef • byDef)
  
    instance hasFullFunExt : HasFullFunExt U :=
    { dupSwap        := dupSwapCongr U,
      dupSwapExt     := dupSwap,
      dupConst       := dupConstCongr U,
      dupConstExt    := dupConst,
      rightDup       := rightDupCongrCongr U,
      rightDupExt    := rightDupCongr U,
      rightDupExtExt := rightDup,
      substDup       := substDupCongrCongr U,
      substDupExt    := substDupCongr U,
      substDupExtExt := substDup }

  end HasDirectNonLinearFunExt

end HasFullFunOp
