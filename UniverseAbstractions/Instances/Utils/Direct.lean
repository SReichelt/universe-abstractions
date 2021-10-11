import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.FunctorExtensionality
import UniverseAbstractions.Lemmas.DerivedFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true



variable (U : Universe) [HasIdentity U] [HasEmbeddedFunctors U]



class HasDirectLinearFunOp where
(idFun   (A : U)                                     : A ⟶ A)
(idEq    {A : U} (a : A)                             : (idFun A) a ≃ a)
(appFun  (A B : U)                                   : A ⟶ (A ⟶ B) ⟶ B)
(appEq   {A B : U} (a : A) (F : A ⟶ B)               : (appFun A B) a F ≃ F a)
(compFun (A B C : U)                                 : (A ⟶ B) ⟶ (B ⟶ C) ⟶ (A ⟶ C))
(compEq  {A B C : U} (F : A ⟶ B) (G : B ⟶ C) (a : A) : (compFun A B C) F G a ≃ G (F a))

namespace HasDirectLinearFunOp

  open MetaRelation.HasRefl HasFunctors HasLinearFunOp

  instance hasLinearFunOp [HasDirectLinearFunOp U] : HasLinearFunOp U :=
  { defIdFun         := λ A           => ⟨idFun A,             idEq⟩,
    defAppFun        := λ {A} a B     => ⟨(appFun A B) a,      appEq a⟩,
    defAppFunFun     := λ A B         => ⟨appFun A B,          λ a => refl ((appFun A B) a)⟩,
    defCompFun       := λ {A B C} F G => ⟨(compFun A B C) F G, compEq F G⟩,
    defCompFunFun    := λ {A B} F {C} => ⟨(compFun A B C) F,   λ G => refl ((compFun A B C) F G)⟩,
    defCompFunFunFun := λ A B C       => ⟨compFun A B C,       λ F => refl ((compFun A B C) F)⟩ }

  def fromLinearFunOp [HasLinearFunOp U] : HasDirectLinearFunOp U :=
  { idFun   := HasLinearFunOp.idFun,
    idEq    := λ _ => byDef,
    appFun  := HasLinearFunOp.appFunFun,
    appEq   := λ _ _ => byDef₂,
    compFun := HasLinearFunOp.compFunFunFun,
    compEq  := λ _ _ _ => byDef₃ }

end HasDirectLinearFunOp

class HasDirectSubLinearFunOp where
(constFun (A B : U)                 : B ⟶ A ⟶ B)
(constEq  {A B : U} (b : B) (a : A) : (constFun A B) b a ≃ b)

namespace HasDirectSubLinearFunOp

  open MetaRelation.HasRefl HasFunctors HasLinearFunOp

  instance hasSubLinearFunOp [HasDirectSubLinearFunOp U] : HasSubLinearFunOp U :=
  { defConstFun    := λ A {B} b => ⟨(constFun A B) b, constEq b⟩,
    defConstFunFun := λ A B     => ⟨constFun A B,     λ b => refl ((constFun A B) b)⟩ }

  def fromSubLinearFunOp [HasAffineFunOp U] : HasDirectSubLinearFunOp U :=
  { constFun := HasSubLinearFunOp.constFunFun,
    constEq  := λ _ _ => byDef₂ }

end HasDirectSubLinearFunOp

class HasDirectNonLinearFunOp where
(dupFun (A B : U)                         : (A ⟶ A ⟶ B) ⟶ (A ⟶ B))
(dupEq  {A B : U} (F : A ⟶ A ⟶ B) (a : A) : (dupFun A B) F a ≃ F a a)

namespace HasDirectNonLinearFunOp

  open MetaRelation.HasRefl HasFunctors HasLinearFunOp

  instance hasNonLinearFunOp [HasDirectNonLinearFunOp U] : HasNonLinearFunOp U :=
  { defDupFun    := λ {A B} F => ⟨(dupFun A B) F, dupEq F⟩,
    defDupFunFun := λ A B     => ⟨dupFun A B,     λ F => refl ((dupFun A B) F)⟩ }

  def fromNonLinearFunOp [HasFullFunOp U] : HasDirectNonLinearFunOp U :=
  { dupFun := HasNonLinearFunOp.dupFunFun,
    dupEq  := λ _ _ => byDef₂ }

end HasDirectNonLinearFunOp



namespace HasLinearFunOp

  open HasFunctors HasCongrArg HasCongrFun

  variable [HasLinearFunOp U]

  class HasDirectLinearFunExt where
  (rightId (A B : U) : compFunFun (idFun A) B ≃ idFun (A ⟶ B))
  (leftId  (A B : U) : revCompFunFun A (idFun B) ≃ idFun (A ⟶ B))
  (swapApp (A B : U) : swapFunFun (appFunFun A B) ≃ idFun (A ⟶ B))
  (swapCompFun (A B C : U) :
     swapFunFunFun (B ⟶ C) A C • compFunFunFun A B C ≃
     revCompFunFun A (appFunFun B C))
  (swapRevCompFun (A B C : U) :
     swapFunFunFun (A ⟶ B) A C • revCompFunFunFun A B C ≃
     compFunFun (appFunFun A B) ((A ⟶ B) ⟶ C) • revCompFunFunFun (A ⟶ B) B C)
  (compAssoc (A B C D : U) :
     compFunFun (compFunFunFun B C D) ((C ⟶ D) ⟶ (A ⟶ D)) •
     revCompFunFunFun (C ⟶ D) (B ⟶ D) (A ⟶ D) •
     compFunFunFun A B D ≃
     revCompFunFun (B ⟶ C) (compFunFunFun A C D) • compFunFunFun A B C)

  namespace HasDirectLinearFunExt

    def fromLinearFunExt [HasLinearFunExt U] : HasDirectLinearFunExt U :=
    { rightId        := HasLinearFunExt.rightIdExt,
      leftId         := HasLinearFunExt.leftIdExt,
      swapApp        := HasLinearFunExt.swapAppExt,
      swapCompFun    := HasLinearFunExt.swapCompFunExtExt,
      swapRevCompFun := HasLinearFunExt.swapRevCompFunExtExt,
      compAssoc      := HasLinearFunExt.compAssocExtExtExt }

    variable [HasDirectLinearFunExt U]

    def rightIdCongr {A B : U} (F : A ⟶ B) :
      F • idFun A ≃ F :=
    byDef • congrFun (rightId A B) F • byDef⁻¹

    def leftIdCongr {A B : U} (F : A ⟶ B) :
      idFun B • F ≃ F :=
    byDef • congrFun (leftId A B) F • (byDef (F := defRevCompFunFun _ _))⁻¹

    def swapAppCongr {A B : U} (F : A ⟶ B) :
      swapFun (appFunFun A B) F ≃ F :=
    byDef • congrFun (swapApp A B) F • byDef⁻¹

    def swapCompFunCongr {A B : U} (F : A ⟶ B) (C : U) :
      swapFunFun (compFunFun F C) ≃ appFunFun B C • F :=
    byDef •
    congrFun (swapCompFun A B C) F •
    (byDef • byArgDef • byDef (F := defCompFun _ _))⁻¹

    def swapCompFunCongrCongr {A B : U} (F : A ⟶ B) (a : A) (C : U) :
      swapFun (compFunFun F C) a ≃ appFun (F a) C :=
    (byDef • byDef) • congrFun (swapCompFunCongr U F C) a • byDef⁻¹

    def swapRevCompFunCongr (A : U) {B C : U} (F : B ⟶ C) :
      swapFunFun (revCompFunFun A F) ≃ revCompFunFun (A ⟶ B) F • appFunFun A B :=
    (byDef • byArgDef • byDef) •
    congrFun (swapRevCompFun A B C) F •
    (byDef • byArgDef • byDef (F := defCompFun _ _))⁻¹

    def swapRevCompFunCongrCongr {A B C : U} (F : B ⟶ C) (a : A) :
      swapFun (revCompFunFun A F) a ≃ F • appFun a B :=
    (byDef • byArgDef • byDef) • congrFun (swapRevCompFunCongr U A F) a • byDef⁻¹

    def compAssocCongr {A B : U} (F : A ⟶ B) (C D : U) :
      revCompFunFun (C ⟶ D) (compFunFun F D) • compFunFunFun B C D ≃ compFunFunFun A C D • compFunFun F C :=
    (byDef • byArgDef • byDef) •
    congrFun (compAssoc A B C D) F •
    (byDef • byArgDef • byArgDef₂ • byArgDef (F := defCompFun _ _) • byDef (F := defCompFun _ _))⁻¹

    def compAssocCongrCongr {A B C : U} (F : A ⟶ B) (G : B ⟶ C) (D : U) :
      compFunFun F D • compFunFun G D ≃ compFunFun (G • F) D :=
    (byDef • byArgDef • byDef) •
    congrFun (compAssocCongr U F C D) G •
    (byDef • byArgDef • byDef (F := defCompFun _ _))⁻¹

    def compAssocCongrCongrCongr {A B C D : U} (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) :
      (H • G) • F ≃ H • (G • F) :=
    byDef •
    congrFun (compAssocCongrCongr U F G D) H •
    (byDef • byArgDef • byDef (F := defCompFun _ _))⁻¹

    instance hasLinearFunExt : HasLinearFunExt U :=
    { rightId              := rightIdCongr U,
      rightIdExt           := rightId,
      leftId               := leftIdCongr U,
      leftIdExt            := leftId,
      swapApp              := swapAppCongr U,
      swapAppExt           := swapApp,
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

  open HasFunctors HasCongrArg HasCongrFun HasLinearFunOp HasSubLinearFunOp

  variable [HasAffineFunOp U]

  class HasDirectSubLinearFunExt where
  (rightConst (A B C : U) :
     compFunFunFun A B C • constFunFun A B ≃
     revCompFunFun (B ⟶ C) (constFunFun A C) • appFunFun B C)
  (leftConst (A B C : U) :
     compFunFun (constFunFun B C) (A ⟶ C) • compFunFunFun A B C ≃
     constFun (A ⟶ B) (constFunFun A C))

  namespace HasDirectSubLinearFunExt

    def fromAffineFunExt [HasAffineFunExt U] : HasDirectSubLinearFunExt U :=
    { rightConst := HasAffineFunExt.rightConstExtExt,
      leftConst  := HasAffineFunExt.leftConstExtExt }

    variable [HasLinearFunExt U] [HasDirectSubLinearFunExt U]

    def rightConstCongr (A : U) {B : U} (b : B) (C : U) :
      compFunFun (constFun A b) C ≃ constFunFun A C • appFun b C :=
    (byDef • byArgDef • byDef) •
    congrFun (rightConst A B C) b •
    (byDef • byArgDef • byDef (F := defCompFun _ _))⁻¹

    def rightConstCongrCongr (A : U) {B C : U} (b : B) (F : B ⟶ C) :
      F • constFun A b ≃ constFun A (F b) :=
    (byDef • byArgDef • byDef) •
    congrFun (rightConstCongr U A b C) F •
    byDef⁻¹

    def leftConstCongr {A B : U} (F : A ⟶ B) (C : U) :
      compFunFun F C • constFunFun B C ≃ constFunFun A C :=
    byDef •
    congrFun (leftConst A B C) F •
    (byDef • byArgDef • byDef (F := defCompFun _ _))⁻¹

    def leftConstCongrCongr {A B C : U} (F : A ⟶ B) (c : C) :
      constFun B c • F ≃ constFun A c :=
    byDef •
    congrFun (leftConstCongr U F C) c •
    (byDef • byArgDef • byDef (F := defCompFun _ _))⁻¹

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

  open HasFunctors HasCongrArg HasCongrFun HasLinearFunOp HasSubLinearFunOp HasAffineFunOp HasNonLinearFunOp

  variable [HasFullFunOp U]

  class HasDirectNonLinearFunExt where
  (dupSwap (A B : U) : dupFunFun A B • swapFunFunFun A A B ≃ dupFunFun A B)
  (dupConst (A B : U) : dupFunFun A B • constFunFun A (A ⟶ B) ≃ idFun (A ⟶ B))
  (dupDup (A B : U) : dupFunFun A B • dupFunFun A (A ⟶ B) ≃
                      dupFunFun A B • revCompFunFun A (dupFunFun A B))
  (rightDup (A B C : U) :
     compFunFunFun A B C • dupFunFun A B ≃
     revCompFunFun (B ⟶ C) (dupFunFun A C) •
     compFunFun (revCompFunFunFun A B C) (A ⟶ A ⟶ C) •
     compFunFunFun A (A ⟶ B) (A ⟶ C))
  (substDup (A B C : U) :
     compFunFun (revCompFunFun A (dupFunFun B C)) (A ⟶ C) •
     substFunFunFun A B C ≃
     substFun (substFunFunFun A B C) (compFunFunFun (A ⟶ B ⟶ B ⟶ C) (A ⟶ B ⟶ C) (A ⟶ C) •
     substFunFunFun A B (B ⟶ C)))

  namespace HasDirectNonLinearFunExt

    def fromFullFunExt [HasFullFunExt U] : HasDirectNonLinearFunExt U :=
    { dupSwap  := HasFullFunExt.dupSwapExt,
      dupConst := HasFullFunExt.dupConstExt,
      dupDup   := HasFullFunExt.dupDupExt,
      rightDup := HasFullFunExt.rightDupExtExt,
      substDup := HasFullFunExt.substDupExtExt }

    variable [HasAffineFunExt U] [HasDirectNonLinearFunExt U]

    def dupSwapCongr {A B : U} (F : A ⟶ A ⟶ B) :
      dupFun (swapFunFun F) ≃ dupFun F :=
    byDef •
    congrFun (dupSwap A B) F •
    (byDef • byArgDef • byDef (F := defCompFun _ _))⁻¹

    def dupConstCongr {A B : U} (F : A ⟶ B) :
      dupFun (constFun A F) ≃ F :=
    byDef •
    congrFun (dupConst A B) F •
    (byDef • byArgDef • byDef (F := defCompFun _ _))⁻¹

    def dupDupCongr {A B : U} (F : A ⟶ A ⟶ A ⟶ B) :
      dupFun (dupFun F) ≃ dupFun (dupFunFun A B • F) :=
    (byDef • byArgDef • byDef) •
    congrFun (dupDup A B) F •
    (byDef • byArgDef • byDef (F := defCompFun _ _))⁻¹

    def rightDupCongr {A B : U} (F : A ⟶ A ⟶ B) (C : U) :
      compFunFun (dupFun F) C ≃ dupFunFun A C • compFunFun F (A ⟶ C) • revCompFunFunFun A B C :=
    (byDef • byArgDef • byArgDef₂ • byArgDef • byDef) •
    congrFun (rightDup A B C) F •
    (byDef • byArgDef • byDef (F := defCompFun _ _))⁻¹

    def rightDupCongrCongr {A B C : U} (F : A ⟶ A ⟶ B) (G : B ⟶ C) :
      G • dupFun F ≃ dupFun (revCompFunFun A G • F) :=
    (byDef • byArgDef • byArgDef₂ • byArgDef • byDef) •
    congrFun (rightDupCongr U F C) G •
    byDef⁻¹

    def substDupCongr {A B : U} (F : A ⟶ B) (C : U) :
      substFunFun F C • revCompFunFun A (dupFunFun B C) ≃ substFunFun F C • substFunFun F (B ⟶ C) :=
    (byDef₂ • congrFun byArgDef (substFunFun F C) • byFunDef • byArgDef • byDef) •
    congrFun (substDup A B C) F •
    (byDef • byArgDef • byDef (F := defCompFun _ _))⁻¹

    def substDupCongrCongr {A B C : U} (F : A ⟶ B) (G : A ⟶ B ⟶ B ⟶ C) :
      substFun F (dupFunFun B C • G) ≃ substFun F (substFun F G) :=
    let e : (substFunFun F C) (revCompFun (dupFunFun B C) G) ≃ substFun F (dupFunFun B C • G) := byDef;
    (byDef • byArgDef • byDef) •
    congrFun (substDupCongr U F C) G •
    (e • byArgDef • byDef (F := defCompFun _ _))⁻¹

    instance hasFullFunExt : HasFullFunExt U :=
    { dupSwap        := dupSwapCongr U,
      dupSwapExt     := dupSwap,
      dupConst       := dupConstCongr U,
      dupConstExt    := dupConst,
      dupDup         := dupDupCongr U,
      dupDupExt      := dupDup,
      rightDup       := rightDupCongrCongr U,
      rightDupExt    := rightDupCongr U,
      rightDupExtExt := rightDup,
      substDup       := substDupCongrCongr U,
      substDupExt    := substDupCongr U,
      substDupExtExt := substDup }

  end HasDirectNonLinearFunExt

end HasFullFunOp
