import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Singletons
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Lemmas.DerivedFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true



namespace HasInternalProducts

  open HasFunctors HasCongrArg HasCongrFun HasLinearFunOp HasSubLinearFunOp HasNonLinearFunOp
       HasProducts HasTop

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasLinearFunOp U]
           [HasInternalProducts U]

  def defFstFun [HasSubLinearFunOp U] (A B : U) : A ⊓ B ⟶{λ P => fst P} A :=
  elimFun (constFunFun B A)
  ◄ byDef₂

  @[reducible] def fstFun [HasSubLinearFunOp U] (A B : U) : A ⊓ B ⟶ A := defFstFun A B

  instance fst.isFunApp [HasSubLinearFunOp U] {A B : U} {P : A ⊓ B} : IsFunApp (A ⊓ B) (fst P) :=
  { F := fstFun A B,
    a := P,
    e := byDef }

  def defSndFun [HasSubLinearFunOp U] (A B : U) : A ⊓ B ⟶{λ P => snd P} B :=
  elimFun (constFun A (idFun B))
  ◄ byDef₂

  @[reducible] def sndFun [HasSubLinearFunOp U] (A B : U) : A ⊓ B ⟶ B := defSndFun A B

  instance snd.isFunApp [HasSubLinearFunOp U] {A B : U} {P : A ⊓ B} : IsFunApp (A ⊓ B) (snd P) :=
  { F := sndFun A B,
    a := P,
    e := byDef }

  def defDupIntroFun [HasNonLinearFunOp U] (A : U) : A ⟶{λ a => intro a a} A ⊓ A :=
  dupFun (introFunFun A A)
  ◄ byDef₂

  @[reducible] def dupIntroFun [HasNonLinearFunOp U] (A : U) : A ⟶ A ⊓ A := defDupIntroFun A

  def defRevIntroFun (A : U) {B : U} (b : B) : A ⟶{λ a => intro a b} A ⊓ B :=
  swapFun (introFunFun A B) b
  ◄ byDef₂

  @[reducible] def revIntroFun (A : U) {B : U} (b : B) : A ⟶ A ⊓ B := defRevIntroFun A b

  def defRevIntroFunFun (A B : U) : B ⟶{λ b => revIntroFun A b} (A ⟶ A ⊓ B) :=
  defSwapFunFun (introFunFun A B)

  @[reducible] def revIntroFunFun (A B : U) : B ⟶ A ⟶ A ⊓ B := defRevIntroFunFun A B

  instance revIntroFun.isFunApp {A B : U} {b : B} :
    IsFunApp B (revIntroFun A b) :=
  { F := revIntroFunFun A B,
    a := b,
    e := byDef }

  instance revIntroFunFun.isFunApp {A B : U} :
    IsFunApp (A ⟶ B ⟶ A ⊓ B) (revIntroFunFun A B) :=
  swapFunFun.isFunApp

  instance intro.isFunApp₂ {A B : U} {a : A} {b : B} : IsFunApp₂ A B (intro a b) :=
  ⟨{ F := revIntroFun A b,
     a := a,
     e := byDef }⟩

  def defRevElimFun {A B C : U} (F : B ⟶ A ⟶ C) :
    A ⊓ B ⟶{λ P => F (snd P) (fst P)} C :=
  elimFun (swapFunFun F)
  ◄ byDef₂

  @[reducible] def revElimFun {A B C : U} (F : B ⟶ A ⟶ C) : A ⊓ B ⟶ C := defRevElimFun F

  def defRevElimFunFun (A B C : U) : (B ⟶ A ⟶ C) ⟶{λ F => revElimFun F} (A ⊓ B ⟶ C) :=
  elimFunFun A B C • swapFunFunFun B A C
  ◄ byDefDef

  @[reducible] def revElimFunFun (A B C : U) : (B ⟶ A ⟶ C) ⟶ (A ⊓ B ⟶ C) := defRevElimFunFun A B C

  instance revElimFun.isFunApp {A B C : U} {F : B ⟶ A ⟶ C} :
    IsFunApp (B ⟶ A ⟶ C) (revElimFun F) :=
  { F := revElimFunFun A B C,
    a := F,
    e := byDef }

  def invElim {A B C : U} (F : A ⊓ B ⟶ C) (a : A) (b : B) : C := F (intro a b)

  def defInvElimFun {A B C : U} (F : A ⊓ B ⟶ C) (a : A) : B ⟶{λ b => invElim F a b} C :=
  F • introFun a B
  ◄ byArgDef

  @[reducible] def invElimFun {A B C : U} (F : A ⊓ B ⟶ C) (a : A) : B ⟶ C := defInvElimFun F a

  def defInvElimFunFun {A B C : U} (F : A ⊓ B ⟶ C) : A ⟶{λ a => invElimFun F a} (B ⟶ C) :=
  revCompFunFun B F • introFunFun A B
  ◄ byDefDef

  @[reducible] def invElimFunFun {A B C : U} (F : A ⊓ B ⟶ C) : A ⟶ B ⟶ C := defInvElimFunFun F

  def defInvElimFunFunFun (A B C : U) : (A ⊓ B ⟶ C) ⟶{λ P => invElimFunFun P} (A ⟶ B ⟶ C) :=
  compFunFun (introFunFun A B) (B ⟶ C) • revCompFunFunFun B (A ⊓ B) C
  ◄ byDefDef

  instance invElimFun.isFunApp {A B C : U} {F : A ⊓ B ⟶ C} {a : A} :
    IsFunApp A (invElimFun F a) :=
  { F := invElimFunFun F,
    a := a,
    e := byDef }

  @[reducible] def invElimFunFunFun (A B C : U) : (A ⊓ B ⟶ C) ⟶ (A ⟶ B ⟶ C) :=
  defInvElimFunFunFun A B C

  instance invElimFunFun.isFunApp {A B C : U} {F : A ⊓ B ⟶ C} :
    IsFunApp (A ⊓ B ⟶ C) (invElimFunFun F) :=
  { F := invElimFunFunFun A B C,
    a := F,
    e := byDef }

  def defReplaceFstFun {A B : U} (F : A ⟶ B) (C : U) :
    A ⊓ C ⟶{λ P => intro (F (fst P)) (snd P)} B ⊓ C :=
  elimFun (introFunFun B C • F)
  ◄ byDef₂ • byFunDef

  @[reducible] def replaceFstFun {A B : U} (F : A ⟶ B) (C : U) : A ⊓ C ⟶ B ⊓ C :=
  defReplaceFstFun F C

  def defReplaceFstFunFun (A B C : U) :
    (A ⟶ B) ⟶{λ F => replaceFstFun F C} (A ⊓ C ⟶ B ⊓ C) :=
  elimFunFun A C (B ⊓ C) • revCompFunFun A (introFunFun B C)
  ◄ byDefDef

  @[reducible] def replaceFstFunFun (A B C : U) : (A ⟶ B) ⟶ (A ⊓ C ⟶ B ⊓ C) :=
  defReplaceFstFunFun A B C

  instance replaceFstFun.isFunApp {A B C : U} {F : A ⟶ B} :
    IsFunApp (A ⟶ B) (replaceFstFun F C) :=
  { F := replaceFstFunFun A B C,
    a := F,
    e := byDef }

  def defReplaceSndFun (A : U) {B C : U} (F : B ⟶ C) :
    A ⊓ B ⟶{λ P => intro (fst P) (F (snd P))} A ⊓ C :=
  revElimFun (revIntroFunFun A C • F)
  ◄ byDef₂ • byFunDef

  @[reducible] def replaceSndFun (A : U) {B C : U} (F : B ⟶ C) : A ⊓ B ⟶ A ⊓ C :=
  defReplaceSndFun A F

  def defReplaceSndFunFun (A B C : U) :
    (B ⟶ C) ⟶{λ F => replaceSndFun A F} (A ⊓ B ⟶ A ⊓ C) :=
  revElimFunFun A B (A ⊓ C) • revCompFunFun B (revIntroFunFun A C)
  ◄ byDefDef

  @[reducible] def replaceSndFunFun (A B C : U) : (B ⟶ C) ⟶ (A ⊓ B ⟶ A ⊓ C) :=
  defReplaceSndFunFun A B C

  instance replaceSndFun.isFunApp {A B C : U} {F : B ⟶ C} :
    IsFunApp (B ⟶ C) (replaceSndFun A F) :=
  { F := replaceSndFunFun A B C,
    a := F,
    e := byDef }

  def defCommFun (A B : U) : A ⊓ B ⟶{λ P => intro (snd P) (fst P)} B ⊓ A :=
  elimFun (revIntroFunFun B A)
  ◄ byDef₂

  @[reducible] def commFun (A B : U) : A ⊓ B ⟶ B ⊓ A := defCommFun A B

  @[reducible] def intro₃L {A B C : U} (a : A) (b : B) (c : C) : (A ⊓ B) ⊓ C := intro (intro a b) c
  @[reducible] def intro₃R {A B C : U} (a : A) (b : B) (c : C) : A ⊓ (B ⊓ C) := intro a (intro b c)

  def intro₃LFunFun (A B C : U) : A ⟶ B ⟶ C ⟶ (A ⊓ B) ⊓ C :=
  revCompFunFun B (introFunFun (A ⊓ B) C) • introFunFun A B
  def intro₃RFunFun (A B C : U) : A ⟶ B ⟶ C ⟶ A ⊓ (B ⊓ C) :=
  invElimFunFunFun B C (A ⊓ (B ⊓ C)) • introFunFun A (B ⊓ C)

  def elim₃LFun                    {A B C D : U} (F : A ⟶ B ⟶ C ⟶ D) : (A ⊓ B) ⊓ C ⟶ D := elimFun (elimFun F)
  def elim₃RFun {A B C D : U} (F : A ⟶ B ⟶ C ⟶ D) : A ⊓ (B ⊓ C) ⟶ D := elimFun (elimFunFun B C D • F)

  def defAssocLRFun (A B C : U) :
    (A ⊓ B) ⊓ C ⟶{λ P => intro₃R (fst (fst P)) (snd (fst P)) (snd P)} A ⊓ (B ⊓ C) :=
  elim₃LFun (intro₃RFunFun A B C)
  ◄ byDef • byDef₃ • congrFun (congrFun byArgDef _) _ • byFunDef₂ • byFunDef

  @[reducible] def assocLRFun (A B C : U) : (A ⊓ B) ⊓ C ⟶ A ⊓ (B ⊓ C) := defAssocLRFun A B C

  def defAssocRLFun (A B C : U) :
    A ⊓ (B ⊓ C) ⟶{λ P => intro₃L (fst P) (fst (snd P)) (snd (snd P))} (A ⊓ B) ⊓ C :=
  elim₃RFun (intro₃LFunFun A B C)
  ◄ byDef₂ • congrFun byArgDef _ • byFunDef • byDef₂ • congrFun byArgDef _ •
    congrFun (congrArg _ byArgDef) _ • congrFun byArgDef _ • byFunDef

  @[reducible] def assocRLFun (A B C : U) : A ⊓ (B ⊓ C) ⟶ (A ⊓ B) ⊓ C := defAssocRLFun A B C

  def defMergeFun [HasNonLinearFunOp U] {A B C : U} (F : A ⟶ B) (G : A ⟶ C) :
    A ⟶{λ a => intro (F a) (G a)} B ⊓ C :=
  substFun F (revIntroFunFun B C • G)
  ◄ byDef₂ • byFunDef

  @[reducible] def mergeFun [HasNonLinearFunOp U] {A B C : U} (F : A ⟶ B) (G : A ⟶ C) : A ⟶ B ⊓ C := defMergeFun F G

  def defMergeFunFun [HasNonLinearFunOp U] {A B : U} (F : A ⟶ B) (C : U) :
    (A ⟶ C) ⟶{λ G => mergeFun F G} (A ⟶ B ⊓ C) :=
  substFunFun F (B ⊓ C) • revCompFunFun A (revIntroFunFun B C)
  ◄ byDefDef

  @[reducible] def mergeFunFun [HasNonLinearFunOp U] {A B : U} (F : A ⟶ B) (C : U) : (A ⟶ C) ⟶ (A ⟶ B ⊓ C) :=
  defMergeFunFun F C

  instance mergeFun.isFunApp [HasNonLinearFunOp U] {A B C : U} {F : A ⟶ B} {G : A ⟶ C} :
    IsFunApp (A ⟶ C) (mergeFun F G) :=
  { F := mergeFunFun F C,
    a := G,
    e := byDef }

  def defMergeFunFunFun [HasNonLinearFunOp U] (A B C : U) : (A ⟶ B) ⟶{λ F => mergeFunFun F C} ((A ⟶ C) ⟶ (A ⟶ B ⊓ C)) :=
  compFunFun (revCompFunFun A (revIntroFunFun B C)) (A ⟶ B ⊓ C) •
  substFunFunFun A B (B ⊓ C)
  ◄ byDefDef

  @[reducible] def mergeFunFunFun [HasNonLinearFunOp U] (A B C : U) : (A ⟶ B) ⟶ (A ⟶ C) ⟶ (A ⟶ B ⊓ C) :=
  defMergeFunFunFun A B C

  instance mergeFunFun.isFunApp [HasNonLinearFunOp U] {A B C : U} {F : A ⟶ B} :
    IsFunApp (A ⟶ B) (mergeFunFun F C) :=
  { F := mergeFunFunFun A B C,
    a := F,
    e := byDef }

  def distr [HasSubLinearFunOp U] {A B C : U} (F : A ⟶ B ⊓ C) : (A ⟶ B) ⊓ (A ⟶ C) :=
  intro (fstFun B C • F) (sndFun B C • F)

  def defDistrFun [HasSubLinearFunOp U] [HasNonLinearFunOp U] (A B C : U) :
    (A ⟶ B ⊓ C) ⟶{λ F => distr F} (A ⟶ B) ⊓ (A ⟶ C) :=
  mergeFun (revCompFunFun A (fstFun B C)) (revCompFunFun A (sndFun B C))
  ◄ defCongrFun (defCongrArg (defIntroFunFun _ _) byDef) _ • defCongrArg (defIntroFun _ _) byDef

  @[reducible] def distrFun [HasSubLinearFunOp U] [HasNonLinearFunOp U] (A B C : U) :
    (A ⟶ B ⊓ C) ⟶ (A ⟶ B) ⊓ (A ⟶ C) :=
  defDistrFun A B C

  instance distr.isFunApp [HasSubLinearFunOp U] [HasNonLinearFunOp U] {A B C : U} {F : A ⟶ B ⊓ C} :
    IsFunApp (A ⟶ B ⊓ C) (distr F) :=
  { F := distrFun A B C,
    a := F,
    e := byDef }

  def invDistrFun [HasNonLinearFunOp U] {A B C : U} (P : (A ⟶ B) ⊓ (A ⟶ C)) : A ⟶ B ⊓ C :=
  mergeFun (fst P) (snd P)

  def defInvDistrFunFun [HasNonLinearFunOp U] (A B C : U) : (A ⟶ B) ⊓ (A ⟶ C) ⟶{λ P => invDistrFun P} (A ⟶ B ⊓ C) :=
  elimFun (mergeFunFunFun A B C)
  ◄ byDef₂

  @[reducible] def invDistrFunFun [HasNonLinearFunOp U] (A B C : U) : (A ⟶ B) ⊓ (A ⟶ C) ⟶ (A ⟶ B ⊓ C) :=
  defInvDistrFunFun A B C

  instance invDistrFun.isFunApp [HasNonLinearFunOp U] {A B C : U} {P : (A ⟶ B) ⊓ (A ⟶ C)} :
    IsFunApp ((A ⟶ B) ⊓ (A ⟶ C)) (invDistrFun P) :=
  { F := invDistrFunFun A B C,
    a := P,
    e := byDef }

  def defProdTopIntroFun [HasInternalTop U] (A : U) : A ⟶{λ a => intro (top U) a} Top U ⊓ A :=
  defIntroFun (top U) A

  @[reducible] def prodTopIntroFun [HasInternalTop U] (A : U) : A ⟶ Top U ⊓ A :=
  defProdTopIntroFun A

  def defProdTopElimFun [HasInternalTop U] (A : U) : Top U ⊓ A ⟶{λ P => snd P} A :=
  elimFun (HasInternalTop.elimFun (idFun A))
  ◄ byDef₂

  @[reducible] def prodTopElimFun [HasInternalTop U] (A : U) : Top U ⊓ A ⟶ A :=
  defProdTopElimFun A

end HasInternalProducts
