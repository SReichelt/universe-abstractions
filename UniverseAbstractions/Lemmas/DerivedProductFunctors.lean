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
       HasFullFunOp HasProducts HasTop

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasInternalProducts U]

  def defFstFun [HasAffineFunOp U] (A B : U) : A ⊓ B ⟶{λ P => fst P} A :=
  elimFun (constFunFun B A)
  ◄ byDef₂

  @[reducible] def fstFun [HasAffineFunOp U] (A B : U) : A ⊓ B ⟶ A := defFstFun A B

  instance fst.isFunApp [HasAffineFunOp U] {A B : U} {P : A ⊓ B} : IsFunApp (A ⊓ B) (fst P) :=
  { F := fstFun A B,
    a := P,
    e := byDef }

  def defSndFun [HasAffineFunOp U] (A B : U) : A ⊓ B ⟶{λ P => snd P} B :=
  elimFun (constFun A (idFun B))
  ◄ byDef₂

  @[reducible] def sndFun [HasAffineFunOp U] (A B : U) : A ⊓ B ⟶ B := defSndFun A B

  instance snd.isFunApp [HasAffineFunOp U] {A B : U} {P : A ⊓ B} : IsFunApp (A ⊓ B) (snd P) :=
  { F := sndFun A B,
    a := P,
    e := byDef }

  def defDupIntroFun [HasFullFunOp U] (A : U) : A ⟶{λ a => intro a a} A ⊓ A :=
  dupFun (introFunFun A A)
  ◄ byDef₂

  @[reducible] def dupIntroFun [HasFullFunOp U] (A : U) : A ⟶ A ⊓ A := defDupIntroFun A

  def defRevIntroFun [HasLinearFunOp U] (A : U) {B : U} (b : B) : A ⟶{λ a => intro a b} A ⊓ B :=
  swapFun (introFunFun A B) b
  ◄ byDef₂

  @[reducible] def revIntroFun [HasLinearFunOp U] (A : U) {B : U} (b : B) : A ⟶ A ⊓ B := defRevIntroFun A b

  def defRevIntroFunFun [HasLinearFunOp U] (A B : U) : B ⟶{λ b => revIntroFun A b} (A ⟶ A ⊓ B) :=
  defSwapFunFun (introFunFun A B)

  @[reducible] def revIntroFunFun [HasLinearFunOp U] (A B : U) : B ⟶ A ⟶ A ⊓ B := defRevIntroFunFun A B

  instance revIntroFun.isFunApp [HasLinearFunOp U] {A B : U} {b : B} :
    IsFunApp B (revIntroFun A b) :=
  { F := revIntroFunFun A B,
    a := b,
    e := byDef }

  instance revIntroFunFun.isFunApp [HasLinearFunOp U] {A B : U} :
    IsFunApp (A ⟶ B ⟶ A ⊓ B) (revIntroFunFun A B) :=
  swapFunFun.isFunApp

  instance intro.isFunApp₂ [HasLinearFunOp U] {A B : U} {a : A} {b : B} : IsFunApp₂ A B (intro a b) :=
  ⟨{ F := revIntroFun A b,
     a := a,
     e := byDef }⟩

  -- TODO: Define `IsFunApp` instances.

  def defRevElimFun [HasLinearFunOp U] {A B C : U} (F : B ⟶ A ⟶ C) :
    A ⊓ B ⟶{λ P => F (snd P) (fst P)} C :=
  elimFun (swapFunFun F)
  ◄ byDef₂

  @[reducible] def revElimFun [HasLinearFunOp U] {A B C : U} (F : B ⟶ A ⟶ C) : A ⊓ B ⟶ C := defRevElimFun F

  def defRevElimFunFun [HasLinearFunOp U] (A B C : U) : (B ⟶ A ⟶ C) ⟶{λ F => revElimFun F} (A ⊓ B ⟶ C) :=
  elimFunFun A B C • swapFunFunFun B A C
  ◄ byDefDef

  @[reducible] def revElimFunFun [HasLinearFunOp U] (A B C : U) : (B ⟶ A ⟶ C) ⟶ (A ⊓ B ⟶ C) := defRevElimFunFun A B C

  def invElim [HasLinearFunOp U] {A B C : U} (F : A ⊓ B ⟶ C) (a : A) (b : B) : C := F (intro a b)

  def defInvElimFun [HasLinearFunOp U] {A B C : U} (F : A ⊓ B ⟶ C) (a : A) : B ⟶{λ b => invElim F a b} C :=
  F • introFun a B
  ◄ byArgDef

  @[reducible] def invElimFun [HasLinearFunOp U] {A B C : U} (F : A ⊓ B ⟶ C) (a : A) : B ⟶ C := defInvElimFun F a

  def defInvElimFunFun [HasLinearFunOp U] {A B C : U} (F : A ⊓ B ⟶ C) : A ⟶{λ a => invElimFun F a} (B ⟶ C) :=
  revCompFunFun B F • introFunFun A B
  ◄ byDefDef

  @[reducible] def invElimFunFun [HasLinearFunOp U] {A B C : U} (F : A ⊓ B ⟶ C) : A ⟶ B ⟶ C := defInvElimFunFun F

  def defInvElimFunFunFun [HasLinearFunOp U] (A B C : U) : (A ⊓ B ⟶ C) ⟶{λ P => invElimFunFun P} (A ⟶ B ⟶ C) :=
  compFunFun (introFunFun A B) (B ⟶ C) • revCompFunFunFun B (A ⊓ B) C
  ◄ byDefDef

  @[reducible] def invElimFunFunFun [HasLinearFunOp U] (A B C : U) : (A ⊓ B ⟶ C) ⟶ (A ⟶ B ⟶ C) :=
  defInvElimFunFunFun A B C

  def defReplaceFstFun [HasLinearFunOp U] {A B : U} (F : A ⟶ B) (C : U) :
    A ⊓ C ⟶{λ P => intro (F (fst P)) (snd P)} B ⊓ C :=
  elimFun (introFunFun B C • F)
  ◄ byDef₂ • byFunDef

  @[reducible] def replaceFstFun [HasLinearFunOp U] {A B : U} (F : A ⟶ B) (C : U) : A ⊓ C ⟶ B ⊓ C :=
  defReplaceFstFun F C

  def defReplaceFstFunFun [HasLinearFunOp U] (A B C : U) :
    (A ⟶ B) ⟶{λ F => replaceFstFun F C} (A ⊓ C ⟶ B ⊓ C) :=
  elimFunFun A C (B ⊓ C) • revCompFunFun A (introFunFun B C)
  ◄ byDefDef

  @[reducible] def replaceFstFunFun [HasLinearFunOp U] (A B C : U) : (A ⟶ B) ⟶ (A ⊓ C ⟶ B ⊓ C) :=
  defReplaceFstFunFun A B C

  def defReplaceSndFun [HasLinearFunOp U] {A B : U} (F : A ⟶ B) (C : U) :
    C ⊓ A ⟶{λ P => intro (fst P) (F (snd P))} C ⊓ B :=
  revElimFun (revIntroFunFun C B • F)
  ◄ byDef₂ • byFunDef

  @[reducible] def replaceSndFun [HasLinearFunOp U] {A B : U} (F : A ⟶ B) (C : U) : C ⊓ A ⟶ C ⊓ B :=
  defReplaceSndFun F C

  def defReplaceSndFunFun [HasLinearFunOp U] (A B C : U) :
    (A ⟶ B) ⟶{λ F => replaceSndFun F C} (C ⊓ A ⟶ C ⊓ B) :=
  revElimFunFun C A (C ⊓ B) • revCompFunFun A (revIntroFunFun C B)
  ◄ byDefDef

  @[reducible] def replaceSndFunFun [HasLinearFunOp U] (A B C : U) : (A ⟶ B) ⟶ (C ⊓ A ⟶ C ⊓ B) :=
  defReplaceSndFunFun A B C

  def defCommFun [HasLinearFunOp U] (A B : U) : A ⊓ B ⟶{λ P => intro (snd P) (fst P)} B ⊓ A :=
  elimFun (revIntroFunFun B A)
  ◄ byDef₂

  @[reducible] def commFun [HasLinearFunOp U] (A B : U) : A ⊓ B ⟶ B ⊓ A := defCommFun A B

  @[reducible] def intro₃L {A B C : U} (a : A) (b : B) (c : C) : (A ⊓ B) ⊓ C := intro (intro a b) c
  @[reducible] def intro₃R {A B C : U} (a : A) (b : B) (c : C) : A ⊓ (B ⊓ C) := intro a (intro b c)

  def intro₃LFunFun [HasLinearFunOp U] (A B C : U) : A ⟶ B ⟶ C ⟶ (A ⊓ B) ⊓ C :=
  revCompFunFun B (introFunFun (A ⊓ B) C) • introFunFun A B
  def intro₃RFunFun [HasLinearFunOp U] (A B C : U) : A ⟶ B ⟶ C ⟶ A ⊓ (B ⊓ C) :=
  invElimFunFunFun B C (A ⊓ (B ⊓ C)) • introFunFun A (B ⊓ C)

  def elim₃LFun                    {A B C D : U} (F : A ⟶ B ⟶ C ⟶ D) : (A ⊓ B) ⊓ C ⟶ D := elimFun (elimFun F)
  def elim₃RFun [HasLinearFunOp U] {A B C D : U} (F : A ⟶ B ⟶ C ⟶ D) : A ⊓ (B ⊓ C) ⟶ D := elimFun (elimFunFun B C D • F)

  def defAssocLRFun [HasLinearFunOp U] (A B C : U) :
    (A ⊓ B) ⊓ C ⟶{λ P => intro₃R (fst (fst P)) (snd (fst P)) (snd P)} A ⊓ (B ⊓ C) :=
  elim₃LFun (intro₃RFunFun A B C)
  ◄ byDef • byDef₃ • congrFun (congrFun byArgDef _) _ • byFunDef₂ • byFunDef

  @[reducible] def assocLRFun [HasLinearFunOp U] (A B C : U) : (A ⊓ B) ⊓ C ⟶ A ⊓ (B ⊓ C) := defAssocLRFun A B C

  def defAssocRLFun [HasLinearFunOp U] (A B C : U) :
    A ⊓ (B ⊓ C) ⟶{λ P => intro₃L (fst P) (fst (snd P)) (snd (snd P))} (A ⊓ B) ⊓ C :=
  elim₃RFun (intro₃LFunFun A B C)
  ◄ byDef₂ • congrFun byArgDef _ • byFunDef • byDef₂ • congrFun byArgDef _ •
    congrFun (congrArg _ byArgDef) _ • congrFun byArgDef _ • byFunDef

  @[reducible] def assocRLFun [HasLinearFunOp U] (A B C : U) : A ⊓ (B ⊓ C) ⟶ (A ⊓ B) ⊓ C := defAssocRLFun A B C

  def defMergeFun [HasFullFunOp U] {A B C : U} (F : A ⟶ B) (G : A ⟶ C) :
    A ⟶{λ a => intro (F a) (G a)} B ⊓ C :=
  substFun F (revIntroFunFun B C • G)
  ◄ byDef₂ • byFunDef

  @[reducible] def mergeFun [HasFullFunOp U] {A B C : U} (F : A ⟶ B) (G : A ⟶ C) : A ⟶ B ⊓ C := defMergeFun F G

  def defMergeFunFun [HasFullFunOp U] {A B : U} (F : A ⟶ B) (C : U) :
    (A ⟶ C) ⟶{λ G => mergeFun F G} (A ⟶ B ⊓ C) :=
  substFunFun F (B ⊓ C) • revCompFunFun A (revIntroFunFun B C)
  ◄ byDefDef

  @[reducible] def mergeFunFun [HasFullFunOp U] {A B : U} (F : A ⟶ B) (C : U) : (A ⟶ C) ⟶ (A ⟶ B ⊓ C) :=
  defMergeFunFun F C

  def defMergeFunFunFun [HasFullFunOp U] (A B C : U) : (A ⟶ B) ⟶{λ F => mergeFunFun F C} ((A ⟶ C) ⟶ (A ⟶ B ⊓ C)) :=
  compFunFun (revCompFunFun A (revIntroFunFun B C)) (A ⟶ B ⊓ C) •
  substFunFunFun A B (B ⊓ C)
  ◄ byDefDef

  @[reducible] def mergeFunFunFun [HasFullFunOp U] (A B C : U) : (A ⟶ B) ⟶ (A ⟶ C) ⟶ (A ⟶ B ⊓ C) :=
  defMergeFunFunFun A B C

  def distr [HasAffineFunOp U] {A B C : U} (F : A ⟶ B ⊓ C) : (A ⟶ B) ⊓ (A ⟶ C) :=
  intro (fstFun B C • F) (sndFun B C • F)

  def defDistrFun [HasFullFunOp U] (A B C : U) : (A ⟶ B ⊓ C) ⟶{λ F => distr F} (A ⟶ B) ⊓ (A ⟶ C) :=
  mergeFun (revCompFunFun A (fstFun B C)) (revCompFunFun A (sndFun B C))
  ◄ defCongrFun (defCongrArg (defIntroFunFun _ _) byDef) _ • defCongrArg (defIntroFun _ _) byDef

  @[reducible] def distrFun [HasFullFunOp U] (A B C : U) : (A ⟶ B ⊓ C) ⟶ (A ⟶ B) ⊓ (A ⟶ C) := defDistrFun A B C

  def invDistrFun [HasFullFunOp U] {A B C : U} (P : (A ⟶ B) ⊓ (A ⟶ C)) : A ⟶ B ⊓ C :=
  mergeFun (fst P) (snd P)

  def defInvDistrFunFun [HasFullFunOp U] (A B C : U) : (A ⟶ B) ⊓ (A ⟶ C) ⟶{λ P => invDistrFun P} (A ⟶ B ⊓ C) :=
  elimFun (mergeFunFunFun A B C)
  ◄ byDef₂

  @[reducible] def invDistrFunFun [HasFullFunOp U] (A B C : U) : (A ⟶ B) ⊓ (A ⟶ C) ⟶ (A ⟶ B ⊓ C) :=
  defInvDistrFunFun A B C

  def defProdTopIntroFun [HasInternalTop U] (A : U) : A ⟶{λ a => intro (top U) a} Top U ⊓ A :=
  defIntroFun (top U) A

  @[reducible] def prodTopIntroFun [HasInternalTop U] (A : U) : A ⟶ Top U ⊓ A :=
  defProdTopIntroFun A

  def defProdTopElimFun [HasLinearFunOp U] [HasInternalTop U] (A : U) : Top U ⊓ A ⟶{λ P => snd P} A :=
  elimFun (HasInternalTop.elimFun (idFun A))
  ◄ byDef₂

  @[reducible] def prodTopElimFun [HasLinearFunOp U] [HasInternalTop U] (A : U) : Top U ⊓ A ⟶ A :=
  defProdTopElimFun A

end HasInternalProducts
