-- TODO: Adapt to `HasIdentity`.
#exit 0



import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Singletons
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Lemmas.DerivedFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true



namespace HasInternalProducts

  open HasProducts HasTop

  variable {U : Universe} [HasInternalFunctors U] [HasInternalProducts U]

  def defFstFun [HasSubLinearFunOp U] (A B : U) : A ⊓ B ⟶[λ P => fst P] A :=
  elimFun (HasSubLinearFunOp.constFunFun B A)
  ◄ λ _ => by simp

  @[reducible] def fstFun' [HasSubLinearFunOp U] (A B : U) : A ⊓ B ⟶' A := defFstFun A B
  @[reducible] def fstFun  [HasSubLinearFunOp U] (A B : U) : A ⊓ B ⟶  A := HasFunctors.fromExternal (fstFun' A B)

  def defSndFun [HasAffineFunOp    U] (A B : U) : A ⊓ B ⟶[λ P => snd P] B :=
  elimFun (HasSubLinearFunOp.constFun A (HasLinearFunOp.idFun B))
  ◄ λ _ => by simp

  @[reducible] def sndFun' [HasAffineFunOp U] (A B : U) : A ⊓ B ⟶' B := defSndFun A B
  @[reducible] def sndFun  [HasAffineFunOp U] (A B : U) : A ⊓ B ⟶  B := HasFunctors.fromExternal (sndFun' A B)

  def defDupIntroFun [HasNonLinearFunOp U] (A : U) : A ⟶[λ a => intro a a] A ⊓ A :=
  HasNonLinearFunOp.dupFun (introFunFun A A)
  ◄ λ _ => by simp

  @[reducible] def dupIntroFun' [HasNonLinearFunOp U] (A : U) : A ⟶' A ⊓ A := defDupIntroFun A
  @[reducible] def dupIntroFun  [HasNonLinearFunOp U] (A : U) : A ⟶  A ⊓ A := HasFunctors.fromExternal (dupIntroFun' A)

  def defRevIntroFun [HasLinearFunOp U] (A : U) {B : U} (b : B) : A ⟶[λ a => intro a b] A ⊓ B :=
  HasLinearFunOp.swapFun (introFunFun A B) b
  ◄ λ _ => by simp

  @[reducible] def revIntroFun [HasLinearFunOp U] (A : U) {B : U} (b : B) : A ⟶ A ⊓ B := defRevIntroFun A b

  def defRevIntroFunFun [HasLinearFunOp U] (A B : U) : B ⟶[λ b => revIntroFun A b] (A ⟶ A ⊓ B) :=
  HasLinearFunOp.swapFunFun (introFunFun A B)
  ◄ λ _ => by simp [revIntroFun, defRevIntroFun]

  @[reducible] def revIntroFunFun [HasLinearFunOp U] (A B : U) : B ⟶ A ⟶ A ⊓ B := defRevIntroFunFun A B

  def defRevElimFun [HasLinearFunOp U] {A B C : U} (F : B ⟶ A ⟶ C) :
    A ⊓ B ⟶[λ P => F (snd P) (fst P)] C :=
  elimFun (HasLinearFunOp.swapFunFun F)
  ◄ λ _ => by simp

  @[reducible] def revElimFun [HasLinearFunOp U] {A B C : U} (F : B ⟶ A ⟶ C) : A ⊓ B ⟶ C := defRevElimFun F

  def defRevElimFunFun [HasLinearFunOp U] (A B C : U) : (B ⟶ A ⟶ C) ⟶[λ F => revElimFun F] (A ⊓ B ⟶ C) :=
  elimFunFun A B C • HasLinearFunOp.swapFunFunFun B A C
  ◄ λ _ => by simp [revElimFun, defRevElimFun]

  @[reducible] def revElimFunFun [HasLinearFunOp U] (A B C : U) : (B ⟶ A ⟶ C) ⟶ (A ⊓ B ⟶ C) := defRevElimFunFun A B C

  def invElim [HasLinearFunOp U] {A B C : U} (F : A ⊓ B ⟶ C) (a : A) (b : B) : C := F (intro a b)

  def defInvElimFun [HasLinearFunOp U] {A B C : U} (F : A ⊓ B ⟶ C) (a : A) : B ⟶[λ b => invElim F a b] C :=
  F • introFun a B
  ◄ λ _ => by simp [invElim]

  @[reducible] def invElimFun [HasLinearFunOp U] {A B C : U} (F : A ⊓ B ⟶ C) (a : A) : B ⟶ C := defInvElimFun F a

  def defInvElimFunFun [HasLinearFunOp U] {A B C : U} (F : A ⊓ B ⟶ C) : A ⟶[λ a => invElimFun F a] (B ⟶ C) :=
  HasLinearFunOp.revCompFunFun B F • introFunFun A B
  ◄ λ _ => by simp [invElimFun, defInvElimFun]

  @[reducible] def invElimFunFun [HasLinearFunOp U] {A B C : U} (F : A ⊓ B ⟶ C) : A ⟶ B ⟶ C := defInvElimFunFun F

  def defInvElimFunFunFun [HasLinearFunOp U] (A B C : U) : (A ⊓ B ⟶ C) ⟶[λ P => invElimFunFun P] (A ⟶ B ⟶ C) :=
  HasLinearFunOp.compFunFun (introFunFun A B) (B ⟶ C) • HasLinearFunOp.revCompFunFunFun B (A ⊓ B) C
  ◄ λ _ => by simp [invElimFunFun, defInvElimFunFun]

  @[reducible] def invElimFunFunFun [HasLinearFunOp U] (A B C : U) : (A ⊓ B ⟶ C) ⟶ (A ⟶ B ⟶ C) :=
  defInvElimFunFunFun A B C

  def defReplaceFstFun [HasLinearFunOp U] {A B : U} (F : A ⟶ B) (C : U) :
    A ⊓ C ⟶[λ P => intro (F (fst P)) (snd P)] B ⊓ C :=
  elimFun (introFunFun B C • F)
  ◄ λ _ => by simp

  @[reducible] def replaceFstFun [HasLinearFunOp U] {A B : U} (F : A ⟶ B) (C : U) : A ⊓ C ⟶ B ⊓ C :=
  defReplaceFstFun F C

  def defReplaceFstFunFun [HasLinearFunOp U] (A B C : U) :
    (A ⟶ B) ⟶[λ F => replaceFstFun F C] (A ⊓ C ⟶ B ⊓ C) :=
  elimFunFun A C (B ⊓ C) • HasLinearFunOp.revCompFunFun A (introFunFun B C)
  ◄ λ _ => by simp [replaceFstFun, defReplaceFstFun]

  @[reducible] def replaceFstFunFun [HasLinearFunOp U] (A B C : U) : (A ⟶ B) ⟶ (A ⊓ C ⟶ B ⊓ C) :=
  defReplaceFstFunFun A B C

  def defReplaceSndFun [HasLinearFunOp U] {A B : U} (F : A ⟶ B) (C : U) :
    C ⊓ A ⟶[λ P => intro (fst P) (F (snd P))] C ⊓ B :=
  revElimFun (revIntroFunFun C B • F)
  ◄ λ _ => by simp

  @[reducible] def replaceSndFun [HasLinearFunOp U] {A B : U} (F : A ⟶ B) (C : U) : C ⊓ A ⟶ C ⊓ B :=
  defReplaceSndFun F C

  def defReplaceSndFunFun [HasLinearFunOp U] (A B C : U) :
    (A ⟶ B) ⟶[λ F => replaceSndFun F C] (C ⊓ A ⟶ C ⊓ B) :=
  revElimFunFun C A (C ⊓ B) • HasLinearFunOp.revCompFunFun A (revIntroFunFun C B)
  ◄ λ _ => by simp [replaceSndFun, defReplaceSndFun]

  @[reducible] def replaceSndFunFun [HasLinearFunOp U] (A B C : U) : (A ⟶ B) ⟶ (C ⊓ A ⟶ C ⊓ B) :=
  defReplaceSndFunFun A B C

  def defCommFun [HasLinearFunOp U] (A B : U) : A ⊓ B ⟶[λ P => intro (snd P) (fst P)] B ⊓ A :=
  elimFun (revIntroFunFun B A)
  ◄ λ _ => by simp

  @[reducible] def commFun' [HasLinearFunOp U] (A B : U) : A ⊓ B ⟶' B ⊓ A := defCommFun A B
  @[reducible] def commFun  [HasLinearFunOp U] (A B : U) : A ⊓ B ⟶  B ⊓ A := HasFunctors.fromExternal (commFun' A B)

  @[reducible] def intro₃L {A B C : U} (a : A) (b : B) (c : C) : (A ⊓ B) ⊓ C := intro (intro a b) c
  @[reducible] def intro₃R {A B C : U} (a : A) (b : B) (c : C) : A ⊓ (B ⊓ C) := intro a (intro b c)

  def intro₃LFunFun [HasLinearFunOp U] (A B C : U) : A ⟶ B ⟶ C ⟶ (A ⊓ B) ⊓ C :=
  HasLinearFunOp.revCompFunFun B (introFunFun (A ⊓ B) C) • introFunFun A B
  def intro₃RFunFun [HasLinearFunOp U] (A B C : U) : A ⟶ B ⟶ C ⟶ A ⊓ (B ⊓ C) :=
  invElimFunFunFun B C (A ⊓ (B ⊓ C)) • introFunFun A (B ⊓ C)

  def elim₃LFun                    {A B C D : U} (F : A ⟶ B ⟶ C ⟶ D) : (A ⊓ B) ⊓ C ⟶ D := elimFun (elimFun F)
  def elim₃RFun [HasLinearFunOp U] {A B C D : U} (F : A ⟶ B ⟶ C ⟶ D) : A ⊓ (B ⊓ C) ⟶ D := elimFun (elimFunFun B C D • F)

  def defAssocLRFun [HasLinearFunOp U] (A B C : U) :
    (A ⊓ B) ⊓ C ⟶[λ P => intro₃R (fst (fst P)) (snd (fst P)) (snd P)] A ⊓ (B ⊓ C) :=
  elim₃LFun (intro₃RFunFun A B C)
  ◄ λ _ => by simp [elim₃LFun, intro₃RFunFun, invElimFunFun, defInvElimFunFun]

  @[reducible] def assocLRFun' [HasLinearFunOp U] (A B C : U) : (A ⊓ B) ⊓ C ⟶' A ⊓ (B ⊓ C) := defAssocLRFun A B C
  @[reducible] def assocLRFun  [HasLinearFunOp U] (A B C : U) : (A ⊓ B) ⊓ C ⟶  A ⊓ (B ⊓ C) := HasFunctors.fromExternal (assocLRFun' A B C)

  def defAssocRLFun [HasLinearFunOp U] (A B C : U) :
    A ⊓ (B ⊓ C) ⟶[λ P => intro₃L (fst P) (fst (snd P)) (snd (snd P))] (A ⊓ B) ⊓ C :=
  elim₃RFun (intro₃LFunFun A B C)
  ◄ λ _ => by simp [elim₃RFun, intro₃LFunFun]

  @[reducible] def assocRLFun' [HasLinearFunOp U] (A B C : U) : A ⊓ (B ⊓ C) ⟶' (A ⊓ B) ⊓ C := defAssocRLFun A B C
  @[reducible] def assocRLFun  [HasLinearFunOp U] (A B C : U) : A ⊓ (B ⊓ C) ⟶  (A ⊓ B) ⊓ C := HasFunctors.fromExternal (assocRLFun' A B C)

  def defMergeFun [HasFullFunOp U] {A B C : U} (F : A ⟶ B) (G : A ⟶ C) :
    A ⟶[λ a => intro (F a) (G a)] B ⊓ C :=
  HasFullFunOp.substFun F (revIntroFunFun B C • G)
  ◄ λ _ => by simp

  @[reducible] def mergeFun [HasFullFunOp U] {A B C : U} (F : A ⟶ B) (G : A ⟶ C) : A ⟶ B ⊓ C := defMergeFun F G

  def defMergeFunFun [HasFullFunOp U] {A B : U} (F : A ⟶ B) (C : U) :
    (A ⟶ C) ⟶[λ G => mergeFun F G] (A ⟶ B ⊓ C) :=
  HasFullFunOp.substFunFun F (B ⊓ C) • HasLinearFunOp.revCompFunFun A (revIntroFunFun B C)
  ◄ λ _ => by simp [mergeFun, defMergeFun]

  @[reducible] def mergeFunFun [HasFullFunOp U] {A B : U} (F : A ⟶ B) (C : U) : (A ⟶ C) ⟶ (A ⟶ B ⊓ C) :=
  defMergeFunFun F C

  def defMergeFunFunFun [HasFullFunOp U] (A B C : U) : (A ⟶ B) ⟶[λ F => mergeFunFun F C] ((A ⟶ C) ⟶ (A ⟶ B ⊓ C)) :=
  HasLinearFunOp.compFunFun (HasLinearFunOp.revCompFunFun A (revIntroFunFun B C)) (A ⟶ B ⊓ C) •
  HasFullFunOp.substFunFunFun A B (B ⊓ C)
  ◄ λ _ => by simp [mergeFunFun, defMergeFunFun]

  @[reducible] def mergeFunFunFun [HasFullFunOp U] (A B C : U) : (A ⟶ B) ⟶ (A ⟶ C) ⟶ (A ⟶ B ⊓ C) :=
  defMergeFunFunFun A B C

  def distr [HasAffineFunOp U] {A B C : U} (F : A ⟶ B ⊓ C) : (A ⟶ B) ⊓ (A ⟶ C) :=
  intro (fstFun B C • F) (sndFun B C • F) -- TODO: Rewrite using tactic, as a test

  def defDistrFun [HasFullFunOp U] (A B C : U) : (A ⟶ B ⊓ C) ⟶[λ F => distr F] (A ⟶ B) ⊓ (A ⟶ C) :=
  mergeFun (HasLinearFunOp.revCompFunFun A (fstFun B C)) (HasLinearFunOp.revCompFunFun A (sndFun B C))
  ◄ λ _ => by simp [distr]

  @[reducible] def distrFun [HasFullFunOp U] (A B C : U) : (A ⟶ B ⊓ C) ⟶ (A ⟶ B) ⊓ (A ⟶ C) := defDistrFun A B C

  def invDistrFun [HasFullFunOp U] {A B C : U} (P : (A ⟶ B) ⊓ (A ⟶ C)) : A ⟶ B ⊓ C :=
  mergeFun (fst P) (snd P)

  def defInvDistrFunFun [HasFullFunOp U] (A B C : U) : (A ⟶ B) ⊓ (A ⟶ C) ⟶[λ P => invDistrFun P] (A ⟶ B ⊓ C) :=
  elimFun (mergeFunFunFun A B C)
  ◄ λ _ => by simp [invDistrFun]

  @[reducible] def invDistrFunFun [HasFullFunOp U] (A B C : U) : (A ⟶ B) ⊓ (A ⟶ C) ⟶ (A ⟶ B ⊓ C) :=
  defInvDistrFunFun A B C

  def defProdTopIntroFun [HasInternalTop U] (A : U) : A ⟶[λ a => intro (top U) a] Top U ⊓ A :=
  defIntroFun (top U) A

  @[reducible] def prodTopIntroFun [HasInternalTop U] (A : U) : A ⟶ Top U ⊓ A :=
  defProdTopIntroFun A

  def defProdTopElimFun [HasLinearFunOp U] [HasInternalTop U] (A : U) : Top U ⊓ A ⟶[λ P => snd P] A :=
  elimFun (HasInternalTop.elimFun (HasLinearFunOp.idFun A))
  ◄ λ _ => by simp [HasInternalTop.elimFun]

  @[reducible] def prodTopElimFun [HasLinearFunOp U] [HasInternalTop U] (A : U) : Top U ⊓ A ⟶ A :=
  defProdTopElimFun A

end HasInternalProducts
