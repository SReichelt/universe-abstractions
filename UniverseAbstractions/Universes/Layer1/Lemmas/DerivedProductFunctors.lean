import UniverseAbstractions.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Axioms.Singletons
import UniverseAbstractions.Universes.Layer1.Axioms.Products
import UniverseAbstractions.Universes.Layer1.Meta.Tactics.Functoriality



namespace UniverseAbstractions.Layer1

set_option autoBoundImplicitLocal false

open HasFunctors HasLinearLogic HasSubLinearLogic HasNonLinearLogic HasProducts HasTop



namespace HasProductFun

  variable {U : Universe} [HasFunctors U] [HasLinearLogic U] [HasProductFun U]

  section

    variable [HasSubLinearLogic U]

    def defFstFun (A B : U) : A ⊓ B ⟶{fst} A := ⟨elimFun (Λ a b => a)⟩
    def defSndFun (A B : U) : A ⊓ B ⟶{snd} B := ⟨elimFun (Λ a b => b)⟩

    @[reducible] def fstFun (A B : U) : A ⊓ B ⟶ A := (defFstFun A B).F
    @[reducible] def sndFun (A B : U) : A ⊓ B ⟶ B := (defSndFun A B).F

    instance fst.isFunApp {A B : U} {P : A ⊓ B} : IsFunApp (A ⊓ B) (fst P) := ⟨fstFun A B, P⟩
    instance snd.isFunApp {A B : U} {P : A ⊓ B} : IsFunApp (A ⊓ B) (snd P) := ⟨sndFun A B, P⟩

  end

  section

    variable [HasNonLinearLogic U]

    def defDupIntroFun (A : U) : A ⟶{λ a => intro a a} A ⊓ A := by functoriality

    @[reducible] def dupIntroFun (A : U) : A ⟶ A ⊓ A := (defDupIntroFun A).F

  end

  @[reducible] def invElim {A B C : U} (F : A ⊓ B ⟶ C) (a : A) (b : B) : C := F (intro a b)

  def defInvElimFun₃ (A B C : U) : (A ⊓ B ⟶ C) ⟶ A ⟶ B ⟶{invElim} C := by functoriality

  @[reducible] def invElimFun {A B C : U} (F : A ⊓ B ⟶ C) (a : A) : B ⟶ C := (((defInvElimFun₃ A B C).app F).app a).F
  @[reducible] def invElimFun₂ {A B C : U} (F : A ⊓ B ⟶ C) : A ⟶ B ⟶ C := ((defInvElimFun₃ A B C).app F).F
  @[reducible] def invElimFun₃ (A B C : U) : (A ⊓ B ⟶ C) ⟶ (A ⟶ B ⟶ C) := (defInvElimFun₃ A B C).F

  instance invElim.isFunApp {A B C : U} {F : A ⊓ B ⟶ C} {a : A} {b : B} : IsFunApp B (invElim F a b) :=
  ⟨invElimFun F a, b⟩

  instance invElimFun.isFunApp {A B C : U} {F : A ⊓ B ⟶ C} {a : A} : IsFunApp A (invElimFun F a) :=
  ⟨invElimFun₂ F, a⟩

  instance invElimFun₂.isFunApp {A B C : U} {F : A ⊓ B ⟶ C} : IsFunApp (A ⊓ B ⟶ C) (invElimFun₂ F) :=
  ⟨invElimFun₃ A B C, F⟩

  def defReplaceFstFun₂ (A B C : U) : (A ⟶ B) ⟶ A ⊓ C ⟶{λ F P => intro (F (fst P)) (snd P)} B ⊓ C :=
  ⟨λ F => ⟨elimFun (Λ a b => intro (F a) b)⟩,
   by functoriality⟩

  @[reducible] def replaceFstFun {A B : U} (F : A ⟶ B) (C : U) : A ⊓ C ⟶ B ⊓ C := ((defReplaceFstFun₂ A B C).app F).F
  @[reducible] def replaceFstFun₂ (A B C : U) : (A ⟶ B) ⟶ (A ⊓ C ⟶ B ⊓ C) := (defReplaceFstFun₂ A B C).F

  instance replaceFstFun.isFunApp {A B C : U} {F : A ⟶ B} : IsFunApp (A ⟶ B) (replaceFstFun F C) :=
  ⟨replaceFstFun₂ A B C, F⟩

  def defReplaceSndFun₂ (A B C : U) :
    (B ⟶ C) ⟶ A ⊓ B ⟶{λ F P => intro (fst P) (F (snd P))} A ⊓ C :=
  ⟨λ F => ⟨elimFun (Λ a b => intro a (F b))⟩,
   by functoriality⟩

  @[reducible] def replaceSndFun (A : U) {B C : U} (F : B ⟶ C) : A ⊓ B ⟶ A ⊓ C := ((defReplaceSndFun₂ A B C).app F).F
  @[reducible] def replaceSndFun₂ (A B C : U) : (B ⟶ C) ⟶ (A ⊓ B ⟶ A ⊓ C) := (defReplaceSndFun₂ A B C).F

  instance replaceSndFun.isFunApp {A B C : U} {F : B ⟶ C} :
    IsFunApp (B ⟶ C) (replaceSndFun A F) :=
  ⟨replaceSndFun₂ A B C, F⟩

  def defReplaceBothFun (A B C D : U) :
    (A ⟶ B) ⟶ (C ⟶ D) ⟶ A ⊓ C ⟶{λ F G P => intro (F (fst P)) (G (snd P))} B ⊓ D :=
  ⟨λ F => ⟨λ G => ⟨elimFun (Λ a b => intro (F a) (G b))⟩,
           by functoriality⟩,
   by functoriality⟩

  @[reducible] def replaceBothFun {A B C D : U} (F : A ⟶ B) (G : C ⟶ D) : A ⊓ C ⟶ B ⊓ D := (((defReplaceBothFun A B C D).app F).app G).F
  @[reducible] def replaceBothFun₂ {A B : U} (F : A ⟶ B) (C D : U) : (C ⟶ D) ⟶ (A ⊓ C ⟶ B ⊓ D) := ((defReplaceBothFun A B C D).app F).F
  @[reducible] def replaceBothFun₃ (A B C D : U) : (A ⟶ B) ⟶ (C ⟶ D) ⟶ (A ⊓ C ⟶ B ⊓ D) := (defReplaceBothFun A B C D).F

  instance replaceBothFun.isFunApp {A B C D : U} {F : A ⟶ B} {G : C ⟶ D} :
    IsFunApp (C ⟶ D) (replaceBothFun F G) :=
  ⟨replaceBothFun₂ F C D, G⟩

  instance replaceBothFun₂.isFunApp {A B C D : U} {F : A ⟶ B} :
    IsFunApp (A ⟶ B) (replaceBothFun₂ F C D) :=
  ⟨replaceBothFun₃ A B C D, F⟩

  @[reducible] def comm {A B : U} (P : A ⊓ B) : B ⊓ A := intro (snd P) (fst P)

  def defCommFun (A B : U) : A ⊓ B ⟶{comm} B ⊓ A := ⟨elimFun (Λ a b => intro b a)⟩

  @[reducible] def commFun (A B : U) : A ⊓ B ⟶ B ⊓ A := (defCommFun A B).F

  instance comm.isFunApp {A B : U} {P : A ⊓ B} : IsFunApp (A ⊓ B) (comm P) := ⟨commFun A B, P⟩

  def intro₃L {A B C : U} (a : A) (b : B) (c : C) : (A ⊓ B) ⊓ C := intro (intro a b) c
  def intro₃R {A B C : U} (a : A) (b : B) (c : C) : A ⊓ (B ⊓ C) := intro a (intro b c)

  def defIntro₃LFun₃ (A B C : U) : A ⟶ B ⟶ C ⟶{intro₃L} (A ⊓ B) ⊓ C := by functoriality
  def defIntro₃RFun₃ (A B C : U) : A ⟶ B ⟶ C ⟶{intro₃R} A ⊓ (B ⊓ C) := by functoriality

  @[reducible] def intro₃LFun₃ (A B C : U) : A ⟶ B ⟶ C ⟶ (A ⊓ B) ⊓ C := (defIntro₃LFun₃ A B C).F
  @[reducible] def intro₃RFun₃ (A B C : U) : A ⟶ B ⟶ C ⟶ A ⊓ (B ⊓ C) := (defIntro₃RFun₃ A B C).F

  instance intro₃L.isFunApp₃ {A B C : U} {a : A} {b : B} {c : C} : IsFunApp₃ A B C (intro₃L a b c) :=
  ⟨intro₃LFun₃ A B C, a, b, c⟩
  instance intro₃R.isFunApp₃ {A B C : U} {a : A} {b : B} {c : C} : IsFunApp₃ A B C (intro₃R a b c) :=
  ⟨intro₃RFun₃ A B C, a, b, c⟩

  def elim₃L {A B C D : U} (F : A ⟶ B ⟶ C ⟶ D) (P : (A ⊓ B) ⊓ C) : D := F (fst (fst P)) (snd (fst P)) (snd P)
  def elim₃R {A B C D : U} (F : A ⟶ B ⟶ C ⟶ D) (P : A ⊓ (B ⊓ C)) : D := F (fst P) (fst (snd P)) (snd (snd P))

  def defElim₃LFun₂ (A B C D : U) : (A ⟶ B ⟶ C ⟶ D) ⟶ (A ⊓ B) ⊓ C ⟶{elim₃L} D :=
  ⟨λ F => ⟨elimFun (elimFun F)⟩,
   by functoriality⟩

  def defElim₃RFun₂ (A B C D : U) : (A ⟶ B ⟶ C ⟶ D) ⟶ A ⊓ (B ⊓ C) ⟶{elim₃R} D :=
  ⟨λ F => ⟨elimFun (Λ a => elimFun (F a))⟩,
   by functoriality⟩

  @[reducible] def elim₃LFun {A B C D : U} (F : A ⟶ B ⟶ C ⟶ D) : (A ⊓ B) ⊓ C ⟶ D := ((defElim₃LFun₂ A B C D).app F).F
  @[reducible] def elim₃LFun₂ (A B C D : U) : (A ⟶ B ⟶ C ⟶ D) ⟶ ((A ⊓ B) ⊓ C ⟶ D) := (defElim₃LFun₂ A B C D).F

  @[reducible] def elim₃RFun {A B C D : U} (F : A ⟶ B ⟶ C ⟶ D) : A ⊓ (B ⊓ C) ⟶ D := ((defElim₃RFun₂ A B C D).app F).F
  @[reducible] def elim₃RFun₂ (A B C D : U) : (A ⟶ B ⟶ C ⟶ D) ⟶ (A ⊓ (B ⊓ C) ⟶ D) := (defElim₃RFun₂ A B C D).F

  instance elim₃L.isFunApp {A B C D : U} {F : A ⟶ B ⟶ C ⟶ D} {P : (A ⊓ B) ⊓ C} :
    IsFunApp ((A ⊓ B) ⊓ C) (elim₃L F P) :=
  ⟨elim₃LFun F, P⟩

  instance elim₃LFun.isFunApp {A B C D : U} {F : A ⟶ B ⟶ C ⟶ D} :
    IsFunApp (A ⟶ B ⟶ C ⟶ D) (elim₃LFun F) :=
  ⟨elim₃LFun₂ A B C D, F⟩

  instance elim₃R.isFunApp {A B C D : U} {F : A ⟶ B ⟶ C ⟶ D} {P : A ⊓ (B ⊓ C)} :
    IsFunApp (A ⊓ (B ⊓ C)) (elim₃R F P) :=
  ⟨elim₃RFun F, P⟩

  instance elim₃RFun.isFunApp {A B C D : U} {F : A ⟶ B ⟶ C ⟶ D} :
    IsFunApp (A ⟶ B ⟶ C ⟶ D) (elim₃RFun F) :=
  ⟨elim₃RFun₂ A B C D, F⟩

  @[reducible] def assocLR {A B C : U} (P : (A ⊓ B) ⊓ C) : A ⊓ (B ⊓ C) :=
  intro₃R (fst (fst P)) (snd (fst P)) (snd P)
  @[reducible] def assocRL {A B C : U} (P : A ⊓ (B ⊓ C)) : (A ⊓ B) ⊓ C :=
  intro₃L (fst P) (fst (snd P)) (snd (snd P))

  def defAssocLRFun (A B C : U) : (A ⊓ B) ⊓ C ⟶{assocLR} A ⊓ (B ⊓ C) := ⟨elim₃LFun (intro₃RFun₃ A B C)⟩
  def defAssocRLFun (A B C : U) : A ⊓ (B ⊓ C) ⟶{assocRL} (A ⊓ B) ⊓ C := ⟨elim₃RFun (intro₃LFun₃ A B C)⟩

  @[reducible] def assocLRFun (A B C : U) : (A ⊓ B) ⊓ C ⟶ A ⊓ (B ⊓ C) := (defAssocLRFun A B C).F
  @[reducible] def assocRLFun (A B C : U) : A ⊓ (B ⊓ C) ⟶ (A ⊓ B) ⊓ C := (defAssocRLFun A B C).F

  instance assocLR.isFunApp {A B C : U} {P : (A ⊓ B) ⊓ C} : IsFunApp ((A ⊓ B) ⊓ C) (assocLR P) :=
  ⟨assocLRFun A B C, P⟩
  instance assocRL.isFunApp {A B C : U} {P : A ⊓ (B ⊓ C)} : IsFunApp (A ⊓ (B ⊓ C)) (assocRL P) :=
  ⟨assocRLFun A B C, P⟩

  section

    @[reducible] def merge {A B C : U} (F : A ⟶ B) (G : A ⟶ C) (a : A) : B ⊓ C := intro (F a) (G a)

    variable [HasNonLinearLogic U]

    def defMergeFun₃ (A B C : U) : (A ⟶ B) ⟶ (A ⟶ C) ⟶ A ⟶{merge} B ⊓ C := by functoriality

    @[reducible] def mergeFun {A B C : U} (F : A ⟶ B) (G : A ⟶ C) : A ⟶ B ⊓ C := (((defMergeFun₃ A B C).app F).app G).F
    @[reducible] def mergeFun₃ (A B C : U) : (A ⟶ B) ⟶ (A ⟶ C) ⟶ (A ⟶ B ⊓ C) := (defMergeFun₃ A B C).F

    instance merge.isFunApp {A B C : U} {F : A ⟶ B} {G : A ⟶ C} {a : A} :
      IsFunApp A (merge F G a) :=
    ⟨mergeFun F G, a⟩

    instance mergeFun.isFunApp₂ {A B C : U} {F : A ⟶ B} {G : A ⟶ C} :
      IsFunApp₂ (A ⟶ B) (A ⟶ C) (mergeFun F G) :=
    ⟨mergeFun₃ A B C, F, G⟩

  end

  section

    variable [HasSubLinearLogic U]

    @[reducible] def distr {A B C : U} (F : A ⟶ B ⊓ C) : (A ⟶ B) ⊓ (A ⟶ C) :=
    intro (Λ a => fst (F a)) (Λ a => snd (F a))

    variable [HasNonLinearLogic U]

    def defDistrFun (A B C : U) : (A ⟶ B ⊓ C) ⟶{distr} (A ⟶ B) ⊓ (A ⟶ C) := by functoriality

    @[reducible] def distrFun (A B C : U) : (A ⟶ B ⊓ C) ⟶ (A ⟶ B) ⊓ (A ⟶ C) := (defDistrFun A B C).F

    instance distr.isFunApp {A B C : U} {F : A ⟶ B ⊓ C} : IsFunApp (A ⟶ B ⊓ C) (distr F) :=
    ⟨distrFun A B C, F⟩

  end

  section

    @[reducible] def invDistr {A B C : U} (P : (A ⟶ B) ⊓ (A ⟶ C)) (a : A) : B ⊓ C :=
    merge (fst P) (snd P) a

    variable [HasNonLinearLogic U]

    def defInvDistrFun₂ (A B C : U) : (A ⟶ B) ⊓ (A ⟶ C) ⟶ A ⟶{invDistr} (B ⊓ C) :=
    ⟨λ _ => by functoriality,
     ⟨elimFun (Λ F G a => merge F G a)⟩⟩

    @[reducible] def invDistrFun {A B C : U} (P : (A ⟶ B) ⊓ (A ⟶ C)) : A ⟶ B ⊓ C :=
    ((defInvDistrFun₂ A B C).app P).F
    @[reducible] def invDistrFun₂ (A B C : U) : (A ⟶ B) ⊓ (A ⟶ C) ⟶ (A ⟶ B ⊓ C) :=
    (defInvDistrFun₂ A B C).F

    instance invDistr.isFunApp {A B C : U} {P : (A ⟶ B) ⊓ (A ⟶ C)} {a : A} :
      IsFunApp A (invDistr P a) :=
    ⟨invDistrFun P, a⟩

    instance invDistrFun.isFunApp {A B C : U} {P : (A ⟶ B) ⊓ (A ⟶ C)} :
      IsFunApp ((A ⟶ B) ⊓ (A ⟶ C)) (invDistrFun P) :=
    ⟨invDistrFun₂ A B C, P⟩

  end

  section

    variable [HasTop U]

    def defProdTopIntroFun (A : U) : A ⟶{intro (top U)} Top U ⊓ A :=
    (defIntroFun₂ (Top U) A).app (top U)

    @[reducible] def prodTopIntroFun (A : U) : A ⟶ Top U ⊓ A :=
    (defProdTopIntroFun A).F

    def defProdTopElimFun (A : U) : Top U ⊓ A ⟶{snd} A :=
    ⟨elimFun (HasTop.elimFun (idFun A))⟩

    @[reducible] def prodTopElimFun (A : U) : Top U ⊓ A ⟶ A :=
    (defProdTopElimFun A).F

  end

end HasProductFun
