import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Singletons
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Lemmas.DerivedFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v iv



namespace HasInternalProducts

  open HasFunctors HasCongrArg HasCongrFun HasLinearFunOp HasSubLinearFunOp HasNonLinearFunOp
       HasProducts HasProductEq HasTop

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasLinearFunOp U]
           [HasInternalProducts U]

  section

    variable [HasSubLinearFunOp U]

    def defFstFun (A B : U) : A ⊓ B ⟶{λ P => fst P} A :=
    elimFun (constFunFun B A)
    ◄ byDef₂

    @[reducible] def fstFun (A B : U) : A ⊓ B ⟶ A := defFstFun A B

    instance fst.isFunApp {A B : U} {P : A ⊓ B} : IsFunApp (A ⊓ B) (fst P) :=
    { F := fstFun A B,
      a := P,
      e := byDef }

    def defSndFun (A B : U) : A ⊓ B ⟶{λ P => snd P} B :=
    elimFun (constFun A (idFun B))
    ◄ byDef₂

    @[reducible] def sndFun (A B : U) : A ⊓ B ⟶ B := defSndFun A B

    instance snd.isFunApp {A B : U} {P : A ⊓ B} : IsFunApp (A ⊓ B) (snd P) :=
    { F := sndFun A B,
      a := P,
      e := byDef }

  end

  section

    variable [HasNonLinearFunOp U]

    def defDupIntroFun (A : U) : A ⟶{λ a => intro a a} A ⊓ A :=
    dupFun (introFunFun A A)
    ◄ byDef₂

    @[reducible] def dupIntroFun (A : U) : A ⟶ A ⊓ A := defDupIntroFun A

  end

  def defRevIntroFun (A B : U) : B ⟶ A ⟶{λ b a => intro a b} A ⊓ B :=
  HasSwapFunFun.defSwapDefFun₂ (defIntroFun A B)

  @[reducible] def revIntroFun (A : U) {B : U} (b : B) : A ⟶ A ⊓ B := (defRevIntroFun A B).defFun b
  @[reducible] def revIntroFunFun (A B : U) : B ⟶ A ⟶ A ⊓ B := defRevIntroFun A B

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

  def intro.congrArgFst {A B : U} {a₁ a₂ : A} (ha : a₁ ≃ a₂) (b : B) :
    intro a₁ b ≃ intro a₂ b :=
  defCongrArg₂A (defIntroFun A B) ha b

  def intro.congrArgSnd {A B : U} (a : A) {b₁ b₂ : B} (hb : b₁ ≃ b₂) :
    intro a b₁ ≃ intro a b₂ :=
  defCongrArg₂B (defIntroFun A B) a hb

  def intro.congrArg {A B : U} {a₁ a₂ : A} (ha : a₁ ≃ a₂) {b₁ b₂ : B} (hb : b₁ ≃ b₂) :
    intro a₁ b₁ ≃ intro a₂ b₂ :=
  defCongrArg₂ (defIntroFun A B) ha hb

  def intro.congrArgEq [HasProductEq U U] {A B : U} {a : A} {b : B} {P : A ⊓ B}
                       (ha : a ≃ fst P) (hb : b ≃ snd P) :
    intro a b ≃ P :=
  introEq P • intro.congrArg ha hb

  def defRevElimFun (A B C : U) : (B ⟶ A ⟶ C) ⟶ A ⊓ B ⟶{λ F P => F (snd P) (fst P)} C :=
  ⟨λ F => elimFun (swapFunFun F)
          ◄ byDef₂,
   elimFunFun A B C • swapFunFunFun B A C
   ◄ byDefDef⟩

  @[reducible] def revElimFun {A B C : U} (F : B ⟶ A ⟶ C) : A ⊓ B ⟶ C := (defRevElimFun A B C).defFun F
  @[reducible] def revElimFunFun (A B C : U) : (B ⟶ A ⟶ C) ⟶ (A ⊓ B ⟶ C) := defRevElimFun A B C

  instance revElimFun.isFunApp {A B C : U} {F : B ⟶ A ⟶ C} :
    IsFunApp (B ⟶ A ⟶ C) (revElimFun F) :=
  { F := revElimFunFun A B C,
    a := F,
    e := byDef }

  def invElim {A B C : U} (F : A ⊓ B ⟶ C) (a : A) (b : B) : C := F (intro a b)

  def defInvElimFun (A B C : U) : (A ⊓ B ⟶ C) ⟶ A ⟶ B ⟶{λ F a b => invElim F a b} C :=
  ⟨λ F => ⟨λ a => F • introFun a B
                  ◄ byArgDef,
           revCompFunFun B F • introFunFun A B
           ◄ byDefDef⟩,
   compFunFun (introFunFun A B) (B ⟶ C) • revCompFunFunFun B (A ⊓ B) C
   ◄ byDefDef⟩

  @[reducible] def invElimFun {A B C : U} (F : A ⊓ B ⟶ C) (a : A) : B ⟶ C := ((defInvElimFun A B C).defFun F).defFun a
  @[reducible] def invElimFunFun {A B C : U} (F : A ⊓ B ⟶ C) : A ⟶ B ⟶ C := (defInvElimFun A B C).defFun F
  @[reducible] def invElimFunFunFun (A B C : U) : (A ⊓ B ⟶ C) ⟶ (A ⟶ B ⟶ C) := defInvElimFun A B C

  instance invElimFun.isFunApp {A B C : U} {F : A ⊓ B ⟶ C} {a : A} :
    IsFunApp A (invElimFun F a) :=
  { F := invElimFunFun F,
    a := a,
    e := byDef }

  instance invElimFunFun.isFunApp {A B C : U} {F : A ⊓ B ⟶ C} :
    IsFunApp (A ⊓ B ⟶ C) (invElimFunFun F) :=
  { F := invElimFunFunFun A B C,
    a := F,
    e := byDef }

  def defReplaceFstFun (A B C : U) :
    (A ⟶ B) ⟶ A ⊓ C ⟶{λ F P => intro (F (fst P)) (snd P)} B ⊓ C :=
  ⟨λ F => elimFun (introFunFun B C • F)
          ◄ byDef₂ • byFunDef,
   elimFunFun A C (B ⊓ C) • revCompFunFun A (introFunFun B C)
   ◄ byDefDef⟩

  @[reducible] def replaceFstFun {A B : U} (F : A ⟶ B) (C : U) : A ⊓ C ⟶ B ⊓ C := (defReplaceFstFun A B C).defFun F
  @[reducible] def replaceFstFunFun (A B C : U) : (A ⟶ B) ⟶ (A ⊓ C ⟶ B ⊓ C) := defReplaceFstFun A B C

  def defReplaceFstDefFun {A B : U} {f : A → B} (F : A ⟶{f} B) (C : U) :
    A ⊓ C ⟶{λ P => intro (f (fst P)) (snd P)} B ⊓ C :=
  replaceFstFun F C
  ◄ intro.congrArgFst byDef (snd _)

  instance replaceFstFun.isFunApp {A B C : U} {F : A ⟶ B} :
    IsFunApp (A ⟶ B) (replaceFstFun F C) :=
  { F := replaceFstFunFun A B C,
    a := F,
    e := byDef }

  def defReplaceSndFun (A B C : U) :
    (B ⟶ C) ⟶ A ⊓ B ⟶{λ F P => intro (fst P) (F (snd P))} A ⊓ C :=
  ⟨λ F => elimFun (compFunFun F (A ⊓ C) • introFunFun A C)
          ◄ byDef₂ • byDef₂ • byFunDef,
   elimFunFun A B (A ⊓ C) • compFunFun (introFunFun A C) (B ⟶ A ⊓ C) • compFunFunFun B C (A ⊓ C)
   ◄ byDefDefDef • byArgDef⟩

  @[reducible] def replaceSndFun (A : U) {B C : U} (F : B ⟶ C) : A ⊓ B ⟶ A ⊓ C := (defReplaceSndFun A B C).defFun F
  @[reducible] def replaceSndFunFun (A B C : U) : (B ⟶ C) ⟶ (A ⊓ B ⟶ A ⊓ C) := defReplaceSndFun A B C

  def defReplaceSndDefFun (A : U) {B C : U} {f : B → C} (F : B ⟶{f} C) :
    A ⊓ B ⟶{λ P => intro (fst P) (f (snd P))} A ⊓ C :=
  replaceSndFun A F
  ◄ intro.congrArgSnd (fst _) byDef

  instance replaceSndFun.isFunApp {A B C : U} {F : B ⟶ C} :
    IsFunApp (B ⟶ C) (replaceSndFun A F) :=
  { F := replaceSndFunFun A B C,
    a := F,
    e := byDef }

  def defReplaceBothFun (A B C D : U) :
    (A ⟶ B) ⟶ (C ⟶ D) ⟶ A ⊓ C ⟶{λ F G P => intro (F (fst P)) (G (snd P))} B ⊓ D :=
  ⟨λ F => ⟨λ G => elimFun (compFunFun G (B ⊓ D) • introFunFun B D • F)
                  ◄ byDef₂ • byDef₂ • congrFun byArgDef _ • byFunDef,
           elimFunFun A C (B ⊓ D) • compFunFun (introFunFun B D • F) (C ⟶ B ⊓ D) • compFunFunFun C D (B ⊓ D)
           ◄ byDefDefDef • byArgDef⟩,
   revCompFunFun (C ⟶ D) (elimFunFun A C (B ⊓ D)) •
   compFunFun (compFunFunFun C D (B ⊓ D)) (A ⟶ C ⟶ B ⊓ D) •
   compFunFunFun A (D ⟶ B ⊓ D) (C ⟶ B ⊓ D) •
   revCompFunFun A (introFunFun B D)
   ◄ byDef • congrArg (revCompFunFun (C ⟶ D) (elimFunFun A C (B ⊓ D)))
                      (byDefDefDef • byArgDef • byDef)⟩

  @[reducible] def replaceBothFun {A B C D : U} (F : A ⟶ B) (G : C ⟶ D) : A ⊓ C ⟶ B ⊓ D := ((defReplaceBothFun A B C D).defFun F).defFun G
  @[reducible] def replaceBothFunFun {A B : U} (F : A ⟶ B) (C D : U) : (C ⟶ D) ⟶ A ⊓ C ⟶ B ⊓ D := (defReplaceBothFun A B C D).defFun F
  @[reducible] def replaceBothFunFunFun (A B C D : U) : (A ⟶ B) ⟶ (C ⟶ D) ⟶ A ⊓ C ⟶ B ⊓ D := defReplaceBothFun A B C D

  def defReplaceBothDefFun {A B C D : U} {f : A → B} (F : A ⟶{f} B) {g : C → D} (G : C ⟶{g} D) :
    A ⊓ C ⟶{λ P => intro (f (fst P)) (g (snd P))} B ⊓ D :=
  replaceBothFun F G
  ◄ intro.congrArg byDef byDef

  instance replaceBothFun.isFunApp {A B C D : U} {F : A ⟶ B} {G : C ⟶ D} :
    IsFunApp (C ⟶ D) (replaceBothFun F G) :=
  { F := replaceBothFunFun F C D,
    a := G,
    e := byDef }

  instance replaceBothFunFun.isFunApp {A B C D : U} {F : A ⟶ B} :
    IsFunApp (A ⟶ B) (replaceBothFunFun F C D) :=
  { F := replaceBothFunFunFun A B C D,
    a := F,
    e := byDef }

  def defReplaceBothFun₂ {A A' B C C' D : U} (F : A ⟶ A' ⟶ B) (G : C ⟶ C' ⟶ D) :
    A ⊓ C ⟶ A' ⊓ C' ⟶{λ P Q => intro (F (fst P) (fst Q)) (G (snd P) (snd Q))} B ⊓ D :=
  ⟨λ P => ((defReplaceBothFun A' B C' D).defFun (F (fst P))).defFun (G (snd P)),
   elimFun (compFunFun G (A' ⊓ C' ⟶ B ⊓ D) • replaceBothFunFunFun A' B C' D • F)
   ◄ byDef₂ • byDef₂ • congrFun byArgDef _ • byFunDef⟩

  @[reducible] def replaceBothFun₂ {A A' B C C' D : U} (F : A ⟶ A' ⟶ B) (G : C ⟶ C' ⟶ D) :
    A ⊓ C ⟶ A' ⊓ C' ⟶ B ⊓ D :=
  defReplaceBothFun₂ F G

  def defReplaceBothDefFun₂ {A A' B C C' D : U} {f : A → A' → B} (F : A ⟶ A' ⟶{f} B)
                                                {g : C → C' → D} (G : C ⟶ C' ⟶{g} D) :
    A ⊓ C ⟶ A' ⊓ C' ⟶{λ P Q => intro (f (fst P) (fst Q)) (g (snd P) (snd Q))} B ⊓ D :=
  replaceBothFun₂ F G
  ◄◄ intro.congrArg byDef₂ byDef₂

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

  def elim₃LFun {A B C D : U} (F : A ⟶ B ⟶ C ⟶ D) : (A ⊓ B) ⊓ C ⟶ D := elimFun (elimFun F)
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

  section

    variable [HasNonLinearFunOp U]

    def defMergeFun (A B C : U) :
      (A ⟶ B) ⟶(A ⟶ C) ⟶ A ⟶{λ F G a => intro (F a) (G a)} B ⊓ C :=
    ⟨λ F => ⟨λ G => substFun F (revIntroFunFun B C • G)
                    ◄ byDef₂ • byFunDef,
             substFunFun F (B ⊓ C) • revCompFunFun A (revIntroFunFun B C)
             ◄ byDefDef⟩,
     compFunFun (revCompFunFun A (revIntroFunFun B C)) (A ⟶ B ⊓ C) •
     substFunFunFun A B (B ⊓ C)
     ◄ byDefDef⟩

    @[reducible] def mergeFun {A B C : U} (F : A ⟶ B) (G : A ⟶ C) : A ⟶ B ⊓ C := ((defMergeFun A B C).defFun F).defFun G
    @[reducible] def mergeFunFun {A B : U} (F : A ⟶ B) (C : U) : (A ⟶ C) ⟶ (A ⟶ B ⊓ C) := (defMergeFun A B C).defFun F
    @[reducible] def mergeFunFunFun (A B C : U) : (A ⟶ B) ⟶ (A ⟶ C) ⟶ (A ⟶ B ⊓ C) := defMergeFun A B C

    instance mergeFun.isFunApp {A B C : U} {F : A ⟶ B} {G : A ⟶ C} :
      IsFunApp (A ⟶ C) (mergeFun F G) :=
    { F := mergeFunFun F C,
      a := G,
      e := byDef }

    instance mergeFunFun.isFunApp {A B C : U} {F : A ⟶ B} :
      IsFunApp (A ⟶ B) (mergeFunFun F C) :=
    { F := mergeFunFunFun A B C,
      a := F,
      e := byDef }

  end

  section

    variable [HasSubLinearFunOp U]

    def distr {A B C : U} (F : A ⟶ B ⊓ C) : (A ⟶ B) ⊓ (A ⟶ C) :=
    intro (fstFun B C • F) (sndFun B C • F)

    variable [HasNonLinearFunOp U]

    def defDistrFun (A B C : U) : (A ⟶ B ⊓ C) ⟶{λ F => distr F} (A ⟶ B) ⊓ (A ⟶ C) :=
    mergeFun (revCompFunFun A (fstFun B C)) (revCompFunFun A (sndFun B C))
    ◄ intro.congrArg byDef byDef

    @[reducible] def distrFun (A B C : U) : (A ⟶ B ⊓ C) ⟶ (A ⟶ B) ⊓ (A ⟶ C) := defDistrFun A B C

    instance distr.isFunApp {A B C : U} {F : A ⟶ B ⊓ C} : IsFunApp (A ⟶ B ⊓ C) (distr F) :=
    { F := distrFun A B C,
      a := F,
      e := byDef }

  end

  section

    variable [HasNonLinearFunOp U]

    def invDistrFun {A B C : U} (P : (A ⟶ B) ⊓ (A ⟶ C)) : A ⟶ B ⊓ C :=
    mergeFun (fst P) (snd P)

    def defInvDistrFunFun (A B C : U) :
      (A ⟶ B) ⊓ (A ⟶ C) ⟶{λ P => invDistrFun P} (A ⟶ B ⊓ C) :=
    elimFun (mergeFunFunFun A B C)
    ◄ byDef₂

    @[reducible] def invDistrFunFun (A B C : U) :
      (A ⟶ B) ⊓ (A ⟶ C) ⟶ (A ⟶ B ⊓ C) :=
    defInvDistrFunFun A B C

    instance invDistrFun.isFunApp {A B C : U} {P : (A ⟶ B) ⊓ (A ⟶ C)} :
      IsFunApp ((A ⟶ B) ⊓ (A ⟶ C)) (invDistrFun P) :=
    { F := invDistrFunFun A B C,
      a := P,
      e := byDef }

  end

  section

    variable [HasInternalTop U]

    def defProdTopIntroFun (A : U) : A ⟶{λ a => intro (top U) a} Top U ⊓ A :=
    (defIntroFun (Top U) A).defFun (top U)

    @[reducible] def prodTopIntroFun (A : U) : A ⟶ Top U ⊓ A :=
    defProdTopIntroFun A

    def defProdTopElimFun (A : U) : Top U ⊓ A ⟶{λ P => snd P} A :=
    elimFun (HasInternalTop.elimFun (idFun A))
    ◄ byDef₂

    @[reducible] def prodTopElimFun (A : U) : Top U ⊓ A ⟶ A :=
    defProdTopElimFun A

  end

end HasInternalProducts



namespace MetaRelation

  open HasProducts HasInternalProducts

  variable {α : Sort u} {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasInternalFunctors V]
           [HasInternalProducts V] (R S : MetaRelation α V)

  def productRelation : MetaRelation α V := λ a b => R a b ⊓ S a b

  namespace productRelation

    instance hasRefl [hR : HasRefl R] [hS : HasRefl S] : HasRefl (productRelation R S) :=
    ⟨λ a => intro (hR.refl a) (hS.refl a)⟩

    instance hasSymm [hR : HasSymm R] [hS : HasSymm S] : HasSymm (productRelation R S) :=
    ⟨λ P => intro (hR.symm (fst P)) (hS.symm (snd P))⟩

    instance hasTrans [hR : HasTrans R] [hS : HasTrans S] : HasTrans (productRelation R S) :=
    ⟨λ P Q => intro (hR.trans (fst P) (fst Q)) (hS.trans (snd P) (snd Q))⟩

    instance isPreorder    [hR : IsPreorder    R] [hS : IsPreorder    S] : IsPreorder    (productRelation R S) := ⟨⟩
    instance isEquivalence [hR : IsEquivalence R] [hS : IsEquivalence S] : IsEquivalence (productRelation R S) := ⟨⟩

    variable [HasLinearFunOp V]

    instance hasSymmFun [HasSymm R] [HasSymm S] [hR : HasSymmFun R] [hS : HasSymmFun S] :
      HasSymmFun (productRelation R S) :=
    ⟨λ a b => defReplaceBothDefFun (hR.defSymmFun a b) (hS.defSymmFun a b)⟩

    instance hasTransFun [HasTrans R] [HasTrans S] [hR : HasTransFun R] [hS : HasTransFun S] :
      HasTransFun (productRelation R S) :=
    ⟨λ a b c => defReplaceBothDefFun₂ (hR.defTransFun a b c) (hS.defTransFun a b c)⟩

    variable [hEq : HasProductEq V V]

    def hasRefl.fstEq [hR : HasRefl R] [hS : HasRefl S] (a : α) :
      fst ((hasRefl R S).refl a) ≃ hR.refl a :=
    hEq.fstEq (hR.refl a) (hS.refl a)

    def hasRefl.sndEq [hR : HasRefl R] [hS : HasRefl S] (a : α) :
      snd ((hasRefl R S).refl a) ≃ hS.refl a :=
    hEq.sndEq (hR.refl a) (hS.refl a)

    def hasSymm.fstEq [hR : HasSymm R] [hS : HasSymm S] {a b : α} (f : (productRelation R S) a b) :
      fst ((hasSymm R S).symm f) ≃ hR.symm (fst f) :=
    hEq.fstEq (hR.symm (fst f)) (hS.symm (snd f))

    def hasSymm.sndEq [hR : HasSymm R] [hS : HasSymm S] {a b : α} (f : (productRelation R S) a b) :
      snd ((hasSymm R S).symm f) ≃ hS.symm (snd f) :=
    hEq.sndEq (hR.symm (fst f)) (hS.symm (snd f))

    def hasTrans.fstEq [hR : HasTrans R] [hS : HasTrans S] {a b c : α}
                       (f : (productRelation R S) a b) (g : (productRelation R S) b c) :
      fst ((hasTrans R S).trans f g) ≃ hR.trans (fst f) (fst g) :=
    hEq.fstEq (hR.trans (fst f) (fst g)) (hS.trans (snd f) (snd g))

    def hasTrans.sndEq [hR : HasTrans R] [hS : HasTrans S] {a b c : α}
                       (f : (productRelation R S) a b) (g : (productRelation R S) b c) :
      snd ((hasTrans R S).trans f g) ≃ hS.trans (snd f) (snd g) :=
    hEq.sndEq (hR.trans (fst f) (fst g)) (hS.trans (snd f) (snd g))

  end productRelation

end MetaRelation
