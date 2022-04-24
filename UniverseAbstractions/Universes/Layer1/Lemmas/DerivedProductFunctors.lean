import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Axioms.Singletons
import UniverseAbstractions.Universes.Layer1.Axioms.Products
import UniverseAbstractions.Universes.Layer1.Meta.Tactics.Functoriality



namespace UniverseAbstractions.Layer1

set_option autoBoundImplicitLocal false

open HasFunctors HasLinearLogic HasSubLinearLogic HasNonLinearLogic



namespace HasProducts

  variable {U : Universe} [HasFunctors U] [HasLinearLogic U] [HasProducts U]

  section

    variable [HasSubLinearLogic U]

    def fstFun (A B : U) : A ⊓ B ⟶ A := elimFun (Λ a b => a)
    def sndFun (A B : U) : A ⊓ B ⟶ B := elimFun (Λ a b => b)

    @[reducible] def fst {A B : U} (P : A ⊓ B) : A := (fstFun A B) P
    @[reducible] def snd {A B : U} (P : A ⊓ B) : B := (sndFun A B) P

  end

  section

    variable [HasNonLinearLogic U]

    def dupIntroFun (A : U) : A ⟶ A ⊓ A := Λ a => intro a a

  end

  def invElimFun₂ {A B C : U} (F : A ⊓ B ⟶ C) : A ⟶ B ⟶ C := Λ a b => F (intro a b)
  def invElimFun₃ (A B C : U) : (A ⊓ B ⟶ C) ⟶ (A ⟶ B ⟶ C) := Λ F => invElimFun₂ F

  instance invElimFun₂.isFunApp {A B C : U} {F : A ⊓ B ⟶ C} : IsFunApp (A ⊓ B ⟶ C) (invElimFun₂ F) :=
  ⟨invElimFun₃ A B C, F⟩

  def replaceFstFun {A B : U} (F : A ⟶ B) (C : U) : A ⊓ C ⟶ B ⊓ C := elimFun (Λ a b => intro (F a) b)
  def replaceFstFun₂ (A B C : U) : (A ⟶ B) ⟶ (A ⊓ C ⟶ B ⊓ C) := Λ F => replaceFstFun F C

  instance replaceFstFun.isFunApp {A B C : U} {F : A ⟶ B} : IsFunApp (A ⟶ B) (replaceFstFun F C) :=
  ⟨replaceFstFun₂ A B C, F⟩

  def replaceSndFun (A : U) {B C : U} (G : B ⟶ C) : A ⊓ B ⟶ A ⊓ C := elimFun (Λ a b => intro a (G b))
  def replaceSndFun₂ (A B C : U) : (B ⟶ C) ⟶ (A ⊓ B ⟶ A ⊓ C) := Λ G => replaceSndFun A G

  instance replaceSndFun.isFunApp {A B C : U} {F : B ⟶ C} : IsFunApp (B ⟶ C) (replaceSndFun A F) :=
  ⟨replaceSndFun₂ A B C, F⟩

  def replaceBothFun {A B C D : U} (F : A ⟶ B) (G : C ⟶ D) : A ⊓ C ⟶ B ⊓ D := elimFun (Λ a b => intro (F a) (G b))
  def replaceBothFun₃ (A B C D : U) : (A ⟶ B) ⟶ (C ⟶ D) ⟶ (A ⊓ C ⟶ B ⊓ D) := Λ F G => replaceBothFun F G

  instance replaceBothFun.isFunApp₂ {A B C D : U} {F : A ⟶ B} {G : C ⟶ D} :
    IsFunApp₂ (A ⟶ B) (C ⟶ D) (replaceBothFun F G) :=
  ⟨replaceBothFun₃ A B C D, F, G⟩

  def commFun (A B : U) : A ⊓ B ⟶ B ⊓ A := elimFun (Λ a b => intro b a)

  def intro₃LFun₃ (A B C : U) : A ⟶ B ⟶ C ⟶ (A ⊓ B) ⊓ C := Λ a b c => intro (intro a b) c
  def intro₃RFun₃ (A B C : U) : A ⟶ B ⟶ C ⟶ A ⊓ (B ⊓ C) := Λ a b c => intro a (intro b c)

  def elim₃LFun {A B C D : U} (F : A ⟶ B ⟶ C ⟶ D) : (A ⊓ B) ⊓ C ⟶ D := elimFun (elimFun F)
  def elim₃LFun₂ (A B C D : U) : (A ⟶ B ⟶ C ⟶ D) ⟶ ((A ⊓ B) ⊓ C ⟶ D) := Λ F => elim₃LFun F

  def elim₃RFun {A B C D : U} (F : A ⟶ B ⟶ C ⟶ D) : A ⊓ (B ⊓ C) ⟶ D := elimFun (Λ a => elimFun (F a))
  def elim₃RFun₂ (A B C D : U) : (A ⟶ B ⟶ C ⟶ D) ⟶ (A ⊓ (B ⊓ C) ⟶ D) := Λ F => elim₃RFun F

  instance elim₃LFun.isFunApp {A B C D : U} {F : A ⟶ B ⟶ C ⟶ D} :
    IsFunApp (A ⟶ B ⟶ C ⟶ D) (elim₃LFun F) :=
  ⟨elim₃LFun₂ A B C D, F⟩

  instance elim₃RFun.isFunApp {A B C D : U} {F : A ⟶ B ⟶ C ⟶ D} :
    IsFunApp (A ⟶ B ⟶ C ⟶ D) (elim₃RFun F) :=
  ⟨elim₃RFun₂ A B C D, F⟩

  def assocLRFun (A B C : U) : (A ⊓ B) ⊓ C ⟶ A ⊓ (B ⊓ C) := elim₃LFun (intro₃RFun₃ A B C)
  def assocRLFun (A B C : U) : A ⊓ (B ⊓ C) ⟶ (A ⊓ B) ⊓ C := elim₃RFun (intro₃LFun₃ A B C)

  section

    variable [HasNonLinearLogic U]

    def mergeFun {A B C : U} (F : A ⟶ B) (G : A ⟶ C) : A ⟶ B ⊓ C := Λ a => intro (F a) (G a)
    def mergeFun₃ (A B C : U) : (A ⟶ B) ⟶ (A ⟶ C) ⟶ (A ⟶ B ⊓ C) := Λ F G => mergeFun F G

    instance mergeFun.isFunApp₂ {A B C : U} {F : A ⟶ B} {G : A ⟶ C} :
      IsFunApp₂ (A ⟶ B) (A ⟶ C) (mergeFun F G) :=
    ⟨mergeFun₃ A B C, F, G⟩

  end

  section

    variable [HasSubLinearLogic U] [HasNonLinearLogic U]

    def distrFun (A B C : U) : (A ⟶ B ⊓ C) ⟶ (A ⟶ B) ⊓ (A ⟶ C) :=
    mergeFun (Λ F a => fst (F a)) (Λ F a => snd (F a))

  end

  section

    variable [HasNonLinearLogic U]

    def invDistrFun {A B C : U} (P : (A ⟶ B) ⊓ (A ⟶ C)) : A ⟶ B ⊓ C := elim (mergeFun₃ A B C) P
    def invDistrFun₂ (A B C : U) : (A ⟶ B) ⊓ (A ⟶ C) ⟶ (A ⟶ B ⊓ C) := Λ P => invDistrFun P

    instance invDistrFun.isFunApp {A B C : U} {P : (A ⟶ B) ⊓ (A ⟶ C)} :
      IsFunApp ((A ⟶ B) ⊓ (A ⟶ C)) (invDistrFun P) :=
    ⟨invDistrFun₂ A B C, P⟩

  end

  section


    variable [HasTop U]

    def prodTopIntroFun (A : U) : A ⟶ HasTop.Top U ⊓ A := Λ a => intro (HasTop.top U) a

    def prodTopElimFun (A : U) : HasTop.Top U ⊓ A ⟶ A := elimFun (HasTop.elimFun (idFun A))

  end

end HasProducts
