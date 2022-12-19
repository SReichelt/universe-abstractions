import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Axioms.Singletons
import UniverseAbstractions.Universes.Layer1.Axioms.Products
import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations
import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations.Cartesian
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedFunctors
import UniverseAbstractions.Universes.Layer1.Meta.Tactics.Functoriality



namespace UniverseAbstractions.Layer1

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

open HasFunctors HasLinearLogic HasProducts HasPreorderRelation



namespace HasProducts

  variable {U : Universe} [HasLinearLogic U] [HasProducts U]

  section

    variable [HasSubLinearLogic U]

    @[reducible] def fstFun (A B : U) : A ⊓ B ⥤ A := elimFun (Λ a b => a)
    @[reducible] def sndFun (A B : U) : A ⊓ B ⥤ B := elimFun (Λ a b => b)

    instance fst.isFunApp {A B : U} {P : A ⊓ B} : IsFunApp (fst P) := ⟨fstFun A B, P⟩
    instance snd.isFunApp {A B : U} {P : A ⊓ B} : IsFunApp (snd P) := ⟨sndFun A B, P⟩

  end

  section

    variable [HasNonLinearLogic U]

    def dupIntroFun (A : U) : A ⥤ A ⊓ A := Λ a => intro a a

  end

  @[reducible] def evalFun (A B : U) : (A ⥤ B) ⊓ A ⥤ B := elimFun (HasIdFun.appFun₂ A B)

  def invElimFun₂ {A B Y : U} (F : A ⊓ B ⥤ Y) : A ⥤ B ⥤ Y := Λ a b => F (intro a b)
  def invElimFun₃ (A B Y : U) : (A ⊓ B ⥤ Y) ⥤ (A ⥤ B ⥤ Y) := Λ F => invElimFun₂ F

  instance invElimFun₂.isFunApp {A B Y : U} {F : A ⊓ B ⥤ Y} : IsFunApp (invElimFun₂ F) :=
    ⟨invElimFun₃ A B Y, F⟩

  def replaceFstFun {A B : U} (F : A ⥤ B) (C : U) : A ⊓ C ⥤ B ⊓ C := elimFun (Λ a b => intro (F a) b)
  def replaceFstFun₂ (A B C : U) : (A ⥤ B) ⥤ (A ⊓ C ⥤ B ⊓ C) := Λ F => replaceFstFun F C

  instance replaceFstFun.isFunApp {A B C : U} {F : A ⥤ B} : IsFunApp (replaceFstFun F C) :=
    ⟨replaceFstFun₂ A B C, F⟩

  def replaceSndFun (A : U) {B C : U} (G : B ⥤ C) : A ⊓ B ⥤ A ⊓ C := elimFun (Λ a b => intro a (G b))
  def replaceSndFun₂ (A B C : U) : (B ⥤ C) ⥤ (A ⊓ B ⥤ A ⊓ C) := Λ G => replaceSndFun A G

  instance replaceSndFun.isFunApp {A B C : U} {F : B ⥤ C} : IsFunApp (replaceSndFun A F) :=
    ⟨replaceSndFun₂ A B C, F⟩

  def replaceBothFun {A B C D : U} (F : A ⥤ B) (G : C ⥤ D) : A ⊓ C ⥤ B ⊓ D :=
    elimFun (Λ a b => intro (F a) (G b))
  def replaceBothFun₃ (A B C D : U) : (A ⥤ B) ⥤ (C ⥤ D) ⥤ (A ⊓ C ⥤ B ⊓ D) :=
    Λ F G => replaceBothFun F G

  instance replaceBothFun.isFunApp₂ {A B C D : U} {F : A ⥤ B} {G : C ⥤ D} :
      IsFunApp₂ (replaceBothFun F G) :=
    ⟨replaceBothFun₃ A B C D, F, G⟩

  def commFun (A B : U) : A ⊓ B ⥤ B ⊓ A := elimFun (Λ a b => intro b a)

  def intro₃LFun₃ (A B C : U) : A ⥤ B ⥤ C ⥤ (A ⊓ B) ⊓ C := Λ a b c => intro (intro a b) c
  def intro₃RFun₃ (A B C : U) : A ⥤ B ⥤ C ⥤ A ⊓ (B ⊓ C) := Λ a b c => intro a (intro b c)

  def elim₃LFun {A B C Y : U} (F : A ⥤ B ⥤ C ⥤ Y) : (A ⊓ B) ⊓ C ⥤ Y := elimFun (elimFun F)
  def elim₃LFun₂ (A B C Y : U) : (A ⥤ B ⥤ C ⥤ Y) ⥤ ((A ⊓ B) ⊓ C ⥤ Y) := Λ F => elim₃LFun F
  def elim₃RFun {A B C Y : U} (F : A ⥤ B ⥤ C ⥤ Y) : A ⊓ (B ⊓ C) ⥤ Y := elimFun (Λ a => elimFun (F a))
  def elim₃RFun₂ (A B C Y : U) : (A ⥤ B ⥤ C ⥤ Y) ⥤ (A ⊓ (B ⊓ C) ⥤ Y) := Λ F => elim₃RFun F

  instance elim₃LFun.isFunApp {A B C Y : U} {F : A ⥤ B ⥤ C ⥤ Y} : IsFunApp (elim₃LFun F) :=
    ⟨elim₃LFun₂ A B C Y, F⟩

  instance elim₃RFun.isFunApp {A B C Y : U} {F : A ⥤ B ⥤ C ⥤ Y} : IsFunApp (elim₃RFun F) :=
    ⟨elim₃RFun₂ A B C Y, F⟩

  def assocLRFun (A B C : U) : (A ⊓ B) ⊓ C ⥤ A ⊓ (B ⊓ C) := elim₃LFun (intro₃RFun₃ A B C)
  def assocRLFun (A B C : U) : A ⊓ (B ⊓ C) ⥤ (A ⊓ B) ⊓ C := elim₃RFun (intro₃LFun₃ A B C)

  section

    variable [HasNonLinearLogic U]

    def mergeFun {A B C : U} (F : A ⥤ B) (G : A ⥤ C) : A ⥤ B ⊓ C := Λ a => intro (F a) (G a)
    def mergeFun₃ (A B C : U) : (A ⥤ B) ⥤ (A ⥤ C) ⥤ (A ⥤ B ⊓ C) := Λ F G => mergeFun F G

    instance mergeFun.isFunApp₂ {A B C : U} {F : A ⥤ B} {G : A ⥤ C} : IsFunApp₂ (mergeFun F G) :=
      ⟨mergeFun₃ A B C, F, G⟩

  end

  section

    variable [HasSubLinearLogic U] [HasNonLinearLogic U]

    @[reducible] def distrFun (A B C : U) : (A ⥤ B ⊓ C) ⥤ (A ⥤ B) ⊓ (A ⥤ C) :=
      mergeFun (Λ F a => fst (F a)) (Λ F a => snd (F a))

  end

  section

    variable [HasNonLinearLogic U]

    @[reducible] def invDistrFun₂ (A B C : U) : (A ⥤ B) ⊓ (A ⥤ C) ⥤ (A ⥤ B ⊓ C) :=
      elimFun (mergeFun₃ A B C)

  end

  section

    variable [HasTop U]

    def prodTopIntroFun (A : U) : A ⥤ ⊤_U ⊓ A := Λ a => intro ∗_U a
    def prodTopElimFun (A : U) : ⊤_U ⊓ A ⥤ A := elimFun (HasTop.elimFun (idFun A))

  end

  section

    variable [HasBot U]

    def prodBotIntroFun (A : U) : ⊥_U ⥤ ⊥_U ⊓ A := HasBot.elimFun (⊥_U ⊓ A)
    def prodBotElimFun (A : U) : ⊥_U ⊓ A ⥤ ⊥_U := elimFun (HasBot.elimFun (A ⥤ ⊥_U))

  end

end HasProducts



namespace Prerelation

  @[reducible] def product {α : Sort u} {V : Universe} [HasLinearLogic V] [HasProducts V]
                           (R S : Prerelation α V) :
      Prerelation α V :=
    λ a b => R a b ⊓ S a b

  namespace product

    variable {α : Sort u} {V : Universe} [HasLinearLogic V] [HasProducts V]
             (R S : Prerelation α V)

    instance isFull [hR : IsFull R] [hS : IsFull S] : IsFull (product R S) :=
      ⟨λ a b => intro (hR.inst a b) (hS.inst a b)⟩

    instance hasRefl  [hR : HasRefl  R] [hS : HasRefl  S] : HasRefl  (product R S) :=
      ⟨λ a => intro (hR.refl a) (hS.refl a)⟩
    instance hasSymm  [hR : HasSymm  R] [hS : HasSymm  S] : HasSymm  (product R S) :=
      ⟨λ a b => elimFun (Λ el er => intro el⁻¹ er⁻¹)⟩
    instance hasTrans [hR : HasTrans R] [hS : HasTrans S] : HasTrans (product R S) :=
      ⟨λ a b c => elimFun (Λ gl gr => elimFun (Λ fl fr => intro (gl • fl) (gr • fr)))⟩

    instance isPreorder    [IsPreorder    R] [IsPreorder    S] : IsPreorder    (product R S) := ⟨⟩
    instance isEquivalence [IsEquivalence R] [IsEquivalence S] : IsEquivalence (product R S) := ⟨⟩

  end product

end Prerelation



namespace HasProducts

  def prodRel (U : Universe) [HasLinearLogic U] [HasProducts U] : Prerelation U U :=
    λ A B => A ⊓ B

  variable (U : Universe) [HasFullLogic U] [HasProducts U]

  instance hasProductObjects : HasProductObjects U where
    prod          := prodRel U
    fstHom        := fstFun
    sndHom        := sndFun
    prodIntroFun₂ := mergeFun₃

  instance hasExponentialObjects : HasExponentialObjects U where
    exp      := funRel U
    evalHom  := evalFun
    curryFun := invElimFun₃

end HasProducts
