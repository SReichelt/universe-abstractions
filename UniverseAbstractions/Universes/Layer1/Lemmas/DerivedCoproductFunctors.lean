import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Axioms.Singletons
import UniverseAbstractions.Universes.Layer1.Axioms.Products
import UniverseAbstractions.Universes.Layer1.Axioms.Coproducts
import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations
import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations.Cartesian
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedFunctors
import UniverseAbstractions.Universes.Layer1.Meta.Tactics.Functoriality



namespace UniverseAbstractions.Layer1

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

open HasFunctors HasLinearLogic HasCoproducts HasPreorderRelation



namespace HasCoproducts

  variable {U : Universe} [HasLinearLogic U] [HasCoproducts U]

  def leftCoIntro {A B C : U} (F : A ⊔ B ⥤ C) (a : A) : C := F (leftIntro a B)
  def leftCoIntroFun {A B C : U} (F : A ⊔ B ⥤ C) : A ⥤ C := Λ a => leftCoIntro F a
  def leftCoIntroFun₂ (A B C : U) : (A ⊔ B ⥤ C) ⥤ (A ⥤ C) := Λ F => leftCoIntroFun F

  def rightCoIntro {A B C : U} (F : A ⊔ B ⥤ C) (b : B) : C := F (rightIntro A b)
  def rightCoIntroFun {A B C : U} (F : A ⊔ B ⥤ C) : B ⥤ C := Λ b => rightCoIntro F b
  def rightCoIntroFun₂ (A B C : U) : (A ⊔ B ⥤ C) ⥤ (B ⥤ C) := Λ F => rightCoIntroFun F

  instance leftCoIntro.isFunApp {A B C : U} {F : A ⊔ B ⥤ C} {a : A} : IsFunApp (leftCoIntro F a) :=
    ⟨leftCoIntroFun F, a⟩

  instance leftCoIntroFun.isFunApp {A B C : U} {F : A ⊔ B ⥤ C} : IsFunApp (leftCoIntroFun F) :=
    ⟨leftCoIntroFun₂ A B C, F⟩

  instance rightCoIntro.isFunApp {A B C : U} {F : A ⊔ B ⥤ C} {b : B} :
      IsFunApp (rightCoIntro F b) :=
    ⟨rightCoIntroFun F, b⟩

  instance rightCoIntroFun.isFunApp {A B C : U} {F : A ⊔ B ⥤ C} : IsFunApp (rightCoIntroFun F) :=
    ⟨rightCoIntroFun₂ A B C, F⟩

  def dupIntroFun (A : U) : A ⥤ A ⊔ A := Λ a => leftIntro a A

  def replaceFstFun {A B : U} (F : A ⥤ B) (C : U) : A ⊔ C ⥤ B ⊔ C :=
    elimFun (Λ a => leftIntro (F a) C) (rightIntroFun B C)
  def replaceFstFun₂ (A B C : U) : (A ⥤ B) ⥤ (A ⊔ C ⥤ B ⊔ C) := Λ F => replaceFstFun F C

  instance replaceFstFun.isFunApp {A B C : U} {F : A ⥤ B} : IsFunApp (replaceFstFun F C) :=
    ⟨replaceFstFun₂ A B C, F⟩

  def replaceSndFun (A : U) {B C : U} (G : B ⥤ C) : A ⊔ B ⥤ A ⊔ C :=
    elimFun (leftIntroFun A C) (Λ b => rightIntro A (G b))
  def replaceSndFun₂ (A B C : U) : (B ⥤ C) ⥤ (A ⊔ B ⥤ A ⊔ C) := Λ G => replaceSndFun A G

  instance replaceSndFun.isFunApp {A B C : U} {F : B ⥤ C} : IsFunApp (replaceSndFun A F) :=
    ⟨replaceSndFun₂ A B C, F⟩

  def replaceBothFun {A B C D : U} (F : A ⥤ B) (G : C ⥤ D) : A ⊔ C ⥤ B ⊔ D :=
    elimFun (Λ a => leftIntro (F a) D) (Λ c => rightIntro B (G c))
  def replaceBothFun₃ (A B C D : U) : (A ⥤ B) ⥤ (C ⥤ D) ⥤ (A ⊔ C ⥤ B ⊔ D) :=
    Λ F G => replaceBothFun F G

  instance replaceBothFun.isFunApp₂ {A B C D : U} {F : A ⥤ B} {G : C ⥤ D} :
      IsFunApp₂ (replaceBothFun F G) :=
    ⟨replaceBothFun₃ A B C D, F, G⟩

  def commFun (A B : U) : A ⊔ B ⥤ B ⊔ A := elimFun (rightIntroFun B A) (leftIntroFun B A)

  def leftIntro₃LFun (A B C : U) : A ⥤ (A ⊔ B) ⊔ C := Λ a => leftIntro (leftIntro a B) C
  def leftIntro₃RFun (A B C : U) : A ⥤ A ⊔ (B ⊔ C) := leftIntroFun A (B ⊔ C)
  def middleIntro₃LFun (A B C : U) : B ⥤ (A ⊔ B) ⊔ C := Λ b => leftIntro (rightIntro A b) C
  def middleIntro₃RFun (A B C : U) : B ⥤ A ⊔ (B ⊔ C) := Λ b => rightIntro A (leftIntro b C)
  def rightIntro₃LFun (A B C : U) : C ⥤ (A ⊔ B) ⊔ C := rightIntroFun (A ⊔ B) C
  def rightIntro₃RFun (A B C : U) : C ⥤ A ⊔ (B ⊔ C) := Λ c => rightIntro A (rightIntro B c)

  def elim₃LFun {A B C D : U} (F : A ⥤ D) (G : B ⥤ D) (H : C ⥤ D) : (A ⊔ B) ⊔ C ⥤ D :=
    elimFun (elimFun F G) H
  def elim₃LFun₄ (A B C D : U) : (A ⥤ D) ⥤ (B ⥤ D) ⥤ (C ⥤ D) ⥤ ((A ⊔ B) ⊔ C ⥤ D) :=
    Λ F G H => elim₃LFun F G H
  def elim₃RFun {A B C D : U} (F : A ⥤ D) (G : B ⥤ D) (H : C ⥤ D) : A ⊔ (B ⊔ C) ⥤ D :=
    elimFun F (elimFun G H)
  def elim₃RFun₄ (A B C D : U) : (A ⥤ D) ⥤ (B ⥤ D) ⥤ (C ⥤ D) ⥤ (A ⊔ (B ⊔ C) ⥤ D) :=
    Λ F G H => elim₃RFun F G H

  instance elim₃LFun.isFunApp₃ {A B C D : U} {F : A ⥤ D} {G : B ⥤ D} {H : C ⥤ D} :
      IsFunApp₃ (elim₃LFun F G H) :=
    ⟨elim₃LFun₄ A B C D, F, G, H⟩

  instance elim₃RFun.isFunApp₃ {A B C D : U} {F : A ⥤ D} {G : B ⥤ D} {H : C ⥤ D} :
      IsFunApp₃ (elim₃RFun F G H) :=
    ⟨elim₃RFun₄ A B C D, F, G, H⟩

  def assocLRFun (A B C : U) : (A ⊔ B) ⊔ C ⥤ A ⊔ (B ⊔ C) :=
    elim₃LFun (leftIntro₃RFun A B C) (middleIntro₃RFun A B C) (rightIntro₃RFun A B C)
  def assocRLFun (A B C : U) : A ⊔ (B ⊔ C) ⥤ (A ⊔ B) ⊔ C :=
    elim₃RFun (leftIntro₃LFun A B C) (middleIntro₃LFun A B C) (rightIntro₃LFun A B C)

  section

    variable [HasProducts U]

    def distrFun [HasNonLinearLogic U] (A B C : U) : (A ⊔ B ⥤ C) ⥤ (A ⥤ C) ⊓ (B ⥤ C) :=
      Λ F => HasProducts.intro (leftCoIntroFun F) (rightCoIntroFun F)

    def invDistrFun₂ (A B C : U) : (A ⥤ C) ⊓ (B ⥤ C) ⥤ (A ⊔ B ⥤ C) :=
      HasProducts.elimFun (elimFun₃ A B C)

  end

  section

    variable [HasBot U]

    def coprodBotIntroFun (A : U) : A ⥤ ⊥_U ⊔ A := rightIntroFun ⊥_U A
    def coprodBotElimFun (A : U) : ⊥_U ⊔ A ⥤ A := elimFun (HasBot.elimFun A) (idFun A)

  end

end HasCoproducts

open HasCoproducts



namespace HasClassicalLogic

  variable {U : Universe} [HasLinearLogic U] [HasNonLinearLogic U]
           [HasBot U] [HasClassicalLogic U] [HasCoproducts U]

  def excludedMiddle  (A : U) : A ⊔ ~A := byContradiction (Λ F => rightCoIntro F (leftCoIntroFun F))
  def excludedMiddle' (A : U) : ~A ⊔ A := byContradiction (Λ F => leftCoIntro F (rightCoIntroFun F))

end HasClassicalLogic



namespace Prerelation

  @[reducible] def coproduct {α : Sort u} {V : Universe} [HasLinearLogic V] [HasCoproducts V]
                             (R S : Prerelation α V) :
      Prerelation α V :=
    λ a b => R a b ⊔ S a b

  namespace coproduct

    variable {α : Sort u} {V : Universe} [HasLinearLogic V] [HasCoproducts V]
             (R S : Prerelation α V)

    instance isFull_left [hR : IsFull R] : IsFull (coproduct R S) :=
      ⟨λ a b => leftIntro (hR.inst a b) (S a b)⟩
    instance isFull_right [hS : IsFull S] : IsFull (coproduct R S) :=
      ⟨λ a b => rightIntro (R a b) (hS.inst a b)⟩

    instance hasRefl_left [hR : HasRefl R] : HasRefl (coproduct R S) :=
      ⟨λ a => leftIntro (hR.refl a) (S a a)⟩
    instance hasRefl_right [hS : HasRefl S] : HasRefl (coproduct R S) :=
      ⟨λ a => rightIntro (R a a) (hS.refl a)⟩
    instance hasSymm [hR : HasSymm R] [hS : HasSymm S] : HasSymm (coproduct R S) :=
      ⟨λ a b => elimFun (Λ el => leftIntro el⁻¹ (S b a)) (Λ er => rightIntro (R b a) er⁻¹)⟩

  end coproduct

end Prerelation



namespace HasCoproducts

  def coprodRel (U : Universe) [HasLinearLogic U] [HasCoproducts U] : Prerelation U U :=
    λ A B => A ⊔ B

  variable (U : Universe) [HasLinearLogic U] [HasCoproducts U]

  instance hasCoproductObjects : HasCoproductObjects U where
    prod                      := coprodRel U
    fstHom        (A B   : U) := leftIntroFun A B
    sndHom        (A B   : U) := rightIntroFun A B
    prodIntroFun₂ (A B C : U) := elimFun₃ B C A

end HasCoproducts
