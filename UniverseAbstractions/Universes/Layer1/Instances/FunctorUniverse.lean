import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Axioms.Singletons
import UniverseAbstractions.Universes.Layer1.Axioms.Products
import UniverseAbstractions.Universes.Layer1.Axioms.Coproducts
import UniverseAbstractions.Universes.Layer1.Axioms.Equivalences
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedFunctors
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedSingletonFunctors
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedProductFunctors
import UniverseAbstractions.Universes.Layer1.Meta.Tactics.Functoriality



namespace UniverseAbstractions.Layer1

set_option autoBoundImplicitLocal false

universe u uu v vv w

open HasFunctors HasIdFun HasConstFun HasSubstFun HasLinearLogic HasSubLinearLogic HasNonLinearLogic
     Prerelation



def functorUniverse {U : Universe.{u, uu}} (A : U) (V : Universe.{v, vv}) [HasFunctors U V] :
    Universe.{v, vv} where
  I := V
  h := ⟨λ B => A ⟶ B⟩

namespace functorUniverse

  notation:20 "{" A:0 " ⟶} " V:21 => functorUniverse A V

  variable {U V : Universe} [HasFunctors U V] (A : U)

  def type (B : V) : {A ⟶} V := B
  infixr:20 " !⟶ " => functorUniverse.type

  def embedInst [HasConstFun U V] {B : V} (b : B) : A !⟶ B := constFun A b

  variable [hFun : HasInnerFunctors V] [HasFullInnerLogic V] [HasFullLogic U V]

  instance hasFunctors : HasInnerFunctors ({A ⟶} V) where
    Fun   := hFun.Fun
    apply := revSubstFun

  def embeddedIdFun (B : V) : A ⟶ B ⟶ B := embedInst A (idFun B)

  def embeddedRevAppFun {B : V} (F : A ⟶ B) (C : V) : A ⟶ (B ⟶ C) ⟶ C := Λ a G => G (F a)
  def embeddedRevAppFun₂ (B C : V) := embedInst A (revAppFun₂ B C)

  def embeddedCompFun {B C D : V} (F : A ⟶ B ⟶ C) (G : A ⟶ C ⟶ D) : A ⟶ B ⟶ D := Λ a b => G a (F a b)
  def embeddedRevCompFun₂ (B : V) {C D : V} (G : A ⟶ C ⟶ D) : A ⟶ (B ⟶ C) ⟶ (B ⟶ D) := Λ a F b => G a (F b)
  def embeddedRevCompFun₃ (B C D : V) := embedInst A (revCompFun₃ B C D)

  def embeddedConstFun (B : V) {C : V} (G : A ⟶ C) : A ⟶ B ⟶ C := Λ a b => G a
  def embeddedConstFun₂ (B C : V) := embedInst A (constFun₂ B C)

  def embeddedDupFun {B C : V} (F : A ⟶ B ⟶ B ⟶ C) : A ⟶ B ⟶ C := Λ a b => F a b b
  def embeddedDupFun₂ (B C : V) := embedInst A (dupFun₂ B C)

  instance hasFullLogic : HasFullInnerLogic ({A ⟶} V) where
    defIdFun       (B : V)       := ⟨embeddedIdFun A B⟩
    defRevAppFun   F C           := ⟨embeddedRevAppFun A F C⟩
    defRevAppFun₂  (B C : V)     := ⟨embeddedRevAppFun₂ A B C⟩
    defCompFun     F G           := ⟨embeddedCompFun A F G⟩
    defRevCompFun₃ (B C D : V)   := ⟨λ G => ⟨embeddedRevCompFun₂ A B G⟩,
                                     ⟨embeddedRevCompFun₃ A B C D⟩⟩
    defConstFun    (B : V) {C} G := ⟨embeddedConstFun A B G⟩
    defConstFun₂   (B C : V)     := ⟨embeddedConstFun₂ A B C⟩
    defDupFun      F             := ⟨embeddedDupFun A F⟩
    defDupFun₂     (B C : V)     := ⟨embeddedDupFun₂ A B C⟩

  def embeddedTopElimFun [HasTop V] {B : V} (F : A ⟶ B) : A ⟶ (⊤_V ⟶ B) :=
    Λ a => HasTop.elimFun (F a)

  instance hasTop [hTop : HasTop V] : HasTop ({A ⟶} V) where
    T            := hTop.Top
    t            := embedInst A ∗_V
    defElimFun F := ⟨embeddedTopElimFun A F⟩

  instance hasBot [hBot : HasBot V] : HasBot ({A ⟶} V) where
    B         := hBot.Bot
    elimFun B := embedInst A (hBot.elimFun B)

  instance hasClassicalLogic [HasBot V] [HasClassicalLogic V] : HasClassicalLogic ({A ⟶} V) where
    byContradictionFun := λ B : V => embedInst A (HasClassicalLogic.byContradictionFun B)

  section

    variable [hProd : HasInnerProducts V]

    def embeddedFst {B C : V} (F : A ⟶ B ⊓ C) : A ⟶ B := Λ a => HasProducts.fst (F a)
    def embeddedSnd {B C : V} (F : A ⟶ B ⊓ C) : A ⟶ C := Λ a => HasProducts.snd (F a)

    def embeddedIntro {B C : V} (F : A ⟶ B) (G : A ⟶ C) : A ⟶ B ⊓ C :=
      Λ a => HasProducts.intro (F a) (G a)
    def embeddedIntroFun {B : V} (F : A ⟶ B) (C : V) : A ⟶ C ⟶ B ⊓ C :=
      Λ a => HasProducts.introFun (F a) C
    def embeddedIntroFun₂ (B C : V) : A ⟶ B ⟶ C ⟶ B ⊓ C :=
      embedInst A (HasProducts.introFun₂ B C)

    def embeddedElimFun {B C D : V} (F : A ⟶ B ⟶ C ⟶ D) : A ⟶ (B ⊓ C ⟶ D) :=
      Λ a => HasProducts.elimFun (F a)
    def embeddedElimFun₂ (B C D : V) : A ⟶ (B ⟶ C ⟶ D) ⟶ (B ⊓ C ⟶ D) :=
      embedInst A (HasProducts.elimFun₂ B C D)

    instance hasProducts : HasInnerProducts ({A ⟶} V) where
      Prod                     := hProd.Prod
      fst                      := embeddedFst A
      snd                      := embeddedSnd A
      intro                    := embeddedIntro A
      defIntroFun  F C         := ⟨embeddedIntroFun A F C⟩
      defIntroFun₂ (B C : V)   := ⟨embeddedIntroFun₂ A B C⟩
      defElimFun   F           := ⟨embeddedElimFun A F⟩
      defElimFun₂  (B C D : V) := ⟨embeddedElimFun₂ A B C D⟩

  end

  instance hasCoproducts [hCoprod : HasInnerCoproducts V] : HasInnerCoproducts ({A ⟶} V) where
    Coprod              := hCoprod.Coprod
    leftIntroFun  B C   := embedInst A (hCoprod.leftIntroFun B C)
    rightIntroFun B C   := embedInst A (hCoprod.rightIntroFun B C)
    elimFun₃      B C D := embedInst A (hCoprod.elimFun₃ B C D)

  section

    variable {β : Sort w} (R : Prerelation β V)

    def embedPrerelation : Prerelation β ({A ⟶} V) := R

    instance isFull [hR : IsFull R] : IsFull (embedPrerelation A R) := ⟨λ B C => embedInst A (hR.inst B C)⟩

    instance hasRefl  [hR : HasRefl  R] : HasRefl  (embedPrerelation A R) := ⟨λ B     => embedInst A (hR.refl         B)⟩
    instance hasSymm  [hR : HasSymm  R] : HasSymm  (embedPrerelation A R) := ⟨λ B C   => embedInst A (hR.symmFun      B C)⟩
    instance hasTrans [hR : HasTrans R] : HasTrans (embedPrerelation A R) := ⟨λ B C D => embedInst A (hR.revTransFun₂ B C D)⟩

    instance isPreorder    [hR : IsPreorder    R] : IsPreorder    (embedPrerelation A R) := ⟨⟩
    instance isEquivalence [hR : IsEquivalence R] : IsEquivalence (embedPrerelation A R) := ⟨⟩

  end

  section

    variable {β : Sort w} (Hom Iso : Prerelation β V) [IsPreorder Hom] [hIso : IsIsoRel Hom Iso]

    def embeddedIsoRefl (b : β) : A ⟶ Iso b b := embedInst A (HasRefl.refl b)

    def embeddedIsoSymm {b c : β} (F : A ⟶ Iso b c) : A ⟶ Iso c b := Λ a => (F a)⁻¹
    def embeddedIsoSymmFun (b c : β) : A ⟶ Iso b c ⟶ Iso c b :=
      embedInst A (HasSymm.symmFun b c)

    def embeddedIsoTrans {b c d : β} (F : A ⟶ Iso b c) (G : A ⟶ Iso c d) : A ⟶ Iso b d :=
      Λ a => G a • F a
    def embeddedIsoRevTransFun (b : β) {c d : β} (G : A ⟶ Iso c d) : A ⟶ Iso b c ⟶ Iso b d :=
      Λ a E => G a • E
    def embeddedIsoRevTransFun₂ (b c d : β) : A ⟶ Iso c d ⟶ Iso b c ⟶ Iso b d :=
      embedInst A (HasTrans.revTransFun₂ b c d)

    def isIsoRel : IsIsoRel (embedPrerelation A Hom) (embedPrerelation A Iso) where
      to                    := ⟨λ b c => embedInst A (hIso.to.inst  b c)⟩
      inv                   := ⟨λ b c => embedInst A (hIso.inv.inst b c)⟩
      defRefl         b     := ⟨embeddedIsoRefl A Hom Iso b⟩
      defSymm         F     := ⟨embeddedIsoSymm A Hom Iso F⟩
      defSymmFun      b c   := ⟨embeddedIsoSymmFun A Hom Iso b c⟩
      defTrans        F G   := ⟨embeddedIsoTrans A Hom Iso F G⟩
      defRevTransFun₂ b c d := ⟨λ G => ⟨embeddedIsoRevTransFun A Hom Iso b G⟩,
                                        ⟨embeddedIsoRevTransFun₂ A Hom Iso b c d⟩⟩

  end

  section

    variable [hEquiv : HasEquivalences V]

    def equivIsoRel' := isIsoRel A (funRel V) (HasEquivalences.equivRel V)

    def equivIsoRel :
        IsIsoRel (funRel ({A ⟶} V)) (embedPrerelation A (HasEquivalences.equivRel V)) where
      to                          := (equivIsoRel' A).to
      inv                         := (equivIsoRel' A).inv
      defRefl         (B : V)     := ⟨((equivIsoRel' A).defRefl B).inst⟩
      defSymm                     := (equivIsoRel' A).defSymm
      defSymmFun      (B C  : V)  := ⟨((equivIsoRel' A).defSymmFun B C).F⟩
      defTrans                    := (equivIsoRel' A).defTrans
      defRevTransFun₂ (B C D : V) := ⟨λ G => ⟨(((equivIsoRel' A).defRevTransFun₂ B C D).app G).F⟩,
                                      ⟨((equivIsoRel' A).defRevTransFun₂ B C D).F⟩⟩

    instance hasEquivalences : HasEquivalences ({A ⟶} V) where
      Equiv := hEquiv.Equiv
      hIso  := equivIsoRel A

    -- TODO standard equivalences

  end

end functorUniverse
