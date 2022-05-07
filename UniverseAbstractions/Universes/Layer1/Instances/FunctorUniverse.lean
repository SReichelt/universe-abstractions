import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Axioms.Singletons
import UniverseAbstractions.Universes.Layer1.Axioms.Products
import UniverseAbstractions.Universes.Layer1.Axioms.Coproducts
import UniverseAbstractions.Universes.Layer1.Axioms.Equivalences

import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedFunctors
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedSingletonFunctors

import UniverseAbstractions.Universes.Layer1.Meta.Tactics.Functoriality



namespace UniverseAbstractions.Layer1

set_option autoBoundImplicitLocal false

universe u uu

open HasLinearLogic HasSubLinearLogic HasNonLinearLogic



def functorUniverse {U : Universe.{u, uu}} [HasFunctors U] [HasFullLogic U] (A : U) :
  Universe.{u, uu} :=
{ I := U,
  h := ⟨λ B => A ⟶ B⟩ }

namespace functorUniverse

  notation:20 "{" A:0 " ⟶} " U':21 => functorUniverse (U := U') A

  variable {U : Universe} [hFun : HasFunctors U] [HasFullLogic U] (A : U)

  def type (B : U) : {A ⟶} U := B
  infixr:20 " !⟶ " => functorUniverse.type

  def idInst : A !⟶ A := idFun A
  def embedInst {B : U} (b : B) : A !⟶ B := constFun A b

  instance hasFunctors : HasFunctors ({A ⟶} U) :=
  { Fun   := hFun.Fun,
    apply := revSubstFun }

  def embeddedIdFun (B : U) : A ⟶ B ⟶ B := embedInst A (idFun B)

  def embeddedAppFun {B : U} (F : A ⟶ B) (C : U) : A ⟶ (B ⟶ C) ⟶ C := Λ a G => G (F a)
  def embeddedAppFun₂ (B C : U) := embedInst A (revAppFun₂ B C)

  def embeddedCompFun {B C D : U} (F : A ⟶ B ⟶ C) (G : A ⟶ C ⟶ D) : A ⟶ B ⟶ D := Λ a b => G a (F a b)
  def embeddedCompFun₂ {B C : U} (F : A ⟶ B ⟶ C) (D : U) : A ⟶ (C ⟶ D) ⟶ (B ⟶ D) := Λ a G b => G (F a b)
  def embeddedCompFun₃ (B C D : U) := embedInst A (compFun₃ B C D)

  def embeddedConstFun (B : U) {C : U} (G : A ⟶ C) : A ⟶ B ⟶ C := Λ a b => G a
  def embeddedConstFun₂ (B C : U) := embedInst A (constFun₂ B C)

  def embeddedDupFun {B C : U} (F : A ⟶ B ⟶ B ⟶ C) : A ⟶ B ⟶ C := Λ a b => F a b b
  def embeddedDupFun₂ (B C : U) := embedInst A (dupFun₂ B C)

  instance hasFullLogic : HasFullLogic ({A ⟶} U) :=
  { defIdFun      := λ B     => ⟨embeddedIdFun A B⟩,
    defRevAppFun₂ := λ B C   => ⟨λ F => ⟨embeddedAppFun A F C⟩,
                                 ⟨embeddedAppFun₂ A B C⟩⟩,
    defCompFun₃   := λ B C D => ⟨λ F => ⟨λ G => ⟨embeddedCompFun A F G⟩,
                                         ⟨embeddedCompFun₂ A F D⟩⟩,
                                 ⟨embeddedCompFun₃ A B C D⟩⟩,
    defConstFun₂  := λ B C   => ⟨λ G => ⟨embeddedConstFun A B G⟩,
                                 ⟨embeddedConstFun₂ A B C⟩⟩,
    defDupFun₂    := λ B C   => ⟨λ F => ⟨embeddedDupFun A F⟩,
                                 ⟨embeddedDupFun₂ A B C⟩⟩ }

  def embeddedTopElimFun [HasTop U] {B : U} (F : A ⟶ B) : A ⟶ (⊤_U ⟶ B) :=
  Λ a => HasTop.elimFun (F a)

  instance hasTop [hTop : HasTop U] : HasTop ({A ⟶} U) :=
  { T          := hTop.Top,
    t          := embedInst A ∗_U,
    defElimFun := λ F => ⟨embeddedTopElimFun A F⟩ }

  instance hasBot [hBot : HasBot U] : HasBot ({A ⟶} U) :=
  { B       := hBot.Bot,
    elimFun := λ B => embedInst A (hBot.elimFun B) }

  instance hasClassicalLogic [HasBot U] [HasClassicalLogic U] : HasClassicalLogic ({A ⟶} U) :=
  { byContradictionFun := λ B : U => embedInst A (HasClassicalLogic.byContradictionFun B) }

  instance hasProducts [hProd : HasProducts U] : HasProducts ({A ⟶} U) :=
  { Prod      := hProd.Prod,
    introFun₂ := λ B C   => embedInst A (hProd.introFun₂ B C),
    elimFun₂  := λ B C D => embedInst A (hProd.elimFun₂ B C D) }

  instance hasCoproducts [hCoprod : HasCoproducts U] : HasCoproducts ({A ⟶} U) :=
  { Coprod        := hCoprod.Coprod,
    leftIntroFun  := λ B C   => embedInst A (hCoprod.leftIntroFun B C),
    rightIntroFun := λ B C   => embedInst A (hCoprod.rightIntroFun B C),
    elimFun₃      := λ B C D => embedInst A (hCoprod.elimFun₃ B C D) }

  instance hasEquivalences [hEquiv : HasEquivalences U] : HasEquivalences ({A ⟶} U) :=
  { Equiv   := hEquiv.Equiv,
    toFun₂  := λ B C => embedInst A (hEquiv.toFun₂  B C),
    invFun₂ := λ B C => embedInst A (hEquiv.invFun₂ B C) }

  section

    variable [hEquivOp : HasEquivOp U]

    def embeddedEquivRefl (B : U) : A ⟶ (B ⟷ B) := embedInst A (HasEquivOp.refl B)

    def embeddedEquivSymm {B C : U} (F : A ⟶ (B ⟷ C)) : A ⟶ (C ⟷ B) := Λ a => HasEquivOp.symm (F a)
    def embeddedEquivSymmFun (B C : U) : A ⟶ (B ⟷ C) ⟶ (C ⟷ B) :=
    embedInst A (HasEquivOp.symmFun B C)

    def embeddedEquivTrans {B C D : U} (F : A ⟶ (B ⟷ C)) (G : A ⟶ (C ⟷ D)) : A ⟶ (B ⟷ D) :=
    Λ a => HasEquivOp.trans (F a) (G a)
    def embeddedEquivTransFun {B C : U} (F : A ⟶ (B ⟷ C)) (D : U) : A ⟶ (C ⟷ D) ⟶ (B ⟷ D) :=
    Λ a => HasEquivOp.transFun (F a) D
    def embeddedEquivTransFun₂ (B C D : U) : A ⟶ (B ⟷ C) ⟶ (C ⟷ D) ⟶ (B ⟷ D) :=
    embedInst A (HasEquivOp.transFun₂ B C D)

    instance hasEquivOp : HasEquivOp ({A ⟶} U) :=
    { defRefl      := λ B     => ⟨embeddedEquivRefl A B⟩,
      defSymm      := λ F     => ⟨embeddedEquivSymm A F⟩,
      defSymmFun   := λ B C   => ⟨embeddedEquivSymmFun A B C⟩,
      defTrans     := λ F G   => ⟨embeddedEquivTrans A F G⟩,
      defTransFun₂ := λ B C D => ⟨λ F => ⟨embeddedEquivTransFun A F D⟩,
                                  ⟨embeddedEquivTransFun₂ A B C D⟩⟩ }

    -- TODO standard equivalences

  end

end functorUniverse
