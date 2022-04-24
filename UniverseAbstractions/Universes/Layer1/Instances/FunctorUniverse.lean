import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedFunctors
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

  def functorInst {B C : U} (F : A ⟶ B ⟶ C) : (A !⟶ B) ⟶ (A !⟶ C) := F
  def embedFunctor {B C : U} (G : B ⟶ C) : (A !⟶ B) ⟶ (A !⟶ C) := embedInst A G

  def embeddedIdFun (B : U) : A ⟶ B ⟶ B := embedFunctor A (idFun B)

  def embeddedAppFun {B : U} (F : A ⟶ B) (C : U) : A ⟶ (B ⟶ C) ⟶ C := Λ a G => G (F a)
  def embeddedAppFun₂ (B C : U) := embedFunctor A (revAppFun₂ B C)

  def embeddedCompFun {B C D : U} (F : A ⟶ B ⟶ C) (G : A ⟶ C ⟶ D) : A ⟶ B ⟶ D := Λ a b => G a (F a b)
  def embeddedCompFun₂ {B C : U} (F : A ⟶ B ⟶ C) (D : U) : A ⟶ (C ⟶ D) ⟶ (B ⟶ D) := Λ a G b => G (F a b)
  def embeddedCompFun₃ (B C D : U) := embedFunctor A (compFun₃ B C D)

  def embeddedConstFun (B : U) {C : U} (G : A ⟶ C) : A ⟶ B ⟶ C := Λ a b => G a
  def embeddedConstFun₂ (B C : U) := embedFunctor A (constFun₂ B C)

  def embeddedDupFun {B C : U} (F : A ⟶ B ⟶ B ⟶ C) : A ⟶ B ⟶ C := Λ a b => F a b b
  def embeddedDupFun₂ (B C : U) := embedFunctor A (dupFun₂ B C)

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

end functorUniverse
