import UniverseAbstractions.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedFunctors

import UniverseAbstractions.MathlibFragments.Init.CoreExt



namespace UniverseAbstractions.Layer1

set_option autoBoundImplicitLocal false

universe u uu

open HasLinearLogic HasSubLinearLogic HasNonLinearLogic



def functorUniverse {U : Universe.{u, uu}} [HasFunctors U] [HasFullLogic U] (A : U) :
  Universe.{u, uu} :=
{ a    := U,
  inst := ⟨λ B => A ⟶ B⟩ }

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
  def embedFunctor {B C : U} (F : B ⟶ C) : (A !⟶ B) ⟶ (A !⟶ C) := embedInst A F

  instance hasFullLogic : HasFullLogic ({A ⟶} U) :=
  { idFun      := λ B     : U => embedFunctor A (idFun      B),
    revAppFun₂ := λ B C   : U => embedFunctor A (revAppFun₂ B C),
    compFun₃   := λ B C D : U => embedFunctor A (compFun₃   B C D),
    constFun₂  := λ B C   : U => embedFunctor A (constFun₂  B C),
    dupFun₂    := λ B C   : U => embedFunctor A (dupFun₂    B C) }

end functorUniverse
