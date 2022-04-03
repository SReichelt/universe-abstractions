import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.FunctorExtensionality
import UniverseAbstractions.Axioms.Universe.Singletons
import UniverseAbstractions.Lemmas.DerivedFunctors
import UniverseAbstractions.Lemmas.DerivedFunctorExtensionality



set_option autoBoundImplicitLocal false
--set_option pp.universes true



namespace HasInternalTop

  open HasFunctors HasCongrArg HasCongrFun HasLinearFunOp HasSubLinearFunOp HasAffineFunOp
       HasSubsingletonExt HasLinearFunExt HasAffineFunExt HasTop HasTopEq HasTopExt

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasInternalTop U]

  section

    variable [HasConstFun U U]

    def defIntroFun (A : U) : A ⟶{λ _ => top U} Top U :=
    HasConstFun.defConstFun A (top U)

    @[reducible] def introFun (A : U) : A ⟶ Top U := defIntroFun A

    def HasTopExt.introFunEq [HasSubsingletonExt U U] [HasTopEq U]
                            {A : U} (F : A ⟶ Top U) :
      F ≃{λ a => topEq (F a) ◅} introFun A :=
    eqExt F (introFun A)

    def HasTopExt.elimFunConstEq [HasTopExt U] {A : U} (a : A) :
      elimFun a ≃ HasConstFun.constFun (Top U) a :=
    (elimFunEq byDef)⁻¹

  end

  section

    variable [HasLinearFunOp U] [HasTopExt U]

    def defElimFun₂ (A : U) :
      A ⟶ Top U ⟶{λ a _ => a} A :=
    ⟨λ a => defElimFun a,
     swapFunFun (elimFun (idFun A))
     ◄ elimFunEq (F := swapFun (elimFun (idFun A)) _) (byDef₂ • byDef)⟩

    @[reducible] def elimFunFun (A : U) :
      A ⟶ Top U ⟶ A :=
    defElimFun₂ A

    instance elimFun.isFunApp {A : U} {a : A} :
      IsFunApp A (elimFun a) :=
    { F := elimFunFun A,
      a := a,
      e := byDef }

  end

  def HasTopExt.elimFunEqExt [HasLinearFunOp U] [HasLinearFunExt U] [HasTopExt U] {A : U}
                             {F : A ⟶ Top U ⟶ A} (h : swapFun F (top U) ≃ idFun A) :
    F ≃ elimFunFun A :=
  (reverseSwap (elimFunEq (h • byDef)))⁻¹

  def HasTopExt.elimFunFunConstEq [HasAffineFunOp U] [HasAffineFunExt U] [HasTopExt U] (A : U) :
    elimFunFun A ≃ constFunFun (Top U) A :=
  (elimFunEqExt (swapConstFun (top U) A))⁻¹

  section

    variable [HasLinearFunOp U]

    def defInvElimFun (A : U) : (Top U ⟶ A) ⟶{λ F => F (top U)} A :=
    HasRevAppFun.defRevAppFun (top U) A

    @[reducible] def invElimFun (A : U) : (Top U ⟶ A) ⟶ A := defInvElimFun A

  end

end HasInternalTop



namespace HasInternalBot

  open HasLinearFunOp HasBot

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasInternalBot U]

  section

    variable [HasLinearFunOp U]

    def contraIntroFun (A : U) : A ⟶ Not A ⟶ Bot U :=
    revAppFunFun A (Bot U)

    def notNotFun (A : U) : A ⟶ Not (Not A) := contraIntroFun A

    def notTopIntroFun [HasInternalTop U] : Not (HasTop.Top U) ⟶ Bot U :=
    HasInternalTop.invElimFun (Bot U)

  end

end HasInternalBot
