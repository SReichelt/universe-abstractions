import UniverseAbstractions.Universes.Layer2.Axioms.Universes
import UniverseAbstractions.Universes.Layer2.Axioms.Functors



namespace UniverseAbstractions.Layer2

set_option autoImplicit false

universe u

open Universe Layer1.HasFunctors Layer1.HasPiAppFun HasPiTypeBase HasFunctors HasExternalLinearLogic



namespace HasExternalLinearLogic

  section

    variable (α β : Sort u) {U : Universe.{u}} [HasLinearLogic U]
             [Layer1.HasEquivalenceRelationBase U.V α] [Layer1.HasEquivalenceRelationBase U.V β]
             [HasExternalLinearLogic α U] [HasExternalLinearLogic β U] (C : U)

    instance hasSwapPi : HasSwapPi (Function.const α (Function.const β C)) :=
      ⟨λ F b => DefPi.mk (Layer1.HasExternalLinearLogic.defSwapFun F b)
                         (λ _ => revAppFun.byDef β • compFun.byDef α)⟩

  end

  section

    variable {α β : Sort u} {U : Universe.{u}} [HasLinearLogic U]
             [Layer1.HasEquivalenceRelationBase U.V α] [Layer1.HasEquivalenceRelationBase U.V β]
             [HasExternalLinearLogic α U] [HasExternalLinearLogic β U] {C : U}

    instance swapFun.hasDefInstEq (F : α ⥤ β ⥤ C) (b : β) :
        DefType.HasDefInstEq (Layer1.HasSwapPi.defSwapFun F b) :=
      HasSwapPi.hasDefInstEq (P := Function.const α (Function.const β C)) F b

    def swapFun.byDef {F : α ⥤ β ⥤ C} {b : β} {a : α} : (Layer1.HasSwapPi.swapFun F b) a ≃ F a b :=
      HasFunctors.byDef

  end

  section

    variable {α : Sort u} {U : Universe.{u}} [hUU : HasUnivFunctors U U]
             [Layer1.HasEquivalenceRelationBase U.V α] [h : HasExternalLinearLogic α U] {B C : U}

    instance (F : α ⥤ B) :
        Layer1.HasPiType (λ G => Function.const (B ⥤ C) (Function.const (α ⥤ B) (α ⥤ C)) G F) :=
      (HasFunctors.toHasPiTypeBase (B ⥤ C) (α ⥤ C)).toLayer1

    instance compFun₂.hasDefInstEq (F : α ⥤ B) :
        DefType.HasDefInstEq (Layer1.HasRevCompFunPiFun.defCompFun₂ F C) :=
      ⟨_⟩

  end
#exit
  section

    variable (α β : Sort u) {U : Universe.{u}} [HasLinearLogic U]
             [Layer1.HasEquivalenceRelationBase U.V α] [Layer1.HasEquivalenceRelationBase U.V β]
             [HasExternalLinearLogic α U] [HasExternalLinearLogic β U] (C : U)

    instance hasSwapPi₂ : HasSwapPi₂ (Function.const α (Function.const β C)) :=
      ⟨λ F => DefPi.mk (Layer1.HasExternalLinearLogic.defSwapFun₂ F)
                       (λ _ => compFun₂.byDef _ • congrArg (Layer1.HasRevCompFunPiFun.compFun₂ F C) (revAppFun₂.byDef β) • compFun.byDef β)⟩

  end

#exit
namespace HasLinearLogic

  variable {U : Universe} [HasFunctors U] [HasLinearLogic U]

  instance defSwapFun₃.defEq (A B C : U) : DefFun₃.DefEq (defSwapFun₃ A B C) :=
  ⟨λ F => ⟨λ b => ⟨λ a => DefFun.byDef • compFun.byDef⟩,
           ⟨λ b => DefFun.byDef • congrArg _ DefFun.byDef • compFun.byDef⟩⟩,
   ⟨λ F => DefFun.byDef • congrArg _ DefFun.byDef • compFun.byDef⟩⟩

  def defSwapFun₃ (A B C : U) :
    (A ⥤ B ⥤ C) ⥤ B ⥤ A ⥤{λ F b a => F a b,
                          ⟨λ F => ⟨λ b => ⟨λ a₁ a₂ => Λ e => congrFun (congrArg F e) b⟩,
                                   λ a => ⟨λ b₁ b₂ => Λ e => congrArg (F a) e⟩⟩,
                           λ b a => ⟨λ F₁ F₂ => Λ e => congrFun₂ e a b⟩⟩} C :=
  ⟨Layer1.HasLinearLogic.defSwapFun₃ A B C, defSwapFun₃.defEq A B C⟩

  instance defSwapDefFun₂.defEq {A B C : U} {f : A → B → C} (F : A ⥤ B ⥤{f} C) [DefFun₂.DefEq F] :
    DefFun₂.DefEq (defSwapDefFun₂ F) :=
  ⟨λ b => ⟨λ a => DefFun₂.byDef • (((defSwapFun₃.defEq A B C).app F.F).app b).e a⟩,
   ⟨((defSwapFun₃.defEq A B C).app F.F).toDefFun.e⟩⟩

  def defSwapDefFun₂ {A B C : U} {f : A → B → C} (F : A ⥤ B ⥤{f} C) [DefFun₂.DefEq F] :
    B ⥤ A ⥤{λ b a => f a b,
            ⟨λ b => ⟨λ a₁ a₂ => Λ e => DefFun₂.byDef • congrFun (congrArg F.F e) b • DefFun₂.byDef⁻¹⟩,
             λ a => ⟨λ b₁ b₂ => Λ e => DefFun₂.byDef • congrArg (F.F a) e • DefFun₂.byDef⁻¹⟩⟩} C :=
  ⟨Layer1.HasLinearLogic.defSwapDefFun₂ F, defSwapDefFun₂.defEq F⟩

  instance defSwapDefFun₃.defEq {A B C D : U} {f : A → B → C → D} (F : A ⥤ B ⥤ C ⥤{f} D)
                                [hF : DefFun₃.DefEq F] :
    DefFun₃.DefEq (defSwapDefFun₃ F) :=
  ⟨λ b => ⟨λ a => (hF.app a).app b,
           ⟨λ a => DefFun.byDef •
                   congrFun DefFun.byDef b •
                   (((defSwapFun₃.defEq A B (C ⥤ D)).app F.F).app b).e a⟩⟩,
   ⟨λ b => ((defSwapFun₃.defEq A B (C ⥤ D)).app F.F).toDefFun.e b⟩⟩

  def defSwapDefFun₃ {A B C D : U} {f : A → B → C → D} (F : A ⥤ B ⥤ C ⥤{f} D)
                     [hF : DefFun₃.DefEq F] :
    B ⥤ A ⥤ C ⥤{λ b a c => f a b c,
                ⟨λ b => ⟨λ a => ⟨λ c₁ c₂ => Λ e => DefFun.byDef •
                                                   congrArg ((F.app a).app b).F e •
                                                   DefFun.byDef⁻¹⟩,
                         λ c => ⟨λ a₁ a₂ => Λ e => DefFun₃.byDef •
                                                   congrFun₂ (congrArg F.F e) b c •
                                                   DefFun₃.byDef⁻¹⟩⟩,
                 λ a c => ⟨λ b₁ b₂ => Λ e => DefFun₃.byDef •
                                             congrFun (congrArg (F.F a) e) c •
                                             DefFun₃.byDef⁻¹⟩⟩} D :=
  ⟨Layer1.HasLinearLogic.defSwapDefFun₃ F, defSwapDefFun₃.defEq F⟩

  instance defRevSwapFun₃.defEq (A B C : U) : DefFun₃.DefEq (defRevSwapFun₃ A B C) :=
  defSwapDefFun₃.defEq (Layer1.HasLinearLogic.defSwapFun₃ A B C)

  @[reducible] def defRevSwapFun₃ (A B C : U) :
    B ⥤ (A ⥤ B ⥤ C) ⥤ A ⥤{λ b F a => F a b,
                         ⟨λ b => ⟨λ F => ⟨λ a₁ a₂ => Λ e => congrFun (congrArg F e) b⟩,
                                  λ a => ⟨λ F₁ F₂ => Λ e => congrFun₂ e a b⟩⟩,
                          λ F a => ⟨λ b₁ b₂ => Λ e => congrArg (F a) e⟩⟩} C :=
  ⟨Layer1.HasLinearLogic.defRevSwapFun₃ A B C, defRevSwapFun₃.defEq A B C⟩

  instance defRevCompFun₃.defEq (A B C : U) : DefFun₃.DefEq (defRevCompFun₃ A B C) :=
  defSwapDefFun₃.defEq (Layer1.HasLinearLogic.defCompFun₃ A B C)

  @[reducible] def defRevCompFun₃ (A B C : U) :
    (B ⥤ C) ⥤ (A ⥤ B) ⥤ A ⥤{λ G F a => G (F a),
                            ⟨λ G => ⟨λ F => ⟨λ a₁ a₂ => congrArgFun G (F a₁) (F a₂) ⊙
                                                        congrArgFun F a₁ a₂⟩,
                                     λ a => ⟨λ F₁ F₂ => congrArgFun G (F₁ a) (F₂ a) ⊙
                                                        congrFunFun F₁ F₂ a⟩⟩,
                             λ F a => ⟨λ G₁ G₂ => congrFunFun G₁ G₂ (F a)⟩⟩} C :=
  ⟨Layer1.HasLinearLogic.defRevCompFun₃ A B C, defRevCompFun₃.defEq A B C⟩

end HasLinearLogic



namespace HasNonLinearLogic

  open HasLinearLogic

  variable {U : Universe} [HasFunctors U] [HasLinearLogic U] [HasNonLinearLogic U]

  def dupFun.byDef {A B : U} {F : A ⥤ A ⥤ B} {a : A} : (dupFun F) a ≃ F a a :=
  DefFun.byDef

  instance defRevSelfAppFun₂.defEq (A B : U) : DefFun₂.DefEq (defRevSelfAppFun₂ A B) :=
  ⟨λ F => ⟨λ G => DefFun₂.byDef • dupFun.byDef⟩,
   ⟨λ F => DefFun.byDef • congrArg _ DefFun.byDef • compFun.byDef⟩⟩

  def defRevSelfAppFun₂ (A B : U) :
    ((A ⥤ B) ⥤ A) ⥤ (A ⥤ B) ⥤{λ F G => G (F G),
                              ⟨λ F => ⟨λ G₁ G₂ => Λ e => congr e (congrArg F e)⟩,
                               λ G => ⟨λ F₁ F₂ => Λ e => congrArg G (congrFun e G)⟩⟩} B :=
  ⟨Layer1.HasNonLinearLogic.defRevSelfAppFun₂ A B, defRevSelfAppFun₂.defEq A B⟩

  instance defSubstFun₃.defEq (A B C : U) : DefFun₃.DefEq (defSubstFun₃ A B C) :=
  ⟨λ F => ⟨λ G => ⟨λ a => DefFun₂.byDef • congrFun compFun.byDef a • dupFun.byDef⟩,
           ⟨λ G => DefFun.byDef • congrArg _ DefFun.byDef • compFun.byDef⟩⟩,
   ⟨λ F => DefFun.byDef •
           congrArg _ (DefFun.byDef • congrArg _ DefFun.byDef • compFun.byDef) •
           compFun.byDef⟩⟩

  def defSubstFun₃ (A B C : U) :
    (A ⥤ B) ⥤ (A ⥤ B ⥤ C) ⥤ A ⥤{λ F G a => G a (F a),
                                ⟨λ F => ⟨λ G => ⟨λ a₁ a₂ => Λ e => congr (congrArg G e)
                                                                         (congrArg F e)⟩,
                                         λ a => ⟨λ G₁ G₂ => Λ e => congrFun (congrFun e a) (F a)⟩⟩,
                                 λ G a => ⟨λ F₁ F₂ => Λ e => congrArg (G a) (congrFun e a)⟩⟩} C :=
  ⟨Layer1.HasNonLinearLogic.defSubstFun₃ A B C, defSubstFun₃.defEq A B C⟩

  instance defRevSubstFun₃.defEq (A B C : U) : DefFun₃.DefEq (defRevSubstFun₃ A B C) :=
  defSwapDefFun₃.defEq (Layer1.HasNonLinearLogic.defSubstFun₃ A B C)

  def defRevSubstFun₃ (A B C : U) :
    (A ⥤ B ⥤ C) ⥤ (A ⥤ B) ⥤ A ⥤{λ G F a => G a (F a),
                                ⟨λ G => ⟨λ F => ⟨λ a₁ a₂ => Λ e => congr (congrArg G e)
                                                                         (congrArg F e)⟩,
                                         λ a => ⟨λ F₁ F₂ => Λ e => congrArg (G a) (congrFun e a)⟩⟩,
                                 λ F a => ⟨λ G₁ G₂ => Λ e => congrFun (congrFun e a) (F a)⟩⟩} C :=
  ⟨Layer1.HasNonLinearLogic.defRevSubstFun₃ A B C, defRevSubstFun₃.defEq A B C⟩

end HasNonLinearLogic
