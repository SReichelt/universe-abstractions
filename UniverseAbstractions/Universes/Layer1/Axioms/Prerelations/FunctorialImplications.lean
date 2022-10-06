import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations.AttachedRelations



namespace UniverseAbstractions.Layer1

set_option autoImplicit false
set_option linter.unusedVariables false

open HasPiType HasFunctors HasPreorderRelation

universe u v v' v''



namespace HasPreorderRelation

  variable {V : Universe} [HasLinearLogic V]


  section

    variable {α : Sort u} {β : Sort v} {γ : Sort v'} [HasPreorderRelation V α]
             [HasPreorderRelation V β] [HasPreorderRelation V γ]

    class HasFunctorialImplication (F : PreorderFunctor α β) (G : PreorderFunctor α γ) extends
      HasExternalPiType₂ (λ a b => (F a ⟶ F b) ⥤ (G a ⟶ G b))

    namespace HasFunctorialImplication

      variable (F : PreorderFunctor α β) (G : PreorderFunctor α γ)
               [h : HasFunctorialImplication F G]

      instance (a : α) : HasExternalPiType (λ b => (F a ⟶ F b) ⥤ (G a ⟶ G b)) :=
        h.hasAppPiType a

      @[reducible] def FunImp : V := Pi₂ (λ a b => (F a ⟶ F b) ⥤ (G a ⟶ G b))

      @[reducible] def DefFunImp (h : ∀ a b, (F a ⟶ F b) ⥤ (G a ⟶ G b)) :=
        DefPi₂ (λ a b => (F a ⟶ F b) ⥤ (G a ⟶ G b)) h

    end HasFunctorialImplication

  end

  open HasFunctorialImplication


  class HasTrivFunImp {α : Sort u} {β : Sort v} [HasPreorderRelation V α] [HasPreorderRelation V β]
                      (F : PreorderFunctor α β)
                      [HasFunctorialImplication (PreorderFunctor.idFun α) F] where
    defTrivFunImp : DefFunImp (PreorderFunctor.idFun α) F F.hφ.inst

  namespace HasTrivFunImp

    variable {α : Sort u} {β : Sort v} [HasPreorderRelation V α] [HasPreorderRelation V β]
             (F : PreorderFunctor α β) [HasFunctorialImplication (PreorderFunctor.idFun α) F]
             [h : HasTrivFunImp F]

    @[reducible] def trivFunImp : FunImp (PreorderFunctor.idFun α) F := h.defTrivFunImp

  end HasTrivFunImp


  class HasRightCompFunImp {α : Sort u} {β : Sort v} {γ : Sort v'} [HasPreorderRelation V α]
                           [HasPreorderRelation V β] [HasPreorderRelation V γ]
                           (F : PreorderFunctor α β) (G : PreorderFunctor β γ)
                           [HasFunctorialImplication F (PreorderFunctor.compFun F G)] where
    defRightCompFunImp : DefFunImp F (PreorderFunctor.compFun F G) (λ a b => G.hφ.inst (F a) (F b))

  namespace HasRightCompFunImp

    variable {α : Sort u} {β : Sort v} {γ : Sort v'} [HasPreorderRelation V α]
             [HasPreorderRelation V β] [HasPreorderRelation V γ] (F : PreorderFunctor α β)
             (G : PreorderFunctor β γ) [HasFunctorialImplication F (PreorderFunctor.compFun F G)]
             [h : HasRightCompFunImp F G]

    @[reducible] def rightCompFunImp : FunImp F (PreorderFunctor.compFun F G) :=
      h.defRightCompFunImp

  end HasRightCompFunImp


  class HasLeftCompFunImp {α : Sort u} {β : Sort v} {γ : Sort v'} {δ : Sort v''}
                          [HasPreorderRelation V α] [HasPreorderRelation V β]
                          [HasPreorderRelation V γ] [HasPreorderRelation V δ]
                          (F : PreorderFunctor α β) (G : PreorderFunctor β γ)
                          (H : PreorderFunctor α δ)
                          [HasFunctorialImplication (PreorderFunctor.compFun F G) H]
                          [HasFunctorialImplication F H] where
    defLeftCompFunImp (i : FunImp (PreorderFunctor.compFun F G) H) :
      DefFunImp F H (λ a b => i a b ⊙ G.hφ.inst (F a) (F b))
    defLeftCompFunImpFun :
      FunImp (PreorderFunctor.compFun F G) H ⥤{λ i => (defLeftCompFunImp i).inst} FunImp F H

  namespace HasLeftCompFunImp

    variable {α : Sort u} {β : Sort v} {γ : Sort v'} {δ : Sort v''} [HasPreorderRelation V α]
             [HasPreorderRelation V β] [HasPreorderRelation V γ] [HasPreorderRelation V δ]

    @[reducible] def leftCompFunImp {F : PreorderFunctor α β} {G : PreorderFunctor β γ}
                                    {H : PreorderFunctor α δ}
                                    [HasFunctorialImplication (PreorderFunctor.compFun F G) H]
                                    [HasFunctorialImplication F H] [h : HasLeftCompFunImp F G H]
                                    (i : FunImp (PreorderFunctor.compFun F G) H) :
        FunImp F H :=
      h.defLeftCompFunImp i

    @[reducible] def leftCompFunImpFun (F : PreorderFunctor α β) (G : PreorderFunctor β γ)
                                       (H : PreorderFunctor α δ)
                                       [HasFunctorialImplication (PreorderFunctor.compFun F G) H]
                                       [HasFunctorialImplication F H] [h : HasLeftCompFunImp F G H] :
        FunImp (PreorderFunctor.compFun F G) H ⥤ FunImp F H :=
      h.defLeftCompFunImpFun

    instance leftCompFunImp.isFunApp {F : PreorderFunctor α β} {G : PreorderFunctor β γ}
                                     {H : PreorderFunctor α δ}
                                     [HasFunctorialImplication (PreorderFunctor.compFun F G) H]
                                     [HasFunctorialImplication F H] [h : HasLeftCompFunImp F G H]
                                     {i : FunImp (PreorderFunctor.compFun F G) H} :
        IsFunApp (leftCompFunImp i) :=
      ⟨leftCompFunImpFun F G H, i⟩

  end HasLeftCompFunImp


  -- TODO: non-linear and sub-linear implications


  class HasIdFunImp {α : Sort u} {β : Sort v} [HasPreorderRelation V α] [HasPreorderRelation V β]
                    (F : PreorderFunctor α β) [HasFunctorialImplication F F] where
    defIdFunImp : DefFunImp F F (λ a b => HasIdFun.idFun (F a ⟶ F b))

  namespace HasIdFunImp

    variable {α : Sort u} {β : Sort v} [HasPreorderRelation V α] [HasPreorderRelation V β]
             (F : PreorderFunctor α β) [HasFunctorialImplication F F] [h : HasIdFunImp F]

    @[reducible] def idFunImp : FunImp F F := h.defIdFunImp

  end HasIdFunImp


  class HasCompFunImp {α : Sort u} {β : Sort v} {γ : Sort v'} {δ : Sort v''}
                      [HasPreorderRelation V α] [HasPreorderRelation V β] [HasPreorderRelation V γ]
                      [HasPreorderRelation V δ] (F : PreorderFunctor α β) (G : PreorderFunctor α γ)
                      (H : PreorderFunctor α δ) [HasFunctorialImplication F G]
                      [HasFunctorialImplication G H] [HasFunctorialImplication F H] where
    defCompFunImp (i : FunImp F G) (j : FunImp G H) : DefFunImp F H (λ a b => j a b ⊙ i a b)
    defRevCompFunImpFun₂ : FunImp G H ⥤ FunImp F G ⥤{λ j i => (defCompFunImp i j).inst} FunImp F H

  namespace HasCompFunImp

    variable {α : Sort u} {β : Sort v} {γ : Sort v'} {δ : Sort v''} [HasPreorderRelation V α]
             [HasPreorderRelation V β] [HasPreorderRelation V γ] [HasPreorderRelation V δ]

    @[reducible] def compFunImp {F : PreorderFunctor α β} {G : PreorderFunctor α γ}
                                {H : PreorderFunctor α δ} [HasFunctorialImplication F G]
                                [HasFunctorialImplication G H] [HasFunctorialImplication F H]
                                [h : HasCompFunImp F G H] (i : FunImp F G) (j : FunImp G H) :
        FunImp F H :=
      h.defCompFunImp i j

    @[reducible] def revCompFunImpFun₂ (F : PreorderFunctor α β) (G : PreorderFunctor α γ)
                                       (H : PreorderFunctor α δ) [HasFunctorialImplication F G]
                                       [HasFunctorialImplication G H] [HasFunctorialImplication F H]
                                       [h : HasCompFunImp F G H] :
        FunImp G H ⥤ FunImp F G ⥤ FunImp F H :=
      h.defRevCompFunImpFun₂

    instance compFunImp.isFunApp₂ {F : PreorderFunctor α β} {G : PreorderFunctor α γ}
                                  {H : PreorderFunctor α δ} [HasFunctorialImplication F G]
                                  [HasFunctorialImplication G H] [HasFunctorialImplication F H]
                                  [h : HasCompFunImp F G H] {i : FunImp F G} {j : FunImp G H} :
        IsFunApp₂ (compFunImp i j) :=
      ⟨revCompFunImpFun₂ F G H, j, i⟩

  end HasCompFunImp

end HasPreorderRelation
