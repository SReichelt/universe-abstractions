import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations.AttachedRelations
import UniverseAbstractions.Universes.Layer1.Meta.Tactics.Functoriality



namespace UniverseAbstractions.Layer1

set_option autoImplicit false

open HasFunctors HasSwapFun

universe u u'



namespace HasEquivalenceRelationBase

  variable {W V : Universe} [HasLinearLogic W]

  section

    class HasCongrArg (α : Sort u) [HasEquivalenceRelationBase W α] [HasFunctors α V] (Y : V)
                      [HasEquivalenceRelationBase W Y] where
      congrArgFun (F : α ⥤ Y) : EquivalenceFunctor (apply F)

    namespace HasCongrArg

      section

        variable {α : Sort u} [HasEquivalenceRelationBase W α] [HasFunctors α V] {Y : V}
                 [HasEquivalenceRelationBase W Y] [h : HasCongrArg α Y]

        @[reducible] def congrArg (F : α ⥤ Y) {a₁ a₂ : α} (e : a₁ ≃ a₂) : F a₁ ≃ F a₂ :=
          (h.congrArgFun F) e

        instance congrArg.isFunApp {F : α ⥤ Y} {a₁ a₂ : α} {e : a₁ ≃ a₂} :
            IsFunApp (a₁ ≃ a₂) (congrArg F e) :=
          ⟨(h.congrArgFun F).inst a₁ a₂, e⟩

        class MatchesFunDef {f : α → Y} (F : α ⥤{f} Y) where
          e (a : α) : F.inst a ≃ f a

        namespace MatchesFunDef

          variable {f : α → Y} (F : α ⥤{f} Y) [hDef : MatchesFunDef F]

          def defCongrArg {a₁ a₂ : α} (e : a₁ ≃ a₂) : f a₁ ≃ f a₂ :=
            hDef.e a₂ • congrArg F.inst e • (hDef.e a₁)⁻¹

          def defCongrArgFun : EquivalenceFunctor f := ⟨λ a₁ a₂ => Λ e => defCongrArg F e⟩

          instance defCongrArg.isFunApp {a₁ a₂ : α} {e : a₁ ≃ a₂} :
              IsFunApp (a₁ ≃ a₂) (defCongrArg F e) :=
            ⟨(defCongrArgFun F).inst a₁ a₂, e⟩

        end MatchesFunDef

      end

      section

        variable {α : Sort u} {β : Sort u'} [HasEquivalenceRelationBase W α]
                 [HasEquivalenceRelationBase W β] [HasFunctors α V] [HasFunctors β V]
                 [hSwap : HasSwapFun α β V] {Y : V} [HasEquivalenceRelationBase W Y]
                 [∀ (F : α ⥤ β ⥤ Y) (b : β), MatchesFunDef ((hSwap.defSwapFun₂ F).app b)]
                 [hα : HasCongrArg α Y] [hβ : HasCongrArg β Y]

        def congrArgFun₂ (F : α ⥤ β ⥤ Y) : EquivalenceFunctor₂ (apply₂ F) where
          app  a := hβ.congrArgFun (F a)
          app₂ b := MatchesFunDef.defCongrArgFun ((hSwap.defSwapFun₂ F).app b)

        @[reducible] def congrArg₂ (F : α ⥤ β ⥤ Y) {a₁ a₂ : α} (ea : a₁ ≃ a₂) {b₁ b₂ : β}
                                   (eb : b₁ ≃ b₂) :
            F a₁ b₁ ≃ F a₂ b₂ :=
          EquivalenceFunctor₂.apply (congrArgFun₂ F) ea eb

        instance congrArg₂.isFunApp₂ {F : α ⥤ β ⥤ Y} {a₁ a₂ : α} {ea : a₁ ≃ a₂} {b₁ b₂ : β}
                                     {eb : b₁ ≃ b₂} :
            IsFunApp₂ (a₁ ≃ a₂) (b₁ ≃ b₂) (congrArg₂ F ea eb) :=
          inferInstance

        class MatchesFunDef₂ {f : α → β → Y} (F : α ⥤ β ⥤{f} Y) where
          e (a : α) (b : β) : F.inst a b ≃ f a b

        namespace MatchesFunDef₂

          variable {f : α → β → Y} (F : α ⥤ β ⥤{f} Y) [hDef : MatchesFunDef₂ F]

          def defCongrArg₂ {a₁ a₂ : α} (ea : a₁ ≃ a₂) {b₁ b₂ : β} (eb : b₁ ≃ b₂) :
              f a₁ b₁ ≃ f a₂ b₂ :=
            hDef.e a₂ b₂ • congrArg₂ F.inst ea eb • (hDef.e a₁ b₁)⁻¹

          def defCongrArgFun₂ (a₁ a₂ : α) (b₁ b₂ : β) : a₁ ≃ a₂ ⟶ b₁ ≃ b₂ ⟶ f a₁ b₁ ≃ f a₂ b₂ :=
            Λ ea eb => defCongrArg₂ F ea eb

          instance defCongrArg₂.isFunApp₂ {a₁ a₂ : α} {ea : a₁ ≃ a₂} {b₁ b₂ : β} {eb : b₁ ≃ b₂} :
              IsFunApp₂ (a₁ ≃ a₂) (b₁ ≃ b₂) (defCongrArg₂ F ea eb) :=
            ⟨defCongrArgFun₂ F a₁ a₂ b₁ b₂, ea, eb⟩

        end MatchesFunDef₂

      end

    end HasCongrArg

  end

end HasEquivalenceRelationBase
