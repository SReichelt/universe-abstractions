namespace UniverseAbstractions.Helpers

set_option autoBoundImplicitLocal false

universe u v w w' w'' w''' w''''



inductive BinaryTree (α : Sort u) where
  | leaf (a : α)
  | inner (a b : BinaryTree α)

def BinaryTree.mapReduce {α : Sort u} {β : Sort v} (map : α → β) (reduce : β → β → β) :
    BinaryTree α → β
  | leaf a => map a
  | inner a b => reduce (mapReduce map reduce a) (mapReduce map reduce b)



structure AbstractBiFun {α : Sort u} {β : Sort v} {γ : Sort w} (AppFun : (β → γ) → Sort w')
                        (AppFun₂ : (α → γ) → Sort w'') (f : α → β → γ) :
  Sort (max 1 u v w' w'') where
(app  (a : α) : AppFun  (f a))
(app₂ (b : β) : AppFun₂ (λ a => f a b))

namespace AbstractBiFun

  def swap {α : Sort u} {β : Sort v} {γ : Sort w} {AppFun : (β → γ) → Sort w'}
           {AppFun₂ : (α → γ) → Sort w''} {f : α → β → γ} (F : AbstractBiFun AppFun AppFun₂ f) :
      AbstractBiFun AppFun₂ AppFun (λ b a => f a b) where
    app  := F.app₂
    app₂ := F.app

  def app₃ {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort w'} {AppFun : (γ → δ) → Sort w''}
           {AppFun₂ : (β → δ) → Sort w'''} {AppFun₃ : (α → δ) → Sort w''''} {f : α → β → γ → δ}
           (F : AbstractBiFun (AbstractBiFun AppFun AppFun₂) (AbstractBiFun AppFun AppFun₃) f)
           (c : γ) :
      AbstractBiFun AppFun₂ AppFun₃ (λ a b => f a b c) where
    app  a := (F.app  a).app₂ c
    app₂ b := (F.app₂ b).app₂ c

end AbstractBiFun
