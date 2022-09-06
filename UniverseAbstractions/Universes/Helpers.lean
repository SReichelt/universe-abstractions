namespace UniverseAbstractions.Helpers

set_option autoImplicit false

universe u v w w' w'' w''' w'''' w''''' w''''''



inductive BinaryTree (α : Sort u) where
  | leaf (a : α)
  | inner (a b : BinaryTree α)

def BinaryTree.mapReduce {α : Sort u} {β : Sort v} (map : α → β) (reduce : β → β → β) :
    BinaryTree α → β
  | leaf a => map a
  | inner a b => reduce (mapReduce map reduce a) (mapReduce map reduce b)



structure AbstractMultiFun₂ {α : Sort u} {β : Sort v} {γ : Sort w} (AppFun : (β → γ) → Sort w')
                            (AppFun₂ : (α → γ) → Sort w'') (f : α → β → γ) :
    Sort (max 1 u v w' w'') where
  app  (a : α) : AppFun  (f a)
  app₂ (b : β) : AppFun₂ (λ a => f a b)

namespace AbstractMultiFun₂

  def swap {α : Sort u} {β : Sort v} {γ : Sort w} {AppFun : (β → γ) → Sort w'}
           {AppFun₂ : (α → γ) → Sort w''} {f : α → β → γ} (F : AbstractMultiFun₂ AppFun AppFun₂ f) :
      AbstractMultiFun₂ AppFun₂ AppFun (λ b a => f a b) where
    app  := F.app₂
    app₂ := F.app

end AbstractMultiFun₂


def AbstractMultiFun₃' {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort w'}
                       (AppFun : (γ → δ) → Sort w'') (AppFun₂ : (β → δ) → Sort w''')
                       (AppFun₃ : (α → δ) → Sort w'''') (f : α → β → γ → δ) :=
  AbstractMultiFun₂ (AbstractMultiFun₂ AppFun AppFun₂) (AbstractMultiFun₂ AppFun AppFun₃) f

structure AbstractMultiFun₃ {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort w'}
                            (AppFun : (γ → δ) → Sort w'') (AppFun₂ : (β → δ) → Sort w''')
                            (AppFun₃ : (α → δ) → Sort w'''') (f : α → β → γ → δ) :
    Sort (max 1 u v w w'' w''' w'''') where
  app   (a : α)         : AbstractMultiFun₂ AppFun AppFun₂ (f a)
  app₂₃ (b : β) (c : γ) : AppFun₃ (λ a => f a b c)

namespace AbstractMultiFun₃

  def app₂ {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort w'} {AppFun : (γ → δ) → Sort w''}
           {AppFun₂ : (β → δ) → Sort w'''} {AppFun₃ : (α → δ) → Sort w''''} {f : α → β → γ → δ}
           (F : AbstractMultiFun₃ AppFun AppFun₂ AppFun₃ f) (b : β) :
      AbstractMultiFun₂ AppFun AppFun₃ (λ a c => f a b c) where
    app  a := (F.app a).app b
    app₂ c := F.app₂₃ b c

  def app₃ {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort w'} {AppFun : (γ → δ) → Sort w''}
           {AppFun₂ : (β → δ) → Sort w'''} {AppFun₃ : (α → δ) → Sort w''''} {f : α → β → γ → δ}
           (F : AbstractMultiFun₃ AppFun AppFun₂ AppFun₃ f) (c : γ) :
      AbstractMultiFun₂ AppFun₂ AppFun₃ (λ a b => f a b c) where
    app  a := (F.app a).app₂ c
    app₂ b := F.app₂₃ b c

  def fromNested {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort w'} {AppFun : (γ → δ) → Sort w''}
                 {AppFun₂ : (β → δ) → Sort w'''} {AppFun₃ : (α → δ) → Sort w''''} {f : α → β → γ → δ}
                 (F : AbstractMultiFun₃' AppFun AppFun₂ AppFun₃ f) :
      AbstractMultiFun₃ AppFun AppFun₂ AppFun₃ f where
    app   a   := F.app a
    app₂₃ b c := (F.app₂ b).app₂ c

  def toNested {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort w'} {AppFun : (γ → δ) → Sort w''}
               {AppFun₂ : (β → δ) → Sort w'''} {AppFun₃ : (α → δ) → Sort w''''} {f : α → β → γ → δ}
               (F : AbstractMultiFun₃ AppFun AppFun₂ AppFun₃ f) :
      AbstractMultiFun₃' AppFun AppFun₂ AppFun₃ f where
    app  := F.app
    app₂ := F.app₂

end AbstractMultiFun₃


structure AbstractMultiFun₄ {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort w'} {ε : Sort w''}
                            (AppFun : (δ → ε) → Sort w''') (AppFun₂ : (γ → ε) → Sort w'''')
                            (AppFun₃ : (β → ε) → Sort w''''') (AppFun₄ : (α → ε) → Sort w'''''')
                            (f : α → β → γ → δ → ε) :
    Sort (max 1 u v w w' w''' w'''' w''''' w'''''') where
  app    (a : α)                 : AbstractMultiFun₃ AppFun AppFun₂ AppFun₃ (f a)
  app₂₃₄ (b : β) (c : γ) (d : δ) : AppFun₄ (λ a => f a b c d)
