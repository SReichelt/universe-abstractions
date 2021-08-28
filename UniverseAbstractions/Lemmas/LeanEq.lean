set_option autoBoundImplicitLocal false

universe u v w w'



namespace Eq

  @[simp] theorem simp_rec {α : Sort u} {a a' : α} {ha : a = a'}
                           {T : α → Sort v} {x : T a}
                           {β : Sort w} {f : {a : α} → T a → β} :
    @f a' (ha ▸ x) = f x :=
  by subst ha; rfl

  @[simp] theorem simp_rec_rec {α : Sort u} {a a' : α} {ha : a = a'} {ha' : a' = a}
                               {T : α → Sort v} {x : T a} :
    ha' ▸ ha ▸ x = x :=
  by subst ha; rfl

  theorem simp_rec_prop {α : Sort u} {a a' : α} {ha : a = a'}
                        {T : α → Sort v} {x : T a}
                        {p : {a : α} → T a → Prop} :
    @p a' (ha ▸ x) → p x :=
  have s : @p a' (ha ▸ x) = p x := simp_rec;
  λ h => s ▸ h

end Eq
