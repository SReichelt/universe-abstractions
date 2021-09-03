set_option autoBoundImplicitLocal false

universe u v w w'



namespace Eq

  @[simp] theorem simp_rec {α : Sort u} {a a' : α} {ha : a = a'}
                           {T : α → Sort v} {x : T a}
                           {β : Sort w} {f : {a : α} → T a → β} :
    @f a' (ha ▸ x) = f x :=
  by subst ha; rfl

  @[simp] theorem simp_rec' {α : Sort u} {a a' : α} {ha : a = a'}
                            {T : α → Sort v} {x : T a}
                            {β : Sort u} {b b' : β} {hb : b = b'}
                            {U : β → Sort w} {f : {a : α} → {b : β} → T a → U b} :
    hb ▸ @f a' b' (ha ▸ x) = @f a b x :=
  by subst ha; subst hb; rfl

  @[simp] theorem simp_rec_rec {α : Sort u} {a a' : α} {ha : a = a'} {ha' : a' = a}
                               {T : α → Sort v} {x : T a} :
    ha' ▸ ha ▸ x = x :=
  by subst ha; rfl

  theorem elim_rec {α : Sort u} {a a' : α} {ha : a = a'}
                   {T : α → Sort v} {x : T a}
                   {γ : Sort w} {f : {a : α} → T a → γ}
                   {c : γ} :
    @f a' (ha ▸ x) = c ↔ f x = c :=
  by rw [simp_rec (ha := ha) (f := f) (x := x)]; exact Iff.rfl

  theorem elim_rec' {α : Sort u} {a a' : α} {ha : a = a'}
                    {T : α → Sort v} {x : T a}
                    {β : Sort u} {b b' : β} {hb : b = b'}
                    {U : β → Sort w} {f : {a : α} → {b : β} → T a → U b}
                    {c : U b} :
    hb ▸ @f a' b' (ha ▸ x) = c ↔ f x = c :=
  by rw [simp_rec' (ha := ha) (hb := hb) (U := U) (f := f) (x := x)]; exact Iff.rfl

end Eq
