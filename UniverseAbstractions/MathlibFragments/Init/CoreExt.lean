/-
Just some random additions to `Core.lean` that look like they would actually belong there.
-/



universe u v



def Empty.elim {C : Sort v} (e : Empty) : C := Empty.casesOn (λ _ => C) e
def PEmpty.elim {C : Sort v} (e : PEmpty.{u}) : C := PEmpty.casesOn (λ _ => C) e



theorem Prod.ext' {α : Type u} {β : Type v} {p q : α × β} :
        p.fst = q.fst ∧ p.snd = q.snd → p = q := by
  cases p; cases q; simp; exact id

theorem PProd.ext {α : Sort u} {β : Sort v} (p : PProd α β) : PProd.mk p.1 p.2 = p := by
  cases p; rfl

theorem PProd.ext' {α : Sort u} {β : Sort v} {p q : PProd α β} :
        p.fst = q.fst ∧ p.snd = q.snd → p = q := by
  cases p; cases q; simp; exact id



theorem Iff.equivalence              : Equivalence Iff     := ⟨Iff.refl, Iff.symm, Iff.trans⟩
theorem Eq.equivalence  (α : Sort u) : Equivalence (@Eq α) := ⟨Eq.refl,  Eq.symm,  Eq.trans⟩



structure Preorder {α : Sort u} (r : α → α → Prop) : Prop where
  refl  : ∀ x, r x x
  trans : ∀ {x y z}, r x y → r y z → r x z

def Preorder.fromEquivalence {α : Sort u} {r : α → α → Prop} :
  Equivalence r → Preorder r :=
λ e => ⟨e.refl, e.trans⟩
