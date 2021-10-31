/-
Just some random additions to `Core.lean` that look like they would actually belong there.
-/



def Empty.elim {C : Sort v} (e : Empty) : C := Empty.casesOn (λ _ => C) e
def PEmpty.elim {C : Sort v} (e : PEmpty.{u}) : C := PEmpty.casesOn (λ _ => C) e



theorem Iff.isEquivalence              : Equivalence Iff     := ⟨Iff.refl, Iff.symm, Iff.trans⟩
theorem Eq.isEquivalence  (α : Sort u) : Equivalence (@Eq α) := ⟨Eq.refl,  Eq.symm,  Eq.trans⟩
