import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Meta.Helpers
import UniverseAbstractions.Universes.Layer1.Meta.ExprUniverse



namespace UniverseAbstractions.Layer1.Meta

set_option autoBoundImplicitLocal false

open Lean UniverseAbstractions.Meta



def _sort := exprUniverse id

namespace _sort

  instance hasFunctors (A : _sort) : HasFunctors A _sort where
    defFunType Y := { A    := ⟨mkFun A.α Y.α⟩
                      elim := λ (f : mkFun A.α Y.α) (a : A.α) => mkFunApp f a }

  instance hasUnivFunctors : HasUnivFunctors _sort _sort := ⟨⟩

  -- When using this, make sure that `f` is defeq to what `f'` specifies.
  def defFun {A B : _sort} {f' : A → B} (f : mkFun A.α B.α) : A ⥤{f'} B := ⟨f⟩

  def defFun₂ {A B C : _sort} {f' : A → B → C} (f : mkFun A.α (mkFun B.α C.α)) : A ⥤ B ⥤{f'} C :=
    ⟨λ a => defFun (mkFunApp f a), defFun f⟩

  def defFun₃ {A B C D : _sort} {f' : A → B → C → D} (f : mkFun A.α (mkFun B.α (mkFun C.α D.α))) :
      A ⥤ B ⥤ C ⥤{f'} D :=
    ⟨λ a => defFun₂ (mkFunApp f a), defFun f⟩

  instance hasIdFun (A : _sort) : HasIdFun A := ⟨defFun ⌜id⌝⟩
  
  instance hasRevAppFun (A : _sort) : HasRevAppFun A _sort := ⟨λ B => defFun₂ ⌜λ a f => f a⌝⟩

  instance hasConstFun (A : _sort) : HasConstFun A _sort :=
    ⟨λ {B} (b : B.α) => defFun ⌜Function.const _ $b⌝⟩

  instance hasConstFun₂ (A : _sort) : HasConstFun₂ A _sort :=
    ⟨λ B => defFun ⌜Function.const _⌝⟩

  instance hasDupFun (A : _sort) : HasDupFun A _sort :=
    ⟨λ {B} (f : mkFun A.α (mkFun A.α B.α)) => defFun ⌜λ a => $f a a⌝⟩

  instance hasDupFun₂ (A : _sort) : HasDupFun₂ A _sort :=
    ⟨λ B => defFun ⌜λ f a => f a a⌝⟩

  instance hasRevCompFun₂ (A : _sort) : HasRevCompFun₂ A _sort _sort :=
    ⟨λ {B C} (g : mkFun B.α C.α) => defFun₂ ⌜λ f a => $g (f a)⌝⟩

  instance hasRevCompFun₃ (A : _sort) : HasRevCompFun₃ A _sort _sort :=
    ⟨λ B C => defFun ⌜λ g f => g ∘ f⌝⟩

  instance hasLinearLogic    : HasLinearLogic    _sort := ⟨⟩
  instance hasSubLinearLogic : HasSubLinearLogic _sort := ⟨⟩
  instance hasAffineLogic    : HasAffineLogic    _sort := ⟨⟩
  instance hasNonLinearLogic : HasNonLinearLogic _sort := ⟨⟩
  instance hasFullLogic      : HasFullLogic      _sort := ⟨⟩

end _sort
