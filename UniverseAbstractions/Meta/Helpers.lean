import UniverseAbstractions.Meta.TypedExpr



namespace UniverseAbstractions.Meta

set_option autoImplicit false

open Lean Lean.Meta Elab Tactic Qq



-- Dependent and indepent functions.

def mkForAll {u v : Level} (α : Q(Sort u)) (P : Q($α → Sort v)) : Q(Sort (imax u v)) :=
  ⌜∀ a, $P a⌝

def mkForAll.mkApp {u v : Level} (α : Q(Sort u)) (P : Q($α → Sort v)) (f : Q(∀ a, $P a))
                   (a : Q($α)) :
    Q($P $a) :=
  ⌜$f $a⌝

def mkFun {u v : Level} (α : Q(Sort u)) (β : Q(Sort v)) : Q(Sort (imax u v)) :=
  mkForAll α ⌜λ _ => $β⌝

def mkFun.mkApp {u v : Level} (α : Q(Sort u)) (β : Q(Sort v)) (f : Q($α → $β)) (a : Q($α)) :
    Q($β) :=
  mkForAll.mkApp (v := v) α ⌜λ _ => $β⌝ f a



-- Definitions of all functions that match the combinators defined in `Functors.lean`.

def mkIdFun {u : Level} (α : Q(Sort u)) : Q($α → $α) := ⌜λ a => a⌝

def mkPiAppFun {u v : Level} (α : Q(Sort u)) (P : Q($α → Sort v)) (a : Q($α)) :
    Q((∀ a, $P a) → $P $a) :=
  ⌜λ f => f $a⌝

def mkPiAppFunPi {u v : Level} (α : Q(Sort u)) (P : Q($α → Sort v)) :
    Q(∀ a, (∀ a', $P a') → $P a) :=
  ⌜λ a f => f a⌝

def mkSwapPi {u u' v : Level} (α : Q(Sort u)) (β : Q(Sort u')) (P : Q($α → $β → Sort v))
             (f : Q(∀ a b, $P a b)) (b : Q($β)) :
    Q(∀ a, $P a $b) :=
  ⌜λ a => $f a $b⌝

def mkSwapPi₂ {u u' v : Level} (α : Q(Sort u)) (β : Q(Sort u')) (P : Q($α → $β → Sort v))
              (f : Q(∀ a b, $P a b)) :
    Q(∀ b a, $P a b) :=
  ⌜λ b a => $f a b⌝

def mkSwapPiFun {u u' v : Level} (α : Q(Sort u)) (β : Q(Sort u')) (P : Q($α → $β → Sort v)) :
    Q((∀ a b, $P a b) → (∀ b a, $P a b)) :=
  ⌜λ f b a => f a b⌝

def mkCompFunPi {u v w : Level} (α : Q(Sort u)) (β : Q(Sort v)) (Q : Q($β → Sort w))
                (f : Q($α → $β)) (g : Q(∀ b, $Q b)) :
    Q(∀ a, $Q ($f a)) :=
  ⌜λ a => $g ($f a)⌝

def mkRevCompFunPi₂ {u v w : Level} (α : Q(Sort u)) (β : Q(Sort v)) (Q : Q($β → Sort w))
                    (g : Q(∀ b, $Q b)) :
    Q(∀ (f : $α → $β) a, $Q (f a)) :=
  ⌜λ f a => $g (f a)⌝

def mkRevCompFunPiFun {u v w : Level} (α : Q(Sort u)) (β : Q(Sort v)) (Q : Q($β → Sort w)) :
    Q((∀ b, $Q b) → (∀ (f : $α → $β) a, $Q (f a))) :=
  ⌜λ g f a => g (f a)⌝

def mkConstFun {u v : Level} (α : Q(Sort u)) (β : Q(Sort v)) (b : Q($β)) : Q($α → $β) :=
  ⌜λ _ => $b⌝

def mkConstFun₂ {u v : Level} (α : Q(Sort u)) (β : Q(Sort v)) : Q($β → ($α → $β)) :=
  ⌜λ b _ => b⌝

def mkDupPi {u v : Level} (α : Q(Sort u)) (P : Q($α → $α → Sort v)) (f : Q(∀ a a', $P a a')) :
    Q(∀ a, $P a a) :=
  ⌜λ a => $f a a⌝

def mkDupPiFun {u v : Level} (α : Q(Sort u)) (P : Q($α → $α → Sort v)) :
    Q((∀ a a', $P a a') → (∀ a, $P a a)) :=
  ⌜λ f a => f a a⌝

def mkPiSelfAppPi {u v : Level} (α : Q(Sort u)) (Q : Q($α → Sort v)) (f : Q((∀ a, $Q a) → $α)) :
    Q(∀ g, $Q ($f g)) :=
  ⌜λ g => g ($f g)⌝

def mkPiSelfAppPi₂ {u v : Level} (α : Q(Sort u)) (Q : Q($α → Sort v)) :
    Q(∀ (f : (∀ a, $Q a) → $α) g, $Q (f g)) :=
  ⌜λ f g => g (f g)⌝

def mkSubstPi {u v w : Level} (α : Q(Sort u)) (P : Q($α → Sort v)) (Q : Q(∀ a, $P a → Sort w))
              (f : Q(∀ a, $P a)) (g : Q(∀ a b, $Q a b)) :
    Q(∀ a, $Q a ($f a)) :=
  ⌜λ a => $g a ($f a)⌝

def mkRevSubstPi₂ {u v w : Level} (α : Q(Sort u)) (P : Q($α → Sort v)) (Q : Q(∀ a, $P a → Sort w))
                  (g : Q(∀ a b, $Q a b)) :
    Q(∀ (f : ∀ a, $P a) a, $Q a (f a)) :=
  ⌜λ f a => $g a (f a)⌝

def mkRevSubstPiFun {u v w : Level} (α : Q(Sort u)) (P : Q($α → Sort v))
                    (Q : Q(∀ a, $P a → Sort w)) :
    Q((∀ a b, $Q a b) → (∀ (f : ∀ a, $P a) a, $Q a (f a))) :=
  ⌜λ g f a => g a (f a)⌝
