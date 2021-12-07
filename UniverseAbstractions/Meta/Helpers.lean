import UniverseAbstractions.Meta.TypedExpr



set_option autoBoundImplicitLocal false



namespace Lean

  open Meta Elab Tactic Qq



  @[reducible] def FVar {u : Level} (α : ⌜Sort u⌝) := TypedExpr α

  namespace FVar

    def instantiateLambda' {u : Level} {α : ⌜Sort u⌝} (f : Expr)
                           {γ : Type} (k : (a : FVar α) → Name → Expr → MetaM γ) :
      MetaM γ :=
    match f with
    | Expr.lam n d b c =>
      withLocalDecl n c.binderInfo d (fun a : FVar α => k a n (b.instantiate1 a))
    | f =>
      withLocalDeclD `_ α (fun a : FVar α => k a `_ (mkApp f a))

    def instantiateLambda {u v : Level} {α : ⌜Sort u⌝} {β : ⌜$α → Sort v⌝} (f : ⌜(a : $α) → $β a⌝)
                          {γ : Type} (k : (a : FVar α) → Name → ⌜$β $a⌝ → MetaM γ) :
      MetaM γ :=
    instantiateLambda' f k

    variable {u : Level} {α : ⌜Sort u⌝} (a : FVar α) (n : Name)

    def abstractForall {v : Level} (β : ⌜Sort v⌝) : ⌜Sort (imax u v)⌝ :=
    mkForall n BinderInfo.default α (β.abstract #[a])

    def abstractLambda' (b : Expr) : Expr :=
    mkLambda n BinderInfo.default α (b.abstract #[a])

    def abstractLambda {v : Level} {β : ⌜Sort v⌝} (b : β) : abstractForall a n β :=
    a.abstractLambda' n b

  end FVar



  -- A term `b` that depends on an `FVar` `a`. Essentially, this encodes the lambda abstraction
  -- `λ a : α => b`. When working with `b`, `a` must be an `FVar` for Lean algorithms such as
  -- `isDefEq` to work.
  --
  -- If `β` also depends on `a`, `DependentlyTypedTerm` should be used instead.

  structure DependentTerm {u v : Level} {α : ⌜Sort u⌝} (a : FVar α) (β : ⌜Sort v⌝) where
  (n : Name)
  (b : β)

  namespace DependentTerm

    def fromFunction {u v : Level} {α : ⌜Sort u⌝} {β : ⌜Sort v⌝} (f : ⌜$α → $β⌝)
                     {γ : Type} (k : (a : FVar α) → DependentTerm a β → MetaM γ) : MetaM γ :=
    FVar.instantiateLambda' f (fun a n b => k a ⟨n, b⟩)

    variable {u v : Level} {α : ⌜Sort u⌝} {β : ⌜Sort v⌝} {a : FVar α} (t : DependentTerm a β)

    def instantiate : MetaM (DependentTerm a β) := do
      return ⟨t.n, ← t.b.instantiate⟩

    def apply (a' : α) : β := t.b.replaceFVar a a'

    def toFunction : ⌜$α → $β⌝ := a.abstractLambda t.n t.b

    def isId : MetaM Bool := isDefEq t.b a

    def asConstant? : MetaM (Option β) := do
      let fvarId := a.fvarId!
      let b ← t.b.instantiate
      if !(b.containsFVar fvarId) then
        return b
      let b' ← TypedExpr.unfold_reduce b
      if !(b'.containsFVar fvarId) then
        return b'
      none

  end DependentTerm


  structure DependentlyTypedTerm {u v : Level} {α : ⌜Sort u⌝} (a : FVar α)
                                 (T : DependentTerm a ⌜Sort v⌝) where
  (b : DependentTerm a T.b)

  namespace DependentlyTypedTerm

    def fromFunction {u v : Level} {α : ⌜Sort u⌝} {β : ⌜$α → Sort v⌝} (f : ⌜(a : $α) → $β a⌝)
                     {γ : Type} (k : (a : FVar α) → (T : DependentTerm a (mkSort v)) →
                                     (t : DependentlyTypedTerm a T) → MetaM γ) :
      MetaM γ :=
    FVar.instantiateLambda f (fun a n b => k a ⟨n, ⌜$β $a⌝⟩ ⟨⟨n, b⟩⟩)

    variable {u v : Level} {α : ⌜Sort u⌝} {a : FVar α} {T : DependentTerm a ⌜Sort v⌝}
             (t : DependentlyTypedTerm a T)

    def instantiate : MetaM (DependentlyTypedTerm a T) := do
      return ⟨← t.b.instantiate⟩

    def apply (a' : α) : T.apply a' := t.b.apply a'

    def toFunction : a.abstractForall t.b.n T.b := t.b.toFunction

    def isId : MetaM Bool := t.b.isId

    def asConstant? : MetaM (Option T.b) := t.b.asConstant?

  end DependentlyTypedTerm

end Lean
