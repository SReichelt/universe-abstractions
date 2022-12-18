import UniverseAbstractions.Universes.Layer1.Meta.Sort



namespace UniverseAbstractions.Layer1.Meta

set_option autoImplicit false

open Lean Lean.Meta Elab Tactic Qq UniverseAbstractions.Meta
     HasPiType HasFunctors



structure FVar (α : _sort) where
  a : α
  n : Name

namespace FVar

  variable {α : _sort} (a : FVar α)

  def substitute (a' : α) (e : Expr) : Expr := e.replaceFVar a.a a'

  def substituteType' (a' : α) {u : Level} (β : _sort.mkSortType u) : _sort.mkSortType u :=
    substitute a a' β

  def substituteType (a' : α) (β : _sort) : _sort :=
    substituteType' a a' (_sort.mkSortType.fromSort β)

  def abstract (e : Expr) : Expr := e.abstract #[a.a]

  def abstractType' {u : Level} (β : _sort.mkSortType u) : _sort.mkSortType u := abstract a β

  def abstractType (β : _sort) : _sort := abstractType' a (_sort.mkSortType.fromSort β)

end FVar



inductive LambdaBodyCategory (ExprType : Type) where
  | const (e : ExprType)
  | dep

inductive LambdaBodyCategoryExt (ExprType : Type) where
  | const (e : ExprType)
  | id
  | dep

def LambdaBodyCategory.toLambdaBodyCategoryExt {ExprType : Type} :
    LambdaBodyCategory ExprType → LambdaBodyCategoryExt ExprType
  | const e => LambdaBodyCategoryExt.const e
  | dep     => LambdaBodyCategoryExt.dep

instance (ExprType : Type) : Coe (LambdaBodyCategory ExprType) (LambdaBodyCategoryExt ExprType) :=
  ⟨LambdaBodyCategory.toLambdaBodyCategoryExt⟩



-- An expr `y` that depends on an `FVar` `a`. Essentially, this encodes the lambda abstraction
-- `λ a : α => y`. The reason for introducing this type is that when working with `y`, `a` must be
-- an `FVar` for Lean algorithms such as `isDefEq` to work.

structure DependentExpr {α : _sort} (a : FVar α) where
  y : Expr

namespace DependentExpr

  variable {α : _sort} {a : FVar α} (t : DependentExpr a)

  def apply (a' : α) : Expr := FVar.substitute a a' t.y

  def toPi : Expr := mkLambda a.n BinderInfo.default α.α (FVar.abstract a t.y)

  def isId : MetaM Bool := isDefEq t.y a.a

  def classify : MetaM (LambdaBodyCategory Expr) := do
    let fvarId := a.a.fvarId!
    let y ← instantiateMVars t.y
    unless y.containsFVar fvarId do
      return LambdaBodyCategory.const y
    let y' ← reduce y
    unless y'.containsFVar fvarId do
      return LambdaBodyCategory.const y'
    pure LambdaBodyCategory.dep

  def classifyExt : MetaM (LambdaBodyCategoryExt Expr) := do
    if ← t.isId then
      return LambdaBodyCategoryExt.id
    t.classify

  def mvarId? : Option MVarId :=
    match t.y with
    | Expr.app (Expr.mvar mvarId ..) .. => mvarId
    | _ => none

end DependentExpr


-- Typed version of `DependentExpr`. The type may be dependent as well.

structure DependentTypedExpr {α : _sort} (a : FVar α) (β : DependentExpr a) where
  y : TypedExpr β.y

namespace DependentTypedExpr

  variable {α : _sort} {a : FVar α} {β : DependentExpr a} (t : DependentTypedExpr a β)

  def toDependentExpr : DependentExpr a := ⟨t.y⟩

  def apply (a' : α) : TypedExpr (FVar.substitute a a' β.y) := t.toDependentExpr.apply a'

  def toPi : TypedExpr (mkForall a.n BinderInfo.default α.α (FVar.abstract a β.y)) :=
    t.toDependentExpr.toPi

  def isId : MetaM Bool := t.toDependentExpr.isId

  def classify : MetaM (LambdaBodyCategory (TypedExpr β.y)) := t.toDependentExpr.classify
  def classifyExt : MetaM (LambdaBodyCategoryExt (TypedExpr β.y)) := t.toDependentExpr.classifyExt

  def mvarId? : Option MVarId := t.toDependentExpr.mvarId?

end DependentTypedExpr


structure LambdaAbstraction {α : _sort} {v : Level} {p : α → _sort.mkSortType v}
                            (P : [α ⥤ _sort.mkSortType v]_{p}) where
  {a : FVar α}
  t : DependentTypedExpr a ⟨p a.a⟩

namespace LambdaAbstraction

  def fromPi {α : _sort} {v : Level} {p : α → _sort.mkSortType v} {P : [α ⥤ _sort.mkSortType v]_{p}}
             (f : Pi (_sort.defFunToProp P)) {γ : Type} (k : LambdaAbstraction P → MetaM γ) :
      MetaM γ :=
    match f with
    | Expr.lam n d b c =>
      withLocalDecl n c d (fun a => k (LambdaAbstraction.mk (a := ⟨a, n⟩) ⟨b.instantiate1 a⟩))
    | f =>
      withLocalDeclD Name.anonymous α.α
                     (fun a => k (LambdaAbstraction.mk (a := ⟨a, Name.anonymous⟩) ⟨mkApp f a⟩))

  variable {α : _sort} {v : Level} {p : α → _sort.mkSortType v} {P : [α ⥤ _sort.mkSortType v]_{p}}
           (f : LambdaAbstraction P)

  def type : DependentExpr f.a := ⟨p f.a.a⟩

  def y : p f.a.a := f.t.y

  def mkDependentExpr (e : Expr) : DependentExpr f.a := ⟨e⟩

  def mkDependentTypedExpr {α : Expr} (e : TypedExpr α) :
      DependentTypedExpr f.a (f.mkDependentExpr α) :=
    ⟨e⟩

end LambdaAbstraction
