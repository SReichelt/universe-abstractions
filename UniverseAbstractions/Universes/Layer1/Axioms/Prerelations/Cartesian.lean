import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations.AttachedRelations



namespace UniverseAbstractions.Layer1

set_option autoBoundImplicitLocal false

universe u



namespace HasPreorderRelation

  -- Layer 1 version of a cartesian closed category.
  -- Some facts about these are derived in `CartesianLemmas.lean`.
  -- TODO: Define a universe of such preorders.

  variable {V : Universe} [HasLinearLogic V] (α : Sort u) [hα : HasPreorderRelation V α]

  class HasTerminalObject where
    trm : α
    trmIntroHom (a : α) : a ⟶ trm

  @[reducible] def HasTerminalObject.terminal [h : HasTerminalObject α] : α := h.trm
  prefix:max "⊤" => HasPreorderRelation.HasTerminalObject.terminal

  class HasInitialObject extends HasTerminalObject (opposite α)

  @[reducible] def HasInitialObject.initial [h : HasInitialObject α] : α := h.trm
  prefix:max "⊥" => HasPreorderRelation.HasInitialObject.initial

  class HasProductObjects where
    prod : α → α → α
    fstHom (a b : α) : prod a b ⟶ a
    sndHom (a b : α) : prod a b ⟶ b
    prodIntroFun₂ (a b c : α) : (a ⟶ b) ⟶ (a ⟶ c) ⟶ (a ⟶ prod b c)

  @[reducible] def HasProductObjects.product [h : HasProductObjects α] (a b : α) : α :=
    h.prod (V := V) a b
  infixr:35 "⊗" => HasPreorderRelation.HasProductObjects.product _

  class HasCoproductObjects extends HasProductObjects (opposite α)

  @[reducible] def HasCoproductObjects.coproduct [h : HasCoproductObjects α] (a b : α) : α :=
    h.prod (V := V) a b
  infixr:34 "⊕" => HasPreorderRelation.HasCoproductObjects.coproduct _

  class HasExponentialObjects [HasProductObjects α] where
    exp : α → α → α
    evalHom (a b : α) : exp a b ⊗ a ⟶ b
    curryFun (a b c : α) : (a ⊗ b ⟶ c) ⟶ (a ⟶ exp b c)

  @[reducible] def HasExponentialObjects.exponential [HasProductObjects α]
                                                     [h : HasExponentialObjects α] (b a : α) : α :=
    h.exp (V := V) a b
  infix:36 "⌃" => HasPreorderRelation.HasExponentialObjects.exponential _

end HasPreorderRelation
