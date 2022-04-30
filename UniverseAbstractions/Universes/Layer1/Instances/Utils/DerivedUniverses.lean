import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Instances.Utils.Trivial



namespace UniverseAbstractions.Layer1

set_option autoBoundImplicitLocal false

universe u v w



-- A universe that is like `U` except that every type has an additional instance `none`.
def optionUniverse (U : Universe.{u + 1}) : Universe.{u + 1} :=
{ I := U.I,
  h := ⟨λ A => Option A⟩ }


inductive BinaryTree (α : Sort u) where
| leaf (a : α)
| inner (a b : BinaryTree α)

def BinaryTree.mapReduce {α : Sort u} {β : Sort v} (map : α → β) (reduce : β → β → β) :
  BinaryTree α → β
| leaf a => map a
| inner a b => reduce (mapReduce map reduce a) (mapReduce map reduce b)


-- A universe where the index type `I` is wrapped in a binary tree corresponding to a binary
-- operation on types. In this generic variant, the binary operation is defined on a separate type
-- `α` that sits in between types and their instances.
def binaryOpUniverse {I : Sort v} {α : Sort w} (map : I → α) (op : α → α → α) (Inst : α → Sort u) :
  Universe.{u} :=
{ I := BinaryTree I,
  h := ⟨λ A => Inst (BinaryTree.mapReduce map op A)⟩ }

-- A simpler variant of `binaryOpUniverse` where the binary operation is defined directly on the
-- (Lean) type of instances.
def binaryInstOpUniverse (U : Universe.{u}) (Op : Sort u → Sort u → Sort u) : Universe.{u} :=
binaryOpUniverse U.h.Inst Op id


-- `binaryInstOpUniverse` where the operation is a function type constructor. This enables the
-- addition of trivial functors to any universe.
def functionUniverse (U : Universe.{u}) : Universe.{u} := binaryInstOpUniverse U (λ α β => α → β)

namespace functionUniverse

  variable (U : Universe)

  instance hasFunctors : HasFunctors (functionUniverse U) :=
  { Fun   := BinaryTree.inner,
    apply := id }

  instance hasTrivialFunctoriality : HasTrivialFunctoriality (functionUniverse U) := ⟨λ f => ⟨f⟩⟩

end functionUniverse
