import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Instances.Utils.Trivial



namespace UniverseAbstractions.Layer1

set_option autoBoundImplicitLocal false

universe u



-- A universe that is like `U` except that every type has an additional instance `none`.
def optionUniverse (U : Universe.{u + 1}) : Universe.{u + 1} where
  I := U.I
  h := ⟨λ A => Option A⟩


-- A universe where the index type `I` is wrapped in a binary tree corresponding to a binary
-- operation on types. In this generic variant, the binary operation is defined on a separate type
-- `α` that sits in between types and their instances.
def binaryOpUniverse {I : Sort v} {α : Sort w} (map : I → α) (op : α → α → α) (Inst : α → Sort u) :
    Universe.{u} where
  I := BinaryTree I
  h := ⟨λ A => Inst (BinaryTree.mapReduce map op A)⟩

-- A simpler variant of `binaryOpUniverse` where the binary operation is defined directly on the
-- (Lean) type of instances.
def binaryInstOpUniverse (U : Universe.{u}) (Op : Sort u → Sort u → Sort u) : Universe.{u} :=
  binaryOpUniverse U.h.Inst Op id


-- `binaryInstOpUniverse` where the operation is a function type constructor. This enables the
-- addition of trivial functors to any universe.
def functionUniverse (U : Universe.{u}) : Universe.{u} := binaryInstOpUniverse U (λ α β => α → β)

namespace functionUniverse

  variable (U : Universe)

  instance hasInnerFunctors : HasInnerFunctors (functionUniverse U) where
    Fun   := BinaryTree.inner
    apply := id

  instance hasTrivialFunctoriality :
      HasTrivialFunctoriality (functionUniverse U) (functionUniverse U) :=
    ⟨λ f => ⟨f⟩⟩

end functionUniverse
