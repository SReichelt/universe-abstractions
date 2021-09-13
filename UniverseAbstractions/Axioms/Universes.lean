import mathlib4_experiments.Data.Equiv.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w



-- A type class that says that a given type `I : Sort v` can itself be used like `Sort u`, i.e.
-- its instances can be regarded as types.
-- * The canonical instance of `HasInstances` is `Sort u` itself (with `Prop` as a special case),
--   as defined below as `sortHasInstances`.
-- * Another common case is `Bundled C` (see below) for a type class `C : Sort u → Sort v` (say,
--   `Group`, `Ring`, `Category`, etc.). I.e., for a given `S : Bundled C`, we can treat `S` as a
--   type.
--
-- `I` can be considered an index type, where each index stands for a type.

class HasInstances (I : Sort v) : Sort (max (u + 1) v) where
(Inst : I → Sort u)

namespace HasInstances

  instance coeSort (I : Sort v) [h : HasInstances.{u, v} I] : CoeSort I (Sort u) := ⟨h.Inst⟩

  -- Although `coeSort` lets us write `a : α` instead of `a : HasInstances.Inst α`, in other cases
  -- we need to invoke `HasInstances.Inst α` explicitly. A custom notation `⌈α⌉` is much easier on
  -- the eye.
  notation "⌈" α:0 "⌉" => HasInstances.Inst α

  instance sortHasInstances : HasInstances.{u, u + 1} (Sort u) := ⟨id⟩

end HasInstances



-- A slight generalization of a type class `C : Sort u → Sort w`. We replace `Sort u` with an
-- index type `I` that is an instance of `HasInstances`.

def GeneralizedTypeClass (I : Sort v) [HasInstances.{u, v} I] : Sort (max v (w + 1)) := I → Sort w

-- For each (generalized) type class `C : I → Sort w`, we can define a "bundled instance"
-- `S : Bundled C` as a dependent pair of an `α : I` and `inst : C α`. We can treat `S` as a type
-- by "forgetting" `inst`.

structure Bundled {I : Sort v} [HasInstances.{u, v} I] (C : GeneralizedTypeClass.{u, v, w} I) :
  Sort (max 1 (u + 1) v (w + 1)) where
(α    : I)
[inst : C α]

namespace Bundled

  instance hasInstances {I : Sort v} [HasInstances.{u, v} I] (C : GeneralizedTypeClass.{u, v, w} I) :
    HasInstances (Bundled C) :=
  ⟨λ S => ⌈S.α⌉⟩

end Bundled



-- An abstract "universe" type that enriches the Lean universe `u` with additional information.
-- This is just a bundled version of `HasInstances` itself. I.e. everything which satisfies
-- `HasInstances` (such as `Sort u` and any `Bundled C`, see above) can be considered as a
-- `Universe`.
--
-- A `Universe` on its own is usually not very useful, but can have additional structure defined as
-- type classes on `Universe`. See e.g. `Functors.lean`.
--
-- Although we could make `Universe` polymorphic in the second (Lean) universe argument of
-- `HasInstances`, we specifically choose `u + 1` and specifically adapt to this restriction where
-- necessary. Otherwise, the number of different (Lean) universe variables tends to explode because
-- we are frequently dealing with both 

def Universe : Type (u + 1) := Bundled HasInstances.{u, u + 1}

namespace Universe

  instance hasInstances : HasInstances.{u + 1, u + 2} Universe.{u} := Bundled.hasInstances HasInstances

  variable (U : Universe)

  instance instInst : HasInstances.{u, u + 1} U.α := U.inst
  instance : HasInstances ⌈U⌉ := instInst U

end Universe

def sort : Universe.{u} := ⟨Sort u⟩
@[reducible] def prop := sort.{0}
@[reducible] def type := sort.{1}



def UniverseClass := GeneralizedTypeClass.{u + 1, u + 2, u + 1} Universe.{u}

def univ (C : UniverseClass.{u}) : Universe.{u + 1} := ⟨Bundled C⟩

instance {C : UniverseClass.{u}} (U : univ C) : HasInstances.{u, u + 1} ⌈U⌉ := Universe.instInst U.α



-- A type class on a universe that says that we can find a specific type in it.
--
-- We use `Equiv` from mathlib to give the universe implementation a bit of flexibility, but note
-- that if `v > 1`, the equivalence may contain an equality of types nonetheless, which we avoid in
-- the rest of the formalization. This equality is not necessarily a problem because in most
-- implementations, `⌈α⌉` and `α'` will in fact be exactly the same.

class HasEmbeddedType (U : Universe.{u}) (α' : Sort v) : Sort (max (u + 1) v) where
{α : U}
(h : ⌈α⌉ ≃ α')

namespace HasEmbeddedType

  def EmbeddedType (U : Universe.{u}) (α' : Sort v) [h : HasEmbeddedType U α'] := h.α

  variable (U : Universe.{u}) {α' : Sort v} [h : HasEmbeddedType U α']

  def toExternal   (a : h.α) : α'  := h.h.toFun  a
  def fromExternal (a : α')  : h.α := h.h.invFun a

  @[simp] theorem fromToExternal (a : h.α) : fromExternal U (toExternal   U a) = a := h.h.leftInv a
  @[simp] theorem toFromExternal (a : α')  : toExternal   U (fromExternal U a) = a := h.h.rightInv a

end HasEmbeddedType
