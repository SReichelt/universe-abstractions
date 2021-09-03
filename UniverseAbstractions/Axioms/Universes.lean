import mathlib4_experiments.Data.Equiv.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v



-- A type class that says that a given type can be used like `Sort u`, i.e. its instances can be
-- regarded as types.
-- * The canonical instance of `HasInstances` is `Sort u` itself (with `Prop` as a special case),
--   as defined below as `sortHasInstances`.
-- * Another common case is `Bundled C` (see below) for a type class `C : Sort u → Sort v` (say,
--   `Group`, `Ring`, `Category`, etc.). I.e., for a given `S : Bundled C`, we can treat `S` as a
--   type.

class HasInstances (U : Sort v) : Sort (max (u + 1) v) where
(Inst : U → Sort u)

namespace HasInstances

  instance coeSort (U : Sort v) [h : HasInstances.{u, v} U] : CoeSort U (Sort u) := ⟨h.Inst⟩

  -- Although `coeSort` lets us write `a : α` instead of `a : HasInstances.Inst α`, in other cases
  -- we need to invoke `HasInstances.Inst α` explicitly. A custom notation `⌈α⌉` is much easier on
  -- the eye.
  notation "⌈" α:0 "⌉" => HasInstances.Inst α

  instance sortHasInstances : HasInstances.{u, u + 1} (Sort u) := ⟨id⟩

end HasInstances



-- A slight generalization of a type class `C : Sort u → Sort v`. We replace `Sort u` with an
-- arbitrary type `U` that is an instance of `HasInstances`.

def GeneralizedTypeClass (U : Type u) [HasInstances.{u, u + 1} U] : Type (max u v) := U → Sort v

-- For each (generalized) type class `C : U → Sort v`, we can define a "bundled instance"
-- `S : Bundled C` as a dependent pair of an `α : U` and `inst : C α`. We can treat `S` as a type
-- by "forgetting" `inst`.

structure Bundled {U : Type u} [HasInstances.{u, u + 1} U] (C : GeneralizedTypeClass.{u, v} U) :
  Type (max u v) where
(α    : U)
[inst : C α]

namespace Bundled

  instance hasInstances {U : Type u} [HasInstances.{u, u + 1} U] (C : GeneralizedTypeClass.{u, v} U) :
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

def Universe : Type (u + 1) := Bundled HasInstances.{u, u + 1}

namespace Universe

  instance hasInstances : HasInstances.{u + 1, u + 2} Universe.{u} := Bundled.hasInstances HasInstances

  variable (U : Universe)

  instance instInst : HasInstances U.α := U.inst
  instance : HasInstances ⌈U⌉ := instInst U

end Universe



def UniverseClass := GeneralizedTypeClass.{u + 1, u + 1} Universe.{u}

def univ (C : UniverseClass.{u}) : Universe.{u + 1} := ⟨Bundled C⟩

instance {C : UniverseClass.{u}} (U : univ C) : HasInstances ⌈U⌉ := Universe.instInst U.α



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
