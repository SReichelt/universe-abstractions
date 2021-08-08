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

  instance hasInstances : HasInstances Universe.{u} := Bundled.hasInstances HasInstances

  variable (U : Universe)

  instance instInst : HasInstances U.α := U.inst
  instance : HasInstances ⌈U⌉ := instInst U

end Universe
