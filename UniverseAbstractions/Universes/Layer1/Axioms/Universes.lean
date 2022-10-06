namespace UniverseAbstractions

set_option autoImplicit false

universe u uu u' u'' v



-- Workaround for Lean compiler problems:
-- Define "compiler_bug" and "compiler_slow" as aliases for "noncomputable".
def makeNoncomputable (c : Lean.Syntax) : Lean.Syntax :=
  let declModifiers := c.getArg 0
  let noncomp := declModifiers.getArg 3
  let noncomp := noncomp.setArgs #[Lean.mkNode `Command.noncomputable #[Lean.mkAtom "noncomputable"]]
  let declModifiers := declModifiers.setArg 3 noncomp
  c.setArg 0 declModifiers

macro "compiler_bug "  c:command : command => pure (makeNoncomputable c)
macro "compiler_slow " c:command : command => pure (makeNoncomputable c)



-- A type class that says that a given type `I : Sort uu` can be used like `Sort u`, i.e. its
-- instances can be regarded as types.
-- * The canonical instance of `HasInstances` is `Sort u` itself (see `sortHasInstances`).
-- * Another common case is `Bundled Φ` for a type class `Φ : Sort u → Sort w` (say, `Group`,
--   `Ring`, `Category`, etc.). I.e., for a given `A : Bundled Φ`, we can treat `A` as a type.
--
-- `I` can be considered an index type, where each index stands for a type.
-- `HasInstances` is essentially `CoeSort` without the (somewhat strange) output parameter.

class HasInstances (I : Sort uu) : Sort (max (u + 1) uu) where
  Inst : I → Sort u

namespace HasInstances

  instance coeSort (I : Sort uu) [h : HasInstances.{u, uu} I] : CoeSort I (Sort u) := ⟨h.Inst⟩

  -- Although `coeSort` lets us write `a : A` instead of `a : HasInstances.Inst A`, in other cases
  -- we need to invoke `HasInstances.Inst A` explicitly. A custom notation `⌈A⌉` is much easier on
  -- the eye.
  notation "⌈" A:0 "⌉" => HasInstances.Inst A

  instance sortHasInstances : HasInstances.{u, u + 1} (Sort u) := ⟨id⟩

end HasInstances



-- An abstract "universe" type that enriches the Lean universe `u` with additional information.
-- This is just a bundled version of `HasInstances` itself. I.e. everything which satisfies
-- `HasInstances` (such as `Sort u` and any `Bundled Φ`) can be considered as a `Universe`.
--
-- A `Universe` on its own is usually not very useful, but can have additional structure defined as
-- type classes on `Universe`. See e.g. `Functors.lean`.

structure Universe : Type (max u uu) where
  I : Sort uu
  [h : HasInstances.{u, uu} I]

namespace Universe

  instance hasInstances : HasInstances.{uu, (max u uu) + 1} Universe.{u, uu} := ⟨Universe.I⟩

  instance instInst (U : Universe.{u, uu}) : HasInstances.{u, uu} U.I := U.h
  instance (U : Universe) : HasInstances U := instInst U

end Universe



namespace Layer1

  structure DefType (U : Universe.{u, uu}) (α : Sort u') where
    A : U
    elim : A → α

  namespace DefType
    
    instance (U : Universe.{u, uu}) (α : Sort u') : Coe (DefType U α) U := ⟨DefType.A⟩

    variable {U : Universe.{u, uu}} {α : Sort u'}

    structure DefInst (A : DefType U α) (a : α) where
      inst : A.A

    namespace DefInst

      instance coeType (A : DefType U α) (a : α) : Coe (DefInst A a) A := ⟨DefInst.inst⟩

      def cast {A : DefType U α} {a b : α} (i : DefInst A a) : DefInst A b := ⟨i.inst⟩

    end DefInst

    def map (A : DefType U α) {β : Sort u''} (f : α → β) : DefType U β where
      A      := A.A
      elim a := f (A.elim a)

  end DefType

  structure DefTypeWithIntro (U : Universe.{u, uu}) (α : Sort u') extends DefType U α where
    defInst (a : α) : DefType.DefInst toDefType a

  namespace DefTypeWithIntro
    
    instance (U : Universe.{u, uu}) (α : Sort u') : Coe (DefTypeWithIntro U α) U := ⟨λ A => A.A⟩

    variable {U : Universe.{u, uu}} {α : Sort u'}

    @[reducible] def inst (A : DefTypeWithIntro U α) (a : α) : A.A := A.defInst a

  end DefTypeWithIntro

end Layer1
