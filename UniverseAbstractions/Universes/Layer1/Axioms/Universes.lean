namespace UniverseAbstractions

set_option autoImplicit false
set_option linter.unusedVariables false

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

  class HasElim {U : Universe.{u, uu}} (A : U) (α : outParam (Sort u')) where
    elim : A → α

  namespace HasElim

    variable {U : Universe.{u, uu}} (A : U) {α : Sort u'}

    instance coeNative [h : HasElim A α] : Coe A α := ⟨h.elim⟩

    -- Same as `A` with the additional assurance that the type that `A` eliminates to is inhabited
    -- (and we are often interested in that particular instance).
    @[reducible] def DefInst [h : HasElim A α] (a : α) : U := A
    notation "[" A:0 "]_{" a:0 "}" => HasElim.DefInst A a

  end HasElim

  class HasIntro {U : Universe.{u, uu}} (A : U) (α : outParam (Sort u')) where
    intro : α → A

  namespace HasIntro

    variable {U : Universe.{u, uu}} (A : U) {α : Sort u'} [h : HasIntro A α]

    instance coeType : Coe α A := ⟨h.intro⟩

  end HasIntro

  class HasType (U : Universe.{u, uu}) (α : Sort u') where
    T : U
    [hElim : HasElim T α]

  namespace HasType

    @[reducible] def UnivType (U : Universe.{u, uu}) (α : Sort u') [h : HasType U α] : U := h.T
    notation "[" α:0 " | " U:0 "]" => HasType.UnivType U α

    instance (U : Universe.{u, uu}) (α : Sort u') [h : HasType U α] : HasElim [α | U] α :=
      h.hElim
    notation "[" α:0 " | " U:0 "]_{" a:0 "}" => [[α | U]]_{a}

    def native {U : Universe.{u, uu}} (A : U) : HasType U A where
      T     := A
      hElim := ⟨id⟩

    variable (U : Universe.{u, uu}) {α : Sort u'} [HasType U α]

    def map {β : Sort u''} (f : α → β) : HasType U β where
      T     := [α | U]
      hElim := ⟨λ a => f a⟩

  end HasType

  class HasTypeWithIntro (U : Universe.{u, uu}) (α : Sort u') extends HasType U α where
    [hIntro : HasIntro T α]

  namespace HasTypeWithIntro

    instance (U : Universe.{u, uu}) (α : Sort u') [h : HasTypeWithIntro U α] : HasIntro [α | U] α :=
      h.hIntro

    def native {U : Universe.{u, uu}} (A : U) : HasTypeWithIntro U A where
      toHasType := HasType.native A
      hIntro    := ⟨id⟩

    def defInst {U : Universe.{u, uu}} {α : Sort u'} [h : HasTypeWithIntro U α] {a : α} :
        [α | U]_{a} :=
      a

  end HasTypeWithIntro

end Layer1
