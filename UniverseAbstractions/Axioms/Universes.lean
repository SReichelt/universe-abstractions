import UniverseAbstractions.MathlibFragments.Init.CoreExt



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w w'



-- A type class that says that a given type `I : Sort v` can itself be used like `Sort u`, i.e.
-- its instances can be regarded as types.
-- * The canonical instance of `HasInstances` is `Sort u` itself (with `Prop` as a special case),
--   as defined below as `sortHasInstances`.
-- * Another common case is `Bundled φ` (see below) for a type class `φ : Sort u → Sort v` (say,
--   `Group`, `Ring`, `Category`, etc.). I.e., for a given `A : Bundled φ`, we can treat `A` as a
--   type.
--
-- `I` can be considered an index type, where each index stands for a type.

class HasInstances (I : Sort v) : Sort (max (u + 1) v) where
(Inst : I → Sort u)

namespace HasInstances

  instance coeSort (I : Sort v) [h : HasInstances.{u, v} I] : CoeSort I (Sort u) := ⟨h.Inst⟩

  -- Although `coeSort` lets us write `a : A` instead of `a : HasInstances.Inst A`, in other cases
  -- we need to invoke `HasInstances.Inst A` explicitly. A custom notation `⌈A⌉` is much easier on
  -- the eye.
  notation "⌈" A:0 "⌉" => HasInstances.Inst A

  instance sortHasInstances : HasInstances.{u, u + 1} (Sort u) := ⟨id⟩
  instance unitHasInstances : HasInstances.{0, 0}     True     := ⟨λ _ => True⟩

end HasInstances



-- For a type class `φ : α → Sort w`, we can define a "bundled instance" `S : Bundled φ` as a
-- dependent pair of an `a : α` and `inst : φ α`.
-- The most important use case is that if `a` is a type (i.e. we have `HasInstances α`), we can
-- treat `S` as a type by "forgetting" `inst`.

structure Bundled {α : Sort u} (φ : α → Sort v) : Sort (max 1 u v) where
(a    : α)
[inst : φ a]

namespace Bundled

  instance hasInstances {I : Sort v} [HasInstances.{u, v} I] (φ : I → Sort w) :
    HasInstances.{u, max 1 v w} (Bundled φ) :=
  ⟨λ S => S.a⟩

end Bundled



-- An abstract "universe" type that enriches the Lean universe `u` with additional information.
-- This is just a bundled version of `HasInstances` itself. I.e. everything which satisfies
-- `HasInstances` (such as `Sort u` and any `Bundled φ`, see above) can be considered as a
-- `Universe`.
--
-- A `Universe` on its own is usually not very useful, but can have additional structure defined as
-- type classes on `Universe`. See e.g. `Functors.lean`.

def Universe : Type (max u v) := Bundled HasInstances.{u, v}

namespace Universe

  instance hasInstances : HasInstances.{v, (max u v) + 1} Universe.{u, v} :=
  Bundled.hasInstances HasInstances

  def univ : Universe.{v, (max u v) + 1} := ⟨Universe.{u, v}⟩

  variable (U : Universe.{u, v})

  instance instInst : HasInstances.{u, v} U.a := U.inst
  instance : HasInstances U := instInst U

end Universe



def sort : Universe.{u, u + 1} := ⟨Sort u⟩
@[reducible] def prop := sort.{0}
@[reducible] def type := sort.{u + 1}
@[reducible] def tsort := sort.{max 1 u}

def unit : Universe.{0, 0} := ⟨True⟩



namespace Bundled

  def univ {U : Universe.{u, v}} (φ : U → Sort w) : Universe.{u, max 1 v w} :=
  ⟨Bundled φ⟩

  def univ.inst {U : Universe.{u, v}} {φ : U → Sort w} (A : univ φ) : φ A.a := A.inst

  def type {U : Universe.{u, v}} {φ : U → Sort w} {A : U} (inst : φ A) : univ φ :=
  { a    := A,
    inst := inst }

end Bundled



def UniverseClass := Universe.univ.{u, v} → Sort w

namespace UniverseClass

  def univ (φ : UniverseClass.{u, v, w}) : Universe.{v, max 1 (u + 1) (v + 1) w} :=
  Bundled.univ φ

  instance {φ : UniverseClass.{u, v, w}} (U : univ φ) : HasInstances.{u, v} U :=
  Universe.instInst U.a

end UniverseClass



namespace Universe

  def emptyUniverse : Universe.{u, v} :=
  { a    := PEmpty.{v},
    inst := ⟨PEmpty.elim⟩ }


  def singletonUniverse (α : Sort u) : Universe.{u, v} :=
  { a    := PUnit.{v},
    inst := ⟨λ _ => α⟩ }
  notation "{" α:0 "}" => Universe.singletonUniverse α

  def singletonUniverse.type (α : Sort u) : {α} := PUnit.unit
  notation "⌊" α:0 "⌋" => Universe.singletonUniverse.type α

  @[reducible] def singletonUniverse.inst {α : Sort u} (a : α) : ⌊α⌋ := a
  notation "⸤" a:0 "⸥" => Universe.singletonUniverse.inst a

  @[reducible] def singletonUniverse.orig {α : Sort u} (a : ⌊α⌋) : α := a
  notation "⸥" a:0 "⸤" => Universe.singletonUniverse.orig a

  instance (U : Universe.{u, v}) : HasInstances ⌊U⌋ := Universe.instInst U


  instance (U : Universe.{u}) : HasInstances.{u} (Option U) :=
  ⟨λ C => match C with
          | none   => PEmpty.{u}
          | some A => A⟩

  def optionUniverse (U : Universe.{u}) : Universe.{u} := ⟨Option U⟩


  instance (U : Universe.{u}) (V : Universe.{v}) : HasInstances.{max 1 u v} (PProd U V) :=
  ⟨λ C => PProd C.fst C.snd⟩

  def productUniverse (U : Universe.{u}) (V : Universe.{v}) : Universe.{max 1 u v} := ⟨PProd U V⟩


  instance (U V : Universe.{u}) : HasInstances.{u} (PSum U V) :=
  ⟨λ C => match C with
          | PSum.inl A => A
          | PSum.inr B => B⟩

  def sumUniverse (U V : Universe.{u}) : Universe.{u} := ⟨PSum U V⟩

end Universe
