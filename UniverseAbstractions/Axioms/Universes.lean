set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w



-- A type class that says that a given type `I : Sort v` can itself be used like `Sort u`, i.e.
-- its instances can be regarded as types.
-- * The canonical instance of `HasInstances` is `Sort u` itself (with `Prop` as a special case),
--   as defined below as `sortHasInstances`.
-- * Another common case is `Bundled ` (see below) for a type class `φ : Sort u → Sort v` (say,
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
  instance unitHasInstances : HasInstances.{0, 1}     Unit     := ⟨λ _ => True⟩
  instance boolHasInstances : HasInstances.{0, 1}     Bool     := ⟨λ b => cond b True False⟩

end HasInstances



-- A slight generalization of a type class `φ : Sort u → Sort w`. We replace `Sort u` with an
-- index type `I` that is an instance of `HasInstances`.

def GeneralizedTypeClass (I : Sort v) [HasInstances.{u, v} I] : Sort (max v (w + 1)) := I → Sort w

-- For each (generalized) type class `φ : I → Sort w`, we can define a "bundled instance"
-- `S : Bundled φ` as a dependent pair of an `A : I` and `inst : φ A`. We can treat `S` as a type
-- by "forgetting" `inst`.

structure Bundled {I : Sort v} [HasInstances.{u, v} I] (φ : GeneralizedTypeClass.{u, v, w} I) :
  Sort (max (u + 1) v (w + 1)) where
(A    : I)
[inst : φ A]

namespace Bundled

  instance hasInstances {I : Sort v} [HasInstances.{u, v} I] (φ : GeneralizedTypeClass.{u, v, w} I) :
    HasInstances.{u, max (u + 1) v (w + 1)} (Bundled φ) :=
  ⟨λ S => ⌈S.A⌉⟩

end Bundled



-- An abstract "universe" type that enriches the Lean universe `u` with additional information.
-- This is just a bundled version of `HasInstances` itself. I.e. everything which satisfies
-- `HasInstances` (such as `Sort u` and any `Bundled φ`, see above) can be considered as a
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

  instance instInst : HasInstances.{u, u + 1} U.A := U.inst
  instance : HasInstances ⌈U⌉ := instInst U

  def univ : Universe.{u + 1} := ⟨Universe.{u}⟩

end Universe



def unit : Universe.{0} := ⟨Unit⟩

namespace unit

  def Inst : unit := ()

  def inst {A : unit} : A := trivial

end unit



def boolean : Universe.{0} := ⟨Bool⟩

namespace boolean

  def True  : boolean := true
  def False : boolean := false

  def inst : True := trivial

end boolean



def sort : Universe.{u} := ⟨Sort u⟩
@[reducible] def prop := sort.{0}
@[reducible] def type := sort.{u + 1}



namespace Bundled

  def TypeClass (U : Universe.{max u w}) := GeneralizedTypeClass.{max u w, (max u w) + 1, w} ⌈U⌉

  def univ {U : Universe.{max u w}} (φ : TypeClass.{u, w} U) : Universe.{max u w} :=
  ⟨Bundled φ⟩

  instance univ.inst {U : Universe.{max u w}} {φ : TypeClass.{u, w} U} (A : univ φ) :
    φ A.A :=
  A.inst

end Bundled



def UniverseClass := Bundled.TypeClass.{(max u w) + 1, w} Universe.univ.{max u w}

namespace UniverseClass

  def univ (φ : UniverseClass.{u, w}) : Universe.{(max u w) + 1} := Bundled.univ.{(max u w) + 1, w} φ

  instance {φ : UniverseClass.{u, w}} (U : univ φ) : HasInstances.{max u w, (max u w) + 1} ⌈U⌉ :=
  Universe.instInst U.A

end UniverseClass



noncomputable def PEmpty.elim {C : Sort v} (e : PEmpty.{u}) : C := PEmpty.rec (λ _ => C) e

namespace Universe

  def emptyUniverse : Universe.{u} :=
  { A    := PEmpty.{u + 1},
    inst := ⟨PEmpty.elim⟩ }


  def singletonUniverse (α : Sort u) : Universe.{u} :=
  { A    := PUnit.{u + 1},
    inst := ⟨λ _ => α⟩ }
  notation "{" α:0 "}" => Universe.singletonUniverse α

  def singletonUniverse.type (α : Sort u) : {α} := PUnit.unit
  notation "⌊" α:0 "⌋" => Universe.singletonUniverse.type α


  instance (U : Universe.{u}) : HasInstances.{u, u + 1} (Option ⌈U⌉) :=
  ⟨λ C => match C with
          | none   => PEmpty.{u}
          | some A => ⌈A⌉⟩

  def optionUniverse (U : Universe.{u}) : Universe.{u} := ⟨Option ⌈U⌉⟩


  structure LiftedType (U : Universe.{u}) : Type (max 1 u v) where
  (A : U)

  structure LiftedInstance {U : Universe.{u}} (A : U) : Sort (max 1 u v) where
  (a : A)

  instance (U : Universe.{u}) : HasInstances.{max 1 u v, (max 1 u v) + 1} (LiftedType.{u, v} U) :=
  ⟨λ C => LiftedInstance.{u, v} C.A⟩

  def liftedUniverse (U : Universe.{u}) : Universe.{max 1 u v} := ⟨LiftedType.{u, v} U⟩


  structure TypeProduct (U : Universe.{u}) (V : Universe.{v}) : Type (max 1 u v) where
  (A : U)
  (B : V)

  instance (U : Universe.{u}) (V : Universe.{v}) : HasInstances.{max 1 u v, (max 1 u v) + 1} (TypeProduct U V) :=
  ⟨λ C => PProd ⌈C.A⌉ ⌈C.B⌉⟩

  def productUniverse (U : Universe.{u}) (V : Universe.{v}) : Universe.{max 1 u v} := ⟨TypeProduct U V⟩


  inductive TypeSum (U V : Universe.{u}) : Type u where
  | inU (A : U)
  | inV (B : V)

  instance (U V : Universe.{u}) : HasInstances.{u, u + 1} (TypeSum U V) :=
  ⟨λ C => match C with
          | TypeSum.inU A => ⌈A⌉
          | TypeSum.inV B => ⌈B⌉⟩

  def sumUniverse (U V : Universe.{u}) : Universe.{u} := ⟨TypeSum U V⟩

end Universe
