import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Properties

import UniverseAbstractions.Lemmas.LeanEq



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w w' w''



-- We usually want a `U : Universe` to have some concept of "functors" that map instances. Here, we
-- need to reconcile three conflicting requirements:
--
-- * We usually want a functor `F : α ⟶ β` with `α β : U` to be an instance of `U`, so that we can
--   define e.g. functors returning functors without having to specify any additional assumptions.
--   E.g. if `U` is the universe of categories, `α ⟶ β` is the functor category from `α` to `β`.
--
-- * However, in some cases we have a more general concept of a functor `α ⟶ β` where `α` and `β`
--   are not necessarily types of the same universe.
--
-- * Moreover, we want to axiomatically assert the existence of certain functors such as identity
--   and composition, which map instances in specific ways. Ideally, we want this mapping to be a
--   definitional equality so that e.g. applying the identity functor is a trivial operation. This
--   implies that the mapping must be part of the type of the axiom.
--
-- In order to meet all requirements, we currently define three kinds of functors, with conversions
-- between them:
--
-- `F : α ⟶[f] β` | `F a` defined as `f a`.
-- `F : α ⟶' β`   | Bundled version of the above; therefore e.g. `(HasIdFun.idFun α) a` (see below)
--                | is definitionally equal to `a`.
-- `F : α ⟶ β`    | An instance of a universe `W`; therefore we cannot ensure that `F a` is
--                | definitionally equal to anything if `W` is arbitrary.
--                | In particular, e.g. `(HasLinearFunOp.idFun α) a = a` not definitionally, but
--                | `by simp` (more specifically, `HasFunctor.fromDefFun.eff`).



class HasFunctoriality (U : Universe.{u}) (V : Universe.{v}) [HasProperties.{u, v, w} U V] :
  Type (max u v w w') where
(IsFun {α : U} {P : HasProperties.Property α V} : HasProperties.Pi P → Sort w')

namespace HasFunctoriality

  variable {U : Universe.{u}} {V : Universe.{v}} [HasProperties.{u, v, w} U V]
           [h : HasFunctoriality.{u, v, w, w'} U V]

  def DefPi {α : U} (P : HasProperties.Property α V) (f : HasProperties.Pi P) := h.IsFun f
  notation:20 "Π[" f:0 "] " P:21 => HasFunctoriality.DefPi P f

  structure Pi {α : U} (P : HasProperties.Property α V) : Sort (max 1 u v w') where
  (f : HasProperties.Pi P)
  (F : Π[f] P)
  notation:20 "Π' " P:21 => HasFunctoriality.Pi P

  @[reducible] def DefFun (α : U) (β : V) (f : α → β) := Π[f] HasProperties.constProp α β
  notation:20 α:21 " ⟶[" f:0 "] " β:21 => HasFunctoriality.DefFun α β f

  @[reducible] def Fun (α : U) (β : V) := Π' HasProperties.constProp α β
  infixr:20 " ⟶' " => HasFunctoriality.Fun

  variable {α : U} {P : HasProperties.Property α V}

  instance coeDefPi (f : HasProperties.Pi P) : CoeFun (Π[f] P) (λ _ => HasProperties.Pi P) := ⟨λ _ => f⟩
  instance coePi                             : CoeFun (Π'   P) (λ _ => HasProperties.Pi P) := ⟨Pi.f⟩

  def toDefPi                            (F : Π'   P) : Π[F.f] P := F.F
  def fromDefPi {f : HasProperties.Pi P} (F : Π[f] P) : Π'     P := ⟨f, F⟩

  instance (F : Π' P)               : CoeDep (Π'   P) F (Π[F.f] P) := ⟨toDefPi F⟩
  instance {f : HasProperties.Pi P} : Coe    (Π[f] P)   (Π'     P) := ⟨fromDefPi⟩

  def castDefPi {f f' : HasProperties.Pi P} (F : Π[f] P) (h : ∀ a, f a = f' a) : Π[f'] P :=
  have h₁ : f = f' := funext h;
  h₁ ▸ F

  @[simp] theorem fromCastDefPi {f f' : HasProperties.Pi P} (F : Π[f] P) (h : ∀ a, f a = f' a) :
    fromDefPi (castDefPi F h) = fromDefPi F :=
  Eq.simp_rec

  @[simp] theorem castCastDefPi {f f' : HasProperties.Pi P} (F : Π[f] P) (h : ∀ a, f a = f' a) :
    castDefPi (castDefPi F h) (λ a => Eq.symm (h a)) = F :=
  Eq.simp_rec_rec (ha := funext h)

  @[simp] theorem toDefPi.eff                            (F : Π'   P) (a : α) : (toDefPi   F) a = F a := rfl
  @[simp] theorem fromDefPi.eff {f : HasProperties.Pi P} (F : Π[f] P) (a : α) : (fromDefPi F) a = F a := rfl

  @[simp] theorem fromToDefPi                          (F : Π'   P) : fromDefPi (toDefPi F) = F :=
  match F with | ⟨_, _⟩ => rfl
  @[simp] theorem toFromDefPi {f : HasProperties.Pi P} (F : Π[f] P) : toDefPi (fromDefPi F) = F := rfl

end HasFunctoriality



class HasFunctors (U : Universe.{u}) (V : Universe.{v}) (W : outParam Universe.{w}) extends
  HasProperties.{u, v, w'} U V, HasFunctoriality.{u, v, w', w''} U V : Type (max u v w w' w'') where
[embed {α : U} (P : HasProperties.Property α V) : HasEmbeddedType.{w, max 1 u v w''} W (Π' P)]

namespace HasFunctors

  variable {U V W : Universe} [h : HasFunctors U V W]

  section Dependent

    instance hasEmbeddedType {α : U} (P : HasProperties.Property α V) : HasEmbeddedType W (Π' P) :=
    h.embed P

    def Pi {α : U} (P : HasProperties.Property α V) : W := HasEmbeddedType.EmbeddedType W (Π' P)
    notation:20 "Π " P:21 => HasFunctors.Pi P

    variable {α : U} {P : HasProperties.Property α V}

    def toExternal   (F : Π  P) : Π' P := HasEmbeddedType.toExternal   W F
    def fromExternal (F : Π' P) : Π  P := HasEmbeddedType.fromExternal W F

    def piCoe (F : Π P) : HasProperties.Pi P := (toExternal F).f
    instance coePi : CoeFun ⌈Π P⌉ (λ _ => HasProperties.Pi P) := ⟨piCoe⟩

    @[simp] theorem fromToExternal (F : Π  P) : fromExternal (toExternal F) = F := HasEmbeddedType.fromToExternal W F
    @[simp] theorem toFromExternal (F : Π' P) : toExternal (fromExternal F) = F := HasEmbeddedType.toFromExternal W F

    @[simp] theorem toExternal.eff   (F : Π  P) (a : α) : (toExternal   F) a = F a := rfl
    @[simp] theorem fromExternal.eff (F : Π' P) (a : α) : (fromExternal F) a = F a :=
    congrFun (congrArg HasFunctoriality.Pi.f (toFromExternal F)) a

    def toDefPi                            (F : Π    P) : Π[piCoe F] P := HasFunctoriality.toDefPi (toExternal F)
    def fromDefPi {f : HasProperties.Pi P} (F : Π[f] P) : Π P          := fromExternal (HasFunctoriality.fromDefPi F)
    instance {f : HasProperties.Pi P} : Coe (Π[f] P) ⌈Π P⌉ := ⟨fromDefPi⟩

    @[simp] theorem fromCastDefPi {f f' : HasProperties.Pi P} (F : Π[f] P) (h : ∀ a, f a = f' a) :
      fromDefPi (HasFunctoriality.castDefPi F h) = fromDefPi F :=
    congrArg fromExternal (HasFunctoriality.fromCastDefPi F h)

    def toDefPi' (F : Π P) {f : HasProperties.Pi P} (h : ∀ a, F a = f a) : Π[f] P :=
    HasFunctoriality.castDefPi (toDefPi F) h

    theorem toDefPi'.eff (F : Π P) {f : HasProperties.Pi P} (h : ∀ a, F a = f a) (a : α) : (toDefPi' F h) a = F a :=
    Eq.symm (h a)

    @[simp] theorem toDefPi.eff                            (F : Π    P) (a : α) : (toDefPi   F) a = F a := rfl
    @[simp] theorem fromDefPi.eff {f : HasProperties.Pi P} (F : Π[f] P) (a : α) : (fromDefPi F) a = F a :=
    fromExternal.eff (HasFunctoriality.fromDefPi F) a

    @[simp] theorem fromToDefPi (F : Π P) : fromDefPi (toDefPi F) = F :=
    Eq.trans (congrArg fromExternal (HasFunctoriality.fromToDefPi (toExternal F))) (fromToExternal F)

    @[simp] theorem fromToDefPi' (F : Π P) {f : HasProperties.Pi P} (h : ∀ a, F a = f a) : fromDefPi (toDefPi' F h) = F :=
    Eq.trans (fromCastDefPi (toDefPi F) h) (fromToDefPi F)

    -- This is annoying to prove, and we don't need it at the moment.
    --@[simp] theorem toFromDefPi' {f : HasProperties.Pi P} (F : Π[f] P) : toDefPi' (fromDefPi F) (fromDefPi.eff F) = F :=
    --sorry

  end Dependent

  section Independent

    @[reducible] def DefFun (α : U) (β : V) (f : α → β) := HasFunctoriality.DefFun α β f

    @[reducible] def Fun (α : U) (β : V) : W := Pi (HasProperties.constProp α β)
    infixr:20 " ⟶ " => HasFunctors.Fun

    -- It would be nice if we could omit the rest of the `Independent` section, but unfortunately
    -- the `Dependent` definitions seem to be too generic for `simp`.

    variable {α : U} {β : V}

    @[reducible] def funCoe (F : α ⟶ β) : α → β := piCoe F
    instance coeFun : CoeFun ⌈α ⟶ β⌉ (λ _ => α → β) := ⟨funCoe⟩

    @[simp] theorem toExternal.Fun.eff   (F : α ⟶  β) (a : α) : (toExternal   F) a = F a := toExternal.eff   F a
    @[simp] theorem fromExternal.Fun.eff (F : α ⟶' β) (a : α) : (fromExternal F) a = F a := fromExternal.eff F a

    @[simp] theorem toDefFun.eff               (F : α ⟶ β)    (a : α) : (toDefPi   F) a = F a := toDefPi.eff   F a
    @[simp] theorem fromDefFun.eff {f : α → β} (F : α ⟶[f] β) (a : α) : (fromDefPi F) a = F a := fromDefPi.eff F a

    def toDefFun' (F : α ⟶ β) {f : α → β} (h : ∀ a, F a = f a) : α ⟶[f] β := toDefPi' F h
    infix:60 " ◄ " => HasFunctors.toDefFun'

    -- Marking this `@[simp]` causes a huge performance hit. I don't understand why.
    theorem toDefFun'.eff (F : α ⟶ β) {f : α → β} (h : ∀ a, F a = f a) (a : α) : (toDefFun' F h) a = F a :=
    toDefPi'.eff F h a

    @[simp] theorem fromToDefFun' (F : α ⟶ β) {f : α → β} (h : ∀ a, F a = f a) : fromDefPi (toDefFun' F h) = F :=
    fromToDefPi' F h

    -- This is annoying to prove, and we don't need it at the moment.
    --@[simp] theorem toFromDefFun' {f : α → β} (F : α ⟶[f] β) : toDefFun' (fromDefPi F) (fromDefPi.eff F) = F :=
    --toFromDefPi' F

  end Independent

end HasFunctors



class HasIdFun (U : Universe) [HasProperties U U] [HasFunctoriality U U] where
(defIdFun (α : U) : α ⟶[id] α)

namespace HasIdFun

  @[reducible] def idFun' {U : Universe} [HasProperties U U] [HasFunctoriality U U] [HasIdFun U] (α : U) : α ⟶' α :=
  defIdFun α

  @[reducible] def idFun {U V : Universe} [HasFunctors U U V] [HasIdFun U] (α : U) : α ⟶ α :=
  HasFunctors.fromExternal (idFun' α)

end HasIdFun

class HasConstFun (U V : Universe) [HasProperties U V] [HasFunctoriality U V] where
(defConstFun (α : U) {β : V} (c : β) : α ⟶[Function.const ⌈α⌉ c] β)

namespace HasConstFun

  @[reducible] def constFun' {U V : Universe} [HasProperties U V] [HasFunctoriality U V] [HasConstFun U V] (α : U) {β : V} (c : β) :
    α ⟶' β :=
  defConstFun α c

  @[reducible] def constFun {U V W : Universe} [HasFunctors U V W] [HasConstFun U V] (α : U) {β : V} (c : β) :
    α ⟶ β :=
  HasFunctors.fromExternal (constFun' α c)

end HasConstFun

class HasCompFun' (U V W : Universe) [HasProperties U V] [HasFunctoriality U V] [HasProperties V W] [HasFunctoriality V W] [HasProperties U W] [HasFunctoriality U W] where
(defCompFun {α : U} {β : V} {γ : W} (F : α ⟶' β) (G : β ⟶' γ) : α ⟶[λ a => G (F a)] γ)

namespace HasCompFun'

  variable {U V W : Universe} [HasProperties U V] [HasFunctoriality U V] [HasProperties V W] [HasFunctoriality V W] [HasProperties U W] [HasFunctoriality U W]
           [HasCompFun' U V W]

  @[reducible] def compFun' {α : U} {β : V} {γ : W} (F : α ⟶' β) (G : β ⟶' γ) : α ⟶' γ :=
  defCompFun F G

  @[reducible] def revCompFun' {α : U} {β : V} {γ : W} (G : β ⟶' γ) (F : α ⟶' β) := compFun' F G
  infixr:90 " ⊙' " => HasCompFun'.revCompFun'

end HasCompFun'

class HasCompFun (U V W X Y : Universe) [HasFunctors U V X] [HasFunctors V W Y] [HasProperties U W] [HasFunctoriality U W] where
(defCompFun {α : U} {β : V} {γ : W} (F : α ⟶ β) (G : β ⟶ γ) : α ⟶[λ a => G (F a)] γ)

namespace HasCompFun

  variable {U V W X Y Z : Universe} [HasFunctors U V X] [HasFunctors V W Y] [HasFunctors U W Z]
           [HasCompFun U V W X Y]

  @[reducible] def compFun {α : U} {β : V} {γ : W} (F : α ⟶ β) (G : β ⟶ γ) : α ⟶ γ :=
  defCompFun F G

  @[reducible] def revCompFun {α : U} {β : V} {γ : W} (G : β ⟶ γ) (F : α ⟶ β) := compFun F G

  instance hasCompFun' : HasCompFun' U V W :=
  ⟨λ F G => HasFunctoriality.castDefPi (defCompFun (HasFunctors.fromExternal F) (HasFunctors.fromExternal G))
                                       (λ _ => by simp)⟩

end HasCompFun



class HasEmbeddedFunctors (U : Universe.{u}) extends HasFunctors.{u, u, u, w, w} U U U : Type (max u w)

namespace HasEmbeddedFunctors

  -- Restricted copies of definitions in `HasFunctors` to help functoriality tactic.

  variable {U : Universe} [HasEmbeddedFunctors U]

  @[reducible] def DefFun (α β : U) (f : α → β) := HasFunctors.DefFun α β f

  @[reducible] def Fun (α β : U) : U := HasFunctors.Fun α β

  variable {α β : U}

  @[reducible] def funCoe (F : α ⟶ β) : α → β := HasFunctors.funCoe F

  @[reducible] def toDefFun               (F : α ⟶ β)    : α ⟶[funCoe F] β := HasFunctors.toDefPi F
  @[reducible] def fromDefFun {f : α → β} (F : α ⟶[f] β) : α ⟶ β           := HasFunctors.fromDefPi F

  @[reducible] def toDefFun' (F : α ⟶ β) {f : α → β} (h : ∀ a, F a = f a) : α ⟶[f] β := HasFunctors.toDefFun' F h

end HasEmbeddedFunctors



-- The following axioms are equivalent to asserting the existence of five functors with specified
-- behavior, writing `Λ` for a functorial `λ` as defined in `Tactics/Functoriality.lean`:
-- id    : `α ⟶ α,                           Λ a => a`
-- const : `β ⟶ (α ⟶ β),                     Λ c a => c`
-- app   : `α ⟶ (α ⟶ β) ⟶ β,                 Λ a F => F a`
-- dup   : `(α ⟶ α ⟶ β) ⟶ (α ⟶ β),           Λ F a => F a a`
-- comp  : `(α ⟶ β) ⟶ (β ⟶ γ) ⟶ (α ⟶ γ),     Λ F G a => G (F a)`
--
-- In `DerivedFunctors.lean`, we derive several functors from these, such as
-- swap  : `(α ⟶ β ⟶ γ) ⟶ (β ⟶ α ⟶ γ),       Λ F b a => F a b`
-- subst : `(α ⟶ β) ⟶ (α ⟶ β ⟶ γ) ⟶ (α ⟶ γ), Λ F G a => G a (F a)`
--
-- Using these, we can give a general algorithm for proving that a function is functorial, which is
-- implemented as a tactic in `Functoriality.lean`.
--
-- We split the axioms into "linear", "affine", and "full" functor operations, where "linear" and
-- "affine" correspond to linear and affine logic, respectively. That is, linear functors use each
-- bound variable exactly once; affine functors use each variable at most once.



class HasLinearFunOp (U : Universe) [HasEmbeddedFunctors U] where
(defIdFun         (α : U)                             : α ⟶[id] α)
(defAppFun        {α : U} (a : α) (β : U)             : (α ⟶ β) ⟶[λ F => F a] β)
(defAppFunFun     (α β : U)                           : α ⟶[λ a => defAppFun a β] ((α ⟶ β) ⟶ β))
(defCompFun       {α β γ : U} (F : α ⟶ β) (G : β ⟶ γ) : α ⟶[λ a => G (F a)] γ)
(defCompFunFun    {α β : U} (F : α ⟶ β) (γ : U)       : (β ⟶ γ) ⟶[λ G => defCompFun F G] (α ⟶ γ))
(defCompFunFunFun (α β γ : U)                         : (α ⟶ β) ⟶[λ F => defCompFunFun F γ] ((β ⟶ γ) ⟶ (α ⟶ γ)))

namespace HasLinearFunOp

  variable {U : Universe} [HasEmbeddedFunctors U] [HasLinearFunOp U]

  def hasIdFun : HasIdFun U := ⟨defIdFun⟩

  @[reducible] def idFun (α : U) : α ⟶ α := defIdFun α

  @[reducible] def appFun {α : U} (a : α) (β : U) : (α ⟶ β) ⟶ β := defAppFun a β
  @[reducible] def appFunFun (α β : U) : α ⟶ (α ⟶ β) ⟶ β := defAppFunFun α β

  def hasCompFun : HasCompFun U U U U U := ⟨defCompFun⟩

  @[reducible] def compFun {α β γ : U} (F : α ⟶ β) (G : β ⟶ γ) : α ⟶ γ := defCompFun F G
  @[reducible] def compFunFun {α β : U} (F : α ⟶ β) (γ : U) : (β ⟶ γ) ⟶ (α ⟶ γ) := defCompFunFun F γ
  @[reducible] def compFunFunFun (α β γ : U) : (α ⟶ β) ⟶ (β ⟶ γ) ⟶ (α ⟶ γ) := defCompFunFunFun α β γ

  @[reducible] def revCompFun {α β γ : U} (G : β ⟶ γ) (F : α ⟶ β) : α ⟶ γ := compFun F G
  infixr:90 " ⊙ " => HasLinearFunOp.revCompFun

end HasLinearFunOp

class HasLinearFunOpEq (U : Universe) [HasEmbeddedFunctors U] [HasLinearFunOp U]
                       [hasIdFun : HasIdFun U] [hasCompFun : HasCompFun U U U U U] where
(defIdFunEq (α : U) : HasLinearFunOp.defIdFun α = HasIdFun.defIdFun α)
(defCompFunEq {α β γ : U} (F : α ⟶ β) (G : β ⟶ γ) : HasLinearFunOp.defCompFun F G = HasCompFun.defCompFun F G)

namespace HasLinearFunOpEq

  def std (U : Universe) [HasEmbeddedFunctors U] [HasLinearFunOp U] :=
  HasLinearFunOpEq.mk (U := U)
                      (hasIdFun := HasLinearFunOp.hasIdFun) (hasCompFun := HasLinearFunOp.hasCompFun)
                      (λ _ => rfl) (λ _ _ => rfl)

  variable {U : Universe} [HasEmbeddedFunctors U] [HasLinearFunOp U] [HasIdFun U] [HasCompFun U U U U U]
           [HasLinearFunOpEq U]

  theorem idFunEq (α : U) : HasLinearFunOp.idFun α = HasIdFun.idFun α :=
  congrArg HasFunctors.fromDefPi (defIdFunEq α)

  theorem compFunEq {α β γ : U} (F : α ⟶ β) (G : β ⟶ γ) : HasLinearFunOp.compFun F G = HasCompFun.compFun F G :=
  congrArg HasFunctors.fromDefPi (defCompFunEq F G)

end HasLinearFunOpEq



class HasSubLinearFunOp (U : Universe) [HasEmbeddedFunctors U] where
(defConstFun    (α : U) {β : U} (c : β) : α ⟶[Function.const ⌈α⌉ c] β)
(defConstFunFun (α β : U)               : β ⟶[λ c => defConstFun α c] (α ⟶ β))

namespace HasSubLinearFunOp

  variable {U : Universe} [HasEmbeddedFunctors U] [HasSubLinearFunOp U]

  def hasConstFun : HasConstFun U U := ⟨defConstFun⟩

  @[reducible] def constFun (α : U) {β : U} (c : β) : α ⟶ β := defConstFun α c
  @[reducible] def constFunFun (α β : U) : β ⟶ (α ⟶ β) := defConstFunFun α β

end HasSubLinearFunOp

class HasSubLinearFunOpEq (U : Universe) [HasEmbeddedFunctors U] [HasSubLinearFunOp U]
                          [hasConstFun : HasConstFun U U] where
(defConstFunEq (α : U) {β : U} (c : β) : HasSubLinearFunOp.defConstFun α c = HasConstFun.defConstFun α c)

namespace HasSubLinearFunOpEq

  def std (U : Universe) [HasEmbeddedFunctors U] [HasSubLinearFunOp U] :
    HasSubLinearFunOpEq U (hasConstFun := HasSubLinearFunOp.hasConstFun) :=
  HasSubLinearFunOpEq.mk (hasConstFun := HasSubLinearFunOp.hasConstFun)
                         (λ _ {_} _ => rfl)

  variable {U : Universe} [HasEmbeddedFunctors U] [HasSubLinearFunOp U] [HasConstFun U U]
           [HasSubLinearFunOpEq U]

  theorem constFunEq (α : U) {β : U} (c : β) : HasSubLinearFunOp.constFun α c = HasConstFun.constFun α c :=
  congrArg HasFunctors.fromDefPi (defConstFunEq α c)

end HasSubLinearFunOpEq

class HasAffineFunOp (U : Universe) [HasEmbeddedFunctors U] extends HasLinearFunOp U, HasSubLinearFunOp U



class HasNonLinearFunOp (U : Universe) [HasEmbeddedFunctors U] where
(defDupFun    {α β : U} (F : α ⟶ α ⟶ β) : α ⟶[λ a => F a a] β)
(defDupFunFun (α β : U)                 : (α ⟶ α ⟶ β) ⟶[λ F => defDupFun F] (α ⟶ β))

namespace HasNonLinearFunOp

  variable {U : Universe} [HasEmbeddedFunctors U] [HasNonLinearFunOp U]

  @[reducible] def dupFun {α β : U} (F : α ⟶ α ⟶ β) : α ⟶ β := defDupFun F
  @[reducible] def dupFunFun (α β : U) : (α ⟶ α ⟶ β) ⟶ (α ⟶ β) := defDupFunFun α β

end HasNonLinearFunOp

class HasFullFunOp (U : Universe) [HasEmbeddedFunctors U] extends HasAffineFunOp U, HasNonLinearFunOp U



class HasFunOp (U : Universe.{u}) extends HasEmbeddedFunctors U, HasFullFunOp U



class HasCompFunProp (U V W : Universe) [HasProperties U V] [HasProperties V W] [h : HasProperties U W]
                     [HasFunctoriality U V] where
(compIsProp {α : U} {β : V} (F : α ⟶' β) (P : HasProperties.Property β W) : h.IsProp (λ a => P (F a)))
(compConstEq {α : U} {β : V} (F : α ⟶' β) (γ : W) : compIsProp F (HasProperties.constProp β γ) = h.constIsProp α γ)

namespace HasCompFunProp

  variable {U V W : Universe} [HasProperties U V] [HasProperties V W] [HasProperties U W]
           [HasFunctoriality U V] [HasFunctoriality V W] [HasFunctoriality U W]
           [h : HasCompFunProp U V W]

  theorem compConstEq' {α : U} {β : V} {γ : W} (F : α ⟶' β) (G : β ⟶' γ) :
    (Π[λ a => G (F a)] ⟨h.compIsProp F (HasProperties.constProp β γ)⟩) = (α ⟶[λ a => G (F a)] γ) :=
  h.compConstEq F γ ▸ rfl

end HasCompFunProp

class HasCompPi' (U V W : Universe) [HasProperties U V] [HasProperties V W] [HasProperties U W]
                 [HasFunctoriality U V] [HasFunctoriality V W] [HasFunctoriality U W]
                 [HasCompFunProp U V W] [HasCompFun' U V W] where
(defCompPi {α : U} {β : V} {P : HasProperties.Property β W} (F : α ⟶' β) (G : Π' P) :
   Π[λ a => G (F a)] ⟨HasCompFunProp.compIsProp F P⟩)
(defCompPiFunEq {α : U} {β : V} {γ : W} (F : α ⟶' β) (G : β ⟶' γ) :
   HasCompFunProp.compConstEq' F G ▸ defCompPi F G = HasCompFun'.defCompFun F G)

namespace HasCompPi'

  variable {U V W : Universe} [HasProperties U V] [HasProperties V W] [HasProperties U W]
           [HasFunctoriality U V] [HasFunctoriality V W] [HasFunctoriality U W]
           [HasCompFunProp U V W] [HasCompFun' U V W] [HasCompPi' U V W]

  @[reducible] def compPi' {α : U} {β : V} {P : HasProperties.Property β W} (F : α ⟶' β) (G : Π' P) :
    Π' ⟨HasCompFunProp.compIsProp F P⟩ :=
  defCompPi F G

end HasCompPi'

class HasCompPi (U V W X Y : Universe) [HasFunctors U V X] [HasFunctors V W Y]
                [HasProperties U W] [HasFunctoriality U W] [HasCompFunProp U V W]
                [HasCompFun U V W X Y] where
(defCompPi {α : U} {β : V} {P : HasProperties.Property β W} (F : α ⟶ β) (G : Π P) :
   Π[λ a => G (F a)] ⟨HasCompFunProp.compIsProp (HasFunctors.toExternal F) P⟩)
(defCompPiFunEq {α : U} {β : V} {γ : W} (F : α ⟶ β) (G : β ⟶ γ) :
   HasCompFunProp.compConstEq' (HasFunctors.toExternal F) (HasFunctors.toExternal G) ▸ defCompPi F G = HasCompFun.defCompFun F G)

namespace HasCompPi

  variable {U V W X Y Z : Universe} [HasFunctors U V X] [HasFunctors V W Y] [HasFunctors U W Z]
           [HasCompFunProp U V W] [HasCompFun U V W X Y] [HasCompPi U V W X Y]

  @[reducible] def compPi {α : U} {β : V} {P : HasProperties.Property β W} (F : α ⟶ β) (G : Π P) :
    Π ⟨HasCompFunProp.compIsProp (HasFunctors.toExternal F) P⟩ :=
  defCompPi F G

  def defCompPiFun {α : U} {β : V} {γ : W} (F : α ⟶ β) (G : β ⟶ γ) : α ⟶[λ a => G (F a)] γ  :=
  HasCompFunProp.compConstEq' (HasFunctors.toExternal F) (HasFunctors.toExternal G) ▸ defCompPi F G

  @[reducible] def compPiFun {α : U} {β : V} {γ : W} (F : α ⟶ β) (G : β ⟶ γ) : α ⟶ γ  :=
  defCompPiFun F G

  theorem compPiFunEq {α : U} {β : V} {γ : W} (F : α ⟶ β) (G : β ⟶ γ) : compPiFun F G = HasCompFun.compFun F G :=
  congrArg HasFunctors.fromDefPi (defCompPiFunEq F G)

  -- TODO
  --instance hasCompPi' : HasCompPi' U V W :=
  --⟨λ F G => HasFunctors.toFromExternal F ▸
  --          HasFunctoriality.castDefPi (defCompPi (HasFunctors.fromExternal F) (HasFunctors.fromExternal G))
  --                                     (λ _ => by simp; rfl),
  -- λ F G => HasFunctors.toFromExternal F ▸
  --          HasFunctors.toFromExternal G ▸
  --          defCompPiFunEq (HasFunctors.fromExternal F) (HasFunctors.fromExternal G)⟩

end HasCompPi



class HasAppPi (U : Universe) [HasEmbeddedFunctors U] [HasLinearFunOp U] where
(defAppPi {α : U} (a : α) (P : HasProperties.Property α U) : (Π P) ⟶[λ F => F a] (P a))
(defAppPiFunEq {α : U} (a : α) (β : U) : defAppPi a (HasProperties.constProp α β) = HasLinearFunOp.defAppFun a β)

namespace HasAppPi

  variable {U : Universe} [HasEmbeddedFunctors U] [HasLinearFunOp U] [HasAppPi U]

  @[reducible] def appPi {α : U} (a : α) (P : HasProperties.Property α U) : (Π P) ⟶ P a := defAppPi a P

  theorem appPiFunEq {α : U} (a : α) (β : U) : appPi a (HasProperties.constProp α β) = HasLinearFunOp.appFun a β :=
  congrArg HasFunctors.fromDefPi (defAppPiFunEq a β)

end HasAppPi



class HasDupPi (U : Universe) [HasEmbeddedFunctors U] [HasNonLinearFunOp U] where
(defDupPi    {α : U} {P : HasProperties.Property α U} (F : α ⟶ Π P) : Π[λ a => F a a] P)
(defDupPiFun {α : U} (P : HasProperties.Property α U)               : (α ⟶ Π P) ⟶[λ F => defDupPi F] (Π P))
(defDupPiFunEq {α β : U} (F : α ⟶ α ⟶ β) : defDupPi F = HasNonLinearFunOp.defDupFun F)
(defDupPiFunFunEq (α β : U) :
   funext (λ F => congrArg HasFunctors.fromDefPi (defDupPiFunEq F)) ▸ defDupPiFun (HasProperties.constProp α β) =
   HasNonLinearFunOp.defDupFunFun α β)

namespace HasDupPi

  variable {U : Universe} [HasEmbeddedFunctors U] [HasNonLinearFunOp U] [HasDupPi U]

  def dupPi {α : U} {P : HasProperties.Property α U} (F : α ⟶ Π P) : Π P := defDupPi F
  def dupPiFun {α : U} (P : HasProperties.Property α U) : (α ⟶ Π P) ⟶ (Π P) := defDupPiFun P

  theorem dupPiFunEq {α β : U} (F : α ⟶ α ⟶ β) : dupPi F = HasNonLinearFunOp.dupFun F :=
  congrArg HasFunctors.fromDefPi (defDupPiFunEq F)

  -- TODO: Can this be made to work?
  --theorem dupPiFunFunEq (α β : U) : dupPiFun (HasProperties.constProp α β) = HasNonLinearFunOp.dupFunFun α β :=
  --Eq.simp_rec_prop (congrArg HasFunctors.fromDefPi (defDupPiFunFunEq α β))

end HasDupPi
