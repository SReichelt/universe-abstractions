import UniverseAbstractions.Axioms.Universes



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w w'



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
-- `F : α ⟶' β`   | Bundled version of the above; therefore e.g. `(HasIdFun.idFun' α) a` (see
--                | below) is definitionally equal to `a`.
-- `F : α ⟶ β`    | An instance of a universe `W`; therefore we cannot ensure that `F a` is
--                | definitionally equal to anything if `W` is arbitrary.
--                | In particular, e.g. `(HasLinearFunOp.idFun α) a = a` not definitionally, but
--                | `by simp` (more specifically, `HasFunctor.fromDefFun.eff`).



class HasFunctoriality (U : Universe.{u}) (V : Universe.{v}) : Type (max u v w) where
(IsFun {α : U} {β : V} : (α → β) → Sort w)

namespace HasFunctoriality

  def DefFun {U : Universe.{u}} {V : Universe.{v}} [h : HasFunctoriality.{u, v, w} U V] (α : U) (β : V)
             (f : α → β) :=
  h.IsFun f
  notation:20 α:21 " ⟶[" f:0 "] " β:21 => HasFunctoriality.DefFun α β f

  structure Fun {U : Universe.{u}} {V : Universe.{v}} [HasFunctoriality.{u, v, w} U V] (α : U) (β : V) :
    Sort (max 1 u v w) where
  (f : α → β)
  (F : α ⟶[f] β)

  infixr:20 " ⟶' " => HasFunctoriality.Fun

  variable {U : Universe.{u}} {V : Universe.{v}} [HasFunctoriality.{u, v, w} U V] {α : U} {β : V}

  instance coeDefFun (f : α → β) : CoeFun (α ⟶[f] β) (λ _ => α → β) := ⟨λ _ => f⟩
  instance coeFun                : CoeFun (α ⟶' β)   (λ _ => α → β) := ⟨Fun.f⟩

  def toDefFun               (F : α ⟶' β)   : α ⟶[F.f] β := F.F
  def fromDefFun {f : α → β} (F : α ⟶[f] β) : α ⟶'     β := ⟨f, F⟩

  instance (F : α ⟶' β) : CoeDep (α ⟶' β)   F (α ⟶[F.F] β) := ⟨toDefFun F⟩
  instance {f : α →  β} : Coe    (α ⟶[f] β)   (α ⟶' β)     := ⟨fromDefFun⟩

  theorem DefFun.ext {f f' : α → β} (h : ∀ a, f a = f' a) : (α ⟶[f] β) = (α ⟶[f'] β) :=
  congrArg (DefFun α β) (funext h)

  def castDefFun {f f' : α → β} (F : α ⟶[f] β) (h : ∀ a, f a = f' a) : α ⟶[f'] β :=
  cast (DefFun.ext h) F

  @[simp] theorem fromCastDefFun {f f' : α → β} (F : α ⟶[f] β) (h : ∀ a, f a = f' a) :
    fromDefFun (castDefFun F h) = fromDefFun F :=
  have h₁ : f = f' := funext h;
  by subst h₁; rfl

  @[simp] theorem castCastDefFun {f f' : α → β} (F : α ⟶[f] β) (h : ∀ a, f a = f' a) :
    castDefFun (castDefFun F h) (λ a => Eq.symm (h a)) = F :=
  have h₁ : f = f' := funext h;
  by subst h₁; rfl

  @[simp] theorem toDefFun.eff               (F : α ⟶' β)   (a : α) : (toDefFun   F) a = F a := rfl
  @[simp] theorem fromDefFun.eff {f : α → β} (F : α ⟶[f] β) (a : α) : (fromDefFun F) a = F a := rfl

  @[simp] theorem fromToDefFun             (F : α ⟶' β)   : fromDefFun (toDefFun F) = F :=
  match F with | ⟨_, _⟩ => rfl
  @[simp] theorem toFromDefFun {f : α → β} (F : α ⟶[f] β) : toDefFun (fromDefFun F) = F := rfl

  theorem Fun.Eq.eff {F F' : α ⟶' β} (h : F = F') (a : α) : F a = F' a := h ▸ rfl

  theorem toDefFun.congr {F F' : α ⟶' β} (h : F = F') :
    castDefFun (toDefFun F) (Fun.Eq.eff h) = toDefFun F' :=
  by subst h; rfl

end HasFunctoriality



class HasFunctors (U : Universe.{u}) (V : Universe.{v}) (X : outParam Universe.{w})
  extends HasFunctoriality.{u, v, w'} U V : Type (max u v w w') where
[embed (α : U) (β : V) : HasEmbeddedType.{w, max 1 u v w'} X (α ⟶' β)]

namespace HasFunctors

  variable {U V X : Universe} [h : HasFunctors U V X]

  instance hasEmbeddedType (α : U) (β : V) : HasEmbeddedType X (α ⟶' β) := h.embed α β

  @[reducible] def DefFun (α : U) (β : V) (f : α → β) := HasFunctoriality.DefFun α β f

  def Fun (α : U) (β : V) : X := HasEmbeddedType.EmbeddedType X (α ⟶' β)
  infixr:20 " ⟶ " => HasFunctors.Fun

  variable {α : U} {β : V}

  def toExternal   (F : α ⟶  β) : α ⟶' β := HasEmbeddedType.toExternal   X F
  def fromExternal (F : α ⟶' β) : α ⟶  β := HasEmbeddedType.fromExternal X F

  def funCoe (F : α ⟶ β) : α → β := (toExternal F).f
  instance coeFun : CoeFun ⌈α ⟶ β⌉ (λ _ => α → β) := ⟨funCoe⟩

  @[simp] theorem fromToExternal (F : α ⟶  β) : fromExternal (toExternal F) = F := HasEmbeddedType.fromToExternal X F
  @[simp] theorem toFromExternal (F : α ⟶' β) : toExternal (fromExternal F) = F := HasEmbeddedType.toFromExternal X F

  @[simp] theorem toExternal.eff   (F : α ⟶  β) (a : α) : (toExternal   F) a = F a := rfl
  @[simp] theorem fromExternal.eff (F : α ⟶' β) (a : α) : (fromExternal F) a = F a :=
  congrFun (congrArg HasFunctoriality.Fun.f (toFromExternal F)) a

  def toDefFun               (F : α ⟶ β)    : α ⟶[funCoe F] β := HasFunctoriality.toDefFun (toExternal F)
  def fromDefFun {f : α → β} (F : α ⟶[f] β) : α ⟶ β           := fromExternal (HasFunctoriality.fromDefFun F)
  instance {f : α → β} : Coe (α ⟶[f] β) ⌈α ⟶ β⌉ := ⟨fromDefFun⟩

  @[simp] theorem fromCastDefFun {f f' : α → β} (F : α ⟶[f] β) (h : ∀ a, f a = f' a) :
    fromDefFun (HasFunctoriality.castDefFun F h) = fromDefFun F :=
  congrArg fromExternal (HasFunctoriality.fromCastDefFun F h)

  def toDefFun' (F : α ⟶ β) {f : α → β} (h : ∀ a, F a = f a) : α ⟶[f] β :=
  HasFunctoriality.castDefFun (toDefFun F) h
  infix:60 " ◄ " => HasFunctors.toDefFun'

  -- Marking this `@[simp]` causes a huge performance hit. I don't understand why.
  theorem toDefFun'.eff (F : α ⟶ β) {f : α → β} (h : ∀ a, F a = f a) (a : α) : (toDefFun' F h) a = F a :=
  Eq.symm (h a)

  @[simp] theorem toDefFun.eff               (F : α ⟶ β)    (a : α) : (toDefFun   F) a = F a := rfl
  @[simp] theorem fromDefFun.eff {f : α → β} (F : α ⟶[f] β) (a : α) : (fromDefFun F) a = F a :=
  fromExternal.eff (HasFunctoriality.fromDefFun F) a

  @[simp] theorem fromToDefFun (F : α ⟶ β) : fromDefFun (toDefFun F) = F :=
  Eq.trans (congrArg fromExternal (HasFunctoriality.fromToDefFun (toExternal F))) (fromToExternal F)

  @[simp] theorem fromToDefFun' (F : α ⟶ β) {f : α → β} (h : ∀ a, F a = f a) : fromDefFun (toDefFun' F h) = F :=
  Eq.trans (fromCastDefFun (toDefFun F) h) (fromToDefFun F)

  @[simp] theorem toFromDefFun' {f : α → β} (F : α ⟶[f] β) : toDefFun' (fromDefFun F) (fromDefFun.eff F) = F :=
  HasFunctoriality.toDefFun.congr (toFromExternal (HasFunctoriality.fromDefFun F))

  theorem toFromDefFun {f : α → β} (F : α ⟶[f] β) : toDefFun (fromDefFun F) ≅ F :=
  heq_of_eqRec_eq _ (toFromDefFun' F)

end HasFunctors



class HasIdFun (U : Universe) [HasFunctoriality U U] where
(defIdFun (α : U) : α ⟶[id] α)

namespace HasIdFun

  @[reducible] def idFun' {U : Universe} [HasFunctoriality U U] [HasIdFun U] (α : U) : α ⟶' α :=
  defIdFun α

  @[reducible] def idFun {U X : Universe} [HasFunctors U U X] [HasIdFun U] (α : U) : α ⟶ α :=
  HasFunctors.fromExternal (idFun' α)

end HasIdFun

class HasConstFun (U V : Universe) [HasFunctoriality U V] where
(defConstFun (α : U) {β : V} (c : β) : α ⟶[Function.const ⌈α⌉ c] β)

namespace HasConstFun

  @[reducible] def constFun' {U V : Universe} [HasFunctoriality U V] [HasConstFun U V] (α : U) {β : V} (c : β) :
    α ⟶' β :=
  defConstFun α c

  @[reducible] def constFun {U V X : Universe} [HasFunctors U V X] [HasConstFun U V] (α : U) {β : V} (c : β) :
    α ⟶ β :=
  HasFunctors.fromExternal (constFun' α c)

end HasConstFun

class HasCompFun' (U V W : Universe) [HasFunctoriality U V] [HasFunctoriality V W] [HasFunctoriality U W] where
(defCompFun {α : U} {β : V} {γ : W} (F : α ⟶' β) (G : β ⟶' γ) : α ⟶[λ a => G (F a)] γ)

namespace HasCompFun'

  variable {U V W : Universe} [HasFunctoriality U V] [HasFunctoriality V W] [HasFunctoriality U W]
           [HasCompFun' U V W]

  @[reducible] def compFun' {α : U} {β : V} {γ : W} (F : α ⟶' β) (G : β ⟶' γ) : α ⟶' γ :=
  defCompFun F G

  @[reducible] def revCompFun' {α : U} {β : V} {γ : W} (G : β ⟶' γ) (F : α ⟶' β) := compFun' F G
  infixr:90 " ⊙' " => HasCompFun'.revCompFun'

end HasCompFun'

class HasCompFun (U V W X Y : Universe) [HasFunctors U V X] [HasFunctors V W Y] [HasFunctoriality U W] where
(defCompFun {α : U} {β : V} {γ : W} (F : α ⟶ β) (G : β ⟶ γ) : α ⟶[λ a => G (F a)] γ)

namespace HasCompFun

  variable {U V W X Y Z : Universe} [HasFunctors U V X] [HasFunctors V W Y] [HasFunctors U W Z]
           [HasCompFun U V W X Y]

  @[reducible] def compFun {α : U} {β : V} {γ : W} (F : α ⟶ β) (G : β ⟶ γ) : α ⟶ γ :=
  defCompFun F G

  @[reducible] def revCompFun {α : U} {β : V} {γ : W} (G : β ⟶ γ) (F : α ⟶ β) := compFun F G

  instance hasCompFun' : HasCompFun' U V W :=
  ⟨λ F G => HasFunctoriality.castDefFun (defCompFun (HasFunctors.fromExternal F) (HasFunctors.fromExternal G))
                                        (λ _ => by simp)⟩

end HasCompFun



class HasEmbeddedFunctors (U : Universe.{u}) extends HasFunctors.{u, u, u, w} U U U : Type (max u w)

namespace HasEmbeddedFunctors

  -- Restricted copies of definitions in `HasFunctors` to help functoriality tactic.

  variable {U : Universe} [HasEmbeddedFunctors U]

  @[reducible] def DefFun (α β : U) (f : α → β) := HasFunctors.DefFun α β f

  @[reducible] def Fun (α β : U) : U := HasFunctors.Fun α β

  variable {α β : U}

  @[reducible] def funCoe (F : α ⟶ β) : α → β := HasFunctors.funCoe F

  @[reducible] def toDefFun               (F : α ⟶ β)    : α ⟶[funCoe F] β := HasFunctors.toDefFun F
  @[reducible] def fromDefFun {f : α → β} (F : α ⟶[f] β) : α ⟶ β           := HasFunctors.fromDefFun F

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
  congrArg HasFunctors.fromDefFun (defIdFunEq α)

  theorem compFunEq {α β γ : U} (F : α ⟶ β) (G : β ⟶ γ) : HasLinearFunOp.compFun F G = HasCompFun.compFun F G :=
  congrArg HasFunctors.fromDefFun (defCompFunEq F G)

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
  congrArg HasFunctors.fromDefFun (defConstFunEq α c)

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
