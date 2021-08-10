import UniverseAbstractions.Axioms.Universes



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w



-- We usually want a `U : Universe` to have some concept of "functors" that map instances. Here, we
-- need to reconcile three conflicting requirements:
--
-- * We usually want a functor `F : α ⟶ β` with `α β : U` to be an instance of `U`, so that we can
--   define e.g. functors returning functors without having to specify any additional assumptions.
--   E.g. if `U` is the universe of categories, `α ⟶ β` is the functor category from `α` to `β`.
--
-- * However, in some cases we have a more general concept of a functor `α ⟶' β` where `α` and `β`
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
-- `α : U`, `β : V` | `F : α ⟶[f] β` | `F a` defined as `f a`.
--                  | `F : α ⟶' β`   | Bundled version of the above; therefore e.g. `(idFun α) a`
--                  |                | (see below) is definitionally equal to `a`.
-- `α β : U`        | `F : α ⟶ β`    | An instance of `U`; therefore `F a` cannot be definitionally
--                  |                | equal to anything if `U` is arbitrary. In particular, e.g.
--                  |                | `(idFun α) a = a` not definitionally, but `by simp` (more
--                  |                | specifically, `fromDefFun.eff`).



class HasFunctoriality {U : Universe.{u}} {V : Universe.{v}} (α : U) (β : V) : Sort (max u v (w + 1)) where
(IsFun : (α → β) → Sort w)

namespace HasFunctoriality

  def DefFun {U : Universe.{u}} {V : Universe.{v}} (α : U) (β : V) [h : HasFunctoriality.{u, v, w} α β] (f : α → β) := h.IsFun f
  notation:20 α:21 " ⟶[" f:0 "] " β:21 => HasFunctoriality.DefFun α β f

  structure BundledFunctor {U : Universe.{u}} {V : Universe.{v}} (α : U) (β : V) [HasFunctoriality.{u, v, w} α β] :
    Sort (max 1 u v w) where
  (f : α → β)
  (F : α ⟶[f] β)

  infixr:20 " ⟶' " => HasFunctoriality.BundledFunctor

  variable {U : Universe.{u}} {V : Universe.{v}} {α : U} {β : V} [HasFunctoriality.{u, v, w} α β]

  instance coeDefFun (f : α → β) : CoeFun (α ⟶[f] β) (λ _ => α → β) := ⟨λ _ => f⟩
  instance coeFun                : CoeFun (α ⟶' β)   (λ _ => α → β) := ⟨BundledFunctor.f⟩

  def toDefFun               (F : α ⟶' β)   : α ⟶[F.f] β := F.F
  def fromDefFun {f : α → β} (F : α ⟶[f] β) : α ⟶'     β := ⟨f, F⟩

  def castDefFun {f f' : α → β} (F : α ⟶[f] β) (h : ∀ a, f a = f' a) : α ⟶[f'] β :=
  have h₁ : f = f' := funext h;
  h₁ ▸ F

  @[simp] theorem fromCastDefFun {f f' : α → β} (F : α ⟶[f] β) (h : ∀ a, f a = f' a) :
    fromDefFun (castDefFun F h) = fromDefFun F :=
  have h₁ : f = f' := funext h;
  by subst h₁; rfl

  def toDefFun' (F : α ⟶' β) {f : α → β} (h : ∀ a, F a = f a) : α ⟶[f] β :=
  castDefFun (toDefFun F) h

  instance (F : α ⟶' β) : CoeDep ⌈α ⟶' β⌉   F (α ⟶[F.F] β) := ⟨toDefFun F⟩
  instance (f : α →  β) : Coe    (α ⟶[f] β)   ⌈α ⟶' β⌉     := ⟨fromDefFun⟩

  @[simp] theorem toDefFun.eff               (F : α ⟶' β)   (a : α) : (toDefFun   F) a = F a := rfl
  @[simp] theorem fromDefFun.eff {f : α → β} (F : α ⟶[f] β) (a : α) : (fromDefFun F) a = F a := rfl

  -- Marking this `@[simp]` causes a huge performance hit. I don't understand why.
  theorem toDefFun'.eff (F : α ⟶' β) {f : α → β} (h : ∀ a, F a = f a) (a : α) : (toDefFun' F h) a = F a :=
  Eq.symm (h a)

  @[simp] theorem fromToDefFun             (F : α ⟶' β)   : fromDefFun (toDefFun F) = F :=
  match F with | ⟨_, _⟩ => rfl
  @[simp] theorem toFromDefFun {f : α → β} (F : α ⟶[f] β) : toDefFun (fromDefFun F) = F := rfl

  @[simp] theorem fromToDefFun' (F : α ⟶' β) {f : α → β} (h : ∀ a, F a = f a) : fromDefFun (toDefFun' F h) = F :=
  Eq.trans (fromCastDefFun (toDefFun F) h) (fromToDefFun F)

  @[simp] theorem toFromDefFun' {f f' : α → β} (F : α ⟶[f] β) (h : ∀ a, f a = f' a) :
    toDefFun' (fromDefFun F) h = castDefFun F h :=
  rfl

end HasFunctoriality



class HasIdFun {U : Universe} (α : U) [HasFunctoriality α α] where
(defIdFun : α ⟶[id] α)

namespace HasIdFun

  variable {U : Universe} (α : U) [HasFunctoriality α α] [HasIdFun α]

  def idFun : α ⟶' α := HasFunctoriality.fromDefFun defIdFun

end HasIdFun

class HasConstFun {U V : Universe} (α : U) (β : V) [HasFunctoriality α β] where
(defConstFun (c : β) : α ⟶[Function.const ⌈α⌉ c] β)

namespace HasConstFun

  variable {U V : Universe} (α : U) {β : V} [HasFunctoriality α β] [HasConstFun α β]

  def constFun (c : β) : α ⟶' β := HasFunctoriality.fromDefFun (defConstFun c)

end HasConstFun

class HasCompFun {U V W : Universe} (α : U) (β : V) (γ : W) [HasFunctoriality α β] [HasFunctoriality β γ] [HasFunctoriality α γ] where
(defCompFun (F : α ⟶' β) (G : β ⟶' γ) : α ⟶[λ a => G (F a)] γ)

namespace HasCompFun

  variable {U V W : Universe} {α : U} {β : V} {γ : W} [HasFunctoriality α β] [HasFunctoriality β γ] [HasFunctoriality α γ] [HasCompFun α β γ]

  def compFun (F : α ⟶' β) (G : β ⟶' γ) : α ⟶' γ := HasFunctoriality.fromDefFun (defCompFun F G)

  @[reducible] def revCompFun (G : β ⟶' γ) (F : α ⟶' β) := compFun F G
  infixr:90 " ⊙' " => HasCompFun.revCompFun

end HasCompFun



class HasEmbeddedFunctor {U : Universe.{u}} (α β : U) : Type (max u w) where
[hFun  : HasFunctoriality.{u, u, w} α β]
[hType : HasEmbeddedType.{u, max 1 u w} U (α ⟶' β)]

class HasEmbeddedFunctors (U : Universe.{u}) : Type (max u w) where
[hasFun (α β : U) : HasEmbeddedFunctor.{u, w} α β]

namespace HasEmbeddedFunctors

  variable {U : Universe} [h : HasEmbeddedFunctors U]

  instance hasFunctoriality (α β : U) : HasFunctoriality α β       := (h.hasFun α β).hFun
  instance hasEmbeddedType  (α β : U) : HasEmbeddedType U (α ⟶' β) := (h.hasFun α β).hType

  def Fun (α β : U) : U := (h.hasFun α β).hType.α
  infixr:20 " ⟶ " => HasEmbeddedFunctors.Fun

  def toExternal   {α β : U} (F : α ⟶  β) : α ⟶' β := HasEmbeddedType.toExternal   U F
  def fromExternal {α β : U} (F : α ⟶' β) : α ⟶  β := HasEmbeddedType.fromExternal U F

  def funCoe {α β : U} (F : α ⟶ β) : α → β := toExternal F
  instance coeFun (α β : U) : CoeFun ⌈α ⟶ β⌉ (λ _ => α → β) := ⟨funCoe⟩

  @[simp] theorem fromToExternal {α β : U} (F : α ⟶ β)  : fromExternal (toExternal F) = F := HasEmbeddedType.fromToExternal U F
  @[simp] theorem toFromExternal {α β : U} (F : α ⟶' β) : toExternal (fromExternal F) = F := HasEmbeddedType.toFromExternal U F

  @[simp] theorem toExternal.eff   {α β : U} (F : α ⟶ β)  (a : α) : (toExternal   F) a = F a := rfl
  @[simp] theorem fromExternal.eff {α β : U} (F : α ⟶' β) (a : α) : (fromExternal F) a = F a :=
  congrFun (congrArg HasFunctoriality.BundledFunctor.f (toFromExternal F)) a

  @[reducible] def DefFun (α β : U) (f : α → β) := HasFunctoriality.DefFun α β f

  variable {α β : U}

  instance coeDefFun (f : α → β) : CoeFun (α ⟶[f] β) (λ _ => α → β) := ⟨λ _ => f⟩

  def toDefFun               (F : α ⟶ β)    : α ⟶[funCoe F] β := HasFunctoriality.toDefFun (toExternal F)
  def fromDefFun {f : α → β} (F : α ⟶[f] β) : α ⟶ β           := fromExternal (HasFunctoriality.fromDefFun F)

  def toDefFun' (F : α ⟶ β) {f : α → β} (h : ∀ a, F a = f a) : α ⟶[f] β :=
  HasFunctoriality.toDefFun' (toExternal F) h
  infix:60 " ◄ " => HasEmbeddedFunctors.toDefFun'

  instance (F : α ⟶ β) : CoeDep ⌈α ⟶ β⌉    F (α ⟶[funCoe F] β) := ⟨toDefFun F⟩
  instance (f : α → β) : Coe    (α ⟶[f] β)   ⌈α ⟶ β⌉           := ⟨fromDefFun⟩

  def castDefFun {f f' : α → β} (F : α ⟶[f] β) (h : ∀ a, f a = f' a) : α ⟶[f'] β :=
  HasFunctoriality.castDefFun F h

  @[simp] theorem fromCastDefFun {f f' : α → β} (F : α ⟶[f] β) (h : ∀ a, f a = f' a) :
    fromDefFun (castDefFun F h) = fromDefFun F :=
  congrArg fromExternal (HasFunctoriality.fromCastDefFun F h)

  -- Marking this `@[simp]` causes a huge performance hit. I don't understand why.
  theorem toDefFun'.eff (F : α ⟶ β) {f : α → β} (h : ∀ a, F a = f a) (a : α) : (toDefFun' F h) a = F a :=
  Eq.symm (h a)

  @[simp] theorem toDefFun.eff               (F : α ⟶ β)    (a : α) : (toDefFun   F) a = F a := rfl
  @[simp] theorem fromDefFun.eff {f : α → β} (F : α ⟶[f] β) (a : α) : (fromDefFun F) a = F a :=
  fromExternal.eff (HasFunctoriality.fromDefFun F) a

  @[simp] theorem fromToDefFun (F : α ⟶ β) : fromDefFun (toDefFun F) = F :=
  Eq.trans (congrArg fromExternal (HasFunctoriality.fromToDefFun (toExternal F))) (fromToExternal F)

  @[simp] theorem fromToDefFun' (F : α ⟶ β) {f : α → β} (h : ∀ a, F a = f a) : fromDefFun (toDefFun' F h) = F :=
  Eq.trans (congrArg fromExternal (HasFunctoriality.fromToDefFun' (toExternal F) h)) (fromToExternal F)

  -- This is annoying to prove, and we don't need it at the moment.
  --@[simp] theorem toFromDefFun' {f : α → β} (F : α ⟶[f] β) : toDefFun' (fromDefFun F) (fromDefFun.eff F) = F := sorry

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

  instance (α : U) : HasIdFun α := ⟨defIdFun α⟩

  @[reducible] def idFun (α : U) : α ⟶ α := defIdFun α

  @[reducible] def appFun {α : U} (a : α) (β : U) : (α ⟶ β) ⟶ β := defAppFun a β
  @[reducible] def appFunFun (α β : U) : α ⟶ (α ⟶ β) ⟶ β := defAppFunFun α β

  instance (α β γ : U) : HasCompFun α β γ :=
  ⟨λ F G => HasEmbeddedFunctors.castDefFun (defCompFun (HasEmbeddedFunctors.fromExternal F)
                                                       (HasEmbeddedFunctors.fromExternal G))
                                           (λ _ => by simp)⟩

  @[reducible] def compFun {α β γ : U} (F : α ⟶ β) (G : β ⟶ γ) : α ⟶ γ := defCompFun F G
  @[reducible] def compFunFun {α β : U} (F : α ⟶ β) (γ : U) : (β ⟶ γ) ⟶ (α ⟶ γ) := defCompFunFun F γ
  @[reducible] def compFunFunFun (α β γ : U) : (α ⟶ β) ⟶ (β ⟶ γ) ⟶ (α ⟶ γ) := defCompFunFunFun α β γ

  @[reducible] def revCompFun {α β γ : U} (G : β ⟶ γ) (F : α ⟶ β) : α ⟶ γ := compFun F G
  infixr:90 " ⊙ " => HasLinearFunOp.revCompFun

end HasLinearFunOp



class HasSubLinearFunOp (U : Universe) [HasEmbeddedFunctors U] where
(defConstFun    (α : U) {β : U} (c : β) : α ⟶[Function.const ⌈α⌉ c] β)
(defConstFunFun (α β : U)               : β ⟶[λ c => defConstFun α c] (α ⟶ β))

namespace HasSubLinearFunOp

  variable {U : Universe} [HasEmbeddedFunctors U] [HasSubLinearFunOp U]

  instance (α β : U) : HasConstFun α β := ⟨λ c => defConstFun α c⟩

  @[reducible] def constFun (α : U) {β : U} (c : β) : α ⟶ β := defConstFun α c
  @[reducible] def constFunFun (α β : U) : β ⟶ (α ⟶ β) := defConstFunFun α β

end HasSubLinearFunOp

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
