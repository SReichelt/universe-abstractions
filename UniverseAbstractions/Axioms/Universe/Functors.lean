import UniverseAbstractions.Axioms.Universes



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w w'



-- We usually want a `U : Universe` to have some concept of "functors" that map instances. Here, we
-- need to reconcile three conflicting requirements:
--
-- * We usually want a functor `F : A ⟶ B` with `A B : U` to be an instance of `U`, so that we can
--   define e.g. functors returning functors without having to specify any additional assumptions.
--   E.g. if `U` is the universe of categories, `A ⟶ B` is the functor category from `A` to `B`.
--
-- * However, in some cases we have a more general concept of a functor `A ⟶ B` where `A` and `B`
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
-- `F : A ⟶[f] B` | `F a` defined as `f a`.
-- `F : A ⟶' B`   | Bundled version of the above; therefore e.g. `(HasIdFun.idFun' A) a` (see
--                | below) is definitionally equal to `a`.
-- `F : A ⟶ B`    | An instance of a universe `W`; therefore we cannot ensure that `F a` is
--                | definitionally equal to anything if `W` is arbitrary.
--                | In particular, e.g. `(HasLinearFunOp.idFun A) a = a` not definitionally, but
--                | `by simp` (more specifically, `HasFunctor.fromDefFun.eff`).



class HasFunctoriality (U : Universe.{u}) (V : Universe.{v}) : Type (max u v w) where
(IsFun {A : U} {B : V} : (A → B) → Sort w)

namespace HasFunctoriality

  def DefFun {U : Universe.{u}} {V : Universe.{v}} [h : HasFunctoriality.{u, v, w} U V] (A : U) (B : V)
             (f : A → B) :=
  h.IsFun f
  notation:20 A:21 " ⟶[" f:0 "] " B:21 => HasFunctoriality.DefFun A B f

  structure Fun {U : Universe.{u}} {V : Universe.{v}} [HasFunctoriality.{u, v, w} U V] (A : U) (B : V) :
    Sort (max 1 u v w) where
  (f : A → B)
  (F : A ⟶[f] B)

  infixr:20 " ⟶' " => HasFunctoriality.Fun

  variable {U : Universe.{u}} {V : Universe.{v}} [HasFunctoriality.{u, v, w} U V] {A : U} {B : V}

  instance coeDefFun (f : A → B) : CoeFun (A ⟶[f] B) (λ _ => A → B) := ⟨λ _ => f⟩
  instance coeFun                : CoeFun (A ⟶' B)   (λ _ => A → B) := ⟨Fun.f⟩

  def toDefFun               (F : A ⟶' B)   : A ⟶[F.f] B := F.F
  def fromDefFun {f : A → B} (F : A ⟶[f] B) : A ⟶'     B := ⟨f, F⟩

  instance (F : A ⟶' B) : CoeDep (A ⟶' B)   F (A ⟶[F.F] B) := ⟨toDefFun F⟩
  instance {f : A →  B} : Coe    (A ⟶[f] B)   (A ⟶' B)     := ⟨fromDefFun⟩

  theorem DefFun.ext {f f' : A → B} (h : ∀ a, f a = f' a) : (A ⟶[f] B) = (A ⟶[f'] B) :=
  congrArg (DefFun A B) (funext h)

  def castDefFun {f f' : A → B} (F : A ⟶[f] B) (h : ∀ a, f a = f' a) : A ⟶[f'] B :=
  cast (DefFun.ext h) F

  @[simp] theorem fromCastDefFun {f f' : A → B} (F : A ⟶[f] B) (h : ∀ a, f a = f' a) :
    fromDefFun (castDefFun F h) = fromDefFun F :=
  have h₁ : f = f' := funext h;
  by subst h₁; rfl

  @[simp] theorem castCastDefFun {f f' : A → B} (F : A ⟶[f] B) (h : ∀ a, f a = f' a) :
    castDefFun (castDefFun F h) (λ a => Eq.symm (h a)) = F :=
  have h₁ : f = f' := funext h;
  by subst h₁; rfl

  @[simp] theorem toDefFun.eff               (F : A ⟶' B)   (a : A) : (toDefFun   F) a = F a := rfl
  @[simp] theorem fromDefFun.eff {f : A → B} (F : A ⟶[f] B) (a : A) : (fromDefFun F) a = F a := rfl

  @[simp] theorem fromToDefFun             (F : A ⟶' B)   : fromDefFun (toDefFun F) = F :=
  match F with | ⟨_, _⟩ => rfl
  @[simp] theorem toFromDefFun {f : A → B} (F : A ⟶[f] B) : toDefFun (fromDefFun F) = F := rfl

  theorem Fun.Eq.eff {F F' : A ⟶' B} (h : F = F') (a : A) : F a = F' a := h ▸ rfl

  theorem toDefFun.congr {F F' : A ⟶' B} (h : F = F') :
    castDefFun (toDefFun F) (Fun.Eq.eff h) = toDefFun F' :=
  by subst h; rfl

end HasFunctoriality



class HasFunctors (U : Universe.{u}) (V : Universe.{v}) (UV : outParam Universe.{w})
  extends HasFunctoriality.{u, v, w'} U V : Type (max u v w w') where
[embed (A : U) (B : V) : HasEmbeddedType.{w, max 1 u v w'} UV (A ⟶' B)]

namespace HasFunctors

  variable {U V UV : Universe} [h : HasFunctors U V UV]

  instance hasEmbeddedType (A : U) (B : V) : HasEmbeddedType UV (A ⟶' B) := h.embed A B

  @[reducible] def DefFun (A : U) (B : V) (f : A → B) := HasFunctoriality.DefFun A B f

  def Fun (A : U) (B : V) : UV := HasEmbeddedType.EmbeddedType UV (A ⟶' B)
  infixr:20 " ⟶ " => HasFunctors.Fun

  variable {A : U} {B : V}

  def toExternal   (F : A ⟶  B) : A ⟶' B := HasEmbeddedType.toExternal   UV F
  def fromExternal (F : A ⟶' B) : A ⟶  B := HasEmbeddedType.fromExternal UV F

  def funCoe (F : A ⟶ B) : A → B := (toExternal F).f
  instance coeFun : CoeFun ⌈A ⟶ B⌉ (λ _ => A → B) := ⟨funCoe⟩

  @[simp] theorem fromToExternal (F : A ⟶  B) : fromExternal (toExternal F) = F := HasEmbeddedType.fromToExternal UV F
  @[simp] theorem toFromExternal (F : A ⟶' B) : toExternal (fromExternal F) = F := HasEmbeddedType.toFromExternal UV F

  @[simp] theorem toExternal.eff   (F : A ⟶  B) (a : A) : (toExternal   F) a = F a := rfl
  @[simp] theorem fromExternal.eff (F : A ⟶' B) (a : A) : (fromExternal F) a = F a :=
  congrFun (congrArg HasFunctoriality.Fun.f (toFromExternal F)) a

  def toDefFun               (F : A ⟶ B)    : A ⟶[funCoe F] B := HasFunctoriality.toDefFun (toExternal F)
  def fromDefFun {f : A → B} (F : A ⟶[f] B) : A ⟶ B           := fromExternal (HasFunctoriality.fromDefFun F)
  instance {f : A → B} : Coe (A ⟶[f] B) ⌈A ⟶ B⌉ := ⟨fromDefFun⟩

  @[simp] theorem fromCastDefFun {f f' : A → B} (F : A ⟶[f] B) (h : ∀ a, f a = f' a) :
    fromDefFun (HasFunctoriality.castDefFun F h) = fromDefFun F :=
  congrArg fromExternal (HasFunctoriality.fromCastDefFun F h)

  def toDefFun' (F : A ⟶ B) {f : A → B} (h : ∀ a, F a = f a) : A ⟶[f] B :=
  HasFunctoriality.castDefFun (toDefFun F) h
  infix:60 " ◄ " => HasFunctors.toDefFun'

  -- Marking this `@[simp]` causes a huge performance hit. I don't understand why.
  theorem toDefFun'.eff (F : A ⟶ B) {f : A → B} (h : ∀ a, F a = f a) (a : A) : (toDefFun' F h) a = F a :=
  Eq.symm (h a)

  @[simp] theorem toDefFun.eff               (F : A ⟶ B)    (a : A) : (toDefFun   F) a = F a := rfl
  @[simp] theorem fromDefFun.eff {f : A → B} (F : A ⟶[f] B) (a : A) : (fromDefFun F) a = F a :=
  fromExternal.eff (HasFunctoriality.fromDefFun F) a

  @[simp] theorem fromToDefFun (F : A ⟶ B) : fromDefFun (toDefFun F) = F :=
  Eq.trans (congrArg fromExternal (HasFunctoriality.fromToDefFun (toExternal F))) (fromToExternal F)

  @[simp] theorem fromToDefFun' (F : A ⟶ B) {f : A → B} (h : ∀ a, F a = f a) : fromDefFun (toDefFun' F h) = F :=
  Eq.trans (fromCastDefFun (toDefFun F) h) (fromToDefFun F)

  @[simp] theorem toFromDefFun' {f : A → B} (F : A ⟶[f] B) : toDefFun' (fromDefFun F) (fromDefFun.eff F) = F :=
  HasFunctoriality.toDefFun.congr (toFromExternal (HasFunctoriality.fromDefFun F))

  theorem toFromDefFun {f : A → B} (F : A ⟶[f] B) : toDefFun (fromDefFun F) ≅ F :=
  heq_of_eqRec_eq _ (toFromDefFun' F)

end HasFunctors



class HasIdFun (U : Universe) [HasFunctoriality U U] where
(defIdFun (A : U) : A ⟶[id] A)

namespace HasIdFun

  @[reducible] def idFun' {U : Universe} [HasFunctoriality U U] [HasIdFun U] (A : U) : A ⟶' A :=
  defIdFun A

  @[reducible] def idFun {U UV : Universe} [HasFunctors U U UV] [HasIdFun U] (A : U) : A ⟶ A :=
  HasFunctors.fromExternal (idFun' A)

end HasIdFun

class HasConstFun (U V : Universe) [HasFunctoriality U V] where
(defConstFun (A : U) {B : V} (b : B) : A ⟶[Function.const ⌈A⌉ b] B)

namespace HasConstFun

  @[reducible] def constFun' {U V : Universe} [HasFunctoriality U V] [HasConstFun U V] (A : U) {B : V} (b : B) :
    A ⟶' B :=
  defConstFun A b

  @[reducible] def constFun {U V UV : Universe} [HasFunctors U V UV] [HasConstFun U V] (A : U) {B : V} (b : B) :
    A ⟶ B :=
  HasFunctors.fromExternal (constFun' A b)

end HasConstFun

class HasCompFun' (U V W : Universe) [HasFunctoriality U V] [HasFunctoriality V W] [HasFunctoriality U W] where
(defCompFun {A : U} {B : V} {C : W} (F : A ⟶' B) (G : B ⟶' C) : A ⟶[λ a => G (F a)] C)

namespace HasCompFun'

  variable {U V W : Universe} [HasFunctoriality U V] [HasFunctoriality V W] [HasFunctoriality U W]
           [HasCompFun' U V W]

  @[reducible] def compFun' {A : U} {B : V} {C : W} (F : A ⟶' B) (G : B ⟶' C) : A ⟶' C :=
  defCompFun F G

  @[reducible] def revCompFun' {A : U} {B : V} {C : W} (G : B ⟶' C) (F : A ⟶' B) := compFun' F G
  infixr:90 " ⊙' " => HasCompFun'.revCompFun'

end HasCompFun'

class HasCompFun (U V W UV VW : Universe) [HasFunctors U V UV] [HasFunctors V W VW] [HasFunctoriality U W] where
(defCompFun {A : U} {B : V} {C : W} (F : A ⟶ B) (G : B ⟶ C) : A ⟶[λ a => G (F a)] C)

namespace HasCompFun

  variable {U V W UV VW UW : Universe} [HasFunctors U V UV] [HasFunctors V W VW] [HasFunctors U W UW]
           [HasCompFun U V W UV VW]

  @[reducible] def compFun {A : U} {B : V} {C : W} (F : A ⟶ B) (G : B ⟶ C) : A ⟶ C :=
  defCompFun F G

  @[reducible] def revCompFun {A : U} {B : V} {C : W} (G : B ⟶ C) (F : A ⟶ B) := compFun F G

  instance hasCompFun' : HasCompFun' U V W :=
  ⟨λ F G => HasFunctoriality.castDefFun (defCompFun (HasFunctors.fromExternal F) (HasFunctors.fromExternal G))
                                        (λ _ => by simp)⟩

end HasCompFun



class HasEmbeddedFunctors (U : Universe.{u}) extends HasFunctors.{u, u, u, w} U U U : Type (max u w)

namespace HasEmbeddedFunctors

  -- Restricted copies of definitions in `HasFunctors` to help functoriality tactic.

  variable {U : Universe} [HasEmbeddedFunctors U]

  @[reducible] def DefFun (A B : U) (f : A → B) := HasFunctors.DefFun A B f

  @[reducible] def Fun (A B : U) : U := HasFunctors.Fun A B

  variable {A B : U}

  @[reducible] def funCoe (F : A ⟶ B) : A → B := HasFunctors.funCoe F

  @[reducible] def toDefFun               (F : A ⟶ B)    : A ⟶[funCoe F] B := HasFunctors.toDefFun F
  @[reducible] def fromDefFun {f : A → B} (F : A ⟶[f] B) : A ⟶ B           := HasFunctors.fromDefFun F

  @[reducible] def toDefFun' (F : A ⟶ B) {f : A → B} (h : ∀ a, F a = f a) : A ⟶[f] B := HasFunctors.toDefFun' F h

end HasEmbeddedFunctors



-- The following axioms are equivalent to asserting the existence of five functors with specified
-- behavior, writing `Λ` for a functorial `λ` as defined in `Tactics/Functoriality.lean`:
-- id    : `A ⟶ A,                           Λ a => a`
-- const : `B ⟶ (A ⟶ B),                     Λ c a => c`
-- app   : `A ⟶ (A ⟶ B) ⟶ B,                 Λ a F => F a`
-- dup   : `(A ⟶ A ⟶ B) ⟶ (A ⟶ B),           Λ F a => F a a`
-- comp  : `(A ⟶ B) ⟶ (B ⟶ C) ⟶ (A ⟶ C),     Λ F G a => G (F a)`
--
-- In `DerivedFunctors.lean`, we derive several functors from these, such as
-- swap  : `(A ⟶ B ⟶ C) ⟶ (B ⟶ A ⟶ C),       Λ F b a => F a b`
-- subst : `(A ⟶ B) ⟶ (A ⟶ B ⟶ C) ⟶ (A ⟶ C), Λ F G a => G a (F a)`
--
-- Using these, we can give a general algorithm for proving that a function is functorial, which is
-- implemented as a tactic in `Functoriality.lean`.
--
-- We split the axioms into "linear", "affine", and "full" functor operations, where "linear" and
-- "affine" correspond to linear and affine logic, respectively. That is, linear functors use each
-- bound variable exactly once; affine functors use each variable at most once.



class HasLinearFunOp (U : Universe) [HasEmbeddedFunctors U] where
(defIdFun         (A : U)                             : A ⟶[id] A)
(defAppFun        {A : U} (a : A) (B : U)             : (A ⟶ B) ⟶[λ F => F a] B)
(defAppFunFun     (A B : U)                           : A ⟶[λ a => defAppFun a B] ((A ⟶ B) ⟶ B))
(defCompFun       {A B C : U} (F : A ⟶ B) (G : B ⟶ C) : A ⟶[λ a => G (F a)] C)
(defCompFunFun    {A B : U} (F : A ⟶ B) (C : U)       : (B ⟶ C) ⟶[λ G => defCompFun F G] (A ⟶ C))
(defCompFunFunFun (A B C : U)                         : (A ⟶ B) ⟶[λ F => defCompFunFun F C] ((B ⟶ C) ⟶ (A ⟶ C)))

namespace HasLinearFunOp

  variable {U : Universe} [HasEmbeddedFunctors U] [HasLinearFunOp U]

  instance hasIdFun : HasIdFun U := ⟨defIdFun⟩

  @[reducible] def idFun (A : U) : A ⟶ A := defIdFun A

  @[reducible] def appFun {A : U} (a : A) (B : U) : (A ⟶ B) ⟶ B := defAppFun a B
  @[reducible] def appFunFun (A B : U) : A ⟶ (A ⟶ B) ⟶ B := defAppFunFun A B

  instance hasCompFun : HasCompFun U U U U U := ⟨defCompFun⟩

  @[reducible] def compFun {A B C : U} (F : A ⟶ B) (G : B ⟶ C) : A ⟶ C := defCompFun F G
  @[reducible] def compFunFun {A B : U} (F : A ⟶ B) (C : U) : (B ⟶ C) ⟶ (A ⟶ C) := defCompFunFun F C
  @[reducible] def compFunFunFun (A B C : U) : (A ⟶ B) ⟶ (B ⟶ C) ⟶ (A ⟶ C) := defCompFunFunFun A B C

  @[reducible] def revCompFun {A B C : U} (G : B ⟶ C) (F : A ⟶ B) : A ⟶ C := compFun F G
  infixr:90 " ⊙ " => HasLinearFunOp.revCompFun

end HasLinearFunOp

class HasLinearFunOpEq (U : Universe) [HasEmbeddedFunctors U] [HasLinearFunOp U]
                       [hasIdFun : HasIdFun U] [hasCompFun : HasCompFun U U U U U] where
(defIdFunEq (A : U) : HasLinearFunOp.defIdFun A = HasIdFun.defIdFun A)
(defCompFunEq {A B C : U} (F : A ⟶ B) (G : B ⟶ C) : HasLinearFunOp.defCompFun F G = HasCompFun.defCompFun F G)

namespace HasLinearFunOpEq

  instance std (U : Universe) [HasEmbeddedFunctors U] [HasLinearFunOp U] : HasLinearFunOpEq U :=
  { defIdFunEq   := λ _   => rfl,
    defCompFunEq := λ _ _ => rfl }

  variable {U : Universe} [HasEmbeddedFunctors U] [HasLinearFunOp U] [HasIdFun U] [HasCompFun U U U U U]
           [HasLinearFunOpEq U]

  theorem idFunEq (A : U) : HasLinearFunOp.idFun A = HasIdFun.idFun A :=
  congrArg HasFunctors.fromDefFun (defIdFunEq A)

  theorem compFunEq {A B C : U} (F : A ⟶ B) (G : B ⟶ C) : HasLinearFunOp.compFun F G = HasCompFun.compFun F G :=
  congrArg HasFunctors.fromDefFun (defCompFunEq F G)

end HasLinearFunOpEq



class HasSubLinearFunOp (U : Universe) [HasEmbeddedFunctors U] where
(defConstFun    (A : U) {B : U} (b : B) : A ⟶[Function.const ⌈A⌉ b] B)
(defConstFunFun (A B : U)               : B ⟶[λ b => defConstFun A b] (A ⟶ B))

namespace HasSubLinearFunOp

  variable {U : Universe} [HasEmbeddedFunctors U] [HasSubLinearFunOp U]

  instance hasConstFun : HasConstFun U U := ⟨defConstFun⟩

  @[reducible] def constFun (A : U) {B : U} (b : B) : A ⟶ B := defConstFun A b
  @[reducible] def constFunFun (A B : U) : B ⟶ (A ⟶ B) := defConstFunFun A B

end HasSubLinearFunOp

class HasSubLinearFunOpEq (U : Universe) [HasEmbeddedFunctors U] [HasSubLinearFunOp U]
                          [HasConstFun U U] where
(defConstFunEq (A : U) {B : U} (b : B) : HasSubLinearFunOp.defConstFun A b = HasConstFun.defConstFun A b)

namespace HasSubLinearFunOpEq

  instance std (U : Universe) [HasEmbeddedFunctors U] [HasSubLinearFunOp U] : HasSubLinearFunOpEq U :=
  { defConstFunEq := λ _ {_} _ => rfl }

  variable {U : Universe} [HasEmbeddedFunctors U] [HasSubLinearFunOp U] [HasConstFun U U]
           [HasSubLinearFunOpEq U]

  theorem constFunEq (A : U) {B : U} (b : B) : HasSubLinearFunOp.constFun A b = HasConstFun.constFun A b :=
  congrArg HasFunctors.fromDefFun (defConstFunEq A b)

end HasSubLinearFunOpEq

class HasAffineFunOp (U : Universe) [HasEmbeddedFunctors U] extends HasLinearFunOp U, HasSubLinearFunOp U



class HasNonLinearFunOp (U : Universe) [HasEmbeddedFunctors U] where
(defDupFun    {A B : U} (F : A ⟶ A ⟶ B) : A ⟶[λ a => F a a] B)
(defDupFunFun (A B : U)                 : (A ⟶ A ⟶ B) ⟶[λ F => defDupFun F] (A ⟶ B))

namespace HasNonLinearFunOp

  variable {U : Universe} [HasEmbeddedFunctors U] [HasNonLinearFunOp U]

  @[reducible] def dupFun {A B : U} (F : A ⟶ A ⟶ B) : A ⟶ B := defDupFun F
  @[reducible] def dupFunFun (A B : U) : (A ⟶ A ⟶ B) ⟶ (A ⟶ B) := defDupFunFun A B

end HasNonLinearFunOp

class HasFullFunOp (U : Universe) [HasEmbeddedFunctors U] extends HasAffineFunOp U, HasNonLinearFunOp U



class HasFunOp (U : Universe.{u}) extends HasEmbeddedFunctors U, HasFullFunOp U
