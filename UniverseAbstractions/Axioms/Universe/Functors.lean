import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Relations
import UniverseAbstractions.Axioms.Universe.Identity



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v uv iu iv iuv



-- We want universes to have some concept of "functors" that map instances in ways that respect
-- properties of types, in particular identity. There are a few requirements that make the
-- definition of functors tricky:
--
-- * We usually want a functor `F : A ⟶ B` with `A B : U` to be an instance of `U`, so that we can
--   define e.g. functors returning functors (`F : C ⟶ (A ⟶ B)`) without having to specify any
--   additional assumptions.
--   E.g. if `U` is the universe of categories, `A ⟶ B` is the functor category from `A` to `B`,
--   and `C ⟶ (A ⟶ B)` is the functor category from `C` to the functor category from `A` to `B`.
--
-- * However, in some cases we have a more general concept of a functor `A ⟶ B` where `A` and `B`
--   are not necessarily types of the same universe.
--
-- * Moreover, we want to axiomatically assert the existence of certain functors such as identity
--   and composition, which map instances in specific ways. We want this mapping to be as close to
--   "definitional" as possible, so we include it in the type, written as `A ⟶{f} B`.



class HasFunctors (U : Universe.{u}) (V : Universe.{v}) (UV : outParam Universe.{uv}) :
  Type (max u v uv) where
(Fun                   : U → V → UV)
(apply {A : U} {B : V} : Fun A B → A → B)

namespace HasFunctors

  open MetaRelation

  infixr:20 " ⟶ " => HasFunctors.Fun

  instance coeFun {U V UV : Universe} [HasFunctors U V UV] (A : U) (B : V) :
    CoeFun ⌈A ⟶ B⌉ (λ _ => A → B) :=
  ⟨apply⟩

  variable {U V UV : Universe} [HasFunctors U V UV] [HasIdentity V] 

  structure DefFun (A : U) (B : V) (f : A → B) where
  (F           : A ⟶ B)
  (eff (a : A) : F a ≃ f a)

  notation:20 A:21 " ⟶{" f:0 "} " B:21 => HasFunctors.DefFun A B f

  class IsFunApp (A : outParam ⌈U⌉) {B : V} (b : B) where
  (F : A ⟶ B)
  (a : A)
  (e : F a ≃ b)

  instance (priority := low) IsFunApp.refl {A : U} {B : V} (F : A ⟶ B) (a : A) : IsFunApp A (F a) :=
  { F := F,
    a := a,
    e := HasRefl.refl (F a) }

  variable {A : U} {B : V}
  
  def toDefFun' (F : A ⟶ B) {f : A → B} (h : ∀ a, F a ≃ f a) : A ⟶{f} B := ⟨F, h⟩

  def toDefFun               (F : A ⟶ B)    : A ⟶{apply F} B := toDefFun' F (λ a => HasRefl.refl (F a))
  def fromDefFun {f : A → B} (F : A ⟶{f} B) : A ⟶ B          := F.F

  def byDef {f : A → B} {F : A ⟶{f} B} {a : A} : (fromDefFun F) a ≃ f a := F.eff a

  notation:60 F:61 " ◄ " h:61 => HasFunctors.toDefFun' F (λ _ => h • HasFunctors.byDef)

  @[simp] theorem fromToDefFun' (F : A ⟶ B) {f : A → B} (h : ∀ a, F a ≃ f a) :
    fromDefFun (toDefFun' F h) = F :=
  rfl
  @[simp] theorem fromToDefFun (F : A ⟶ B) : fromDefFun (toDefFun F) = F := rfl

  @[simp] theorem toFromDefFun' {f : A → B} (F : A ⟶{f} B) : toDefFun' (fromDefFun F) F.eff = F :=
  by induction F; rfl

  instance {F : A ⟶ B} : CoeDep ⌈A ⟶ B⌉ F  (A ⟶{apply F} B) := ⟨toDefFun F⟩
  instance {f : A → B} : Coe    (A ⟶{f} B) ⌈A ⟶ B⌉          := ⟨fromDefFun⟩

  def castDefFun {f f' : A → B} (F : A ⟶{f} B) (h : ∀ a, f a ≃ f' a) : A ⟶{f'} B :=
  ⟨F.F, λ a => h a • F.eff a⟩

  @[simp] theorem fromCastDefFun {f f' : A → B} (F : A ⟶{f} B) (h : ∀ a, f a ≃ f' a) :
    fromDefFun (castDefFun F h) = fromDefFun F :=
  rfl

end HasFunctors



class HasCongrArg (U : Universe.{u}) (V : Universe.{v}) {UV : Universe.{uv}} [HasFunctors U V UV]
                  [HasIdentity.{u, iu} U] [HasIdentity.{v, iv} V] : Type (max u v uv iu iv) where
(congrArg {A : U} {B : V} (F : A ⟶ B) {a₁ a₂ : A} : a₁ ≃ a₂ → F a₁ ≃ F a₂)

namespace HasCongrArg

  open MetaRelation.HasTrans HasFunctors

  variable {U V UV : Universe} [HasFunctors U V UV] [HasIdentity U] [HasIdentity V] [HasCongrArg U V]

  def defCongrArg {A : U} {B : V} {f : A → B} (F : A ⟶{f} B) {a₁ a₂ : A} : a₁ ≃ a₂ → f a₁ ≃ f a₂ :=
  λ h => byDef • congrArg (fromDefFun F) h • byDef⁻¹

  def byArgDef {X XU : Universe} [HasFunctors X U XU] {A : X} {B : U} {C : V}
               {f : A → B} {F : A ⟶{f} B} {G : B ⟶ C} {a : A} :
    G ((fromDefFun F) a) ≃ G (f a) :=
  congrArg G byDef

  def byArgDef₂ {W VW X XU : Universe} [HasFunctors V W VW] [HasIdentity W] [HasCongrArg V W]
                [HasFunctors X U XU] {A : X} {B : U} {C : V} {D : W}
                {f : A → B} {F : A ⟶{f} B} {G : B ⟶ C} {H : C ⟶ D} {a : A} :
    H (G ((fromDefFun F) a)) ≃ H (G (f a)) :=
  congrArg H byArgDef

end HasCongrArg

class HasCongrFun (U : Universe.{u}) (V : Universe.{v}) {UV : Universe.{uv}} [HasFunctors U V UV]
                  [HasIdentity.{uv, iuv} UV] [HasIdentity.{v, iv} V] where
(congrFun {A : U} {B : V} {F₁ F₂ : A ⟶ B} (h : F₁ ≃ F₂) (a : A) : F₁ a ≃ F₂ a)

namespace HasCongrFun

  open HasFunctors

  variable {U V UV : Universe} [HasFunctors U V UV] [HasIdentity UV] [HasIdentity V] [HasCongrFun U V]

  def defCongrFun {A : U} {B : V} {f₁ f₂ : A → B} {F₁ : A ⟶{f₁} B} {F₂ : A ⟶{f₂} B}
                  (h : fromDefFun F₁ ≃ fromDefFun F₂) (a : A) :
    f₁ a ≃ f₂ a :=
  byDef • congrFun h a • byDef⁻¹

  def IsExtensional {A : U} {B : V} (F₁ F₂ : A ⟶ B) (h : ∀ a, F₁ a ≃ F₂ a) := F₁ ≃ F₂
  notation:25 F₁:26 " ≃{" h:0 "} " F₂:26 => HasCongrFun.IsExtensional F₁ F₂ h
  notation:25 F₁:26 " ≃{" h:0 " ▻|} " F₂:26 => HasCongrFun.IsExtensional F₁ F₂ (λ _ => h • byDef)

  def IsExtensional' {A : U} {B : V} (F₁ F₂ : A ⟶ B) {f : A → B}
                     (hf₁ : ∀ a, F₁ a ≃ f a) (hf₂ : ∀ a, f a ≃ F₂ a) :=
  IsExtensional F₁ F₂ (λ a => hf₂ a • hf₁ a)
  notation:25 F₁:26 " ≃{▻ " h:0 "} " F₂:26 => HasCongrFun.IsExtensional' F₁ F₂ (λ _ => byDef) h
  notation:25 F₁:26 " ≃{" hf₁:0 " ▻ " h:0 "} " F₂:26 => HasCongrFun.IsExtensional' F₁ F₂ (λ _ => hf₁ • byDef) h

  def IsExtensional'' {A : U} {B : V} (F₁ F₂ : A ⟶ B) {f : A → B}
                      (hf₁ : ∀ a, F₁ a ≃ f a) (hf₂ : ∀ a, F₂ a ≃ f a) :=
  IsExtensional F₁ F₂ (λ a => (hf₂ a)⁻¹ • hf₁ a)
  notation:25 F₁:26 " ≃{" h:0 " ◅} " F₂:26 => HasCongrFun.IsExtensional'' F₁ F₂ h (λ _ => byDef)
  notation:25 F₁:26 " ≃{" h:0 " ◅ " hf₂:0 "} " F₂:26 => HasCongrFun.IsExtensional'' F₁ F₂ h (λ _ => hf₂ • byDef)
  notation:25 F₁:26 " ≃{" hf₁:0 " ▻-◅} " F₂:26 => HasCongrFun.IsExtensional'' F₁ F₂ (λ _ => hf₁ • byDef) (λ _ => byDef)
  notation:25 F₁:26 " ≃{▻-◅ " hf₂:0 "} " F₂:26 => HasCongrFun.IsExtensional'' F₁ F₂ (λ _ => byDef) (λ _ => hf₂ • byDef)
  notation:25 F₁:26 " ≃{" hf₁:0 " ▻-◅ " hf₂:0 "} " F₂:26 => HasCongrFun.IsExtensional'' F₁ F₂ (λ _ => hf₁ • byDef) (λ _ => hf₂ • byDef)

  def IsExtensional''' {A : U} {B : V} (F₁ F₂ : A ⟶ B) {f₁ f₂ : A → B} (h : ∀ a, f₁ a ≃ f₂ a)
                       (hf₁ : ∀ a, F₁ a ≃ f₁ a) (hf₂ : ∀ a, F₂ a ≃ f₂ a) :=
  IsExtensional F₁ F₂ (λ a => (hf₂ a)⁻¹ • h a • hf₁ a)
  notation:25 F₁:26 " ≃{▻ " h:0 " ◅}" F₂:26 => HasCongrFun.IsExtensional''' F₁ F₂ h (λ _ => byDef) (λ _ => byDef)
  notation:25 F₁:26 " ≃{" hf₁:0 " ▻ " h:0 " ◅} " F₂:26 => HasCongrFun.IsExtensional''' F₁ F₂ h (λ _ => hf₁ • byDef) (λ _ => byDef)
  notation:25 F₁:26 " ≃{▻ " h:0 " ◅ " hf₂:0 "} " F₂:26 => HasCongrFun.IsExtensional''' F₁ F₂ h (λ _ => byDef) (λ _ => hf₂ • byDef)
  notation:25 F₁:26 " ≃{" hf₁:0 " ▻ " h:0 " ◅ " hf₂:0 "} " F₂:26 => HasCongrFun.IsExtensional''' F₁ F₂ h (λ _ => hf₁ • byDef) (λ _ => hf₂ • byDef)

  -- TODO: This currently doesn't work well. When defining instances of `IsExtApp`,
  -- `f₁` and `f₂` are not picked up automatically.
  class IsExtApp {A : U} {B : V} {f₁ f₂ : A → B} (a : A) (eb : f₁ a ≃ f₂ a) where
  {F₁ F₂ : A ⟶ B}
  {h     : ∀ a, f₁ a ≃ f₂ a}
  {hf₁   : ∀ a, F₁ a ≃ f₁ a}
  {hf₂   : ∀ a, F₂ a ≃ f₂ a}
  (e     : IsExtensional''' F₁ F₂ h hf₁ hf₂)

end HasCongrFun



class HasIdFun (U : Universe) {UU : Universe} [HasFunctors U U UU] [HasIdentity U] where
(defIdFun (A : U) : A ⟶{id} A)

namespace HasIdFun

  variable {U UU : Universe} [HasFunctors U U UU] [HasIdentity U] [HasIdFun U]

  @[reducible] def idFun (A : U) : A ⟶ A := defIdFun A

end HasIdFun

class HasConstFun (U V : Universe) {UV : Universe} [HasFunctors U V UV] [HasIdentity V] where
(defConstFun (A : U) {B : V} (b : B) : A ⟶{Function.const ⌈A⌉ b} B)

namespace HasConstFun

  variable {U V UV : Universe} [HasFunctors U V UV] [HasIdentity V] [HasConstFun U V]

  @[reducible] def constFun (A : U) {B : V} (b : B) : A ⟶ B := defConstFun A b

end HasConstFun

class HasCompFun (U V W : Universe) {UV VW UW : Universe} [HasFunctors U V UV] [HasFunctors V W VW] [HasFunctors U W UW]
                 [HasIdentity W] where
(defCompFun {A : U} {B : V} {C : W} (F : A ⟶ B) (G : B ⟶ C) : A ⟶{λ a => G (F a)} C)

namespace HasCompFun

  variable {U V W UV VW UW : Universe} [HasFunctors U V UV] [HasFunctors V W VW] [HasFunctors U W UW]
           [HasIdentity W] [HasCompFun U V W]

  @[reducible] def compFun {A : U} {B : V} {C : W} (F : A ⟶ B) (G : B ⟶ C) : A ⟶ C := defCompFun F G
  notation:90 G:91 " ⊙ " F:90 => HasCompFun.compFun F G

end HasCompFun



class HasInternalFunctors (U : Universe.{u}) [HasIdentity.{u, iu} U] extends
  HasFunctors U U U, HasCongrArg U U : Type (max u iu)

namespace HasInternalFunctors.Helpers

  -- Restricted copies of definitions in `HasFunctors` to help functoriality tactic.

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U]

  @[reducible] def Fun (A B : U) : U := HasFunctors.Fun A B
  @[reducible] def DefFun (A B : U) (f : A → B) := HasFunctors.DefFun A B f

  variable {A B : U}

  @[reducible] def apply (F : A ⟶ B) : A → B := HasFunctors.apply F

  @[reducible] def toDefFun               (F : A ⟶ B)    : A ⟶{apply F} B := HasFunctors.toDefFun F
  @[reducible] def fromDefFun {f : A → B} (F : A ⟶{f} B) : A ⟶ B          := HasFunctors.fromDefFun F

  @[reducible] def toDefFun' (F : A ⟶ B) {f : A → B} (h : ∀ a, F a ≃ f a) : A ⟶{f} B := HasFunctors.toDefFun' F h

end HasInternalFunctors.Helpers



-- The following axioms are equivalent to asserting the existence of five functors with specified
-- behavior, writing `Λ` for a functorial `λ` as defined in `Tactics/Functoriality.lean`:
-- id    : `A ⟶ A,                           Λ a => a`
-- const : `B ⟶ (A ⟶ B),                     Λ b a => b`
-- app   : `A ⟶ (A ⟶ B) ⟶ B,                 Λ a F => F a`
-- dup   : `(A ⟶ A ⟶ B) ⟶ (A ⟶ B),           Λ F a => F a a`
-- comp  : `(A ⟶ B) ⟶ (B ⟶ C) ⟶ (A ⟶ C),     Λ F G a => G (F a)`
--
-- In `DerivedFunctors.lean`, we derive several further functors from these, such as:
-- swap  : `(A ⟶ B ⟶ C) ⟶ (B ⟶ A ⟶ C),       Λ F b a => F a b`
-- subst : `(A ⟶ B) ⟶ (A ⟶ B ⟶ C) ⟶ (A ⟶ C), Λ F G a => G a (F a)`
--
-- Using these, we can give a general algorithm for proving that a function is functorial, which is
-- implemented as a tactic in `Functoriality.lean`.
--
-- We split the axioms into "linear", "affine", and "full" functor operations, where "linear" and
-- "affine" correspond to linear and affine logic, respectively. That is, linear functors use each
-- bound variable exactly once; affine functors use each variable at most once.



class HasLinearFunOp (U : Universe) [HasIdentity U] [HasInternalFunctors U] where
(defIdFun         (A : U)                             : A ⟶{id} A)
(defAppFun        {A : U} (a : A) (B : U)             : (A ⟶ B) ⟶{λ F => F a} B)
(defAppFunFun     (A B : U)                           : A ⟶{λ a => defAppFun a B} ((A ⟶ B) ⟶ B))
(defCompFun       {A B C : U} (F : A ⟶ B) (G : B ⟶ C) : A ⟶{λ a => G (F a)} C)
(defCompFunFun    {A B : U} (F : A ⟶ B) (C : U)       : (B ⟶ C) ⟶{λ G => defCompFun F G} (A ⟶ C))
(defCompFunFunFun (A B C : U)                         : (A ⟶ B) ⟶{λ F => defCompFunFun F C} ((B ⟶ C) ⟶ (A ⟶ C)))

namespace HasLinearFunOp

  open MetaRelation HasFunctors HasCongrArg HasCongrFun

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasLinearFunOp U]

  instance hasIdFun : HasIdFun U := ⟨defIdFun⟩

  @[reducible] def idFun (A : U) : A ⟶ A := defIdFun A

  @[reducible] def appFun {A : U} (a : A) (B : U) : (A ⟶ B) ⟶ B := defAppFun a B
  @[reducible] def appFunFun (A B : U) : A ⟶ (A ⟶ B) ⟶ B := defAppFunFun A B

  instance appFun.isFunApp {A : U} (a : A) (B : U) : IsFunApp A (appFun a B) :=
  { F := appFunFun A B,
    a := a,
    e := byDef }

  instance hasCompFun : HasCompFun U U U := ⟨defCompFun⟩

  @[reducible] def compFun {A B C : U} (F : A ⟶ B) (G : B ⟶ C) : A ⟶ C := defCompFun F G
  @[reducible] def compFunFun {A B : U} (F : A ⟶ B) (C : U) : (B ⟶ C) ⟶ (A ⟶ C) := defCompFunFun F C
  @[reducible] def compFunFunFun (A B C : U) : (A ⟶ B) ⟶ (B ⟶ C) ⟶ (A ⟶ C) := defCompFunFunFun A B C

  instance compFun.isFunApp {A B C : U} {F : A ⟶ B} {G : B ⟶ C} : IsFunApp (B ⟶ C) (compFun F G) :=
  { F := compFunFun F C,
    a := G,
    e := byDef }

  instance compFunFun.isFunApp {A B C : U} {F : A ⟶ B} : IsFunApp (A ⟶ B) (compFunFun F C) :=
  { F := compFunFunFun A B C,
    a := F,
    e := byDef }

  instance isPreorder : IsPreorder (α := U) Fun :=
  { refl  := idFun,
    trans := compFun }

  instance {A B C : U} {F : A ⟶ B} {G : B ⟶ C} : IsFunApp (B ⟶ C) (G • F) :=
  compFun.isFunApp

  instance hasCongrFun : HasCongrFun U U := ⟨λ {A B F₁ F₂} h a => defCongrArg (defAppFun a B) h⟩

  def byFunDef {A B C : U} {f : A → (B ⟶ C)} {F : A ⟶{f} (B ⟶ C)} {a : A} {b : B} :
    (fromDefFun F) a b ≃ (f a) b :=
  congrFun byDef b

  def byFunDef₂ {A B C D : U} {f : A → (B ⟶ C ⟶ D)} {F : A ⟶{f} (B ⟶ C ⟶ D)} {a : A} {b : B} {c : C} :
    (fromDefFun F) a b c ≃ (f a) b c :=
  congrFun byFunDef c

  def byFunDef₃ {A B C D E : U} {f : A → (B ⟶ C ⟶ D ⟶ E)} {F : A ⟶{f} (B ⟶ C ⟶ D ⟶ E)} {a : A} {b : B} {c : C} {d : D} :
    (fromDefFun F) a b c d ≃ (f a) b c d :=
  congrFun byFunDef₂ d

  def byDef₂ {A B C : U} {f : A → B → C} {F' : ∀ a, B ⟶{f a} C} {F : A ⟶{λ a => F' a} (B ⟶ C)} {a : A} {b : B} :
    (fromDefFun F) a b ≃ f a b :=
  byDef • byFunDef

  def byDef₃ {A B C D : U} {f : A → B → C → D} {F'' : ∀ a b, C ⟶{f a b} D} {F' : ∀ a, B ⟶{λ b => F'' a b} (C ⟶ D)}
             {F : A ⟶{λ a => F' a} (B ⟶ C ⟶ D)} {a : A} {b : B} {c : C} :
    (fromDefFun F) a b c ≃ f a b c :=
  byDef₂ • byFunDef₂

end HasLinearFunOp



class HasSubLinearFunOp (U : Universe) [HasIdentity U] [HasInternalFunctors U] where
(defConstFun    (A : U) {B : U} (b : B) : A ⟶{Function.const ⌈A⌉ b} B)
(defConstFunFun (A B : U)               : B ⟶{λ b => defConstFun A b} (A ⟶ B))

namespace HasSubLinearFunOp

  open HasFunctors

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasSubLinearFunOp U]

  instance hasConstFun : HasConstFun U U := ⟨defConstFun⟩

  @[reducible] def constFun (A : U) {B : U} (b : B) : A ⟶ B := defConstFun A b
  @[reducible] def constFunFun (A B : U) : B ⟶ (A ⟶ B) := defConstFunFun A B

  instance constFun.isFunApp {A B : U} {b : B} : IsFunApp B (constFun A b) :=
  { F := constFunFun A B,
    a := b,
    e := byDef }

end HasSubLinearFunOp

class HasAffineFunOp (U : Universe) [HasIdentity U] [HasInternalFunctors U] extends HasLinearFunOp U, HasSubLinearFunOp U



class HasNonLinearFunOp (U : Universe) [HasIdentity U] [HasInternalFunctors U] where
(defDupFun    {A B : U} (F : A ⟶ A ⟶ B) : A ⟶{λ a => F a a} B)
(defDupFunFun (A B : U)                 : (A ⟶ A ⟶ B) ⟶{λ F => defDupFun F} (A ⟶ B))

namespace HasNonLinearFunOp

  open HasFunctors

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasNonLinearFunOp U]

  @[reducible] def dupFun {A B : U} (F : A ⟶ A ⟶ B) : A ⟶ B := defDupFun F
  @[reducible] def dupFunFun (A B : U) : (A ⟶ A ⟶ B) ⟶ (A ⟶ B) := defDupFunFun A B

  instance dupFun.isFunApp {A B : U} {F : A ⟶ A ⟶ B} : IsFunApp (A ⟶ A ⟶ B) (dupFun F) :=
  { F := dupFunFun A B,
    a := F,
    e := byDef }

end HasNonLinearFunOp

class HasFullFunOp (U : Universe) [HasIdentity U] [HasInternalFunctors U] extends HasAffineFunOp U, HasNonLinearFunOp U
