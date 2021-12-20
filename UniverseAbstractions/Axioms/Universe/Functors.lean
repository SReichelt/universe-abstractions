import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.MetaRelations
import UniverseAbstractions.Axioms.Universe.Identity



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w uv vw uvw vv iu iv iuv



-- We want universes to have some concept of "functors" that map instances in ways that respect
-- properties of types, in particular identity.
--
-- We usually want a functor `F : A ⟶ B` with `A B : U` to be an instance of `U`, so that we can
-- define e.g. functors returning functors (`F : C ⟶ (A ⟶ B)`) without having to specify any
-- additional assumptions.
-- E.g. if `U` is the universe of categories, `A ⟶ B` is the functor category from `A` to `B`,
-- and `C ⟶ (A ⟶ B)` is the functor category from `C` to the functor category from `A` to `B`.
--
-- However, in some cases we have a more general concept of a functor `A ⟶ B` where `A` and `B`
-- are not necessarily types of the same universe.
--
-- Moreover, we want to axiomatically assert the existence of certain functors such as identity
-- and composition, which map instances in specific ways. We want this mapping to be as close to
-- "definitional" as possible, so we include it in the type, written as `A ⟶{f} B`.



class HasFunctors (U : Universe.{u}) (V : Universe.{v}) (UV : outParam Universe.{uv}) where
(Fun                   : U → V → UV)
(apply {A : U} {B : V} : Fun A B → A → B)

namespace HasFunctors

  open MetaRelation

  infixr:20 " ⟶ " => HasFunctors.Fun

  instance coeFun {U V UV : Universe} [HasFunctors U V UV] (A : U) (B : V) :
    CoeFun (A ⟶ B) (λ _ => A → B) :=
  ⟨apply⟩

  class IsFunApp {U : outParam Universe} {V : Universe} {UV : outParam Universe}
                 [outParam (HasFunctors U V UV)] [HasIdentity V]
                 (A : outParam U) {B : V} (b : B) where
  (F : A ⟶ B)
  (a : A)
  (e : F a ≃ b)

  class IsFunApp₂ {U₁ U₂ : outParam Universe} {V : Universe} {U₁V U₂V : outParam Universe}
                  [outParam (HasFunctors U₁ V U₁V)] [outParam (HasFunctors U₂ V U₂V)]
                  [HasIdentity V] (A₁ : outParam U₁) (A₂ : outParam U₂) {B : V} (b : B) extends
    IsFunApp A₂ b where
  (h₂ : IsFunApp A₁ b)

  class IsFunApp₃ {U₁ U₂ U₃ : outParam Universe} {V : Universe} {U₁V U₂V U₃V : outParam Universe}
                  [outParam (HasFunctors U₁ V U₁V)] [outParam (HasFunctors U₂ V U₂V)]
                  [outParam (HasFunctors U₃ V U₃V)] [HasIdentity V] (A₁ : outParam U₁)
                  (A₂ : outParam U₂) (A₃ : outParam U₃) {B : V} (b : B) extends
    IsFunApp₂ A₂ A₃ b where
  (h₃ : IsFunApp A₁ b)

  variable {U V UV : Universe} [HasFunctors U V UV] [HasIdentity V]

  instance (priority := low) IsFunApp.refl {A : U} {B : V} (F : A ⟶ B) (a : A) : IsFunApp A (F a) :=
  { F := F,
    a := a,
    e := HasRefl.refl (F a) }

  structure DefFun (A : U) (B : V) (f : A → B) where
  (F           : A ⟶ B)
  (eff (a : A) : F a ≃ f a)

  notation:20 A:21 " ⟶{" f:0 "} " B:21 => HasFunctors.DefFun A B f

  variable {A : U} {B : V}
  
  def toDefFun' (F : A ⟶ B) {f : A → B} (h : ∀ a, F a ≃ f a) : A ⟶{f} B := ⟨F, h⟩

  def toDefFun               (F : A ⟶ B)    : A ⟶{apply F} B := toDefFun' F (λ a => HasRefl.refl (F a))
  def fromDefFun {f : A → B} (F : A ⟶{f} B) : A ⟶ B          := F.F

  def byDef {f : A → B} {F : A ⟶{f} B} {a : A} : (fromDefFun F) a ≃ f a := F.eff a

  notation:60 F:61 " ◄ " h:61 => HasFunctors.toDefFun' F (λ _ => HasInstanceEquivalences.trans HasFunctors.byDef h)

  @[simp] theorem fromToDefFun' (F : A ⟶ B) {f : A → B} (h : ∀ a, F a ≃ f a) :
    fromDefFun (toDefFun' F h) = F :=
  rfl
  @[simp] theorem fromToDefFun (F : A ⟶ B) : fromDefFun (toDefFun F) = F := rfl

  @[simp] theorem toFromDefFun' {f : A → B} (F : A ⟶{f} B) : toDefFun' (fromDefFun F) F.eff = F :=
  by induction F; rfl

  instance {F : A ⟶ B} : CoeDep (A ⟶ B) F  (A ⟶{apply F} B) := ⟨toDefFun F⟩
  instance {f : A → B} : Coe    (A ⟶{f} B) (A ⟶ B)          := ⟨fromDefFun⟩

  def castFun (F : A ⟶ B) (f : A → B) (h : ∀ a, F a ≃ f a) : A ⟶ B := fromDefFun (toDefFun' F h)

  @[simp] theorem simpCastFun (F : A ⟶ B) (f : A → B) (h : ∀ a, F a ≃ f a) :
    castFun F f h = F :=
  fromToDefFun' F h

  def castDefFun {f f' : A → B} (F : A ⟶{f} B) (h : ∀ a, f a ≃ f' a) : A ⟶{f'} B :=
  ⟨F.F, λ a => h a • F.eff a⟩

  @[simp] theorem fromCastDefFun {f f' : A → B} (F : A ⟶{f} B) (h : ∀ a, f a ≃ f' a) :
    fromDefFun (castDefFun F h) = fromDefFun F :=
  rfl

  def defAppFun (F : A ⟶ B) : A ⟶{λ a => F a} B := F
  @[reducible] def appFun (F : A ⟶ B) : A ⟶ B := defAppFun F

end HasFunctors



class HasCongrArg (U : Universe.{u}) (V : Universe.{v}) {UV : Universe.{uv}} [HasFunctors U V UV]
                  [HasIdentity.{u, iu} U] [HasIdentity.{v, iv} V] where
(congrArg {A : U} {B : V} (F : A ⟶ B) {a₁ a₂ : A} : a₁ ≃ a₂ → F a₁ ≃ F a₂)

namespace HasCongrArg

  open HasFunctors

  variable {U V UV : Universe} [HasFunctors U V UV] [HasIdentity U] [HasIdentity V] [HasCongrArg U V]

  def applyCongrArg {A : U} {B : V} (F : A ⟶ B) {a₁ a₂ : A} (h : a₁ ≃ a₂)
                    {b₁ b₂ : B} (h₁ : F a₁ ≃ b₁) (h₂ : F a₂ ≃ b₂) :
    b₁ ≃ b₂ :=
  h₂ • congrArg F h • h₁⁻¹

  def defCongrArg {A : U} {B : V} {f : A → B} (F : A ⟶{f} B) {a₁ a₂ : A} : a₁ ≃ a₂ → f a₁ ≃ f a₂ :=
  λ h => applyCongrArg (fromDefFun F) h byDef byDef

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
                  [HasIdentity.{v, iv} V] [HasIdentity.{uv, iuv} UV] where
(congrFun {A : U} {B : V} {F₁ F₂ : A ⟶ B} (h : F₁ ≃ F₂) (a : A) : F₁ a ≃ F₂ a)

namespace HasCongrFun

  open HasFunctors

  section

    variable {U V UV : Universe} [HasFunctors U V UV] [HasIdentity V] [HasIdentity UV]

    section

      variable [HasCongrFun U V]

      def applyCongrFun {A : U} {B : V} {F₁ F₂ : A ⟶ B} (h : F₁ ≃ F₂) (a : A)
                        {b₁ b₂ : B} (h₁ : F₁ a ≃ b₁) (h₂ : F₂ a ≃ b₂) :
        b₁ ≃ b₂ :=
      h₂ • congrFun h a • h₁⁻¹

      def defCongrFun {A : U} {B : V} {f₁ f₂ : A → B} {F₁ : A ⟶{f₁} B} {F₂ : A ⟶{f₂} B}
                      (h : fromDefFun F₁ ≃ fromDefFun F₂) (a : A) :
        f₁ a ≃ f₂ a :=
      applyCongrFun h a byDef byDef

    end

    -- This definition might seem a little silly: it includes a hypothesis that isn't actually used
    -- in the definition. However, this is quite useful when `IsExtensional` is used as the type of
    -- an axiom. When implementing the axiom, the hypothesis is then accessible in a generic way,
    -- so the implementation shrinks to a proof of `F₁ ≃ F₂` given `∀ a, F₁ a ≃ F₂ a`. If functors
    -- are extensional, then this proof is completely generic (see `Trivial.lean`). In general it
    -- can be regarded as a proof that the instance of `F₁ a ≃ F₂ a` is natural in `a`.

    def IsExtensional {A : U} {B : V} (F₁ F₂ : A ⟶ B) (h : ∀ a, F₁ a ≃ F₂ a) := F₁ ≃ F₂
    notation:25 F₁:26 " ≃{" h:0 "} " F₂:26 => HasCongrFun.IsExtensional F₁ F₂ h
    notation:25 F₁:26 " ≃{" h:0 " ▻|} " F₂:26 => HasCongrFun.IsExtensional F₁ F₂ (λ _ => h • HasFunctors.byDef)

    def IsExtensional' {A : U} {B : V} (F₁ F₂ : A ⟶ B) {f : A → B}
                       (hf₁ : ∀ a, F₁ a ≃ f a) (hf₂ : ∀ a, f a ≃ F₂ a) :=
    IsExtensional F₁ F₂ (λ a => hf₂ a • hf₁ a)
    notation:25 F₁:26 " ≃{▻ " h:0 "} " F₂:26 => HasCongrFun.IsExtensional' F₁ F₂ (λ _ => HasFunctors.byDef) h
    notation:25 F₁:26 " ≃{" hf₁:0 " ▻ " h:0 "} " F₂:26 => HasCongrFun.IsExtensional' F₁ F₂ (λ _ => hf₁ • HasFunctors.byDef) h

    def IsExtensional'' {A : U} {B : V} (F₁ F₂ : A ⟶ B) {f : A → B}
                        (hf₁ : ∀ a, F₁ a ≃ f a) (hf₂ : ∀ a, F₂ a ≃ f a) :=
    IsExtensional F₁ F₂ (λ a => (hf₂ a)⁻¹ • hf₁ a)
    notation:25 F₁:26 " ≃{" h:0 " ◅} " F₂:26 => HasCongrFun.IsExtensional'' F₁ F₂ h (λ _ => HasFunctors.byDef)
    notation:25 F₁:26 " ≃{" h:0 " ◅ " hf₂:0 "} " F₂:26 => HasCongrFun.IsExtensional'' F₁ F₂ h (λ _ => hf₂ • HasFunctors.byDef)
    notation:25 F₁:26 " ≃{▻-◅} " F₂:26 => HasCongrFun.IsExtensional'' F₁ F₂ (λ _ => HasFunctors.byDef) (λ _ => HasFunctors.byDef)
    notation:25 F₁:26 " ≃{" hf₁:0 " ▻-◅} " F₂:26 => HasCongrFun.IsExtensional'' F₁ F₂ (λ _ => hf₁ • HasFunctors.byDef) (λ _ => HasFunctors.byDef)
    notation:25 F₁:26 " ≃{▻-◅ " hf₂:0 "} " F₂:26 => HasCongrFun.IsExtensional'' F₁ F₂ (λ _ => HasFunctors.byDef) (λ _ => hf₂ • HasFunctors.byDef)
    notation:25 F₁:26 " ≃{" hf₁:0 " ▻-◅ " hf₂:0 "} " F₂:26 => HasCongrFun.IsExtensional'' F₁ F₂ (λ _ => hf₁ • HasFunctors.byDef) (λ _ => hf₂ • HasFunctors.byDef)

    def IsExtensional''' {A : U} {B : V} (F₁ F₂ : A ⟶ B) {f₁ f₂ : A → B} (h : ∀ a, f₁ a ≃ f₂ a)
                         (hf₁ : ∀ a, F₁ a ≃ f₁ a) (hf₂ : ∀ a, F₂ a ≃ f₂ a) :=
    IsExtensional F₁ F₂ (λ a => (hf₂ a)⁻¹ • h a • hf₁ a)
    notation:25 F₁:26 " ≃{▻ " h:0 " ◅}" F₂:26 => HasCongrFun.IsExtensional''' F₁ F₂ h (λ _ => HasFunctors.byDef) (λ _ => HasFunctors.byDef)
    notation:25 F₁:26 " ≃{" hf₁:0 " ▻ " h:0 " ◅} " F₂:26 => HasCongrFun.IsExtensional''' F₁ F₂ h (λ _ => hf₁ • HasFunctors.byDef) (λ _ => HasFunctors.byDef)
    notation:25 F₁:26 " ≃{▻ " h:0 " ◅ " hf₂:0 "} " F₂:26 => HasCongrFun.IsExtensional''' F₁ F₂ h (λ _ => HasFunctors.byDef) (λ _ => hf₂ • HasFunctors.byDef)
    notation:25 F₁:26 " ≃{" hf₁:0 " ▻ " h:0 " ◅ " hf₂:0 "} " F₂:26 => HasCongrFun.IsExtensional''' F₁ F₂ h (λ _ => hf₁ • HasFunctors.byDef) (λ _ => hf₂ • HasFunctors.byDef)
    notation:25 F₁:26 " ≃⦃ " A':0 " ▻⟶ " B':0 " ⦄" F₂:26 => HasCongrFun.IsExtensional''' (A := A') (B := B') F₁ F₂ (λ _ => HasFunctors.byDef) (λ _ => HasFunctors.byDef) (λ _ => HasFunctors.byDef)

    def IsDefExtensional {A : U} {B : V} {f₁ f₂ : A → B} (F₁ : A ⟶{f₁} B) (F₂ : A ⟶{f₂} B)
                         (h : ∀ a, f₁ a ≃ f₂ a) :=
    fromDefFun F₁ ≃{▻ h ◅} fromDefFun F₂

    -- TODO: This currently doesn't work well. When defining instances of `IsExtApp`,
    -- `f₁` and `f₂` are not picked up automatically.
    class IsExtApp {A : U} {B : V} {f₁ f₂ : A → B} (a : A) (eb : f₁ a ≃ f₂ a) where
    {F₁ F₂ : A ⟶ B}
    {h     : ∀ a, f₁ a ≃ f₂ a}
    {hf₁   : ∀ a, F₁ a ≃ f₁ a}
    {hf₂   : ∀ a, F₂ a ≃ f₂ a}
    (e     : IsExtensional''' F₁ F₂ h hf₁ hf₂)

  end

  section

    variable {U V W VW UVW : Universe} [HasFunctors V W VW] [HasFunctors U VW UVW] [HasIdentity W] [HasIdentity VW]
             [HasCongrFun V W]

    def byFunDef {A : U} {B : V} {C : W} {f : A → (B ⟶ C)} {F : A ⟶{f} (B ⟶ C)} {a : A} {b : B} :
      (fromDefFun F) a b ≃ (f a) b :=
    congrFun byDef b

    def byDef₂ {A : U} {B : V} {C : W} {f : A → B → C} {F' : ∀ a, B ⟶{f a} C} {F : A ⟶{λ a => F' a} (B ⟶ C)} {a : A} {b : B} :
      (fromDefFun F) a b ≃ f a b :=
    byDef • byFunDef

  end

  section

    variable {U V UV : Universe} [HasFunctors V V V] [HasFunctors U V UV] [HasIdentity V] [HasCongrFun V V]

    def byFunDef₂ {A : U} {B C D : V} {f : A → (B ⟶ C ⟶ D)} {F : A ⟶{f} (B ⟶ C ⟶ D)} {a : A} {b : B} {c : C} :
      (fromDefFun F) a b c ≃ (f a) b c :=
    congrFun byFunDef c

    def byFunDef₃ {A : U} {B C D E : V} {f : A → (B ⟶ C ⟶ D ⟶ E)} {F : A ⟶{f} (B ⟶ C ⟶ D ⟶ E)} {a : A} {b : B} {c : C} {d : D} :
      (fromDefFun F) a b c d ≃ (f a) b c d :=
    congrFun byFunDef₂ d

    def byDef₃ {A : U} {B C D : V} {f : A → B → C → D} {F'' : ∀ a b, C ⟶{f a b} D} {F' : ∀ a, B ⟶{λ b => F'' a b} (C ⟶ D)}
              {F : A ⟶{λ a => F' a} (B ⟶ C ⟶ D)} {a : A} {b : B} {c : C} :
      (fromDefFun F) a b c ≃ f a b c :=
    byDef₂ • byFunDef₂

  end

end HasCongrFun



-- First, some individual universe-polymorphic functors.
-- The following seems to be a good criterion for deciding how much polymorphism we want:
-- Whenever we define a functor `(A ⟶ B) ⟶{λ F => ...} C` taking a functor as an argument, we force
-- `A`, `B`, and `A ⟶ B` into the same universe.
-- If that forces all types to be in the same universe, we usually do not define individual functors
-- any more, but use `HasLinearFunOp`, `HasAffineFunOp`, or `HasFullFunOp`, defined further below.

class HasIdFun (U : Universe) {UU : Universe} [HasFunctors U U UU] [HasIdentity U] where
(defIdFun (A : U) : A ⟶{id} A)

namespace HasIdFun

  variable {U UU : Universe} [HasFunctors U U UU] [HasIdentity U] [HasIdFun U]

  @[reducible] def idFun (A : U) : A ⟶ A := defIdFun A

end HasIdFun

class HasConstFun (U V : Universe) {UV : Universe} [HasFunctors U V UV] [HasIdentity V] where
(defConstFun (A : U) {B : V} (b : B) : A ⟶{Function.const A b} B)

namespace HasConstFun

  variable {U V UV : Universe} [HasFunctors U V UV] [HasIdentity V] [HasConstFun U V]

  @[reducible] def constFun (A : U) {B : V} (b : B) : A ⟶ B := defConstFun A b

end HasConstFun

class HasRevAppFun (U : Universe) [HasFunctors U U U] [HasIdentity U] where
(defRevAppFun {A : U} (a : A) (B : U) : (A ⟶ B) ⟶{λ F => F a} B)

namespace HasRevAppFun

  open HasCongrArg

  variable {U : Universe} [HasFunctors U U U] [HasIdentity U] [HasRevAppFun U]

  @[reducible] def revAppFun {A : U} (a : A) (B : U) : (A ⟶ B) ⟶ B := defRevAppFun a B

  instance hasCongrFun [HasCongrArg U U] : HasCongrFun U U :=
  ⟨λ {A B F₁ F₂} h a => defCongrArg (defRevAppFun a B) h⟩

end HasRevAppFun

class HasCompFun (U V W : Universe) {UV VW UW : Universe} [HasFunctors U V UV] [HasFunctors V W VW]
                 [HasFunctors U W UW] [HasIdentity W] where
(defCompFun {A : U} {B : V} {C : W} (F : A ⟶ B) (G : B ⟶ C) : A ⟶{λ a => G (F a)} C)

namespace HasCompFun

  variable {U V W UV VW UW : Universe} [HasFunctors U V UV] [HasFunctors V W VW] [HasFunctors U W UW]
           [HasIdentity W] [HasCompFun U V W]

  @[reducible] def compFun {A : U} {B : V} {C : W} (F : A ⟶ B) (G : B ⟶ C) : A ⟶ C := defCompFun F G
  notation:90 G:91 " ⊙ " F:90 => HasCompFun.compFun F G

  def defCompDefFun [HasIdentity V] [HasCongrArg V W] {A : U} {B : V} {C : W} {f : A → B}
                    (F : A ⟶{f} B) (G : B ⟶ C) :
    A ⟶{λ a => G (f a)} C :=
  G ⊙ F
  ◄ HasCongrArg.byArgDef

end HasCompFun

class HasCompFunFun (U W : Universe) {UW : Universe} [HasFunctors U W UW] [HasFunctors W UW UW]
                    [HasFunctors W W W] [HasIdentity W] [HasIdentity UW] extends
  HasCompFun U W W where
(defCompFunFun {A : U} {B : W} (F : A ⟶ B) (C : W) : (B ⟶ C) ⟶{λ G => G ⊙ F} (A ⟶ C))

namespace HasCompFunFun

  open HasFunctors

  variable {U W UW : Universe} [HasFunctors U W UW] [HasFunctors W UW UW]
           [HasFunctors W W W] [HasIdentity W] [HasIdentity UW] [HasCompFunFun U W]

  @[reducible] def compFunFun {A : U} {B : W} (F : A ⟶ B) (C : W) : (B ⟶ C) ⟶ (A ⟶ C) :=
  defCompFunFun F C

  instance compFun.isFunApp {A : U} {B C : W} {F : A ⟶ B} {G : B ⟶ C} :
    IsFunApp (B ⟶ C) (G ⊙ F) :=
  { F := compFunFun F C,
    a := G,
    e := byDef }

end HasCompFunFun

class HasRevCompFunFun (U W : Universe) {UW : Universe} [HasFunctors U U U] [HasFunctors U W UW]
                       [HasFunctors U UW UW] [HasIdentity W] [HasIdentity UW] extends
  HasCompFun U U W where
(defRevCompFunFun (A : U) {B : U} {C : W} (G : B ⟶ C) : (A ⟶ B) ⟶{λ F => G ⊙ F} (A ⟶ C))

namespace HasRevCompFunFun

  open HasFunctors

  variable {U W UW : Universe} [HasFunctors U U U] [HasFunctors U W UW]
           [HasFunctors U UW UW] [HasIdentity W] [HasIdentity UW] [HasRevCompFunFun U W]

  @[reducible] def revCompFunFun (A : U) {B : U} {C : W} (G : B ⟶ C) : (A ⟶ B) ⟶ (A ⟶ C) :=
  defRevCompFunFun A G

  instance (priority := low) compFun.isFunApp {A B : U} {C : W} {F : A ⟶ B} {G : B ⟶ C} :
    IsFunApp (A ⟶ B) (G ⊙ F) :=
  { F := revCompFunFun A G,
    a := F,
    e := byDef }

end HasRevCompFunFun

class HasSwapFun (U V W : Universe) {VW UVW UW : Universe} [HasFunctors V W VW] [HasFunctors U VW UVW]
                 [HasFunctors U W UW] [HasIdentity W] where
(defSwapFun {A : U} {B : V} {C : W} (F : A ⟶ B ⟶ C) (b : B) : A ⟶{λ a => F a b} C)

namespace HasSwapFun

  variable {U V W VW UVW UW : Universe} [HasFunctors V W VW] [HasFunctors U VW UVW]
           [HasFunctors U W UW] [HasIdentity W] [HasSwapFun U V W]

  @[reducible] def swapFun {A : U} {B : V} {C : W} (F : A ⟶ B ⟶ C) (b : B) : A ⟶ C := defSwapFun F b

  def defSwapDefFun [HasIdentity VW] [HasCongrFun V W] {A : U} {B : V} {C : W} {f : A → (B ⟶ C)}
                    (F : A ⟶{f} (B ⟶ C)) (b : B) :
    A ⟶{λ a => (f a) b} C :=
  swapFun F b
  ◄ HasCongrFun.byFunDef

end HasSwapFun

class HasSwapFunFun (U V W : Universe) {VW UVW UW VUW : Universe} [HasFunctors V W VW]
                    [HasFunctors U VW UVW] [HasFunctors U W UW] [HasFunctors V UW VUW]
                    [HasIdentity W] [HasIdentity UW] extends
  HasSwapFun U V W where
(defSwapFunFun {A : U} {B : V} {C : W} (F : A ⟶ B ⟶ C) : B ⟶{λ b => HasSwapFun.swapFun F b} (A ⟶ C))

namespace HasSwapFunFun

  open HasFunctors HasSwapFun

  variable {U V W UW VW UVW VUW : Universe} [HasFunctors V W VW] [HasFunctors U VW UVW]
           [HasFunctors U W UW] [HasFunctors V UW VUW] [HasIdentity W] [HasIdentity UW]
           [HasSwapFunFun U V W]

  @[reducible] def swapFunFun {A : U} {B : V} {C : W} (F : A ⟶ B ⟶ C) : B ⟶ A ⟶ C := defSwapFunFun F

  instance swapFun.isFunApp {A : U} {B : V} {C : W} {F : A ⟶ B ⟶ C} {b : B} :
    IsFunApp B (swapFun F b) :=
  { F := swapFunFun F,
    a := b,
    e := byDef }

end HasSwapFunFun

class HasDupFun (U V : Universe) {UV UUV : Universe} [HasFunctors U V UV] [HasFunctors U UV UUV]
                [HasIdentity V] where
(defDupFun {A : U} {B : V} (F : A ⟶ A ⟶ B) : A ⟶{λ a => F a a} B)

namespace HasDupFun

  variable {U V UV UUV : Universe} [HasFunctors U V UV] [HasFunctors U UV UUV] [HasIdentity V]
           [HasDupFun U V]

  @[reducible] def dupFun {A : U} {B : V} (F : A ⟶ A ⟶ B) : A ⟶ B := defDupFun F

  def defDupDefFun [HasIdentity UV] [HasCongrFun U V] {A : U} {B : V} {f : A → (A ⟶ B)}
                   (F : A ⟶{f} (A ⟶ B)) :
    A ⟶{λ a => (f a) a} B :=
  dupFun F
  ◄ HasCongrFun.byFunDef

end HasDupFun

class HasSubstFun (U V W : Universe) {UV VW UVW UW : Universe} [HasFunctors U V UV] [HasFunctors V W VW]
                  [HasFunctors U VW UVW] [HasFunctors U W UW] [HasIdentity W] where
(defSubstFun {A : U} {B : V} {C : W} (F : A ⟶ B) (G : A ⟶ B ⟶ C) : A ⟶{λ a => G a (F a)} C)

namespace HasSubstFun

  variable {U V W UV VW UVW UW : Universe} [HasFunctors U V UV] [HasFunctors V W VW] [HasFunctors U W UW]
           [HasFunctors U VW UVW] [HasFunctors U W UW] [HasIdentity W] [HasSubstFun U V W]

  @[reducible] def substFun {A : U} {B : V} {C : W} (F : A ⟶ B) (G : A ⟶ B ⟶ C) : A ⟶ C := defSubstFun F G

  def defSubstDefFun [HasIdentity V] [HasIdentity VW] [HasCongrArg V W] [HasCongrFun V W]
                     {A : U} {B : V} {C : W} {f : A → B} (F : A ⟶{f} B) {g : A → (B ⟶ C)} (G : A ⟶{g} (B ⟶ C)) :
    A ⟶{λ a => g a (f a)} C :=
  substFun (B := B) F G
  ◄ HasCongrFun.byFunDef • HasCongrArg.byArgDef

end HasSubstFun

class HasRevSubstFunFun (U W : Universe) {UW : Universe} [HasFunctors U U U] [HasFunctors U W UW]
                        [HasFunctors U UW UW] [HasIdentity W] [HasIdentity UW] extends
  HasSubstFun U U W where
(defRevSubstFunFun {A B : U} {C : W} (G : A ⟶ B ⟶ C) : (A ⟶ B) ⟶{λ F => HasSubstFun.substFun F G} (A ⟶ C))

namespace HasRevSubstFunFun

  open HasFunctors HasSubstFun

  variable {U W : Universe} {UW : Universe} [HasFunctors U U U] [HasFunctors U W UW]
           [HasFunctors U UW UW] [HasIdentity W] [HasIdentity UW] [HasRevSubstFunFun U W]

  @[reducible] def revSubstFunFun {A B : U} {C : W} (G : A ⟶ B ⟶ C) : (A ⟶ B) ⟶ (A ⟶ C) :=
  defRevSubstFunFun G

  instance (priority := low) substFun.isFunApp {A B : U} {C : W} {F : A ⟶ B} {G : A ⟶ B ⟶ C} :
    IsFunApp (A ⟶ B) (substFun F G) :=
  { F := revSubstFunFun G,
    a := F,
    e := byDef }

end HasRevSubstFunFun

class HasBiCompFun (U V W X : Universe) {UV UW WX VWX UX : Universe} [HasFunctors U V UV]
                   [HasFunctors U W UW] [HasFunctors W X WX] [HasFunctors V WX VWX]
                   [HasFunctors U X UX] [HasIdentity X] where
(defBiCompFun {A : U} {B : V} {C : W} {D : X} (F : A ⟶ B) (G : A ⟶ C) (H : B ⟶ C ⟶ D) :
   A ⟶{λ a => H (F a) (G a)} D)

namespace HasBiCompFun

  variable {U V W X UV UW WX VWX UX : Universe} [HasFunctors U V UV] [HasFunctors U W UW]
           [HasFunctors W X WX] [HasFunctors V WX VWX] [HasFunctors U X UX] [HasIdentity X]
           [HasBiCompFun U V W X]

  @[reducible] def biCompFun {A : U} {B : V} {C : W} {D : X} (F : A ⟶ B) (G : A ⟶ C) (H : B ⟶ C ⟶ D) :
    A ⟶ D :=
  defBiCompFun F G H

end HasBiCompFun

class HasRevBiCompFunFun (U V X : Universe) {UV UX VUX UUX : Universe} [HasFunctors U U U]
                         [HasFunctors U V UV] [HasFunctors U X UX] [HasFunctors V UX VUX]
                         [HasFunctors U UX UUX] [HasIdentity X] [HasIdentity UX] extends
  HasBiCompFun U V U X where
(defRevBiCompFunFun {A : U} {B : V} {C : U} {D : X} (H : B ⟶ C ⟶ D) (F : A ⟶ B) :
   (A ⟶ C) ⟶{λ G => HasBiCompFun.biCompFun F G H} (A ⟶ D))

namespace HasRevBiCompFunFun

  open HasFunctors HasBiCompFun

  variable {U V X UV UX VUX UUX : Universe} [HasFunctors U U U] [HasFunctors U V UV]
           [HasFunctors U X UX] [HasFunctors V UX VUX] [HasFunctors U UX UUX] [HasIdentity X]
           [HasIdentity UX] [HasRevBiCompFunFun U V X]

  @[reducible] def revBiCompFunFun {A : U} {B : V} {C : U} {D : X} (H : B ⟶ C ⟶ D) (F : A ⟶ B) :
    (A ⟶ C) ⟶ (A ⟶ D) :=
  defRevBiCompFunFun H F

  instance (priority := low) biCompFun.isFunApp {A : U} {B : V} {C : U} {D : X}
                                                {F : A ⟶ B} {G : A ⟶ C} {H : B ⟶ C ⟶ D} :
    IsFunApp (A ⟶ C) (biCompFun F G H) :=
  { F := revBiCompFunFun H F,
    a := G,
    e := byDef }

end HasRevBiCompFunFun

class HasRevBiCompFunFunFun (U X : Universe) {UX : Universe} [HasFunctors U U U] [HasFunctors U X UX]
                            [HasFunctors U UX UX] [HasIdentity X] [HasIdentity UX] extends
  HasRevBiCompFunFun U U X where
(defRevBiCompFunFunFun (A : U) {B C : U} {D : X} (H : B ⟶ C ⟶ D) :
   (A ⟶ B) ⟶{λ F => HasRevBiCompFunFun.revBiCompFunFun H F} ((A ⟶ C) ⟶ (A ⟶ D)))

namespace HasRevBiCompFunFunFun

  open HasFunctors HasRevBiCompFunFun

  variable {U X UX : Universe} [HasFunctors U U U] [HasFunctors U X UX] [HasFunctors U UX UX]
           [HasIdentity X] [HasIdentity UX] [HasRevBiCompFunFunFun U X]

  @[reducible] def revBiCompFunFunFun (A : U) {B C : U} {D : X} (H : B ⟶ C ⟶ D) :
    (A ⟶ B) ⟶ (A ⟶ C) ⟶ (A ⟶ D) :=
  defRevBiCompFunFunFun A H

  instance (priority := low) revBiCompFunFun.isFunApp {A B C : U} {D : X} {F : A ⟶ B} {H : B ⟶ C ⟶ D} :
    IsFunApp (A ⟶ B) (revBiCompFunFun H F) :=
  { F := revBiCompFunFunFun A H,
    a := F,
    e := byDef }

end HasRevBiCompFunFunFun



class IsFunctorial {U V UV : Universe} [HasFunctors U V UV] [HasIdentity V]
                   {A : U} {B : V} (f : A → B) where
(defFun : A ⟶{f} B)

namespace IsFunctorial

  open HasFunctors

  variable {U V UV : Universe} [HasFunctors U V UV] [HasIdentity V] {A : U} {B : V}
           (f : A → B) [h : IsFunctorial f]

  @[reducible] def functor : A ⟶ B := h.defFun

  instance isFunApp (a : A) : IsFunApp A (f a) :=
  { F := functor f,
    a := a,
    e := byDef }

end IsFunctorial

class IsRightFunctorial {U V W VW : Universe} [HasFunctors V W VW] [HasIdentity W]
                        {A : U} {B : V} {C : W} (f : A → B → C) where
(defRightFun (a : A) : B ⟶{λ b => f a b} C)

namespace IsRightFunctorial

  open HasFunctors

  variable {U V W VW : Universe} [HasFunctors V W VW] [HasIdentity W] {A : U} {B : V} {C : W}
           (f : A → B → C) [h : IsRightFunctorial f]

  @[reducible] def rightFun (a : A) : B ⟶ C := h.defRightFun a

  instance isFunApp (a : A) (b : B) : IsFunApp B (f a b) :=
  { F := rightFun f a,
    a := b,
    e := byDef }

end IsRightFunctorial

class IsLeftFunctorial {U V W UW : Universe} [HasFunctors U W UW] [HasIdentity W]
                       {A : U} {B : V} {C : W} (f : A → B → C) where
(defLeftFun (b : B) : A ⟶{λ a => f a b} C)

namespace IsLeftFunctorial

  open HasFunctors

  variable {U V W UW : Universe} [HasFunctors U W UW] [HasIdentity W] {A : U} {B : V} {C : W}
           (f : A → B → C) [h : IsLeftFunctorial f]

  @[reducible] def leftFun (b : B) : A ⟶ C := h.defLeftFun b

  instance isFunApp (a : A) (b : B) : IsFunApp A (f a b) :=
  { F := leftFun f b,
    a := a,
    e := byDef }

end IsLeftFunctorial

class IsBiFunctorial {U V W VW UVW : Universe} [HasFunctors V W VW] [HasFunctors U VW UVW]
                     [HasIdentity W] [HasIdentity VW]
                     {A : U} {B : V} {C : W} (f : A → B → C) extends
  IsRightFunctorial f where
(defRightFunFun : A ⟶{λ a => IsRightFunctorial.rightFun f a} (B ⟶ C))

namespace IsBiFunctorial

  open HasFunctors HasCongrFun HasSwapFun HasSwapFunFun

  variable {U V W VW UVW : Universe} [HasFunctors V W VW] [HasFunctors U VW UVW]
           [HasIdentity W] [HasIdentity VW] {A : U} {B : V} {C : W} (f : A → B → C)
           [h : IsBiFunctorial f]

  @[reducible] def rightFunFun : A ⟶ B ⟶ C := h.defRightFunFun

  variable {UW : Universe} [HasFunctors U W UW] [HasCongrFun V W]

  def defLeftFun [HasSwapFun U V W] (b : B) :
    A ⟶{λ a => f a b} C :=
  swapFun (rightFunFun f) b
  ◄ byDef₂

  instance [HasSwapFun U V W] : IsLeftFunctorial f := ⟨defLeftFun f⟩

  def defLeftFunFun {VUW : Universe} [HasFunctors V UW VUW] [HasIdentity UW]
                    [HasSwapFunFun U V W] :
    B ⟶{λ b => IsLeftFunctorial.leftFun f b} (A ⟶ C) :=
  defSwapFunFun (rightFunFun f)

  @[reducible] def leftFunFun {VUW : Universe} [HasFunctors V UW VUW] [HasIdentity UW]
                              [HasSwapFunFun U V W] :
    B ⟶ A ⟶ C :=
  defLeftFunFun f

  instance isFunApp₂ [HasSwapFun U V W] (a : A) (b : B) : IsFunApp₂ A B (f a b) :=
  { toIsFunApp := IsRightFunctorial.isFunApp f a b,
    h₂         := IsLeftFunctorial.isFunApp  f a b }

end IsBiFunctorial

namespace MetaRelation

  open HasFunctors HasCongrArg HasCongrFun HasSwapFun HasSwapFunFun

  variable {α : Sort u} {V : Universe.{v}} {VV : Universe.{vv}} [HasIdentity.{v, iv} V]
           [HasFunctors V V VV] (R : MetaRelation α V)

  class HasSymmFun [HasSymm R] where
  (defSymmFun (a b : α) : R a b ⟶{λ f => f⁻¹} R b a)

  namespace HasSymmFun

    variable [HasSymm R] [h : HasSymmFun R]

    @[reducible] def symmFun (a b : α) : R a b ⟶ R b a := h.defSymmFun a b

    instance symm.isFunApp {a b : α} {e : R a b} : IsFunApp (R a b) e⁻¹ :=
    { F := symmFun R a b,
      a := e,
      e := byDef }

    variable [HasCongrArg V V]

    def congrArgSymm {a b : α} {e₁ e₂ : R a b} (he : e₁ ≃ e₂) :
      e₁⁻¹ ≃ e₂⁻¹ :=
    defCongrArg (defSymmFun a b) he

  end HasSymmFun

  class HasTransFun [HasIdentity VV] [HasFunctors V VV VV] [HasTrans R] where
  (defTransFun    {a b   : α} (f : R a b) (c : α) : R b c ⟶{λ g => g • f} R a c)
  (defTransFunFun (a b c : α)                     : R a b ⟶{λ f => defTransFun f c} (R b c ⟶ R a c))

  namespace HasTransFun

    variable [HasIdentity VV] [HasFunctors V VV VV] [HasTrans R] [h : HasTransFun R]

    @[reducible] def transFun {a b : α} (f : R a b) (c : α) : R b c ⟶ R a c := h.defTransFun f c
    @[reducible] def transFunFun (a b c : α) : R a b ⟶ R b c ⟶ R a c := h.defTransFunFun a b c

    instance (priority := low) trans.isFunApp {a b c : α} {f : R a b} {g : R b c} : IsFunApp (R b c) (g • f) :=
    { F := transFun R f c,
      a := g,
      e := byDef }

    instance transFun.isFunApp {a b c : α} {f : R a b} : IsFunApp (R a b) (transFun R f c) :=
    { F := transFunFun R a b c,
      a := f,
      e := byDef }

    variable [HasCongrFun V V]

    def defRevTransFun [HasSwapFun V V V] (a : α) {b c : α} (g : R b c) :
      (R a b) ⟶{λ f => g • f} (R a c) :=
    swapFun (transFunFun R a b c) g
    ◄ byDef₂

    @[reducible] def revTransFun [HasSwapFun V V V] (a : α) {b c : α} (g : R b c) :
      R a b ⟶ R a c :=
    defRevTransFun R a g

    def defRevTransFunFun [HasSwapFunFun V V V] (a b c : α) :
      R b c ⟶{λ g => revTransFun R a g} (R a b ⟶ R a c) :=
    defSwapFunFun (transFunFun R a b c)

    @[reducible] def revTransFunFun [HasSwapFunFun V V V] (a b c : α) : R b c ⟶ R a b ⟶ R a c :=
    defRevTransFunFun R a b c

    instance revTransFun.isFunApp [HasSwapFunFun V V V] {a b c : α} {g : R b c} :
      IsFunApp (R b c) (revTransFun R a g) :=
    { F := revTransFunFun R a b c,
      a := g,
      e := byDef }

    instance (priority := low) trans.isMultiFunApp [HasSwapFun V V V] {a b c : α} {f : R a b} {g : R b c} :
      IsFunApp₂ (R a b) (R b c) (g • f) :=
    ⟨{ F := revTransFun R a g,
       a := f,
       e := byDef }⟩

    def congrArgTransLeft [HasCongrArg V V] {a b c : α} (f : R a b) {g₁ g₂ : R b c} (hg : g₁ ≃ g₂) :
      g₁ • f ≃ g₂ • f :=
    defCongrArg (defTransFun f c) hg

    def congrArgTransRight [HasCongrArg V VV] {a b c : α} {f₁ f₂ : R a b} (hf : f₁ ≃ f₂) (g : R b c) :
      g • f₁ ≃ g • f₂ :=
    defCongrFun (defCongrArg (defTransFunFun a b c) hf) g

    def congrArgTrans [HasCongrArg V V] [HasCongrArg V VV] {a b c : α}
                      {f₁ f₂ : R a b} (hf : f₁ ≃ f₂) {g₁ g₂ : R b c} (hg : g₁ ≃ g₂) :
      g₁ • f₁ ≃ g₂ • f₂ :=
    congrArgTransRight R hf g₂ • congrArgTransLeft R f₁ hg

  end HasTransFun

  namespace opposite

    instance hasSymmFun [HasSymm R] [h : HasSymmFun R] :
      HasSymmFun (opposite R) :=
    { defSymmFun := λ a b => h.defSymmFun b a }

    instance hasTransFun [HasIdentity VV] [HasFunctors V VV VV] [HasCongrFun V V]
                         [HasSwapFunFun V V V] [HasTrans R] [h : HasTransFun R] :
      HasTransFun (opposite R) :=
    { defTransFun    := λ f   c => HasTransFun.defRevTransFun R c f,
      defTransFunFun := λ a b c => HasTransFun.defRevTransFunFun R c b a }

  end opposite

  namespace lift

    variable {ω : Sort w} (l : ω → α)

    instance hasSymmFun [HasSymm R] [h : HasSymmFun R] :
      HasSymmFun (lift R l) :=
    { defSymmFun := λ a b => h.defSymmFun (l a) (l b) }

    instance hasTransFun [HasIdentity VV] [HasFunctors V VV VV] [HasTrans R] [h : HasTransFun R] :
      HasTransFun (lift R l) :=
    { defTransFun    := λ f   c => h.defTransFun f (l c),
      defTransFunFun := λ a b c => h.defTransFunFun (l a) (l b) (l c) }

  end lift

end MetaRelation



class HasInternalFunctors (U : Universe.{u}) [HasIdentity.{u, iu} U] extends
  HasFunctors U U U, HasCongrArg U U



-- The following axioms are equivalent to asserting the existence of five functors with specified
-- behavior, writing `Λ` for a functorial `λ` as defined in `Meta/Tactics/Functoriality.lean`:
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



class HasLinearFunOp (U : Universe) [HasIdentity U] [HasInternalFunctors U] extends
  HasIdFun U, HasRevAppFun U, HasCompFunFun U U where
(defRevAppFunFun  (A B : U)   : A ⟶{λ a => HasRevAppFun.revAppFun a B} ((A ⟶ B) ⟶ B))
(defCompFunFunFun (A B C : U) : (A ⟶ B) ⟶{λ F => HasCompFunFun.compFunFun F C} ((B ⟶ C) ⟶ (A ⟶ C)))

namespace HasLinearFunOp

  open MetaRelation HasFunctors HasCongrArg HasCongrFun HasCompFunFun

  variable {U : Universe} [HasIdentity U] [hFun : HasInternalFunctors U] [HasLinearFunOp U]

  @[reducible] def idFun (A : U) : A ⟶ A := HasIdFun.idFun A

  @[reducible] def appFun {A B : U} (F : A ⟶ B) : A ⟶ B := HasFunctors.appFun F
  def defAppFunFun (A B : U) : (A ⟶ B) ⟶{λ F => appFun F} (A ⟶ B) := HasIdFun.defIdFun (A ⟶ B)
  @[reducible] def appFunFun (A B : U) : (A ⟶ B) ⟶ A ⟶ B := defAppFunFun A B

  instance appFun.isFunApp {A B : U} {F : A ⟶ B} : IsFunApp (A ⟶ B) (appFun F) :=
  { F := appFunFun A B,
    a := F,
    e := byDef }

  @[reducible] def revAppFun {A : U} (a : A) (B : U) : (A ⟶ B) ⟶ B := HasRevAppFun.revAppFun a B
  @[reducible] def revAppFunFun (A B : U) : A ⟶ (A ⟶ B) ⟶ B := defRevAppFunFun A B

  instance revAppFun.isFunApp {A B : U} {a : A} : IsFunApp A (revAppFun a B) :=
  { F := revAppFunFun A B,
    a := a,
    e := byDef }

  @[reducible] def compFun {A B C : U} (F : A ⟶ B) (G : B ⟶ C) : A ⟶ C := HasCompFun.compFun F G
  @[reducible] def compFunFun {A B : U} (F : A ⟶ B) (C : U) : (B ⟶ C) ⟶ (A ⟶ C) := HasCompFunFun.compFunFun F C
  @[reducible] def compFunFunFun (A B C : U) : (A ⟶ B) ⟶ (B ⟶ C) ⟶ (A ⟶ C) := defCompFunFunFun A B C

  instance compFun.isFunApp {A B C : U} {F : A ⟶ B} {G : B ⟶ C} :
    IsFunApp (B ⟶ C) (compFun F G) :=
  HasCompFunFun.compFun.isFunApp

  instance compFunFun.isFunApp {A B C : U} {F : A ⟶ B} : IsFunApp (A ⟶ B) (HasCompFunFun.compFunFun F C) :=
  { F := compFunFunFun A B C,
    a := F,
    e := byDef }

  instance isPreorder : IsPreorder hFun.Fun :=
  { refl  := idFun,
    trans := HasCompFun.compFun }

  instance hasTransFun : HasTransFun hFun.Fun :=
  { defTransFun    := defCompFunFun,
    defTransFunFun := defCompFunFunFun }

end HasLinearFunOp



class HasSubLinearFunOp (U : Universe) [HasIdentity U] [HasInternalFunctors U] extends
  HasConstFun U U where
(defConstFunFun (A B : U) : B ⟶{λ b => HasConstFun.constFun A b} (A ⟶ B))

namespace HasSubLinearFunOp

  open HasFunctors

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasSubLinearFunOp U]

  @[reducible] def constFun (A : U) {B : U} (b : B) : A ⟶ B := HasConstFun.constFun A b
  @[reducible] def constFunFun (A B : U) : B ⟶ (A ⟶ B) := defConstFunFun A B

  instance constFun.isFunApp {A B : U} {b : B} : IsFunApp B (constFun A b) :=
  { F := constFunFun A B,
    a := b,
    e := byDef }

end HasSubLinearFunOp

class HasAffineFunOp (U : Universe) [HasIdentity U] [HasInternalFunctors U] extends
  HasLinearFunOp U, HasSubLinearFunOp U



class HasNonLinearFunOp (U : Universe) [HasIdentity U] [HasInternalFunctors U] extends
  HasDupFun U U where
(defDupFunFun (A B : U) : (A ⟶ A ⟶ B) ⟶{λ F => HasDupFun.dupFun F} (A ⟶ B))

namespace HasNonLinearFunOp

  open HasFunctors

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasNonLinearFunOp U]

  @[reducible] def dupFun {A B : U} (F : A ⟶ A ⟶ B) : A ⟶ B := HasDupFun.dupFun F
  @[reducible] def dupFunFun (A B : U) : (A ⟶ A ⟶ B) ⟶ (A ⟶ B) := defDupFunFun A B

  instance dupFun.isFunApp {A B : U} {F : A ⟶ A ⟶ B} : IsFunApp (A ⟶ A ⟶ B) (dupFun F) :=
  { F := dupFunFun A B,
    a := F,
    e := byDef }

end HasNonLinearFunOp

class HasFullFunOp (U : Universe) [HasIdentity U] [HasInternalFunctors U] extends
  HasAffineFunOp U, HasNonLinearFunOp U
