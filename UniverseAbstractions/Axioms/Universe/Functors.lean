import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.MetaRelations
import UniverseAbstractions.Axioms.Universe.Identity



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w uv vw uvw vv iu iv iuv ivv



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

end HasFunctors

class HasCongrArg (U : Universe.{u}) (V : Universe.{v}) {UV : Universe.{uv}} [HasFunctors U V UV]
                  [hId_U : HasIdentity.{u, iu} U] [hId_V : HasIdentity.{v, iv} V] where
(congrArg {A : U} {B : V} (F : A ⟶ B) {a₁ a₂ : A} : a₁ ≃ a₂ → F a₁ ≃ F a₂)

class HasCongrFun (U : Universe.{u}) (V : Universe.{v}) {UV : Universe.{uv}} [HasFunctors U V UV]
                  [hId_V : HasIdentity.{v, iv} V] [hId_UV : HasIdentity.{uv, iuv} UV] where
(congrFun {A : U} {B : V} {F₁ F₂ : A ⟶ B} (h : F₁ ≃ F₂) (a : A) : F₁ a ≃ F₂ a)



namespace HasFunctors

  open HasCongrArg HasCongrFun

  section

    variable {U V UV : Universe} [HasFunctors U V UV] [HasIdentity V]

    -- TODO: include proof of `congrArg` (also for multifunctors)
    -- (Then `congrFun` should probably be a prerequisite instead of derived.)
    structure DefFun (A : U) (B : V) (f : A → B) where
    (F           : A ⟶ B)
    (eff (a : A) : F a ≃ f a)

    notation:20 A:21 " ⟶{" f:0 "} " B:21 => HasFunctors.DefFun A B f

    variable {A : U} {B : V}

    def toDefFun' (F : A ⟶ B) {f : A → B} (h : ∀ a, F a ≃ f a) : A ⟶{f} B := ⟨F, h⟩
    def toDefFun (F : A ⟶ B) : A ⟶{apply F} B := toDefFun' F (λ a => HasInstanceEquivalences.refl (F a))
    @[reducible] def fromDefFun {f : A → B} (F : A ⟶{f} B) : A ⟶ B := F.F

    def byDef {f : A → B} {F : A ⟶{f} B} {a : A} : (fromDefFun F) a ≃ f a := F.eff a

    notation:60 F:61 " ◄ " h:61 => HasFunctors.toDefFun' F (λ _ => HasInstanceEquivalences.trans HasFunctors.byDef h)

    instance {F : A ⟶ B} : CoeDep (A ⟶ B) F  (A ⟶{apply F} B) := ⟨toDefFun F⟩
    instance {f : A → B} : Coe    (A ⟶{f} B) (A ⟶ B)          := ⟨fromDefFun⟩

    def castFun (F : A ⟶ B) (f : A → B) (h : ∀ a, F a ≃ f a) : A ⟶ B := fromDefFun (toDefFun' F h)

    def castDefFun {f f' : A → B} (F : A ⟶{f} B) (h : ∀ a, f a ≃ f' a) : A ⟶{f'} B :=
    ⟨F.F, λ a => h a • F.eff a⟩

    namespace IsFunApp

      instance (priority := low) refl (F : A ⟶ B) (a : A) : IsFunApp A (F a) :=
      { F := F,
        a := a,
        e := HasInstanceEquivalences.refl (F a) }

      def fromDef {f : A → B} (F : A ⟶{f} B) (a : A) : IsFunApp A (f a) :=
      { F := fromDefFun F,
        a := a,
        e := byDef }

    end IsFunApp

    def defAppFun (F : A ⟶ B) : A ⟶{λ a => F a} B := F
    @[reducible] def appFun (F : A ⟶ B) : A ⟶ B := defAppFun F

    variable [HasIdentity U] [HasCongrArg U V]

    def byArgDef {X XU : Universe} [HasFunctors X U XU] {A : X} {B : U} {C : V}
                 {f : A → B} {F : A ⟶{f} B} {G : B ⟶ C} {a : A} :
      G ((fromDefFun F) a) ≃ G (f a) :=
    congrArg G byDef

    def byDefDef {X XU : Universe} [HasFunctors X U XU] {A : X} {B : U} {C : V}
                 {f : A → B} {F : A ⟶{f} B} {g : B → C} {G : B ⟶{g} C} {a : A} :
      (fromDefFun G) ((fromDefFun F) a) ≃ g (f a) :=
    byDef • byArgDef

    def byArgDefDef {W VW X XU : Universe} [HasFunctors V W VW] [HasIdentity W] [HasCongrArg V W]
                    [HasFunctors X U XU] {A : X} {B : U} {C : V} {D : W}
                    {f : A → B} {F : A ⟶{f} B} {g : B → C} {G : B ⟶{g} C} {H : C ⟶ D} {a : A} :
      H ((fromDefFun G) ((fromDefFun F) a)) ≃ H (g (f a)) :=
    congrArg H byDefDef

    def byDefDefDef {W VW X XU : Universe} [HasFunctors V W VW] [HasIdentity W] [HasCongrArg V W]
                    [HasFunctors X U XU] {A : X} {B : U} {C : V} {D : W}
                    {f : A → B} {F : A ⟶{f} B} {g : B → C} {G : B ⟶{g} C} {h : C → D} {H : C ⟶{h} D}
                    {a : A} :
      (fromDefFun H) ((fromDefFun G) ((fromDefFun F) a)) ≃ h (g (f a)) :=
    byDef • byArgDefDef

  end

  section

    variable {U V W VW UVW : Universe} [HasFunctors V W VW] [HasFunctors U VW UVW] [HasIdentity W]
             [HasIdentity VW]

    structure DefFun₂ (A : U) (B : V) (C : W) (f : A → B → C) where
    (defFun (a : A) : B ⟶{f a} C)
    (defFunFun      : A ⟶{λ a => defFun a} (B ⟶ C))

    notation:20 A:21 " ⟶ " B:21 " ⟶{" f:0 "} " C:21 => HasFunctors.DefFun₂ A B C f

    variable {A : U} {B : V} {C : W}

    def toDefFun₂' (F : A ⟶ B ⟶ C) {f : A → B → C} (h : ∀ a b, F a b ≃ f a b) : A ⟶ B ⟶{f} C :=
    ⟨λ a => toDefFun' (F a) (h a), toDefFun F⟩

    def toDefFun₂ (F : A ⟶ B ⟶ C) : A ⟶ B ⟶{λ a => apply (F a)} C :=
    toDefFun₂' F (λ a b => HasInstanceEquivalences.refl (F a b))

    @[reducible] def fromDefFun₂ {f : A → B → C} (F : A ⟶ B ⟶{f} C) : A ⟶ B ⟶ C := F.defFunFun

    instance {F : A ⟶ B ⟶ C} : CoeDep (A ⟶ B ⟶ C) F  (A ⟶ B ⟶{λ a => apply (F a)} C) := ⟨toDefFun₂ F⟩
    instance {f : A → B → C} : Coe    (A ⟶ B ⟶{f} C) (A ⟶ B ⟶ C)                     := ⟨fromDefFun₂⟩

    def castFun₂ (F : A ⟶ B ⟶ C) (f : A → B → C) (h : ∀ a b, F a b ≃ f a b) : A ⟶ B ⟶ C :=
    fromDefFun₂ (toDefFun₂' F h)

    def castDefFun₂ {f f' : A → B → C} (F : A ⟶ B ⟶{f} C) (h : ∀ a b, f a b ≃ f' a b) :
      A ⟶ B ⟶{f'} C :=
    ⟨λ a => castDefFun (F.defFun a) (h a), F.defFunFun⟩

    variable [HasCongrFun V W]

    def byFunDef {f : A → (B ⟶ C)} {F : A ⟶{f} (B ⟶ C)} {a : A} {b : B} :
      (fromDefFun F) a b ≃ (f a) b :=
    congrFun byDef b

    -- This works for `DefFun₂` but is more general.
    def byDef₂ {f : A → B → C} {F' : ∀ a, B ⟶{f a} C} {F : A ⟶{λ a => F' a} (B ⟶ C)} {a : A} {b : B} :
      (fromDefFun F) a b ≃ f a b :=
    byDef • byFunDef

    notation:60 F:61 " ◄◄ " h:61 => HasFunctors.toDefFun₂' F (λ _ _ => HasInstanceEquivalences.trans HasFunctors.byDef₂ h)

  end

  section

    variable {U V W X WX VWX UVWX : Universe} [HasFunctors W X WX] [HasFunctors V WX VWX]
             [HasFunctors U VWX UVWX] [HasIdentity X] [HasIdentity WX] [HasIdentity VWX]

    structure DefFun₃ (A : U) (B : V) (C : W) (D : X) (f : A → B → C → D) where
    (defFun (a : A) : B ⟶ C ⟶{f a} D)
    (defFunFunFun   : A ⟶{λ a => defFun a} (B ⟶ C ⟶ D))

    notation:20 A:21 " ⟶ " B:21 " ⟶ " C:21 " ⟶{" f:0 "} " D:21 => HasFunctors.DefFun₃ A B C D f

    variable {A : U} {B : V} {C : W} {D : X}

    def DefFun₃.defFunFun {f : A → B → C → D} (F : A ⟶ B ⟶ C ⟶{f} D) :
      A ⟶ B ⟶{λ a b => fromDefFun ((F.defFun a).defFun b)} (C ⟶ D) :=
    ⟨λ a => (F.defFun a).defFunFun, F.defFunFunFun⟩

    def toDefFun₃' (F : A ⟶ B ⟶ C ⟶ D) {f : A → B → C → D} (h : ∀ a b c, F a b c ≃ f a b c) :
      A ⟶ B ⟶ C ⟶{f} D :=
    ⟨λ a => toDefFun₂' (F a) (h a), toDefFun F⟩

    def toDefFun₃ (F : A ⟶ B ⟶ C ⟶ D) : A ⟶ B ⟶ C ⟶{λ a b => apply (F a b)} D :=
    toDefFun₃' F (λ a b c => HasInstanceEquivalences.refl (F a b c))

    @[reducible] def fromDefFun₃ {f : A → B → C → D} (F : A ⟶ B ⟶ C ⟶{f} D) : A ⟶ B ⟶ C ⟶ D :=
    F.defFunFunFun

    instance {F : A ⟶ B ⟶ C ⟶ D} : CoeDep (A ⟶ B ⟶ C ⟶ D) F  (A ⟶ B ⟶ C ⟶{λ a b => apply (F a b)} D) := ⟨toDefFun₃ F⟩
    instance {f : A → B → C → D} : Coe    (A ⟶ B ⟶ C ⟶{f} D) (A ⟶ B ⟶ C ⟶ D)                         := ⟨fromDefFun₃⟩

    def castFun₃ (F : A ⟶ B ⟶ C ⟶ D) (f : A → B → C → D) (h : ∀ a b c, F a b c ≃ f a b c) : A ⟶ B ⟶ C ⟶ D :=
    fromDefFun₃ (toDefFun₃' F h)

    def castDefFun₃ {f f' : A → B → C → D} (F : A ⟶ B ⟶ C ⟶{f} D) (h : ∀ a b c, f a b c ≃ f' a b c) :
      A ⟶ B ⟶ C ⟶{f'} D :=
    ⟨λ a => castDefFun₂ (F.defFun a) (h a), F.defFunFunFun⟩

    variable [HasCongrFun V WX] [HasCongrFun W X]

    def byFunDef₂ {f : A → (B ⟶ C ⟶ D)} {F : A ⟶{f} (B ⟶ C ⟶ D)} {a : A} {b : B} {c : C} :
      (fromDefFun F) a b c ≃ (f a) b c :=
    congrFun byFunDef c

    def byDef₃ {f : A → B → C → D} {F'' : ∀ a b, C ⟶{f a b} D} {F' : ∀ a, B ⟶{λ b => F'' a b} (C ⟶ D)}
               {F : A ⟶{λ a => F' a} (B ⟶ C ⟶ D)} {a : A} {b : B} {c : C} :
      (fromDefFun F) a b c ≃ f a b c :=
    byDef • congrFun byDef₂ c

    notation:60 F:61 " ◄◄◄ " h:61 => HasFunctors.toDefFun₃' F (λ _ _ _ => HasInstanceEquivalences.trans HasFunctors.byDef₃ h)

  end

  section

    variable {U V W X Y XY WXY VWXY UVWXY : Universe} [HasFunctors X Y XY] [HasFunctors W XY WXY]
             [HasFunctors V WXY VWXY] [HasFunctors U VWXY UVWXY] [HasIdentity Y] [HasIdentity XY]
             [HasIdentity WXY] [HasIdentity VWXY]

    structure DefFun₄ (A : U) (B : V) (C : W) (D : X) (E : Y) (f : A → B → C → D → E) where
    (defFun (a : A)  : B ⟶ C ⟶ D ⟶{f a} E)
    (defFunFunFunFun : A ⟶{λ a => defFun a} (B ⟶ C ⟶ D ⟶ E))

    notation:20 A:21 " ⟶ " B:21 " ⟶ " C:21 " ⟶ " D:21 " ⟶{" f:0 "} " E:21 => HasFunctors.DefFun₄ A B C D E f

    variable {A : U} {B : V} {C : W} {D : X} {E : Y}

    def DefFun₄.defFunFun {f : A → B → C → D → E} (F : A ⟶ B ⟶ C ⟶ D ⟶{f} E) :
      A ⟶ B ⟶ C ⟶{λ a b c => fromDefFun (((F.defFun a).defFun b).defFun c)} (D ⟶ E) :=
    ⟨λ a => (F.defFun a).defFunFun, F.defFunFunFunFun⟩

    def DefFun₄.defFunFunFun {f : A → B → C → D → E} (F : A ⟶ B ⟶ C ⟶ D ⟶{f} E) :
      A ⟶ B ⟶{λ a b => fromDefFun₂ ((F.defFun a).defFun b)} (C ⟶ D ⟶ E) :=
    DefFun₃.defFunFun (DefFun₄.defFunFun F)

    def toDefFun₄' (F : A ⟶ B ⟶ C ⟶ D ⟶ E) {f : A → B → C → D → E} (h : ∀ a b c d, F a b c d ≃ f a b c d) :
      A ⟶ B ⟶ C ⟶ D ⟶{f} E :=
    ⟨λ a => toDefFun₃' (F a) (h a), toDefFun F⟩

    def toDefFun₄ (F : A ⟶ B ⟶ C ⟶ D ⟶ E) : A ⟶ B ⟶ C ⟶ D ⟶{λ a b c => apply (F a b c)} E :=
    toDefFun₄' F (λ a b c d => HasInstanceEquivalences.refl (F a b c d))

    @[reducible] def fromDefFun₄ {f : A → B → C → D → E} (F : A ⟶ B ⟶ C ⟶ D ⟶{f} E) : A ⟶ B ⟶ C ⟶ D ⟶ E :=
    F.defFunFunFunFun

    instance {F : A ⟶ B ⟶ C ⟶ D ⟶ E} : CoeDep (A ⟶ B ⟶ C ⟶ D ⟶ E) F  (A ⟶ B ⟶ C ⟶ D ⟶{λ a b c => apply (F a b c)} E) := ⟨toDefFun₄ F⟩
    instance {f : A → B → C → D → E} : Coe    (A ⟶ B ⟶ C ⟶ D ⟶{f} E) (A ⟶ B ⟶ C ⟶ D ⟶ E)                             := ⟨fromDefFun₄⟩

    def castFun₄ (F : A ⟶ B ⟶ C ⟶ D ⟶ E) (f : A → B → C → D → E) (h : ∀ a b c d, F a b c d ≃ f a b c d) : A ⟶ B ⟶ C ⟶ D ⟶ E :=
    fromDefFun₄ (toDefFun₄' F h)

    def castDefFun₄ {f f' : A → B → C → D → E} (F : A ⟶ B ⟶ C ⟶ D ⟶{f} E) (h : ∀ a b c d, f a b c d ≃ f' a b c d) :
      A ⟶ B ⟶ C ⟶ D ⟶{f'} E :=
    ⟨λ a => castDefFun₃ (F.defFun a) (h a), F.defFunFunFunFun⟩

    variable [HasCongrFun V WXY] [HasCongrFun W XY] [HasCongrFun X Y]

    def byFunDef₃ {f : A → (B ⟶ C ⟶ D ⟶ E)} {F : A ⟶{f} (B ⟶ C ⟶ D ⟶ E)}
                  {a : A} {b : B} {c : C} {d : D} :
      (fromDefFun F) a b c d ≃ (f a) b c d :=
    congrFun byFunDef₂ d

    def byDef₄ {f : A → B → C → D → E} {F''': ∀ a b c, D ⟶{f a b c} E}
               {F'' : ∀ a b, C ⟶{λ c => F''' a b c} (D ⟶ E)} {F' : ∀ a, B ⟶{λ b => F'' a b} (C ⟶ D ⟶ E)}
               {F : A ⟶{λ a => F' a} (B ⟶ C ⟶ D ⟶ E)} {a : A} {b : B} {c : C} {d : D} :
      (fromDefFun F) a b c d ≃ f a b c d :=
    byDef • congrFun byDef₃ d

    notation:60 F:61 " ◄◄◄◄ " h:61 => HasFunctors.toDefFun₄' F (λ _ _ _ _ => HasInstanceEquivalences.trans HasFunctors.byDef₄ h)

  end

end HasFunctors

namespace HasCongrFun

  open HasFunctors HasCongrArg

  section

    variable {U V UV : Universe} [HasFunctors U V UV] [HasIdentity V] [HasIdentity UV]

    section

      variable [HasCongrFun U V] {A : U} {B : V}

      def applyCongrFun {F₁ F₂ : A ⟶ B} (h : F₁ ≃ F₂) (a : A) {b₁ b₂ : B} (h₁ : F₁ a ≃ b₁)
                        (h₂ : F₂ a ≃ b₂) :
        b₁ ≃ b₂ :=
      h₂ • congrFun h a • h₁⁻¹

      def defCongrFun {f₁ f₂ : A → B} {F₁ : A ⟶{f₁} B} {F₂ : A ⟶{f₂} B}
                      (h : fromDefFun F₁ ≃ fromDefFun F₂) (a : A) :
        f₁ a ≃ f₂ a :=
      applyCongrFun h a byDef byDef

    end

    section

      variable {A : U} {B : V}

      -- This definition might seem a little silly: it includes a hypothesis that isn't actually used
      -- in the definition. However, this is quite useful when `IsExtensional` is used as the type of
      -- an axiom. When implementing the axiom, the hypothesis is then accessible in a generic way,
      -- so the implementation shrinks to a proof of `F₁ ≃ F₂` given `∀ a, F₁ a ≃ F₂ a`. If functors
      -- are extensional, then this proof is completely generic (see `Trivial.lean`). In general it
      -- can be regarded as a proof that the instance of `F₁ a ≃ F₂ a` is natural in `a`.

      -- TODO: Stack extensionality in the same way as functors.

      def IsExtensional (F₁ F₂ : A ⟶ B) (h : ∀ a, F₁ a ≃ F₂ a) := F₁ ≃ F₂
      notation:25 F₁:26 " ≃{" h:0 "} " F₂:26 => HasCongrFun.IsExtensional F₁ F₂ h
      notation:25 F₁:26 " ≃{" h:0 " ▻|} " F₂:26 => HasCongrFun.IsExtensional F₁ F₂ (λ _ => h • HasFunctors.byDef)

      def IsExtensional' (F₁ F₂ : A ⟶ B) {f : A → B}
                         (hf₁ : ∀ a, F₁ a ≃ f a) (hf₂ : ∀ a, f a ≃ F₂ a) :=
      IsExtensional F₁ F₂ (λ a => hf₂ a • hf₁ a)
      notation:25 F₁:26 " ≃{▻ " h:0 "} " F₂:26 => HasCongrFun.IsExtensional' F₁ F₂ (λ _ => HasFunctors.byDef) h
      notation:25 F₁:26 " ≃{" hf₁:0 " ▻ " h:0 "} " F₂:26 => HasCongrFun.IsExtensional' F₁ F₂ (λ _ => hf₁ • HasFunctors.byDef) h

      def IsExtensional'' (F₁ F₂ : A ⟶ B) {f : A → B}
                          (hf₁ : ∀ a, F₁ a ≃ f a) (hf₂ : ∀ a, F₂ a ≃ f a) :=
      IsExtensional F₁ F₂ (λ a => (hf₂ a)⁻¹ • hf₁ a)
      notation:25 F₁:26 " ≃{" h:0 " ◅} " F₂:26 => HasCongrFun.IsExtensional'' F₁ F₂ h (λ _ => HasFunctors.byDef)
      notation:25 F₁:26 " ≃{" h:0 " ◅ " hf₂:0 "} " F₂:26 => HasCongrFun.IsExtensional'' F₁ F₂ h (λ _ => hf₂ • HasFunctors.byDef)
      notation:25 F₁:26 " ≃{▻-◅} " F₂:26 => HasCongrFun.IsExtensional'' F₁ F₂ (λ _ => HasFunctors.byDef) (λ _ => HasFunctors.byDef)
      notation:25 F₁:26 " ≃{" hf₁:0 " ▻-◅} " F₂:26 => HasCongrFun.IsExtensional'' F₁ F₂ (λ _ => hf₁ • HasFunctors.byDef) (λ _ => HasFunctors.byDef)
      notation:25 F₁:26 " ≃{▻-◅ " hf₂:0 "} " F₂:26 => HasCongrFun.IsExtensional'' F₁ F₂ (λ _ => HasFunctors.byDef) (λ _ => hf₂ • HasFunctors.byDef)
      notation:25 F₁:26 " ≃{" hf₁:0 " ▻-◅ " hf₂:0 "} " F₂:26 => HasCongrFun.IsExtensional'' F₁ F₂ (λ _ => hf₁ • HasFunctors.byDef) (λ _ => hf₂ • HasFunctors.byDef)

      def IsExtensional''' (F₁ F₂ : A ⟶ B) {f₁ f₂ : A → B} (h : ∀ a, f₁ a ≃ f₂ a)
                           (hf₁ : ∀ a, F₁ a ≃ f₁ a) (hf₂ : ∀ a, F₂ a ≃ f₂ a) :=
      IsExtensional F₁ F₂ (λ a => (hf₂ a)⁻¹ • h a • hf₁ a)
      notation:25 F₁:26 " ≃{▻ " h:0 " ◅}" F₂:26 => HasCongrFun.IsExtensional''' F₁ F₂ h (λ _ => HasFunctors.byDef) (λ _ => HasFunctors.byDef)
      notation:25 F₁:26 " ≃{" hf₁:0 " ▻ " h:0 " ◅} " F₂:26 => HasCongrFun.IsExtensional''' F₁ F₂ h (λ _ => hf₁ • HasFunctors.byDef) (λ _ => HasFunctors.byDef)
      notation:25 F₁:26 " ≃{▻ " h:0 " ◅ " hf₂:0 "} " F₂:26 => HasCongrFun.IsExtensional''' F₁ F₂ h (λ _ => HasFunctors.byDef) (λ _ => hf₂ • HasFunctors.byDef)
      notation:25 F₁:26 " ≃{" hf₁:0 " ▻ " h:0 " ◅ " hf₂:0 "} " F₂:26 => HasCongrFun.IsExtensional''' F₁ F₂ h (λ _ => hf₁ • HasFunctors.byDef) (λ _ => hf₂ • HasFunctors.byDef)
      notation:25 F₁:26 " ≃⦃" A':0 " ▻ " h:0 " ◅ " B':0 "⦄ " F₂:26 => HasCongrFun.IsExtensional''' (A := A') (B := B') F₁ F₂ h (λ _ => HasFunctors.byDef) (λ _ => HasFunctors.byDef)

      def IsDefExtensional {f₁ f₂ : A → B} (F₁ F₂ : A ⟶{f₁} B) := fromDefFun F₁ ≃{▻-◅} fromDefFun F₂

    end

    class IsExtApp (A : outParam U) {B : V} {b₁ b₂ : B} (h : b₁ ≃ b₂) where
    {F₁ F₂ : A ⟶ B}
    (e     : F₁ ≃ F₂)
    (a     : A)
    (e₁    : F₁ a ≃ b₁)
    (e₂    : F₂ a ≃ b₂)

    namespace IsExtApp

      def fromExt {A : U} {B : V} {F₁ F₂ : A ⟶ B} {f₁ f₂ : A → B} {h : ∀ a, f₁ a ≃ f₂ a}
                  {hf₁ : ∀ a, F₁ a ≃ f₁ a} {hf₂ : ∀ a, F₂ a ≃ f₂ a}
                  (e : IsExtensional''' F₁ F₂ h hf₁ hf₂) (a : A) :
        IsExtApp A (h a) :=
      { e  := e,
        a  := a,
        e₁ := hf₁ a,
        e₂ := hf₂ a }

      instance invCongrFun [HasCongrFun U V] {A : U} {B : V} {F₁ F₂ : A ⟶ B} (e : F₁ ≃ F₂) (a : A) :
        IsExtApp A (congrFun e a) :=
      { e  := e,
        a  := a,
        e₁ := HasInstanceEquivalences.refl (F₁ a),
        e₂ := HasInstanceEquivalences.refl (F₂ a) }

      variable (A : U) {B : V} {b₁ b₂ : B} (h : b₁ ≃ b₂) [h : IsExtApp A h]

      instance isFunApp₁ : IsFunApp A b₁ :=
      { F := h.F₁,
        a := h.a,
        e := h.e₁ }

      instance isFunApp₂ : IsFunApp A b₂ :=
      { F := h.F₂,
        a := h.a,
        e := h.e₂ }

    end IsExtApp

  end

end HasCongrFun

namespace HasCongrArg

  open HasFunctors HasCongrFun

  section

    variable {U V UV : Universe} [HasFunctors U V UV] [HasIdentity U] [HasIdentity V] [HasCongrArg U V]

    def applyCongrArg {A : U} {B : V} (F : A ⟶ B) {a₁ a₂ : A} (h : a₁ ≃ a₂)
                      {b₁ b₂ : B} (h₁ : F a₁ ≃ b₁) (h₂ : F a₂ ≃ b₂) :
      b₁ ≃ b₂ :=
    h₂ • congrArg F h • h₁⁻¹

    def defCongrArg {A : U} {B : V} {f : A → B} (F : A ⟶{f} B) {a₁ a₂ : A} : a₁ ≃ a₂ → f a₁ ≃ f a₂ :=
    λ h => applyCongrArg (fromDefFun F) h byDef byDef

  end

  section

    variable {U V W VW UVW : Universe} [HasFunctors V W VW] [HasFunctors U VW UVW] [HasIdentity W]
             [HasIdentity VW] {A : U} {B : V} {C : W}

    def defCongrArg₂A [HasIdentity U] [HasCongrArg U VW] [HasCongrFun V W]
                      {f : A → B → C} (F : A ⟶ B ⟶{f} C) {a₁ a₂ : A} (ha : a₁ ≃ a₂) (b : B) :
      f a₁ b ≃ f a₂ b :=
    defCongrFun (defCongrArg F.defFunFun ha) b

    def defCongrArg₂B [HasIdentity V] [HasCongrArg V W]
                      {f : A → B → C} (F : A ⟶ B ⟶{f} C) (a : A) {b₁ b₂ : B} (hb : b₁ ≃ b₂) :
      f a b₁ ≃ f a b₂ :=
    defCongrArg (F.defFun a) hb

    section

      variable [HasIdentity U] [HasIdentity V] [HasCongrArg V W] [HasCongrArg U VW] [HasCongrFun V W]
               {A : U} {B : V} {C : W}

      def congrArg₂ (F : A ⟶ B ⟶ C) {a₁ a₂ : A} {b₁ b₂ : B} :
        a₁ ≃ a₂ → b₁ ≃ b₂ → F a₁ b₁ ≃ F a₂ b₂ :=
      λ ha hb => congrFun (congrArg F ha) b₂ • congrArg (F a₁) hb

      def applyCongrArg₂ (F : A ⟶ B ⟶ C) {a₁ a₂ : A} (ha : a₁ ≃ a₂) {b₁ b₂ : B} (hb : b₁ ≃ b₂)
                         {c₁ c₂ : C} (h₁ : F a₁ b₁ ≃ c₁) (h₂ : F a₂ b₂ ≃ c₂) :
        c₁ ≃ c₂ :=
      h₂ • congrArg₂ F ha hb • h₁⁻¹

      def defCongrArg₂ {f : A → B → C} (F : A ⟶ B ⟶{f} C) {a₁ a₂ : A} {b₁ b₂ : B} :
        a₁ ≃ a₂ → b₁ ≃ b₂ → f a₁ b₁ ≃ f a₂ b₂ :=
      λ ha hb => applyCongrArg₂ (fromDefFun₂ F) ha hb byDef₂ byDef₂

    end

  end

end HasCongrArg



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

  open HasFunctors HasCongrArg

  variable {U V W UV VW UW : Universe} [HasFunctors U V UV] [HasFunctors V W VW] [HasFunctors U W UW]
           [HasIdentity W] [HasCompFun U V W]

  @[reducible] def compFun {A : U} {B : V} {C : W} (F : A ⟶ B) (G : B ⟶ C) : A ⟶ C := defCompFun F G
  notation:90 G:91 " ⊙ " F:90 => HasCompFun.compFun F G

  def defCompDefFun [HasIdentity V] [HasCongrArg V W] {A : U} {B : V} {C : W} {f : A → B}
                    (F : A ⟶{f} B) (G : B ⟶ C) :
    A ⟶{λ a => G (f a)} C :=
  G ⊙ F
  ◄ byArgDef

  def defCompDefDefFun [HasIdentity V] [HasCongrArg V W] {A : U} {B : V} {C : W}
                       {f : A → B} {g : B → C} (F : A ⟶{f} B) (G : B ⟶{g} C) :
    A ⟶{λ a => g (f a)} C :=
  fromDefFun G ⊙ F
  ◄ byDefDef

end HasCompFun

class HasCompFunFun (U W : Universe) {UW : Universe} [HasFunctors U W UW] [HasFunctors W UW UW]
                    [HasFunctors W W W] [HasIdentity W] [HasIdentity UW] extends
  HasCompFun U W W where
(defCompFunFun {A : U} {B : W} (F : A ⟶ B) (C : W) : (B ⟶ C) ⟶{λ G => G ⊙ F} (A ⟶ C))

namespace HasCompFunFun

  open HasFunctors HasCompFun

  variable {U W UW : Universe} [HasFunctors U W UW] [HasFunctors W UW UW]
           [HasFunctors W W W] [HasIdentity W] [HasIdentity UW] [HasCompFunFun U W]

  def defCompFun₂ {A : U} {B : W} (F : A ⟶ B) (C : W) : (B ⟶ C) ⟶ A ⟶{λ G a => G (F a)} C :=
  ⟨λ G => defCompFun F G, defCompFunFun F C⟩

  @[reducible] def compFunFun {A : U} {B : W} (F : A ⟶ B) (C : W) : (B ⟶ C) ⟶ (A ⟶ C) :=
  defCompFun₂ F C

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

  open HasFunctors HasCompFun

  variable {U W UW : Universe} [HasFunctors U U U] [HasFunctors U W UW]
           [HasFunctors U UW UW] [HasIdentity W] [HasIdentity UW] [HasRevCompFunFun U W]

  def defRevCompFun₂ (A : U) {B : U} {C : W} (G : B ⟶ C) : (A ⟶ B) ⟶ A ⟶{λ F a => G (F a)} C :=
  ⟨λ F => defCompFun F G, defRevCompFunFun A G⟩

  @[reducible] def revCompFunFun (A : U) {B : U} {C : W} (G : B ⟶ C) : (A ⟶ B) ⟶ (A ⟶ C) :=
  defRevCompFun₂ A G

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

  open HasFunctors

  variable {U V W VW UVW UW : Universe} [HasFunctors V W VW] [HasFunctors U VW UVW]
           [HasFunctors U W UW] [HasIdentity W] [HasSwapFun U V W]

  @[reducible] def swapFun {A : U} {B : V} {C : W} (F : A ⟶ B ⟶ C) (b : B) : A ⟶ C := defSwapFun F b

  def defSwapDefFun' [HasIdentity VW] [HasCongrFun V W] {A : U} {B : V} {C : W} {f : A → (B ⟶ C)}
                     (F : A ⟶{f} (B ⟶ C)) (b : B) :
    A ⟶{λ a => (f a) b} C :=
  swapFun F b
  ◄ byFunDef

  def defSwapDefFun [HasIdentity VW] [HasCongrFun V W] {A : U} {B : V} {C : W} {f : A → B → C}
                    (F : A ⟶ B ⟶{f} C) (b : B) :
    A ⟶{λ a => f a b} C :=
  swapFun F b
  ◄ byDef₂

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

  def defSwapFun₂ {A : U} {B : V} {C : W} (F : A ⟶ B ⟶ C) : B ⟶ A ⟶{λ b a => F a b} C :=
  ⟨λ b => defSwapFun F b, defSwapFunFun F⟩

  @[reducible] def swapFunFun {A : U} {B : V} {C : W} (F : A ⟶ B ⟶ C) : B ⟶ A ⟶ C := defSwapFun₂ F

  instance swapFun.isFunApp {A : U} {B : V} {C : W} {F : A ⟶ B ⟶ C} {b : B} :
    IsFunApp B (swapFun F b) :=
  { F := swapFunFun F,
    a := b,
    e := byDef }

  def defSwapDefFun₂ [HasIdentity VW] [HasCongrFun U W] [HasCongrFun V W] {A : U} {B : V} {C : W}
                     {f : A → B → C} (F : A ⟶ B ⟶{f} C) :
    B ⟶ A ⟶{λ b a => f a b} C :=
  ⟨λ b => defSwapDefFun F b, defSwapFunFun (fromDefFun₂ F)⟩

end HasSwapFunFun

class HasDupFun (U V : Universe) {UV UUV : Universe} [HasFunctors U V UV] [HasFunctors U UV UUV]
                [HasIdentity V] where
(defDupFun {A : U} {B : V} (F : A ⟶ A ⟶ B) : A ⟶{λ a => F a a} B)

namespace HasDupFun

  open HasFunctors

  variable {U V UV UUV : Universe} [HasFunctors U V UV] [HasFunctors U UV UUV] [HasIdentity V]
           [HasDupFun U V]

  @[reducible] def dupFun {A : U} {B : V} (F : A ⟶ A ⟶ B) : A ⟶ B := defDupFun F

  def defDupDefFun [HasIdentity UV] [HasCongrFun U V] {A : U} {B : V} {f : A → (A ⟶ B)}
                   (F : A ⟶{f} (A ⟶ B)) :
    A ⟶{λ a => (f a) a} B :=
  dupFun F
  ◄ byFunDef

end HasDupFun

class HasSubstFun (U V W : Universe) {UV VW UVW UW : Universe} [HasFunctors U V UV] [HasFunctors V W VW]
                  [HasFunctors U VW UVW] [HasFunctors U W UW] [HasIdentity W] where
(defSubstFun {A : U} {B : V} {C : W} (F : A ⟶ B) (G : A ⟶ B ⟶ C) : A ⟶{λ a => G a (F a)} C)

namespace HasSubstFun

  open HasFunctors

  variable {U V W UV VW UVW UW : Universe} [HasFunctors U V UV] [HasFunctors V W VW] [HasFunctors U W UW]
           [HasFunctors U VW UVW] [HasFunctors U W UW] [HasIdentity W] [HasSubstFun U V W]

  @[reducible] def substFun {A : U} {B : V} {C : W} (F : A ⟶ B) (G : A ⟶ B ⟶ C) : A ⟶ C := defSubstFun F G

  def defSubstDefFun' [HasIdentity V] [HasIdentity VW] [HasCongrArg V W] [HasCongrFun V W]
                      {A : U} {B : V} {C : W} {f : A → B} (F : A ⟶{f} B) {g : A → (B ⟶ C)} (G : A ⟶{g} (B ⟶ C)) :
    A ⟶{λ a => (g a) (f a)} C :=
  substFun (B := B) F G
  ◄ byFunDef • byArgDef

  def defSubstDefFun [HasIdentity V] [HasIdentity VW] [HasCongrArg V W] [HasCongrFun V W]
                     {A : U} {B : V} {C : W} {f : A → B} (F : A ⟶{f} B) {g : A → B → C} (G : A ⟶ B ⟶{g} C) :
    A ⟶{λ a => g a (f a)} C :=
  substFun (B := B) F G
  ◄ byDef₂ • byArgDef

end HasSubstFun

class HasRevSubstFunFun (U W : Universe) {UW : Universe} [HasFunctors U U U] [HasFunctors U W UW]
                        [HasFunctors U UW UW] [HasIdentity W] [HasIdentity UW] extends
  HasSubstFun U U W where
(defRevSubstFunFun {A B : U} {C : W} (G : A ⟶ B ⟶ C) : (A ⟶ B) ⟶{λ F => HasSubstFun.substFun F G} (A ⟶ C))

namespace HasRevSubstFunFun

  open HasFunctors HasSubstFun

  variable {U W : Universe} {UW : Universe} [HasFunctors U U U] [HasFunctors U W UW]
           [HasFunctors U UW UW] [HasIdentity W] [HasIdentity UW] [HasRevSubstFunFun U W]

  def defRevSubstFun₂ {A B : U} {C : W} (G : A ⟶ B ⟶ C) : (A ⟶ B) ⟶ A ⟶{λ F a => G a (F a)} C :=
  ⟨λ F => defSubstFun F G, defRevSubstFunFun G⟩

  @[reducible] def revSubstFunFun {A B : U} {C : W} (G : A ⟶ B ⟶ C) : (A ⟶ B) ⟶ (A ⟶ C) :=
  defRevSubstFun₂ G

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

  def defRevBiCompFun₂ {A : U} {B : V} {C : U} {D : X} (H : B ⟶ C ⟶ D) (F : A ⟶ B) :
    (A ⟶ C) ⟶ A ⟶{λ G a => H (F a) (G a)} D :=
  ⟨λ G => defBiCompFun F G H, defRevBiCompFunFun H F⟩

  @[reducible] def revBiCompFunFun {A : U} {B : V} {C : U} {D : X} (H : B ⟶ C ⟶ D) (F : A ⟶ B) :
    (A ⟶ C) ⟶ (A ⟶ D) :=
  defRevBiCompFun₂ H F

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

  def defRevBiCompFun₃ (A : U) {B C : U} {D : X} (H : B ⟶ C ⟶ D) :
    (A ⟶ B) ⟶ (A ⟶ C) ⟶ A ⟶{λ F G a => H (F a) (G a)} D :=
  ⟨λ F => defRevBiCompFun₂ H F, defRevBiCompFunFunFun A H⟩

  @[reducible] def revBiCompFunFunFun (A : U) {B C : U} {D : X} (H : B ⟶ C ⟶ D) :
    (A ⟶ B) ⟶ (A ⟶ C) ⟶ (A ⟶ D) :=
  defRevBiCompFun₃ A H

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
                     {A : U} {B : V} {C : W} (f : A → B → C) where
(defFun : A ⟶ B ⟶{f} C)

namespace IsBiFunctorial

  open HasFunctors HasCongrArg HasCongrFun HasSwapFun HasSwapFunFun

  variable {U V W VW UVW : Universe} [HasFunctors V W VW] [HasFunctors U VW UVW]
           [HasIdentity W] [HasIdentity VW] {A : U} {B : V} {C : W} (f : A → B → C)
           [h : IsBiFunctorial f]

  instance : IsRightFunctorial f := ⟨h.defFun.defFun⟩

  @[reducible] def rightFunFun : A ⟶ B ⟶ C := h.defFun.defFunFun

  def rightFun.congrArg [HasIdentity U] [HasCongrArg U VW] {a₁ a₂ : A} (ha : a₁ ≃ a₂) :
    IsRightFunctorial.rightFun f a₁ ≃ IsRightFunctorial.rightFun f a₂ :=
  defCongrArg h.defFun.defFunFun ha

  variable {UW : Universe} [HasFunctors U W UW] [HasCongrFun V W]

  def defLeftFun [HasSwapFun U V W] (b : B) :
    A ⟶{λ a => f a b} C :=
  swapFun (rightFunFun f) b
  ◄ byDef₂

  instance [HasSwapFun U V W] : IsLeftFunctorial f := ⟨defLeftFun f⟩

  instance isFunApp₂ [HasSwapFun U V W] (a : A) (b : B) : IsFunApp₂ A B (f a b) :=
  { toIsFunApp := IsRightFunctorial.isFunApp f a b,
    h₂         := IsLeftFunctorial.isFunApp  f a b }

  variable {VUW : Universe} [HasFunctors V UW VUW] [HasIdentity UW] [HasCongrFun U W]
           [HasSwapFunFun U V W]

  def defRevFun : B ⟶ A ⟶{λ b a => f a b} C := defSwapDefFun₂ h.defFun

  @[reducible] def leftFunFun : B ⟶ A ⟶ C := (defRevFun f).defFunFun

  def leftFun.congrArg [HasIdentity V] [HasCongrArg V UW] {b₁ b₂ : B} (hb : b₁ ≃ b₂) :
    IsLeftFunctorial.leftFun f b₁ ≃ IsLeftFunctorial.leftFun f b₂ :=
  defCongrArg (defRevFun f).defFunFun hb

end IsBiFunctorial



namespace MetaRelation

  open HasFunctors HasCongrArg HasSwapFun HasSwapFunFun

  variable {α : Sort u} {V : Universe.{v}} {VV : Universe.{vv}} [HasIdentity.{v, iv} V]
           [HasFunctors V V VV]

  class HasSymmFun (R : MetaRelation α V) [hR : HasSymm R] where
  (defSymmFun (a b : α) : R a b ⟶{λ f => f⁻¹} R b a)

  namespace HasSymmFun

    section

      variable (R : MetaRelation α V) [hR : HasSymm R] [h : HasSymmFun R]

      @[reducible] def symmFun (a b : α) : R a b ⟶ R b a := h.defSymmFun a b

      instance symm.isFunApp {a b : α} {f : R a b} : IsFunApp (R a b) f⁻¹ :=
      { F := symmFun R a b,
        a := f,
        e := byDef }

    end

    variable {R : MetaRelation α V} [HasSymm R] [HasSymmFun R] [HasCongrArg V V]

    def congrArgSymm {a b : α} {e₁ e₂ : R a b} (he : e₁ ≃ e₂) : e₁⁻¹ ≃ e₂⁻¹ :=
    defCongrArg (defSymmFun a b) he

  end HasSymmFun

  variable [HasIdentity.{vv, ivv} VV] [HasFunctors V VV VV]

  class HasTransFun (R : MetaRelation α V) [hR : HasTrans R] where
  (defTransFun (a b c : α) : R a b ⟶ R b c ⟶{λ f g => g • f} R a c)

  namespace HasTransFun

    section

      variable (R : MetaRelation α V) [hR : HasTrans R] [h : HasTransFun R]

      @[reducible] def transFun {a b : α} (f : R a b) (c : α) : R b c ⟶ R a c := (h.defTransFun a b c).defFun f
      @[reducible] def transFunFun (a b c : α) : R a b ⟶ R b c ⟶ R a c := h.defTransFun a b c

      instance (priority := low) trans.isFunApp {a b c : α} {f : R a b} {g : R b c} : IsFunApp (R b c) (g • f) :=
      { F := transFun R f c,
        a := g,
        e := byDef }

      instance transFun.isFunApp {a b c : α} {f : R a b} : IsFunApp (R a b) (transFun R f c) :=
      { F := transFunFun R a b c,
        a := f,
        e := byDef }

      def transFun.congrArg [HasCongrArg V VV] {a b : α} {f₁ f₂ : R a b} (hf : f₁ ≃ f₂) (c : α) :
        transFun R f₁ c ≃ transFun R f₂ c :=
      defCongrArg (h.defTransFun a b c).defFunFun hf

      variable [HasCongrFun V V] [HasSwapFunFun V V V]

      def defRevTransFun (a b c : α) :
        R b c ⟶ R a b ⟶{λ g f => g • f} R a c :=
      defSwapDefFun₂ (h.defTransFun a b c)

      @[reducible] def revTransFun (a : α) {b c : α} (g : R b c) :
        R a b ⟶ R a c :=
      (defRevTransFun R a b c).defFun g

      @[reducible] def revTransFunFun (a b c : α) : R b c ⟶ R a b ⟶ R a c :=
      defRevTransFun R a b c

      instance revTransFun.isFunApp {a b c : α} {g : R b c} :
        IsFunApp (R b c) (revTransFun R a g) :=
      { F := revTransFunFun R a b c,
        a := g,
        e := byDef }

      instance (priority := low) trans.isFunApp₂ {a b c : α} {f : R a b} {g : R b c} :
        IsFunApp₂ (R a b) (R b c) (g • f) :=
      ⟨{ F := revTransFun R a g,
         a := f,
         e := byDef }⟩

      def revTransFun.congrArg [HasCongrArg V VV] (a : α) {b c : α} {g₁ g₂ : R b c} (hg : g₁ ≃ g₂) :
        revTransFun R a g₁ ≃ revTransFun R a g₂ :=
      defCongrArg (defRevTransFun R a b c).defFunFun hg

    end

    variable {R : MetaRelation α V} [HasTrans R] [h : HasTransFun R]

    def congrArgTransRight [HasCongrFun V V] [HasCongrArg V VV]
                           {a b c : α} {f₁ f₂ : R a b} (hf : f₁ ≃ f₂) (g : R b c) :
      g • f₁ ≃ g • f₂ :=
    defCongrArg₂A (h.defTransFun a b c) hf g

    def congrArgTransLeft [HasCongrArg V V] {a b c : α} (f : R a b) {g₁ g₂ : R b c} (hg : g₁ ≃ g₂) :
      g₁ • f ≃ g₂ • f :=
    defCongrArg₂B (h.defTransFun a b c) f hg

    def congrArgTrans [HasCongrArg V V] [HasCongrFun V V] [HasCongrArg V VV] {a b c : α}
                      {f₁ f₂ : R a b} (hf : f₁ ≃ f₂) {g₁ g₂ : R b c} (hg : g₁ ≃ g₂) :
      g₁ • f₁ ≃ g₂ • f₂ :=
    defCongrArg₂ (h.defTransFun a b c) hf hg

  end HasTransFun

  namespace opposite

    variable (R : MetaRelation α V)

    instance hasSymmFun [HasSymm R] [h : HasSymmFun R] :
      HasSymmFun (opposite R) :=
    ⟨λ a b => h.defSymmFun b a⟩

    instance hasTransFun [HasIdentity VV] [HasFunctors V VV VV] [HasCongrFun V V]
                         [HasSwapFunFun V V V] [HasTrans R] [h : HasTransFun R] :
      HasTransFun (opposite R) :=
    ⟨λ a b c => HasTransFun.defRevTransFun R c b a⟩

  end opposite

  namespace lift

    variable (R : MetaRelation α V) {ω : Sort w} (l : ω → α)

    instance hasSymmFun [HasSymm R] [h : HasSymmFun R] :
      HasSymmFun (lift R l) :=
    ⟨λ a b => h.defSymmFun (l a) (l b)⟩

    instance hasTransFun [HasIdentity VV] [HasFunctors V VV VV] [HasTrans R] [h : HasTransFun R] :
      HasTransFun (lift R l) :=
    ⟨λ a b c => h.defTransFun (l a) (l b) (l c)⟩

  end lift

end MetaRelation

namespace MetaRelation.emptyRelation

  variable (V : Universe.{v}) {VV : Universe.{vv}} [HasIdentity.{v, iv} V] [HasFunctors V V VV]

  instance hasSymmFun : HasSymmFun (emptyRelation V) :=
  ⟨λ e _ => PEmpty.elim e⟩

  instance hasTransFun [HasIdentity VV] [HasFunctors V VV VV] : HasTransFun (emptyRelation V) :=
  ⟨λ e _ _ => PEmpty.elim e⟩

end MetaRelation.emptyRelation



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



class HasLinearFunOp (U : Universe) [HasIdentity U] [HasInternalFunctors U] where
(defIdFun     (A     : U) : A ⟶{id} A)
(defRevAppFun (A B   : U) : A ⟶ (A ⟶ B) ⟶{λ a F => F a} B)
(defCompFun   (A B C : U) : (A ⟶ B) ⟶ (B ⟶ C) ⟶ A ⟶{λ F G a => G (F a)} C)

namespace HasLinearFunOp

  open MetaRelation HasFunctors HasCongrArg

  variable {U : Universe} [HasIdentity U] [hFun : HasInternalFunctors U] [HasLinearFunOp U]

  instance : HasIdFun U := ⟨defIdFun⟩

  @[reducible] def idFun (A : U) : A ⟶ A := HasIdFun.idFun A

  def defAppFun (A B : U) : (A ⟶ B) ⟶ A ⟶{λ F a => F a} B :=
  ⟨λ F => HasFunctors.defAppFun F, defIdFun (A ⟶ B)⟩

  @[reducible] def appFun {A B : U} (F : A ⟶ B) : A ⟶ B := HasFunctors.appFun F
  @[reducible] def appFunFun (A B : U) : (A ⟶ B) ⟶ A ⟶ B := defAppFun A B

  instance appFun.isFunApp {A B : U} {F : A ⟶ B} : IsFunApp (A ⟶ B) (appFun F) :=
  { F := appFunFun A B,
    a := F,
    e := byDef }

  instance : HasRevAppFun U := ⟨λ {A} a B => (defRevAppFun A B).defFun a⟩

  @[reducible] def revAppFun {A : U} (a : A) (B : U) : (A ⟶ B) ⟶ B := HasRevAppFun.revAppFun a B
  @[reducible] def revAppFunFun (A B : U) : A ⟶ (A ⟶ B) ⟶ B := defRevAppFun A B

  instance revAppFun.isFunApp {A B : U} {a : A} : IsFunApp A (revAppFun a B) :=
  { F := revAppFunFun A B,
    a := a,
    e := byDef }

  instance : HasCompFunFun U U :=
  { defCompFun    := λ {A B C} F G => ((defCompFun A B C).defFun F).defFun G,
    defCompFunFun := λ {A B} F C   => ((defCompFun A B C).defFun F).defFunFun }

  @[reducible] def compFun {A B C : U} (F : A ⟶ B) (G : B ⟶ C) : A ⟶ C := HasCompFun.compFun F G
  @[reducible] def compFunFun {A B : U} (F : A ⟶ B) (C : U) : (B ⟶ C) ⟶ (A ⟶ C) := HasCompFunFun.compFunFun F C
  @[reducible] def compFunFunFun (A B C : U) : (A ⟶ B) ⟶ (B ⟶ C) ⟶ (A ⟶ C) := defCompFun A B C

  instance compFun.isFunApp {A B C : U} {F : A ⟶ B} {G : B ⟶ C} :
    IsFunApp (B ⟶ C) (compFun F G) :=
  HasCompFunFun.compFun.isFunApp

  instance compFunFun.isFunApp {A B C : U} {F : A ⟶ B} :
    IsFunApp (A ⟶ B) (HasCompFunFun.compFunFun F C) :=
  { F := compFunFunFun A B C,
    a := F,
    e := byDef }

  instance isPreorder : IsPreorder hFun.Fun :=
  { refl  := idFun,
    trans := HasCompFun.compFun }

  instance hasTransFun : HasTransFun hFun.Fun :=
  ⟨λ A B C => DefFun₃.defFunFun (defCompFun A B C)⟩

  def revAppFun.congrArg {A : U} {a₁ a₂ : A} (ha : a₁ ≃ a₂) (B : U) :
    revAppFun a₁ B ≃ revAppFun a₂ B :=
  defCongrArg (defRevAppFun A B).defFunFun ha

  def compFun.congrArg {A B C : U} (F : A ⟶ B) {G₁ G₂ : B ⟶ C} (hG : G₁ ≃ G₂) :
    compFun F G₁ ≃ compFun F G₂ :=
  defCongrArg ((defCompFun A B C).defFun F).defFunFun hG

  def compFunFun.congrArg {A B : U} {F₁ F₂ : A ⟶ B} (hF : F₁ ≃ F₂) (C : U) :
    compFunFun F₁ C ≃ compFunFun F₂ C :=
  defCongrArg (defCompFun A B C).defFunFunFun hF

end HasLinearFunOp



class HasSubLinearFunOp (U : Universe) [HasIdentity U] [HasInternalFunctors U] where
(defConstFun (A B : U) : B ⟶ A ⟶{λ b a => b} B)

namespace HasSubLinearFunOp

  open HasFunctors HasCongrArg

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasSubLinearFunOp U]

  instance : HasConstFun U U := ⟨λ A {B} b => (defConstFun A B).defFun b⟩

  @[reducible] def constFun (A : U) {B : U} (b : B) : A ⟶ B := HasConstFun.constFun A b
  @[reducible] def constFunFun (A B : U) : B ⟶ (A ⟶ B) := defConstFun A B

  instance constFun.isFunApp {A B : U} {b : B} : IsFunApp B (constFun A b) :=
  { F := constFunFun A B,
    a := b,
    e := byDef }

  def constFun.congrArg (A : U) {B : U} {b₁ b₂ : B} (hb : b₁ ≃ b₂) :
    constFun A b₁ ≃ constFun A b₂ :=
  defCongrArg (defConstFun A B).defFunFun hb

end HasSubLinearFunOp

class HasAffineFunOp (U : Universe) [HasIdentity U] [HasInternalFunctors U] extends
  HasLinearFunOp U, HasSubLinearFunOp U



class HasNonLinearFunOp (U : Universe) [HasIdentity U] [HasInternalFunctors U] where
(defDupFun (A B : U) : (A ⟶ A ⟶ B) ⟶ A ⟶{λ F a => F a a} B)

namespace HasNonLinearFunOp

  open HasFunctors HasCongrArg

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasNonLinearFunOp U]

  instance : HasDupFun U U := ⟨λ {A B} F => (defDupFun A B).defFun F⟩

  @[reducible] def dupFun {A B : U} (F : A ⟶ A ⟶ B) : A ⟶ B := HasDupFun.dupFun F
  @[reducible] def dupFunFun (A B : U) : (A ⟶ A ⟶ B) ⟶ (A ⟶ B) := defDupFun A B

  instance dupFun.isFunApp {A B : U} {F : A ⟶ A ⟶ B} : IsFunApp (A ⟶ A ⟶ B) (dupFun F) :=
  { F := dupFunFun A B,
    a := F,
    e := byDef }

  def dupFun.congrArg {A B : U} {F₁ F₂ : A ⟶ A ⟶ B} (hF : F₁ ≃ F₂) :
    dupFun F₁ ≃ dupFun F₂ :=
  defCongrArg (defDupFun A B).defFunFun hF

end HasNonLinearFunOp

class HasFullFunOp (U : Universe) [HasIdentity U] [HasInternalFunctors U] extends
  HasAffineFunOp U, HasNonLinearFunOp U
