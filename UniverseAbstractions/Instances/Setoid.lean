/-
A universe of bundled setoids, i.e. types with equivalence relations.
This is one of the simplest universes where functoriality is nontrivial. It is essentially the
same as a universe of groupoids where isomorphisms are propositions. Therefore, it is especially
useful as a blueprint for the universe of categories.
There is a truncation functor from every other universe to the setoid universe, and of course this
can be continued into `sort` by taking the quotient.
-/



import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.FunctorExtensionality
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences
import UniverseAbstractions.Axioms.Universe.DependentTypes.Properties
import UniverseAbstractions.Axioms.Universe.DependentTypes.DependentFunctors
import UniverseAbstractions.Axioms.Universe.DependentTypes.DependentProducts
import UniverseAbstractions.Instances.Utils.Bundled
import UniverseAbstractions.Instances.Utils.Trivial
import UniverseAbstractions.Instances.Sort



set_option autoBoundImplicitLocal false
set_option synthInstance.maxHeartbeats 4000
--set_option pp.universes true

universe u v w w' upv



namespace Setoid

  open Bundled MetaRelation HasFunctors HasCongrArg HasCongrFun HasLinearFunOp HasPropCongrArg

  def typeClass : SimpleTypeClass.{u, max 1 u} := Setoid.{u}
  @[reducible] def univ : Universe.{u, u + 1} := Bundled.univ typeClass.{u}
  @[reducible] def tuniv := univ.{max 1 u}

  instance inst (A : univ.{u}) : Setoid.{u} A := A.inst

  def lift {α : Sort u} {ω : Sort w} (s : Setoid α) (l : ω → α) :
    Setoid ω :=
  { r     := λ a b => l a ≈ l b,
    iseqv := { refl  := λ a   => Setoid.refl  (l a),
               symm  := λ h   => Setoid.symm  h,
               trans := λ h i => Setoid.trans h i } }

  -- Instance equivalences

  instance hasEquivalenceRelation (A : univ.{u}) : HasEquivalenceRelation A prop :=
  ⟨nativeRelation (inst A).r⟩

  instance hasInstanceEquivalences : HasInstanceEquivalences univ.{u} prop :=
  ⟨hasEquivalenceRelation⟩

  -- Functors

  def FunctionEquiv {α : Sort u} {φ : α → univ} (f₁ f₂ : ∀ a, φ a) : Prop :=
  ∀ a, f₁ a ≈ f₂ a

  instance functionSetoid {α : Sort u} (φ : α → univ.{v}) :
    Setoid.{imax u v} (∀ a, φ a) :=
  { r     := FunctionEquiv,
    iseqv := { refl  := λ f   a => (inst (φ a)).refl  (f a),
               symm  := λ h   a => (inst (φ a)).symm  (h a),
               trans := λ h i a => (inst (φ a)).trans (h a) (i a) } }

  instance biFunctionSetoid {α : Sort u} {β : Sort v} (φ : α → β → univ.{w}) :
    Setoid.{imax u v w} (∀ a b, φ a b) :=
  inferInstance

  def IsFun {U : Universe} [HasIdentity U] {A : U} {B : univ} (f : A → B) : Prop :=
  ∀ {a₁ a₂ : A}, a₁ ≃ a₂ → f a₁ ≈ f a₂

  def IsFun₂ {U V : Universe} [HasIdentity U] [HasIdentity V] {A : U} {B : V} {C : univ}
             (f : A → B → C) : Prop :=
  ∀ {a₁ a₂ : A} {b₁ b₂ : B}, a₁ ≃ a₂ → b₁ ≃ b₂ → f a₁ b₁ ≈ f a₂ b₂

  instance hasFunctoriality (U : Universe.{u}) [HasIdentity U] :
  HasFunctoriality U univ.{v} := ⟨IsFun⟩

  instance funSetoid {U : Universe.{u}} [HasIdentity U] (A : U) (B : univ.{v}) :
    Setoid.{max 1 u v} (HasFunctoriality.Fun A B) :=
  lift (functionSetoid (Function.const A B)) HasFunctoriality.Fun.f

  instance hasFunctorialityInstances (U : Universe.{u}) [HasIdentity U] :
    HasFunctorialityInstances U univ.{v} typeClass.{max 1 u v} :=
  ⟨funSetoid⟩

  def isFun₂ {U V : Universe} [HasIdentity U] [HasIdentity V] {A : U} {B : V} {C : univ}
             (F : A ⟶ B ⟶ C) : IsFun₂ (λ a b => F a b) :=
  λ {a₁ a₂ b₁ b₂} h₁ h₂ => Setoid.trans ((F.isFun h₁) b₁) ((F a₂).isFun h₂)

  def defFun {U : Universe} [HasIdentity U] {A : U} {B : univ} {f : A → B} (isFun : IsFun f) :
    A ⟶{f} B :=
  Bundled.HasFunctorialityInstances.defFun isFun

  def defFun₂ {U V : Universe} [HasIdentity U] [HasIdentity V] {A : U} {B : V} {C : univ}
              {f : A → B → C} (isFun : IsFun₂ f) :
    A ⟶{λ a => (defFun (isFun (HasInstanceEquivalences.refl a)))} (B ⟶ C) :=
  defFun (λ h b => (isFun h) (HasInstanceEquivalences.refl b))

  instance hasCongrArg (U : Universe.{u}) [HasIdentity U] : HasCongrArg U univ.{v} :=
  ⟨HasFunctoriality.Fun.isFun⟩

  instance hasCongrFun (U : Universe.{u}) [HasIdentity U] : HasCongrFun U univ.{v} := ⟨id⟩

  instance hasInternalFunctors : HasInternalFunctors tuniv.{u} := ⟨⟩

  instance hasIdFun : HasIdFun univ.{u} := ⟨λ A => defFun id⟩

  instance hasConstFun (U : Universe.{u}) [HasIdentity U] : HasConstFun U univ.{v} :=
  ⟨λ A {B} b => defFun (λ a => Setoid.refl b)⟩

  instance hasRevAppFun : HasRevAppFun tuniv.{u} := ⟨λ a B => defFun (λ h => h a)⟩

  instance hasCompFun (U : Universe.{u}) (V : Universe.{v}) {W : Universe.{w'}} [HasIdentity U]
                      [HasIdentity V] [HasFunctors U V W] [HasCongrArg U V] :
    HasCompFun U V univ.{w} :=
  ⟨λ F G => defFun (λ h => G.isFun (congrArg F h))⟩

  instance hasCompFunFun (U : Universe.{u}) [HasIdentity U] [HasInternalFunctors U] :
    HasCompFunFun U tuniv.{v} :=
                                     -- Work around Lean defeq problem.
  ⟨λ F C => defFun (λ {G₁ G₂} h a => have h₁ : (G₁ ⊙ F).f a = G₁ (F a) := rfl;
                                     have h₂ : (G₂ ⊙ F).f a = G₂ (F a) := rfl;
                                     h₁ ▸ h₂ ▸ h (F a))⟩

  instance hasRevCompFunFun (U : Universe.{u}) [HasIdentity U] [HasInternalFunctors U]
                            [HasCongrFun U U] :
    HasRevCompFunFun U univ.{v} :=
                                           -- Work around Lean defeq problem.
  ⟨λ A {B C} G => defFun (λ {F₁ F₂} e a => have h₁ : (G ⊙ F₁).f a = G (F₁ a) := rfl;
                                           have h₂ : (G ⊙ F₂).f a = G (F₂ a) := rfl;
                                           h₁ ▸ h₂ ▸ G.isFun (congrFun e a))⟩

  instance hasSwapFun (U : Universe.{u}) (V : Universe.{v}) [HasIdentity U] [HasIdentity V] :
    HasSwapFun U V univ.{w} :=
  ⟨λ F b => defFun (λ h => (F.isFun h) b)⟩

  instance hasSwapFunFun : HasSwapFunFun univ.{u} univ.{v} univ.{w} :=
                                   -- Work around Lean defeq problem.
  ⟨λ F => defFun (λ {b₁ b₂} h a => have h₁ : (HasSwapFun.swapFun F b₁).f a = F a b₁ := rfl; 
                                   have h₂ : (HasSwapFun.swapFun F b₂).f a = F a b₂ := rfl; 
                                   h₁ ▸ h₂ ▸ (F a).isFun h)⟩

  instance hasDupFun (U : Universe.{u}) [HasIdentity U] : HasDupFun U univ.{v} :=
  ⟨λ F => defFun (λ h => isFun₂ F h h)⟩

  instance hasSubstFun (U : Universe.{u}) (V : Universe.{v}) {W : Universe.{w'}} [HasIdentity U]
                       [HasIdentity V] [HasFunctors U V W] [HasCongrArg U V] :
    HasSubstFun U V univ.{w} :=
  ⟨λ F G => defFun (λ h => isFun₂ G h (congrArg F h))⟩

  instance hasBiCompFun : HasBiCompFun univ.{u} univ.{v} univ.{w} univ.{w'} :=
  ⟨λ F G H => defFun (λ h => isFun₂ H (F.isFun h) (G.isFun h))⟩

  instance hasRevBiCompFunFun : HasRevBiCompFunFun tuniv.{u} univ.{v} univ.{w'} :=
                                     -- Work around Lean defeq problem.
  ⟨λ H F => defFun (λ {G₁ G₂} h a => have h₁ : (HasBiCompFun.biCompFun F G₁ H).f a = H (F a) (G₁ a) := rfl;
                                     have h₂ : (HasBiCompFun.biCompFun F G₂ H).f a = H (F a) (G₂ a) := rfl;
                                     h₁ ▸ h₂ ▸ (H (F a)).isFun (h a))⟩

  instance hasRevBiCompFunFunFun : HasRevBiCompFunFunFun tuniv.{u} univ.{w'} :=
                                               -- Work around Lean defeq problem.
  ⟨λ A {B C D} H => defFun (λ {F₁ F₂} h G a => have h₁ : ((HasRevBiCompFunFun.revBiCompFunFun H F₁).f G).f a = H (F₁ a) (G a) := rfl;
                                               have h₂ : ((HasRevBiCompFunFun.revBiCompFunFun H F₂).f G).f a = H (F₂ a) (G a) := rfl;
                                               h₁ ▸ h₂ ▸ (H.isFun (h a)) (G a))⟩

  instance hasLinearFunOp : HasLinearFunOp tuniv.{u} :=
  { defRevAppFunFun  := λ A B   => defFun (λ h F => F.isFun h),
    defCompFunFunFun := λ A B C => defFun (λ h G a => G.isFun (h a)) }

  instance hasAffineFunOp : HasAffineFunOp tuniv.{u} :=
  { defConstFunFun := λ A B => defFun (λ h a => h) }

  instance hasFullFunOp : HasFullFunOp tuniv.{u} :=
  { defDupFunFun := λ A B => defFun (λ h a => h a a) }

  instance hasTrivialExtensionality : HasTrivialExtensionality univ.{u} univ.{v} := ⟨id⟩

  instance hasStandardFunctors : HasStandardFunctors tuniv.{u} := ⟨⟩

  -- Setoid truncation from another universe

  def typeSetoid {U : Universe.{u}} [HasIdentity U] (A : U) : Setoid.{u} A :=
  { r     := λ a b => Nonempty (a ≃ b),
    iseqv := { refl  := λ a       => ⟨HasRefl.refl a⟩,
               symm  := λ ⟨e⟩     => ⟨e⁻¹⟩,
               trans := λ ⟨e⟩ ⟨f⟩ => ⟨f • e⟩ } }

  def Truncated {U : Universe.{u}} [HasIdentity U] (A : U) : univ.{u} :=
  { a    := ⌈A⌉,
    inst := typeSetoid A }

  def trunc {U : Universe.{u}} [HasIdentity U] {A : U} (a : A) : Truncated A := a

  def truncFun {U : Universe.{u}} [HasIdentity U] (A : U) : A ⟶ Truncated A :=
  { f     := trunc,
    isFun := λ e => ⟨e⟩ }

  instance trunc.isFunApp {U : Universe.{u}} [HasIdentity U] {A : U} (a : A) :
    IsFunApp A (trunc a) :=
  { F := truncFun A,
    a := a,
    e := Setoid.refl (trunc a) }

  def truncProj {U : Universe.{u}} {V : Universe.{v}} {W : Universe.{w}} [HasIdentity U]
                [HasIdentity V] [HasIdentity W] [HasFunctors U V W] [HasCongrArg U V]
                {A : U} {B : V} (F : A ⟶ B) :
    Truncated A ⟶ Truncated B :=
  { f     := λ a => F a,
    isFun := λ ⟨e⟩ => ⟨congrArg F e⟩ }

  def truncProjFun {U : Universe.{u}} {V : Universe.{v}} {W : Universe.{w}} [HasIdentity U]
                   [HasIdentity V] [HasIdentity W] [HasFunctors U V W] [HasCongrArg U V]
                   [HasCongrFun U V] (A : U) (B : V) :
    (A ⟶ B) ⟶ (Truncated A ⟶ Truncated B) :=
  { f     := truncProj,
    isFun := λ e a => ⟨congrFun e a⟩ }

  instance truncProj.isFunApp {U : Universe.{u}} {V : Universe.{v}} {W : Universe.{w}}
                              [HasIdentity U] [HasIdentity V] [HasIdentity W]
                              [HasFunctors U V W] [HasCongrArg U V] [HasCongrFun U V]
                              {A : U} {B : V} (F : A ⟶ B) :
    IsFunApp (A ⟶ B) (truncProj F) :=
  { F := truncProjFun A B,
    a := F,
    e := Setoid.refl (truncProj F) }

  def truncProjFun' {U : Universe.{u}} {V : Universe.{v}} {W : Universe.{w}} [HasIdentity U]
                    [HasIdentity V] [HasIdentity W] [HasFunctors U V W] [HasCongrArg U V]
                    [HasCongrFun U V] (A : U) (B : V) :
    Truncated (A ⟶ B) ⟶ (Truncated A ⟶ Truncated B) :=
  { f     := truncProj,
    isFun := λ ⟨e⟩ a => ⟨congrFun e a⟩ }

  theorem truncCongr {U : Universe.{u}} {V : Universe.{v}} {W : Universe.{w}} [HasIdentity U]
                     [HasIdentity V] [HasIdentity W] [HasFunctors U V W] [HasCongrArg U V]
                     {A : U} {B : V} (F : A ⟶ B) (a : A) :
    trunc (F a) ≈ (truncProj F) (trunc a) :=
  ⟨HasRefl.refl (F a)⟩

  theorem truncCongrSquare {U : Universe.{u}} {V : Universe.{v}} {W : Universe.{w}} [HasIdentity U]
                           [HasIdentity V] [HasIdentity W] [HasFunctors U V W] [HasCongrArg U V]
                           {A : U} {B : V} (F : A ⟶ B) :
    truncFun B ⊙ F ≈ truncProj F ⊙ truncFun A :=
  truncCongr F

  -- Setoid to quotient

  def AsQuotient (A : univ.{u}) : sort.{u} := Quotient (inst A)

  def toQuotient {A : univ.{u}} (a : A) : AsQuotient A := Quotient.mk a

  def toQuotientFun (A : univ.{u}) : A ⟶ AsQuotient A :=
  { f        := toQuotient,
    congrArg := Quotient.sound }

  instance toQuotient.isFunApp {A : univ.{u}} (a : A) :
    IsFunApp (V := sort.{u}) A (toQuotient a) :=
  { F := toQuotientFun A,
    a := a,
    e := rfl }

  def quotientProj {A : univ.{u}} {B : univ.{v}} (F : A ⟶ B) : AsQuotient A ⟶ AsQuotient B :=
  -- Work around Lean defeq problem.
  let toQuotB : ⌈B ⟶ AsQuotient B⌉ := toQuotientFun B;
  let G : A ⟶ AsQuotient B := toQuotB ⊙ F;
  Quotient.lift G.f (λ _ _ => G.congrArg)

  def toQuotientCongr {A : univ.{u}} {B : univ.{v}} (F : A ⟶ B) (a : A) :
    toQuotient (F a) = (quotientProj F) (toQuotient a) :=
  rfl

  -- TODO: Seems like another defeq problem together with universe issues.
  --def toQuotientCongrSquare {A : univ.{u}} {B : univ.{v}} (F : A ⟶ B) :
  --  toQuotientFun B ⊙ F = quotientProj F ⊙ toQuotientFun A :=
  --rfl

  -- Singletons

  instance unitSetoid : Setoid.{u} PUnit.{u} :=
  { r     := λ _ _ => True,
    iseqv := { refl  := λ _   => trivial,
               symm  := λ _   => trivial,
               trans := λ _ _ => trivial } }

  instance hasTopInstance : HasTopInstance typeClass.{u} := ⟨unitSetoid⟩

  instance hasTopEq : HasTop.HasTopEq univ.{u} := ⟨λ _ => trivial⟩

  instance hasInternalTop : HasInternalTop tuniv.{u} :=
  { defElimFun := λ a => defFun (λ _ => Setoid.refl a) }

  instance emptySetoid : Setoid.{u} PEmpty.{u} :=
  { r     := λ _ _ => False,
    iseqv := { refl  := PEmpty.elim,
               symm  := id,
               trans := Function.const False } }

  instance hasBotInstance : HasBotInstance typeClass.{u} := ⟨emptySetoid⟩

  instance hasInternalBot : HasInternalBot tuniv.{u} :=
  { defElimFun := λ A => defFun False.elim }

  -- Products

  instance productSetoid (α : Sort u) (β : Sort v) [Setoid α] [Setoid β] :
    Setoid.{max 1 u v} (PProd α β) :=
  { r     := λ p₁ p₂ => p₁.fst ≈ p₂.fst ∧ p₁.snd ≈ p₂.snd,
    iseqv := { refl  := λ p   => ⟨Setoid.refl  p.fst,         Setoid.refl  p.snd⟩,
               symm  := λ h   => ⟨Setoid.symm  h.left,        Setoid.symm  h.right⟩,
               trans := λ h i => ⟨Setoid.trans h.left i.left, Setoid.trans h.right i.right⟩ } }

  instance prodSetoid (A : univ.{u}) (B : univ.{v}) : Setoid.{max 1 u v} (PProd A B) :=
  productSetoid A B

  instance hasProductInstances : HasProductInstances univ.{u} univ.{v} typeClass.{max 1 u v} :=
  ⟨prodSetoid⟩

  instance hasProductEq : HasProducts.HasProductEq univ.{u} univ.{v} :=
  { introEq := λ p   => Setoid.refl p,
    fstEq   := λ a b => Setoid.refl a,
    sndEq   := λ a b => Setoid.refl b }

  instance hasInternalProducts : HasInternalProducts tuniv.{u} :=
  { defIntroFun    := λ a B   => defFun (λ h   => ⟨Setoid.refl a, h⟩),
    defIntroFunFun := λ A B   => defFun (λ h b => ⟨h, Setoid.refl b⟩),
    defElimFun     := λ F     => defFun (λ h   => isFun₂ F h.left h.right),
    defElimFunFun  := λ A B C => defFun (λ h p => h p.fst p.snd) }

  -- Equivalences

  instance equivSetoid (A : univ.{u}) (B : univ.{v}) : Setoid.{max 1 u v} (A ⮂ B) :=
  lift (funSetoid A B) EquivDesc.toFun

  instance hasEquivalenceInstances :
    HasEquivalenceInstances univ.{u} univ.{v} typeClass.{max 1 u v} :=
  { Equiv     := EquivDesc,
    desc      := id,
    equivInst := equivSetoid }

  instance hasInternalEquivalences : HasInternalEquivalences tuniv.{u} :=
  { defToFunFun := λ A B => defFun id,
    isExt       := HasTrivialExtensionality.equivDescExt tuniv.{u},
    toFunInj    := id }

  instance hasTrivialEquivalenceCondition : HasTrivialEquivalenceCondition tuniv.{u} :=
  ⟨λ e => { E        := e,
            toFunEq  := Setoid.refl e.toFun,
            invFunEq := Setoid.refl e.invFun }⟩

  -- Dependent functors

  instance hasTypeIdentity : HasTypeIdentity tuniv.{u} := ⟨⟩

  def IsPi {U : Universe.{u}} {UpV : Universe.{upv}} [HasIdentity U]
           [HasFunctors U {tuniv.{v}} UpV] [HasPropCongrArg U tuniv.{v}]
           {A : U} {φ : A ⟶ ⌊tuniv.{v}⌋} (f : HasFunctors.Pi φ) :
    Prop :=
  ∀ {a₁ a₂ : A} (e : a₁ ≃ a₂), f a₁ ≃[propCongrArg φ e] f a₂

  instance hasDependentFunctoriality (U : Universe.{u}) {UpV : Universe.{upv}} [HasIdentity U]
                                     [HasFunctors U {tuniv.{v}} UpV] [HasPropCongrArg U tuniv.{v}] :
  HasDependentFunctoriality U tuniv.{v} := ⟨IsPi⟩

  instance piSetoid {U : Universe.{u}} {UpV : Universe.{upv}} [HasIdentity U]
                    [HasFunctors U {tuniv.{v}} UpV] [HasPropCongrArg U tuniv.{v}]
                    {A : U} (φ : A ⟶ ⌊tuniv.{v}⌋) :
    Setoid.{max 1 u v} (HasDependentFunctoriality.Pi φ) :=
  lift (functionSetoid (HasFunctors.apply φ)) HasDependentFunctoriality.Pi.f

  instance hasDependentFunctorialityInstances (U : Universe.{u}) {UpV : Universe.{upv}}
                                              [HasIdentity U] [HasFunctors U {tuniv.{v}} UpV]
                                              [HasPropCongrArg U tuniv.{v}] :
    HasDependentFunctorialityInstances U tuniv.{v} typeClass.{max 1 u v} :=
  ⟨piSetoid⟩

  instance hasDependentCongrArg (U : Universe.{u}) {UpV : Universe.{upv}} [HasIdentity U]
                                [HasFunctors U {tuniv.{v}} UpV] [HasPropCongrArg U tuniv.{v}] :
    HasDependentCongrArg U tuniv.{v} :=
  ⟨HasDependentFunctoriality.Pi.isFun⟩

  -- Lean bug :-(
  noncomputable def defInPi {U : Universe.{u}} {UpV : Universe.{upv}} [HasIdentity U]
                            [HasFunctors U {tuniv.{v}} UpV] [HasPropCongrArg U tuniv.{v}]
                            {A : U} {φ : A ⟶ ⌊tuniv.{v}⌋} (f : HasFunctors.Pi φ) (isFun : IsPi f) :
    Π{f} (HasFunctors.toDefFun φ) :=
  Bundled.HasDependentFunctorialityInstances.defPi isFun

  -- Dependent products

  instance sigmaSetoid {U : Universe.{u}} {UpV : Universe.{upv}} [HasIdentity U]
                       [HasFunctors U {tuniv.{v}} UpV] [HasPropCongrArg U tuniv.{v}]
                       {A : U} (φ : A ⟶ ⌊tuniv.{v}⌋) :
    Setoid.{max 1 u v} (PSigma (λ a => φ a)) :=
  { r     := λ p₁ p₂ => ∃ e : p₁.fst ≃ p₂.fst, ⌈p₁.snd ≃[propCongrArg φ e] p₂.snd⌉,
    iseqv := { refl  := λ p             => ⟨HasInstanceEquivalences.refl p.fst,
                                            DependentEquivalence.depCongrArgRefl  p.snd⟩,
               symm  := λ ⟨e, h⟩        => ⟨e⁻¹,
                                            DependentEquivalence.depCongrArgSymm  h⟩,
               trans := λ ⟨e, h⟩ ⟨f, i⟩ => ⟨f • e,
                                            DependentEquivalence.depCongrArgTrans h i⟩ } }

  instance hasDependentProductInstances (U : Universe.{u}) {UpV : Universe.{upv}} [HasIdentity U]
                                        [HasFunctors U {tuniv.{v}} UpV]
                                        [HasPropCongrArg U tuniv.{v}] :
    HasDependentProductInstances U tuniv.{v} typeClass.{max 1 u v} :=
  ⟨sigmaSetoid⟩

  instance hasDependentProducts (U : Universe.{u}) {UpV : Universe.{upv}} [HasIdentity U]
                                [HasFunctors U {tuniv.{v}} UpV] [HasPropCongrArg U tuniv.{v}] :
    HasDependentProducts U tuniv.{v} tuniv.{max u v} :=
  Bundled.hasDependentProducts U tuniv.{v}

  instance hasDependentProductEq (U : Universe.{u}) {UpV : Universe.{upv}} [HasIdentity U]
                                 [HasFunctors U {tuniv.{v}} UpV] [HasPropCongrArg U tuniv.{v}] :
    HasDependentProducts.HasDependentProductEq U tuniv.{v} :=
  { introEq := λ p   => Setoid.refl p,
    fstEq   := λ a b => HasInstanceEquivalences.refl a,
    sndEq   := λ a b => DependentEquivalence.depCongrArgRefl b }

  -- TODO
  --instance hasInternalDependentProducts (U : Universe.{u}) {UpV : Universe.{upv}} [HasIdentity U]
  --                                      [HasFunctors U {tuniv.{u}} UpV] [HasPropCongrArg U tuniv.{u}] :
  --  HasInternalDependentProducts U tuniv.{u} :=
  --{ defIntroFun    := λ a B   => defFun (λ h   => ⟨Setoid.refl a, h⟩),
  --  defIntroFunFun := λ A B   => defFun (λ h b => ⟨h, Setoid.refl b⟩),
  --  defElimFun     := λ F     => defFun (λ h   => isFun₂ F h.left h.right),
  --  defElimFunFun  := λ A B C => defFun (λ h p => h p.fst p.snd) }

end Setoid
