import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.FunctorExtensionality
import UniverseAbstractions.Axioms.Universe.Singletons
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences
import UniverseAbstractions.Axioms.Universe.DependentTypes.Properties
import UniverseAbstractions.Axioms.Universe.DependentTypes.DependentFunctors
import UniverseAbstractions.Axioms.Universe.DependentTypes.DependentProducts



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v



class HasTrivialIdentity (U : Universe) [HasIdentity U] where
(mkEq {A : U} (a b : A) : a ≃ b)

namespace HasTrivialIdentity

  open HasLinearFunOp HasInternalEquivalences

  def eq {U : Universe} [HasIdentity U] [HasTrivialIdentity U] {A : U} {a b : A} :
    a ≃ b :=
  mkEq a b

  def defFun {U V : Universe} [HasIdentity V] [HasTrivialIdentity V]
             {UV : Universe} [HasFunctors U V UV]
             {A : U} {B : V} (F : A ⟶ B) {f : A → B} : A ⟶{f} B :=
  ⟨F, λ _ => eq⟩

  instance hasCongrArg (U V : Universe) [HasIdentity U] [HasIdentity V]
                       [HasTrivialIdentity V] {UV : Universe} [HasFunctors U V UV] :
    HasCongrArg U V :=
  ⟨λ {_ _} _ {_ _} _ => eq⟩

  instance hasTopEq (U : Universe) [HasIdentity U] [HasTrivialIdentity U] [HasTop U] :
    HasTop.HasTopEq U :=
  ⟨λ _ => eq⟩

  instance hasProductEq (U V : Universe) {UxV : Universe} [HasIdentity U]
                        [HasTrivialIdentity U] [HasIdentity V] [HasTrivialIdentity V]
                        [HasIdentity UxV] [HasTrivialIdentity UxV] [HasProducts U V UxV] :
    HasProducts.HasProductEq U V :=
  { introEq := λ _   => eq,
    fstEq   := λ _ _ => eq,
    sndEq   := λ _ _ => eq }

  def halfEquivDesc {U V UV VU : Universe} [HasIdentity U] [HasTrivialIdentity U]
                    [HasFunctors U V UV] [HasFunctors V U VU]
                    {A : U} {B : V} {toFun : A ⟶ B} {invFun : B ⟶ A} :
    HalfEquivDesc toFun invFun :=
  ⟨λ _ => eq⟩

  def equivDesc {U V UV VU : Universe} [HasIdentity U] [HasIdentity V]
                [HasTrivialIdentity U] [HasTrivialIdentity V]
                [HasFunctors U V UV] [HasFunctors V U VU]
                {A : U} {B : V} (toFun : A ⟶ B) (invFun : B ⟶ A) :
    A ⮂ B :=
  ⟨toFun, invFun, halfEquivDesc, halfEquivDesc⟩

  def defEquiv {U V UV VU U_V : Universe} [HasIdentity U] [HasIdentity V]
               [HasIdentity UV] [HasIdentity VU]
               [HasTrivialIdentity UV] [HasTrivialIdentity VU]
               [HasFunctors U V UV] [HasFunctors V U VU] [HasEquivalences U V U_V]
               {A : U} {B : V} (E : A ⟷ B) {e : A ⮂ B} :
    A ⟷{e} B :=
  ⟨E, eq, eq⟩

  def defPi {U V UpV UV : Universe} [HasTypeIdentity V] [HasTrivialIdentity V]
            [HasFunctors U {V} UpV] [HasDependentFunctors U V UV]
            {A : U} {p : A → V} {φ : A ⟶{p} ⌊V⌋} (F : Π (HasFunctors.fromDefFun φ))
            {f : ∀ a, p a} :
    Π{f} φ := 
  ⟨F, λ _ => eq⟩

  instance hasPropCongrArg (U V : Universe) {UpV : Universe} [HasIdentity U]
                           [HasTypeIdentity V] [HasFunctors U {V} UpV] [HasCongrArg U {V}]
                           [HasTrivialIdentity V] :
    HasPropCongrArg U V :=
  { congrArgReflEq  := λ     φ         _   => eq (U := V),
    congrArgSymmEq  := λ {_} φ {_ _}   _   => eq (U := V),
    congrArgTransEq := λ {_} φ {_ _ _} _ _ => eq (U := V) }

  instance hasDependentCongrArg (U V : Universe) {UpV UV : Universe}
                                [HasFunctors U {V} UpV] [HasDependentFunctors U V UV]
                                [HasIdentity U] [HasTypeIdentity V] [HasTrivialIdentity V]
                                [HasPropCongrArg U V] :
    HasDependentCongrArg U V :=
  ⟨λ {_ _} _ {_ _} _ => eq⟩

  instance hasDependentProductEq (U V : Universe) {UpV UxV : Universe}
                                 [HasFunctors U {V} UpV] [HasDependentProducts U V UxV]
                                 [HasIdentity U] [HasTrivialIdentity U] [HasTypeIdentity V]
                                 [HasTrivialIdentity V] [HasPropCongrArg U V] [HasIdentity UxV]
                                 [HasTrivialIdentity UxV] :
    HasDependentProducts.HasDependentProductEq U V :=
  { introEq := λ _   => eq,
    fstEq   := λ _ _ => eq,
    sndEq   := λ _ _ => eq }

end HasTrivialIdentity



class HasTrivialFunctoriality (U V : Universe) {UV : Universe} [HasIdentity V]
                              [HasFunctors U V UV] where
(mkDefFun {A : U} {B : V} (f : A → B) : A ⟶{f} B)

namespace HasTrivialFunctoriality

  open MetaRelation HasLinearFunOp HasEquivOp

  def defFun {U V UV : Universe} [HasIdentity V] [HasFunctors U V UV]
             [h : HasTrivialFunctoriality U V] {A : U} {B : V} {f : A → B} :
    A ⟶{f} B :=
  h.mkDefFun f

  def defFun₂ {U V W VW UVW : Universe} [HasIdentity W] [HasIdentity VW] [HasFunctors V W VW]
              [HasFunctors U VW UVW] [hVW : HasTrivialFunctoriality V W]
              [hUVW : HasTrivialFunctoriality U VW] {A : U} {B : V} {C : W} {f : A → B → C} :
    A ⟶ B ⟶{f} C :=
  ⟨λ _ => defFun, defFun⟩

  def defFun₃ {U V W X WX VWX UVWX : Universe} [HasIdentity X] [HasIdentity WX] [HasIdentity VWX]
              [HasFunctors W X WX] [HasFunctors V WX VWX] [HasFunctors U VWX UVWX]
              [hWX : HasTrivialFunctoriality W X] [hVWX : HasTrivialFunctoriality V WX]
              [hUVWX : HasTrivialFunctoriality U VWX] {A : U} {B : V} {C : W} {D : X}
              {f : A → B → C → D} :
    A ⟶ B ⟶ C ⟶{f} D :=
  ⟨λ _ => defFun₂, defFun⟩

  instance isFunctorial {U V UV : Universe} [HasFunctors U V UV] [HasIdentity V]
                        {A : U} {B : V} (f : A → B) [HasTrivialFunctoriality U V] :
    IsFunctorial f :=
  ⟨defFun⟩

  instance isRightFunctorial {U V W VW : Universe} [HasFunctors V W VW] [HasIdentity W]
                             {A : U} {B : V} {C : W} (f : A → B → C)
                             [HasTrivialFunctoriality V W] :
    IsRightFunctorial f :=
  ⟨λ _ => defFun⟩

  instance isLeftFunctorial {U V W UW : Universe} [HasFunctors U W UW] [HasIdentity W]
                            {A : U} {B : V} {C : W} (f : A → B → C)
                            [HasTrivialFunctoriality U W] :
    IsLeftFunctorial f :=
  ⟨λ _ => defFun⟩

  instance isBiFunctorial {U V W VW UVW : Universe} [HasFunctors V W VW] [HasFunctors U VW UVW]
                          [HasIdentity W] [HasIdentity VW]
                          {A : U} {B : V} {C : W} (f : A → B → C)
                          [HasTrivialFunctoriality V W] [HasTrivialFunctoriality U VW] :
    IsBiFunctorial f :=
  ⟨defFun₂⟩

  instance hasIdFun (U : Universe) {UU : Universe} [HasFunctors U U UU] [HasIdentity U]
                    [HasTrivialFunctoriality U U] :
    HasIdFun U :=
  ⟨λ _ => defFun⟩

  instance hasConstFun (U V : Universe) {UV : Universe} [HasFunctors U V UV] [HasIdentity V]
                       [HasTrivialFunctoriality U V] :
    HasConstFun U V :=
  ⟨λ _ {_} _ => defFun⟩

  instance hasRevAppFun (U : Universe) [HasFunctors U U U] [HasIdentity U]
                        [HasTrivialFunctoriality U U] :
    HasRevAppFun U :=
  ⟨λ _ _ => defFun⟩

  instance hasCompFun (U V W : Universe) {UV VW UW : Universe} [HasIdentity W]
                      [HasFunctors U V UV] [HasFunctors V W VW] [HasFunctors U W UW]
                      [HasTrivialFunctoriality U W] :
    HasCompFun U V W :=
  ⟨λ _ _ => defFun⟩

  instance hasCompFunFun (U V : Universe) {UV : Universe} [HasFunctors U V UV]
                         [HasFunctors V UV UV] [HasFunctors V V V] [HasIdentity V]
                         [HasIdentity UV] [HasCompFun U V V] [HasTrivialFunctoriality V UV] :
    HasCompFunFun U V :=
  ⟨λ _ _ => defFun⟩

  instance hasRevCompFunFun (U V : Universe) {UV : Universe} [HasFunctors U U U]
                            [HasFunctors U V UV] [HasFunctors U UV UV] [HasIdentity V]
                            [HasIdentity UV] [HasCompFun U U V] [HasTrivialFunctoriality U UV] :
    HasRevCompFunFun U V :=
  ⟨λ _ {_ _} _ => defFun⟩

  instance hasSwapFun (U V W : Universe) {VW UVW UW : Universe} [HasFunctors V W VW] [HasFunctors U VW UVW]
                      [HasFunctors U W UW] [HasIdentity W] [HasTrivialFunctoriality U W] :
    HasSwapFun U V W :=
  ⟨λ _ _ => defFun⟩

  instance hasSwapFunFun (U V W : Universe) {VW UVW UW VUW : Universe} [HasFunctors V W VW]
                         [HasFunctors U VW UVW] [HasFunctors U W UW] [HasFunctors V UW VUW]
                         [HasIdentity W] [HasIdentity UW] [HasTrivialFunctoriality U W]
                         [HasTrivialFunctoriality V UW] :
    HasSwapFunFun U V W :=
  ⟨λ _ => defFun⟩

  instance hasDupFun (U V : Universe) {UV UUV : Universe} [HasFunctors U V UV] [HasFunctors U UV UUV]
                     [HasIdentity V] [HasTrivialFunctoriality U V] :
    HasDupFun U V :=
  ⟨λ _ => defFun⟩

  instance hasSubstFun (U V W : Universe) {UV VW UVW UW : Universe} [HasFunctors U V UV] [HasFunctors V W VW]
                       [HasFunctors U VW UVW] [HasFunctors U W UW] [HasIdentity W]
                       [HasTrivialFunctoriality U W] :
    HasSubstFun U V W :=
  ⟨λ _ _ => defFun⟩

  instance hasBiCompFun (U V W X : Universe) {UV UW WX VWX UX : Universe} [HasFunctors U V UV]
                        [HasFunctors U W UW] [HasFunctors W X WX] [HasFunctors V WX VWX]
                        [HasFunctors U X UX] [HasIdentity X] [HasTrivialFunctoriality U X] :
    HasBiCompFun U V W X :=
  ⟨λ _ _ _ => defFun⟩

  instance hasRevBiCompFunFun (U V X : Universe) {UV UX VUX UUX : Universe} [HasFunctors U U U]
                              [HasFunctors U V UV] [HasFunctors U X UX] [HasFunctors V UX VUX]
                              [HasFunctors U UX UUX] [HasIdentity X] [HasIdentity UX]
                              [HasTrivialFunctoriality U X] [HasTrivialFunctoriality U UX] :
    HasRevBiCompFunFun U V X :=
  ⟨λ _ _ => defFun⟩

  instance hasRevBiCompFunFunFun (U X : Universe) {UX : Universe} [HasFunctors U U U] [HasFunctors U X UX]
                                 [HasFunctors U UX UX] [HasIdentity X] [HasIdentity UX]
                                 [HasTrivialFunctoriality U X] [HasTrivialFunctoriality U UX] :
    HasRevBiCompFunFunFun U X :=
  ⟨λ _ {_ _ _} _ => defFun⟩

  section MetaRelation

    variable {α : Sort u} {V : Universe.{v}} [HasIdentity V] [HasInternalFunctors V]
             [HasTrivialFunctoriality V V] (R : MetaRelation α V)

    instance hasSymmFun [HasSymm R] : HasSymmFun R :=
    ⟨λ _ _ => defFun⟩

    instance hasTransFun [HasTrans R] : HasTransFun R :=
    ⟨λ _ _ _ => defFun₂⟩

  end MetaRelation

  variable (U : Universe) [HasIdentity U] [HasInternalFunctors U] [HasTrivialFunctoriality U U]

  instance hasLinearFunOp : HasLinearFunOp U :=
  { defIdFun     := λ _     => defFun,
    defRevAppFun := λ _ _   => defFun₂,
    defCompFun   := λ _ _ _ => defFun₃ }

  instance hasAffineFunOp : HasAffineFunOp U :=
  { defConstFun := λ _ _ => defFun₂ }

  instance hasFullFunOp : HasFullFunOp U :=
  { defDupFun := λ _ _ => defFun₂ }

  instance hasInternalTop [HasTop U] : HasInternalTop U :=
  { defElimFun := λ _ => defFun }

  instance hasInternalBot [HasBot U] : HasInternalBot U :=
  { defElimFun := λ _ => defFun }

  instance hasInternalProducts [HasProducts U U U] : HasInternalProducts U :=
  { defIntroFun := λ _ _   => defFun₂,
    defElimFun  := λ _ _ _ => defFun₂ }

  instance hasEquivOpFun [HasLinearFunExt U] [HasInternalEquivalences U] [HasEquivOp U] :
    HasEquivOpFun U :=
  ⟨⟩

end HasTrivialFunctoriality



class HasTrivialExtensionality (U V : Universe) {UV : Universe} [HasIdentity V] [HasIdentity UV]
                               [HasFunctors U V UV] where
(mkFunEq {A : U} {B : V} {F₁ F₂ : A ⟶ B} (e : ∀ a, F₁ a ≃ F₂ a) : F₁ ≃{e} F₂)

namespace HasTrivialExtensionality

  instance fromTrivialIdentity (U V : Universe) {UV : Universe} [HasIdentity V]
                               [HasIdentity UV] [HasTrivialIdentity UV] [HasFunctors U V UV] :
    HasTrivialExtensionality U V :=
  ⟨λ _ => HasTrivialIdentity.eq⟩

  def funEq {U V UV : Universe} [HasIdentity V] [HasIdentity UV] [HasFunctors U V UV]
            [h : HasTrivialExtensionality U V]
            {A : U} {B : V} {F₁ F₂ : A ⟶ B} {e : ∀ a, F₁ a ≃ F₂ a} :
    F₁ ≃{e} F₂ :=
  h.mkFunEq e

  instance hasSubsingletonExt (U V : Universe) [HasIdentity V] {UV : Universe}
                              [HasIdentity UV] [HasFunctors U V UV] [HasTrivialExtensionality U V] :
    HasSubsingletonExt U V :=
  { eqExt := λ _ _ => funEq }

  variable (U : Universe) [HasIdentity U] [HasInternalFunctors U] [HasTrivialExtensionality U U]

  instance hasLinearFunExt [HasLinearFunOp U] : HasLinearFunOp.HasLinearFunExt U :=
  { rightId              := λ _         => funEq,
    rightIdExt           := λ _ _       => funEq,
    leftId               := λ _         => funEq,
    leftIdExt            := λ _ _       => funEq,
    swapRevApp           := λ _         => funEq,
    swapRevAppExt        := λ _ _       => funEq,
    swapCompFun          := λ _ _ _     => funEq,
    swapCompFunExt       := λ _ _       => funEq,
    swapCompFunExtExt    := λ _ _ _     => funEq,
    swapRevCompFun       := λ _ _       => funEq,
    swapRevCompFunExt    := λ _ {_ _} _ => funEq,
    swapRevCompFunExtExt := λ _ _ _     => funEq,
    compAssoc            := λ _ _ _     => funEq,
    compAssocExt         := λ _ _ _     => funEq,
    compAssocExtExt      := λ _ _ _     => funEq,
    compAssocExtExtExt   := λ _ _ _ _   => funEq }

  instance hasAffineFunExt [HasAffineFunOp U] : HasAffineFunOp.HasAffineFunExt U :=
  { rightConst       := λ _ {_ _} _ _ => funEq,
    rightConstExt    := λ _ {_} _ _   => funEq,
    rightConstExtExt := λ _ _ _       => funEq,
    leftConst        := λ _ _         => funEq,
    leftConstExt     := λ _ _         => funEq,
    leftConstExtExt  := λ _ _ _       => funEq }

  instance hasFullFunExt [HasFullFunOp U] : HasFullFunOp.HasFullFunExt U :=
  { dupSwap        := λ _     => funEq,
    dupSwapExt     := λ _ _   => funEq,
    dupConst       := λ _     => funEq,
    dupConstExt    := λ _ _   => funEq,
    rightDup       := λ _ _   => funEq,
    rightDupExt    := λ _ _   => funEq,
    rightDupExtExt := λ _ _ _ => funEq,
    substDup       := λ _ _   => funEq,
    substDupExt    := λ _ _   => funEq,
    substDupExtExt := λ _ _ _ => funEq }

  instance hasStandardFunctors [HasFullFunOp U] : HasStandardFunctors U := ⟨⟩

  instance hasInternalTopExt [HasLinearFunOp U] [HasInternalTop U] [HasTop.HasTopEq U] :
    HasInternalTop.HasTopExt U :=
  { elimFunEq := λ _ => funEq }

  instance hasProductExt [HasLinearFunOp U] [HasInternalProducts U] [HasProducts.HasProductEq U U] :
    HasInternalProducts.HasProductExt U :=
  { introEqExt      := λ _ _   => funEq,
    elimEqExt       := λ _ _   => funEq,
    elimEqExtExt    := λ _     => funEq,
    elimEqExtExtExt := λ _ _ _ => funEq }

  instance halfEquivDescExt [HasLinearFunOp U] {A B : U} {toFun : A ⟶ B} {invFun : B ⟶ A}
                            (e : HalfEquivDesc toFun invFun) :
    HalfEquivDesc.IsExtensional e :=
  ⟨funEq⟩

  instance equivDescExt [HasLinearFunOp U] {A B : U} (e : A ⮂ B) :
    EquivDesc.IsExtensional e :=
  ⟨⟩

  def hasInternalEquivalences [HasTrivialFunctoriality U U] [HasEquivalences U U U]
                              (toFunInj : ∀ {A B : U} {E₁ E₂ : A ⟷ B},
                                            HasEquivalences.toFun E₁ ≃ HasEquivalences.toFun E₂ →
                                            E₁ ≃ E₂) :
    HasInternalEquivalences U :=
  { defToFunFun  := λ _ _ => HasTrivialFunctoriality.defFun,
    isExt        := λ E => equivDescExt U (HasEquivalences.desc E),
    toFunInj     := toFunInj }

  instance [HasTrivialFunctoriality U U] [HasEquivalences U U U] [HasTrivialIdentity U] :
    HasInternalEquivalences U :=
  hasInternalEquivalences U (λ _ => HasTrivialIdentity.eq)

end HasTrivialExtensionality



class HasTrivialEquivalenceCondition (U : Universe) [HasIdentity U] [HasInternalFunctors U]
                                     [HasLinearFunOp U] [HasLinearFunOp.HasLinearFunExt U]
                                     [HasInternalEquivalences U] where
(mkEquiv {A B : U} (e : A ⮂ B) [he : EquivDesc.IsExtensional e] : A ⟷{e} B)

namespace HasTrivialEquivalenceCondition

  open HasLinearFunOp HasInternalEquivalences

  def defEquiv {U : Universe} [HasIdentity U] [HasInternalFunctors U]
               [HasLinearFunOp U] [HasLinearFunExt U] [HasInternalEquivalences U]
               [HasTrivialEquivalenceCondition U]
               {A B : U} {e : A ⮂ B} [he : EquivDesc.IsExtensional e] :
    A ⟷{e} B :=
  mkEquiv e

  variable (U : Universe) [HasIdentity U] [HasInternalFunctors U]
           [HasLinearFunOp U] [HasLinearFunExt U] [HasInternalEquivalences U]
           [HasTrivialEquivalenceCondition U]

  instance hasEquivOp : HasEquivOp U :=
  { defRefl  := λ _   => defEquiv,
    defSymm  := λ _   => defEquiv,
    defTrans := λ _ _ => defEquiv }

  instance hasTypeIdentity : HasTypeIdentity U := ⟨⟩

end HasTrivialEquivalenceCondition



class HasTrivialDependentFunctoriality (U V : Universe) {UV UpV : Universe} [HasTypeIdentity V]
                                       [HasFunctors U {V} UpV] [HasDependentFunctors U V UV] where
(mkDefPi {A : U} {φ : A ⟶ ⌊V⌋} (f : HasFunctors.Pi φ) : Π{f} (HasFunctors.toDefFun φ))

namespace HasTrivialDependentFunctoriality

  def defPi {U V UV UpV : Universe} [HasTypeIdentity V] [HasFunctors U {V} UpV]
            [HasDependentFunctors U V UV] [h : HasTrivialDependentFunctoriality U V]
            {A : U} {φ : A ⟶ ⌊V⌋} {f : HasFunctors.Pi φ} :
    Π{f} (HasFunctors.toDefFun φ) :=
  h.mkDefPi f

  -- TODO: actual dependent functors

end HasTrivialDependentFunctoriality
