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

  instance hasProductEq (U V : Universe) [HasIdentity U] [HasTrivialIdentity U]
                        [HasIdentity V] [HasTrivialIdentity V]
                        {UxV : Universe} [HasIdentity UxV] [HasTrivialIdentity UxV]
                        [HasProducts U V UxV] :
    HasProducts.HasProductEq U V :=
  { introEq := λ _   => eq,
    fstEq   := λ _ _ => eq,
    sndEq   := λ _ _ => eq }

  def defEquiv {U : Universe} [HasIdentity U] [HasTrivialIdentity U]
               [HasInternalFunctors U] [HasLinearFunOp U] [HasLinearFunExt U]
               [HasInternalProducts U] [HasInternalEquivalences U]
               {A B : U} (E : A ⟷ B) {e : EquivDesc A B} : A ⟷{e} B :=
  ⟨E, eq, eq⟩

  def defPi {U V : Universe} [HasIdentity V] [HasTrivialIdentity V]
            {UpV UV : Universe} [HasFunctors U {V} UpV] [HasDependentFunctors U V UV]
            {A : U} {φ : A ⟶ ⌊V⌋} (F : Π φ) {f : HasFunctors.Pi φ} : Π{f} φ := 
  ⟨F, λ _ => eq⟩

  instance hasDependentCongrArg (U V : Universe) {UpV UV : Universe}
                                [HasFunctors U {V} UpV] [HasDependentFunctors U V UV]
                                [HasIdentity U] [HasTypeIdentity V] [HasTrivialIdentity V]
                                [HasCongrArg U {V}] :
    HasDependentCongrArg U V :=
  ⟨λ {_ _} _ {_ _} _ => eq⟩

  instance hasDependentProductEq (U V : Universe) {UpV UxV : Universe}
                                 [HasFunctors U {V} UpV] [HasDependentProducts U V UxV]
                                 [HasIdentity U] [HasTrivialIdentity U] [HasTypeIdentity V]
                                 [HasTrivialIdentity V] [HasCongrArg U {V}] [HasIdentity UxV]
                                 [HasTrivialIdentity UxV] :
    HasDependentProducts.HasDependentProductEq U V :=
  { introEq := λ _   => eq,
    fstEq   := λ _ _ => eq,
    sndEq   := λ _ _ => eq }

end HasTrivialIdentity



class HasTrivialFunctoriality (U V : Universe) [HasIdentity V] {UV : Universe}
                              [HasFunctors U V UV] where
(mkDefFun {A : U} {B : V} (f : A → B) : A ⟶{f} B)

namespace HasTrivialFunctoriality

  open MetaRelation HasLinearFunOp

  def defFun {U V : Universe} [HasIdentity V] {UV : Universe} [HasFunctors U V UV]
             [h : HasTrivialFunctoriality U V] {A : U} {B : V} {f : A → B} :
    A ⟶{f} B :=
  h.mkDefFun f

  instance hasIdFun (U : Universe) [HasIdentity U] {UU : Universe} [HasFunctors U U UU]
                    [HasTrivialFunctoriality U U] :
    HasIdFun U :=
  ⟨λ _ => defFun⟩

  instance hasConstFun (U V : Universe) [HasIdentity V] {UV : Universe} [HasFunctors U V UV]
                       [HasTrivialFunctoriality U V] :
    HasConstFun U V :=
  ⟨λ _ {_} _ => defFun⟩

  instance hasCompFun (U V W : Universe) [HasIdentity W] {UV VW UW : Universe}
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

  instance hasFunProp (U V W : Universe) {UpV UpW VW UpVW : Universe}
                      [HasFunctors U {V} UpV] [HasFunctors U {W} UpW] [HasFunctors V W VW]
                      [HasIdentity {VW}] [HasFunctors U {VW} UpVW]
                      [HasTrivialFunctoriality U {VW}] :
    HasFunProp U V W :=
  ⟨λ _ _ => defFun⟩

  instance hasProdProp (U V W : Universe) {UpV UpW VxW UpVxW : Universe}
                       [HasFunctors U {V} UpV] [HasFunctors U {W} UpW] [HasProducts V W VxW]
                       [HasIdentity {VxW}] [HasFunctors U {VxW} UpVxW]
                       [HasTrivialFunctoriality U {VxW}] :
    HasProdProp U V W :=
  ⟨λ _ _ => defFun⟩

  instance hasEquivProp (U V W : Universe) {UpV UpW VW WV V_W UpV_W : Universe}
                        [HasIdentity V] [HasIdentity W]
                        [HasFunctors U {V} UpV] [HasFunctors U {W} UpW]
                        [HasFunctors V W VW] [HasFunctors W V WV] [HasEquivalences V W V_W]
                        [HasIdentity {V_W}] [HasFunctors U {V_W} UpV_W]
                        [HasTrivialFunctoriality U {V_W}] :
    HasEquivProp U V W :=
  ⟨λ _ _ => defFun⟩

  variable (U : Universe) [HasIdentity U] [HasInternalFunctors U] [HasTrivialFunctoriality U U]

  instance hasLinearFunOp : HasLinearFunOp U :=
  { defIdFun         := λ _     => defFun,
    defRevAppFun     := λ _ _   => defFun,
    defRevAppFunFun  := λ _ _   => defFun,
    defCompFun       := λ _ _   => defFun,
    defCompFunFun    := λ _ _   => defFun,
    defCompFunFunFun := λ _ _ _ => defFun }

  instance hasAffineFunOp : HasAffineFunOp U :=
  { defConstFun    := λ _ {_} _ => defFun,
    defConstFunFun := λ _ _     => defFun }

  instance hasFullFunOp : HasFullFunOp U :=
  { defDupFun    := λ _   => defFun,
    defDupFunFun := λ _ _ => defFun }

  instance hasInternalTop [HasTop U] : HasInternalTop U :=
  { defElimFun := λ _ => defFun }

  instance hasInternalBot [HasBot U] : HasInternalBot U :=
  { defElimFun := λ _ => defFun }

  instance hasInternalProducts [HasProducts U U U] : HasInternalProducts U :=
  { defIntroFun    := λ _ _   => defFun,
    defIntroFunFun := λ _ _   => defFun,
    defElimFun     := λ _     => defFun,
    defElimFunFun  := λ _ _ _ => defFun }

  instance hasEquivOpFun [HasLinearFunExt U] [HasInternalProducts U]
                         [HasInternalEquivalences U] [HasEquivOp U] :
    HasEquivOpFun U :=
  { defSymmFun     := λ _ _   => defFun,
    defTransFun    := λ _ _   => defFun,
    defTransFunFun := λ _ _ _ => defFun }

end HasTrivialFunctoriality



class HasTrivialExtensionality (U V : Universe) [HasIdentity V] {UV : Universe} [HasIdentity UV]
                               [HasFunctors U V UV] where
(mkFunEq {A : U} {B : V} {F₁ F₂ : A ⟶ B} (e : ∀ a, F₁ a ≃ F₂ a) : F₁ ≃{e} F₂)

namespace HasTrivialExtensionality

  instance fromTrivialIdentity (U V : Universe) [HasIdentity V] {UV : Universe}
                               [HasIdentity UV] [HasTrivialIdentity UV] [HasFunctors U V UV] :
    HasTrivialExtensionality U V :=
  ⟨λ _ => HasTrivialIdentity.eq⟩

  def funEq {U V : Universe} [HasIdentity V] {UV : Universe} [HasIdentity UV]
            [HasFunctors U V UV] [h : HasTrivialExtensionality U V]
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
    dupDup         := λ _     => funEq,
    dupDupExt      := λ _ _   => funEq,
    rightDup       := λ _ _   => funEq,
    rightDupExt    := λ _ _   => funEq,
    rightDupExtExt := λ _ _ _ => funEq,
    substDup       := λ _ _   => funEq,
    substDupExt    := λ _ _   => funEq,
    substDupExtExt := λ _ _ _ => funEq }

  instance hasInternalTopExt [HasLinearFunOp U] [HasInternalTop U] [HasTop.HasTopEq U] :
    HasInternalTop.HasTopExt U :=
  { elimFunEq := λ _ => funEq }

  instance hasProductExt [HasLinearFunOp U] [HasInternalProducts U] [HasProducts.HasProductEq U U] :
    HasInternalProducts.HasProductExt U :=
  { introEqExt      := λ _ _   => funEq,
    elimEqExt       := λ _ _   => funEq,
    elimEqExtExt    := λ _     => funEq,
    elimEqExtExtExt := λ _ _ _ => funEq }

  instance hasInternalEquivalences [HasTrivialFunctoriality U U] [HasInternalProducts U]
                                   [HasEquivalences U U U] :
    HasInternalEquivalences U :=
  { defElimFun  := λ _ _ => HasTrivialFunctoriality.defFun,
    leftInvExt  := λ _   => funEq,
    rightInvExt := λ _   => funEq }

end HasTrivialExtensionality



class HasTrivialEquivalenceCondition (U : Universe) [HasIdentity U] [HasInternalFunctors U]
                                     [HasLinearFunOp U] [HasLinearFunOp.HasLinearFunExt U]
                                     [HasInternalProducts U] [HasInternalEquivalences U] where
(mkEquiv {A B : U} (e : HasInternalEquivalences.EquivDesc A B) : A ⟷{e} B)

namespace HasTrivialEquivalenceCondition

  open HasLinearFunOp HasInternalEquivalences

  def defEquiv {U : Universe} [HasIdentity U] [HasInternalFunctors U]
               [HasLinearFunOp U] [HasLinearFunExt U] [HasInternalProducts U]
               [HasInternalEquivalences U] [HasTrivialEquivalenceCondition U]
               {A B : U} {e : EquivDesc A B} :
    A ⟷{e} B :=
  mkEquiv e

  variable (U : Universe) [HasIdentity U] [HasInternalFunctors U]
           [HasLinearFunOp U] [HasLinearFunExt U] [HasInternalProducts U]
           [HasInternalEquivalences U] [HasTrivialEquivalenceCondition U]

  instance hasEquivOp : HasEquivOp U :=
  { defRefl  := λ _   => defEquiv,
    defSymm  := λ _   => defEquiv,
    defTrans := λ _ _ => defEquiv }

  instance hasTypeIdentity : HasTypeIdentity U := ⟨⟩

end HasTrivialEquivalenceCondition



class HasTrivialDependentFunctoriality (U V : Universe) [HasIdentity V] {UV UpV : Universe}
                                       [HasFunctors U {V} UpV] [HasDependentFunctors U V UV] where
(mkDefPi {A : U} {φ : A ⟶ ⌊V⌋} (f : HasFunctors.Pi φ) : Π{f} φ)

namespace HasTrivialDependentFunctoriality

  def defPi {U V : Universe} [HasIdentity V] {UV UpV : Universe} [HasFunctors U {V} UpV]
            [HasDependentFunctors U V UV] [h : HasTrivialDependentFunctoriality U V]
            {A : U} {φ : A ⟶ ⌊V⌋} {f : HasFunctors.Pi φ} :
    Π{f} φ :=
  h.mkDefPi f

  -- TODO

end HasTrivialDependentFunctoriality
