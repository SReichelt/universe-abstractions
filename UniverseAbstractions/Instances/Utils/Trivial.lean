import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.FunctorExtensionality
import UniverseAbstractions.Axioms.Universe.Singletons
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Categories



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u



namespace unit

  open MetaRelation

  def unitEq (α : Sort u) : EquivalenceRelation α unit :=
  { R := unitRelation α Inst,
    h := unitEquivalence α inst }

end unit

class HasTrivialIdentity (U : Universe)

namespace HasTrivialIdentity

  instance hasIdentity' (U : Universe) [HasTrivialIdentity U] :
    HasIdentity' U unit :=
  ⟨λ A => unit.unitEq ⌈A⌉⟩

  instance hasCongrArg (U V : Universe) [HasIdentity U] [HasTrivialIdentity V]
                       {UV : Universe} [HasFunctors U V UV] :
    HasCongrArg U V :=
  ⟨λ {_ _} _ {_ _} _ => unit.inst⟩

  instance hasTopEq (U : Universe) [HasTrivialIdentity U] [HasTop U] :
    HasTop.HasTopEq U :=
  ⟨λ _ => unit.inst⟩

  instance hasProductEq (U V : Universe) [HasTrivialIdentity U] [HasTrivialIdentity V]
                        {UxV : Universe} [HasTrivialIdentity UxV] [HasProducts U V UxV] :
    HasProducts.HasProductEq U V :=
  { introEq := λ _   => unit.inst,
    fstEq   := λ _ _ => unit.inst,
    sndEq   := λ _ _ => unit.inst }

end HasTrivialIdentity



class HasTrivialFunctoriality (U V : Universe) [HasIdentity V] {UV : Universe}
                              [HasFunctors U V UV] where
(mkDefFun {A : U} {B : V} (f : A → B) : A ⟶[f] B)

namespace HasTrivialFunctoriality

  open MetaRelation

  def defFun {U V : Universe} [HasIdentity V] {UV : Universe} [HasFunctors U V UV]
             [h : HasTrivialFunctoriality U V] {A : U} {B : V} {f : A → B} :
    A ⟶[f] B :=
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

  variable (U : Universe) [HasIdentity U] [HasInternalFunctors U] [HasTrivialFunctoriality U U]

  instance hasLinearFunOp : HasLinearFunOp U :=
  { defIdFun         := λ _     => defFun,
    defAppFun        := λ _ _   => defFun,
    defAppFunFun     := λ _ _   => defFun,
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

  instance hasTransFun (α : Sort u) (R : MetaRelation α U) [HasTrans R] :
    HasTransFun R :=
  { defTransFun    := λ _ _   => defFun,
    defTransFunFun := λ _ _ _ => defFun }

  instance hasSymmFun (α : Sort u) (R : MetaRelation α U) [HasSymm R] :
    HasSymmFun R :=
  { defSymmFun := λ _ _ => defFun }

end HasTrivialFunctoriality



class HasTrivialExtensionality (U V : Universe) [HasIdentity V] {UV : Universe} [HasIdentity UV]
                               [HasFunctors U V UV] where
(mkFunEq {A : U} {B : V} {F₁ F₂ : A ⟶ B} (e : ∀ a, F₁ a ≃ F₂ a) : F₁ ≃[e] F₂)

namespace HasTrivialExtensionality

  instance fromTrivialIdentity (U V : Universe) [HasIdentity V] {UV : Universe} [HasTrivialIdentity UV]
                               [HasFunctors U V UV] :
    HasTrivialExtensionality U V :=
  ⟨λ _ => unit.inst⟩

  def funEq {U V : Universe} [HasIdentity V] {UV : Universe} [HasIdentity UV]
            [HasFunctors U V UV] [h : HasTrivialExtensionality U V]
            {A : U} {B : V} {F₁ F₂ : A ⟶ B} {e : ∀ a, F₁ a ≃ F₂ a} :
    F₁ ≃[e] F₂ :=
  h.mkFunEq e

  variable (U : Universe) [HasIdentity U] [HasInternalFunctors U] [HasTrivialExtensionality U U]

  instance hasLinearFunExt [HasLinearFunOp U] : HasLinearFunOp.HasLinearFunExt U :=
  { rightId              := λ _         => funEq,
    rightIdExt           := λ _ _       => funEq,
    leftId               := λ _         => funEq,
    leftIdExt            := λ _ _       => funEq,
    swapApp              := λ _         => funEq,
    swapAppExt           := λ _ _       => funEq,
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
  { introEqExt := λ _ _ => funEq }

end HasTrivialExtensionality
