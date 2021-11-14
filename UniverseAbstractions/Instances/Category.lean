import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.CategoryTheory.Meta
import UniverseAbstractions.Axioms.CategoryTheory.Basic
import UniverseAbstractions.Axioms.CategoryTheory.Extended
import UniverseAbstractions.Instances.Utils.Bundled



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w iw



namespace CategoryTheory.IsCategory

  open Bundled MetaRelation HasFunctors HasCongrArg HasLinearFunOp IsAssociative IsCategoricalPreorder

  def typeClass (W : Universe.{w}) [HasIdentity.{w, iw} W] [HasStandardFunctors W] :
    SimpleTypeClass.{max u (w + 1) iw, max u (w + 1) iw} := IsCategory.{max u (w + 1) iw, w, iw} W
  def univ (W : Universe.{w}) [HasIdentity.{w, iw} W] [HasStandardFunctors W] :
    Universe.{max u (w + 1) iw} := Bundled.univ.{max u (w + 1) iw, max u (w + 1) iw} (typeClass.{u} W)

  variable {W : Universe.{w}} [HasIdentity.{w, iw} W] [HasStandardFunctors W]

  instance inst (A : univ.{u} W) : IsCategory.{max u (w + 1) iw} W ⌈A⌉ := Bundled.inst A

  variable [hIsoUniv : IsIsoUniverse W]

  instance hasEquivalenceRelation (A : univ.{u} W) : HasEquivalenceRelation ⌈A⌉ W :=
  ⟨(hIsoUniv.hasIsomorphisms A).Iso⟩

  instance hasInstanceEquivalences : HasInstanceEquivalences (univ W) W :=
  ⟨hasEquivalenceRelation⟩

  variable [hFunUniv : IsFunUniverse W]

  instance hasFunctoriality : HasFunctoriality (typeClass.{u} W) (typeClass.{v} W) W :=
  ⟨λ {A B : univ W} (φ : A → B) => (hFunUniv.hasCategoryFunctors ⌈A⌉ ⌈B⌉).Fun φ⟩

  def bundledFunctor {A : univ.{u} W} {B : univ.{v} W} (F : A ⟶' B) :
    BundledFunctor (hFunUniv.hasCategoryFunctors ⌈A⌉ ⌈B⌉).Fun :=
  { φ := F.f,
    F := F.isFun }

  instance isCategoryFunctor {A : univ.{u} W} {B : univ.{v} W} (F : A ⟶' B) :
    IsCategoryFunctor (α := ⌈A⌉) (β := ⌈B⌉) F.f :=
  HasCategoryFunctors.isCategoryFunctor (bundledFunctor F)

  instance funIsCategory (A : univ.{u} W) (B : univ.{v} W) :
    IsCategory.{max u v (w + 1) iw, w, iw} W (A ⟶' B) :=
  { Hom                         := λ (F G : A ⟶' B) => NaturalTransformation F G,
    homIsPreorder               := sorry,
    homHasTransFun              := sorry,
    homIsCategoricalPreorder    := sorry,
    homIsCategoricalPreorderExt := sorry }

  instance hasFunctorInstances :
    HasFunctorInstances.{max u (w + 1) iw, max u (w + 1) iw, max u (w + 1) iw} (typeClass.{u} W) :=
  ⟨funIsCategory⟩

  instance hasFunctors : HasFunctors (univ W) (univ W) (univ W) :=
  Bundled.hasFunctors.{max u (w + 1) iw, max u (w + 1) iw, max u (w + 1) iw} (typeClass.{u} W)

  instance hasCongrArg : HasCongrArg (univ W) (univ W) :=
  ⟨λ F => sorry⟩

  instance hasInternalFunctors : HasInternalFunctors (univ W) := ⟨⟩

  instance hasLinearFunOp : HasLinearFunOp (univ W) := sorry

end CategoryTheory.IsCategory
