import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.CategoryTheory.Basic
import UniverseAbstractions.Axioms.CategoryTheory.Functors
import UniverseAbstractions.Instances.Utils.Bundled



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w iw



namespace CategoryTheory.IsCategory

  open Bundled MetaRelation HasFunctors HasCongrArg HasLinearFunOp IsAssociative IsCategoricalPreorder

  def typeClass (M : IsoUniverse.{w, iw}) :
    SimpleTypeClass.{max u (w + 1) iw, max u (w + 1) iw} := IsCategory.{max u (w + 1) iw, w, iw} M
  def univ (M : IsoUniverse.{w, iw}) :
    Universe.{max u (w + 1) iw} := Bundled.univ.{max u (w + 1) iw, max u (w + 1) iw} (typeClass.{u} M)

  variable {M : IsoUniverse.{w, iw}}

  instance inst (A : univ.{u} M) : IsCategory.{max u (w + 1) iw} M ⌈A⌉ := Bundled.inst A

  instance hasInstanceEquivalences : HasInstanceEquivalences (univ M) M.V := ⟨λ A => ⟨(inst A).Iso⟩⟩

  class IsFun {A : univ.{u} M} {B : univ.{v} M} (φ : A → B) extends
    IsCategoryFunctor φ : Sort (max u (w + 1) iw)

  instance hasFunctoriality :
    HasFunctoriality (typeClass.{u} M) (typeClass.{v} M) sort.{max u (w + 1) iw} :=
  ⟨IsFun⟩

  instance funIsCategory (A : univ.{u} M) (B : univ.{v} M) :
    IsCategory.{max u v (w + 1) iw, w, iw} M (Bundled.Fun A B) :=
  sorry

  instance hasFunctorInstances :
    HasFunctorInstances.{max u (w + 1) iw, max u (w + 1) iw, max u (w + 1) iw} (typeClass.{u} M) :=
  ⟨funIsCategory⟩

  instance hasFunctors : HasFunctors (univ M) (univ M) (univ M) :=
  Bundled.hasFunctors.{max u (w + 1) iw, max u (w + 1) iw, max u (w + 1) iw} (typeClass.{u} M)

  instance hasCongrArg : HasCongrArg (univ M) (univ M) :=
  ⟨λ F => sorry⟩

  instance hasInternalFunctors : HasInternalFunctors (univ M) := ⟨⟩

  instance hasLinearFunOp : HasLinearFunOp (univ M) := sorry

end CategoryTheory.IsCategory
