import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations.AttachedRelations
import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations.FunctorCompatibility
import UniverseAbstractions.Universes.Layer1.Axioms.Equivalences



namespace UniverseAbstractions.Layer1

set_option autoImplicit false

universe u uu v

open Universe HasFunctors HasSwapFun HasRevCompFun₂ HasPreorderRelation HasIsomorphisms
     HasEquivalenceRelationBase



structure PropertyUniverse extends Universe.{u, uu} where
  propositionType : toUniverse
  [hPropInst : HasInstances.{v, u} propositionType]
  [hPropLin : HasLinearLogic ⟨propositionType⟩]
  [hPropEquiv : HasEquivalences ⟨propositionType⟩]

namespace PropertyUniverse

  instance (U : PropertyUniverse.{u, uu, v}) : HasInstances.{v, u} U.propositionType := U.hPropInst

  def V (U : PropertyUniverse.{u, uu, v}) : Universe.{v, u} := ⟨U.propositionType⟩
  def inV {U : PropertyUniverse} (A : U.propositionType) : U.V := A

  instance (U : PropertyUniverse.{u, uu, v}) : HasLinearLogic  U.V := U.hPropLin
  instance (U : PropertyUniverse.{u, uu, v}) : HasEquivalences U.V := U.hPropEquiv

  instance (U : PropertyUniverse.{u, uu, v}) : HasPreorderRelation U.V U.propositionType :=
    HasLinearLogic.hasPreorderRelation U.V
  instance (U : PropertyUniverse.{u, uu, v}) : HasIsomorphisms U.propositionType :=
    HasEquivalences.toHasIsomorphisms

  def defPropType (U : PropertyUniverse.{u, uu, v}) : DefType U.toUniverse U.V where
    A    := U.propositionType
    elim := id

  class HasTypeCtors (U : PropertyUniverse.{u, uu, v}) where
    [hCtorFun : HasFunctors U.propositionType U.toUniverse]
    [hCtorCongrArg : HasCongrArg U.propositionType U.propositionType]
    [hIdCtor : HasIdFun U.propositionType]
    [hSwapCtor : HasSwapFun U.propositionType U.propositionType U.toUniverse]
    [hCompCtor : HasCompFun U.propositionType U.propositionType U.toUniverse]

  namespace HasTypeCtors

    section

      variable (U : PropertyUniverse) [h : HasTypeCtors U]

      instance : HasFunctors U.propositionType U.toUniverse := h.hCtorFun

      instance : HasIdFun U.propositionType := h.hIdCtor
      instance : HasSwapFun U.propositionType U.propositionType U.toUniverse := h.hSwapCtor
      instance : HasCompFun U.propositionType U.propositionType U.toUniverse := h.hCompCtor

    end

    def TypeCtor (U : PropertyUniverse) [HasTypeCtors U] : U.toUniverse :=
      U.propositionType ⥤ U.propositionType

    namespace TypeCtor

      def apply {U : PropertyUniverse} [HasTypeCtors U] (φ : TypeCtor U) (A : U.V) : U.V :=
        HasFunctors.apply φ A

      instance coeFun (U : PropertyUniverse) [HasTypeCtors U] :
          CoeFun (TypeCtor U) (λ _ => U.V → U.V) :=
        ⟨apply⟩

      variable {U : PropertyUniverse} [h : HasTypeCtors U]

      @[reducible] def ctorCongrArg (φ : TypeCtor U) {A₁ A₂ : U.V} (E : A₁ ≃ A₂) : φ A₁ ≃ φ A₂ :=
        (h.ctorFunctor φ) E

      @[reducible] def ctorCongrArgFun (φ : TypeCtor U) (A₁ A₂ : U.V) : A₁ ≃ A₂ ⟶ φ A₁ ≃ φ A₂ :=
        (h.ctorFunctor φ).inst A₁ A₂

      instance ctorCongrArg.isFunApp {φ : TypeCtor U} {A₁ A₂ : U.V} {E : A₁ ≃ A₂} :
          IsFunApp (A₁ ≃ A₂) (ctorCongrArg φ E) :=
        ⟨ctorCongrArgFun φ A₁ A₂, E⟩

    end TypeCtor

    @[reducible] def TypeCtor₂ (U : PropertyUniverse) [HasTypeCtors U] : U.toUniverse :=
      U.propositionType ⥤ TypeCtor U

    namespace TypeCtor₂

      def apply {U : PropertyUniverse} [HasTypeCtors U] (φ : TypeCtor₂ U) (A : U.V) : TypeCtor U :=
        HasFunctors.apply φ A

      instance coeFun (U : PropertyUniverse) [HasTypeCtors U] :
          CoeFun (TypeCtor₂ U) (λ _ => U.V → TypeCtor U) :=
        ⟨apply⟩

      def apply₂ {U : PropertyUniverse} [HasTypeCtors U] (φ : TypeCtor₂ U) (A B : U.V) : U.V :=
        φ A B

      variable {U : PropertyUniverse} [h : HasTypeCtors U]

      @[reducible] def ctorCongrArg₂ (φ : TypeCtor₂ U) {A₁ A₂ B₁ B₂ : U.V} (E : A₁ ≃ A₂)
                                     (F : B₁ ≃ B₂) :
          φ A₁ B₁ ≃ φ A₂ B₂ :=
        _ • (TypeCtor.ctorCongrArg (swapFun φ B₁)) E

      @[reducible] def ctorCongrArgFun (φ : TypeCtor U) (A₁ A₂ : U.V) : A₁ ≃ A₂ ⟶ φ A₁ ≃ φ A₂ :=
        (h.ctorFunctor φ).inst A₁ A₂

      instance ctorCongrArg.isFunApp {φ : TypeCtor U} {A₁ A₂ : U.V} {E : A₁ ≃ A₂} :
          IsFunApp (A₁ ≃ A₂) (ctorCongrArg φ E) :=
        ⟨ctorCongrArgFun φ A₁ A₂, E⟩

    end TypeCtor₂

    def DefTypeCtor (U : PropertyUniverse) (f : U.V → U.V) :=
      U.propositionType ⟶{f} U.propositionType


#exit

    namespace DefTypeCtor

      instance (U : PropertyUniverse) (f : U.V → U.V) : Coe (DefTypeCtor U f) (TypeCtor U) :=
        DefFun.coeType (α := U.propositionType) f

      variable {U : PropertyUniverse} [HasUnivFunctors U.V U.V]

      class IsFunctorial {f : U.V → U.V} (φ : DefTypeCtor U f) where
        toFun (A : U.V) : TypeCtor.apply φ A ⟶ f A

    end DefTypeCtor

    def DefTypeCtor₂ (U : PropertyUniverse) (f : U.V → U.V → U.V) :=
      U.propositionType ⟶ U.propositionType ⟶{f} U.propositionType

    namespace DefTypeCtor₂

      instance (U : PropertyUniverse) (f : U.V → U.V → U.V) : Coe (DefTypeCtor₂ U f) (TypeCtor₂ U) :=
        DefFun₂.coeType (α := U.propositionType) (β := U.propositionType) f

      variable {U : PropertyUniverse} [HasUnivFunctors U.V U.V]

      class IsFunctorial {f : U.V → U.V → U.V} (φ : DefTypeCtor₂ U f) where
        toFun (A B : U.V) : TypeCtor₂.apply₂ φ A B ⟶ f A B

    end DefTypeCtor₂

  end HasTypeCtors

end PropertyUniverse

open PropertyUniverse



class HasFunCtor (α : Sort u) (U : PropertyUniverse.{u, uu}) [HasFunctors α U.V] where
  defFunCtor : DefTypeCtor U (λ Y => α ⟶ Y)

namespace HasFunCtor

  variable (α : Sort u) (U : PropertyUniverse.{u, uu}) [HasFunctors α U.V] [h : HasFunCtor α U]

  @[reducible] def funCtor : TypeCtor U := h.defFunCtor

  instance isCovariant [HasUnivFunctors U.V U.V] [HasRevCompFun₂ α U.V U.V] :
      TypeCtor.IsCovariant (funCtor α U) :=
    ⟨revCompFun₂ α⟩

end HasFunCtor



class HasProperties (α : Sort u) (U : PropertyUniverse.{u, uu}) extends
  HasFunctors α (prpUniv U)
