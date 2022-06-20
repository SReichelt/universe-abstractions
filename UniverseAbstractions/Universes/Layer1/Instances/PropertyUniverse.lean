import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors

import UniverseAbstractions.Universes.Helpers



namespace UniverseAbstractions.Layer1

set_option autoImplicit false

universe u uu v w

open Helpers



-- This is obviously just a list. It is intended to be used as a list of parameters.
inductive PropertyType (U : Universe.{u, uu}) : Sort (max 1 uu) where
  | cnst
  | fn (A : U) (P : PropertyType U)

namespace PropertyType

  structure FunDesc (U : Universe.{u, uu}) where
    Ω           : Sort u
    Fun (A : U) : (A → Ω) → Sort (max 1 u v)

  section

    variable {U : Universe.{u, uu}} (desc : FunDesc.{u, uu, v} U)

    def FunctionType : PropertyType U → Sort u
      | cnst   => desc.Ω
      | fn A P => A → FunctionType P

    def FunctorType' (A : U) (P : PropertyType U) (f : A → FunctionType desc P) :
        Sort (max 1 u v) :=
      match P, f with
      | cnst,   f => desc.Fun A f
      | fn B Q, f => AbstractBiFun (FunctorType' B Q) (FunctorType' A Q) f

    def FunctorType (P : PropertyType U) (f : FunctionType desc P) : Sort (max 1 u v) :=
      match P, f with
      | cnst,   f => PUnit
      | fn B Q, f => FunctorType' desc B Q f

    structure BundledFunctor (P : PropertyType U) : Sort (max 1 u v) where
      {f : FunctionType desc P}
      F : FunctorType desc P f

    namespace BundledFunctor

      def const (c : desc.Ω) : BundledFunctor desc cnst where
        f := c
        F := PUnit.unit

      def apply {A : U} {P : PropertyType U} (φ : BundledFunctor desc (fn A P)) (a : A) :
          BundledFunctor desc P where
        f := φ.f a
        F := match P, φ with
             | cnst,   φ => PUnit.unit
             | fn B Q, φ => φ.F.app a

    end BundledFunctor

    def univ : Universe.{max 1 u v, max 1 uu} where
      I := PropertyType U
      h := ⟨BundledFunctor desc⟩

    def Omega : univ desc := cnst

    instance coeToUniv   : Coe desc.Ω (Omega desc) := ⟨BundledFunctor.const desc⟩
    instance coeFromUniv : Coe (Omega desc) desc.Ω := ⟨BundledFunctor.f⟩

    instance univ.hasFunctors (A : U) : HasFunctors A (univ desc) where
      defFunType Y := { A    := fn A Y
                        elim := BundledFunctor.apply desc }

    instance univ.hasUnivFunctors : HasUnivFunctors U (univ desc) where
      hFun := univ.hasFunctors desc

  end

  section

    variable {U : Universe.{u, uu}} {desc : FunDesc.{u, uu, v} U}

    def DefFun (A : U) (P : univ desc) (f : A → P) := FunctorType' desc A P (λ a => (f a).f)
    notation:20 A:21 " ⟶⦃" f:0 "⦄ " P:21 => PropertyType.DefFun A P f

    def DefFun₂ (A B : U) (P : univ desc) (f : A → B → P) :=
      AbstractBiFun (FunctorType' desc B P) (FunctorType' desc A P) (λ a b => (f a b).f)
    notation:20 A:21 " ⟶ " B:21 " ⟶⦃" f:0 "⦄ " P:21 => PropertyType.DefFun₂ A B P f

    def defFun {A : U} {P : univ desc} {f : A → P} (F : A ⟶⦃f⦄ P) : A ⟶{f} P := ⟨⟨F⟩⟩

    def defFun₂ {A B : U} {P : univ desc} {f : A → B → P} (F : A ⟶ B ⟶⦃f⦄ P) : A ⟶ B ⟶{f} P :=
      ⟨λ a => defFun (F.app a),
       defFun F⟩

  end

end PropertyType
