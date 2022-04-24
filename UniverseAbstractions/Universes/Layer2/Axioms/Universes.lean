import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations



namespace UniverseAbstractions.Layer2

set_option autoBoundImplicitLocal false

open Layer1.Prerelation

universe u uu v vv



structure Universe extends Layer1.Universe.{u, uu} where
(V : Layer1.Universe.{v, vv})
[hasFun : Layer1.HasFunctors V]
[hasLin : Layer1.HasLinearLogic V]
[hasEq (A : toUniverse) : Layer1.HasEquivalenceRelation A V]

namespace Universe

  instance : Coe Universe Layer1.Universe := ⟨Universe.toUniverse⟩

  instance hasInstances : Layer1.HasInstances.{uu, (max u uu v vv) + 1} Universe.{u, uu, v, vv} :=
  ⟨λ U => U.I⟩

  section

    variable (U : Universe.{u, uu})

    instance instInst : Layer1.HasInstances.{u, uu} U.I := Layer1.Universe.instInst U
    instance : Layer1.HasInstances U := instInst U

    instance : Layer1.HasFunctors    U.V := U.hasFun
    instance : Layer1.HasLinearLogic U.V := U.hasLin

  end

  variable {U : Universe}

  instance (A : U) : Layer1.HasEquivalenceRelation A U.V := U.hasEq A

  @[reducible] def InstEq {A : U} (a b : A) : U.V := (U.hasEq A).R a b

  namespace InstEq

    infix:25 " ≃ " => Universe.InstEq

    variable {A : U}

    @[reducible] def refl (a : A) : a ≃ a := HasRefl.refl a
    @[reducible] def symm {a b : A} (e : a ≃ b) : b ≃ a := e⁻¹
    @[reducible] def trans {a b c : A} (f : a ≃ b) (g : b ≃ c) : a ≃ c := g • f

  end InstEq

end Universe
