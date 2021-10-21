import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Lemmas.DerivedFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v iu



class HasTop (U : Universe.{u}) where
(T : U)
(t : T)

namespace HasTop

  variable (U : Universe) [h : HasTop U] 

  @[reducible] def Top : U     := h.T
  @[reducible] def top : Top U := h.t

end HasTop

def HasTop.topEquivalence (α : Sort u) (V : Universe.{v}) [HasTop V] : EquivalenceRelation α V :=
{ R := MetaRelation.unitRelation    α (HasTop.Top V),
  h := MetaRelation.unitEquivalence α (HasTop.top V) }

class HasTop.HasTopEq (U : Universe.{u}) [HasTop.{u} U] [HasIdentity.{u, iu} U] where
(topEq (t' : Top U) : t' ≃ top U)

namespace HasTop.HasTopEq

  variable (U : Universe) [HasIdentity U] [HasTop U] [HasTop.HasTopEq U]

  instance isSubsingleton : HasInstanceEquivalences.IsSubsingleton (Top U) :=
  ⟨λ a b => (topEq b)⁻¹ • topEq a⟩

end HasTop.HasTopEq

-- Eliminating from `Top` should not require `SubLinearFunOp`, as conceptually, an instance of
-- `Top` does not hold any data. Therefore, we define a specialized version of `constFun`.

class HasInternalTop (U : Universe.{u}) [HasIdentity.{u, iu} U] [HasInternalFunctors U]
  extends HasTop U where
(defElimFun {A : U} (a : A) : T ⟶[λ _ => a] A)

namespace HasInternalTop

  open HasTop

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasInternalTop U]

  @[reducible] def elimFun {A : U} (a : A) : Top U ⟶ A := defElimFun a

end HasInternalTop

class HasInternalTop.HasTopExt (U : Universe.{u}) [HasIdentity.{u, iu} U] [HasInternalFunctors U]
                               [HasInternalTop U] extends
  HasTop.HasTopEq U where
(elimFunEq {A : U} {a : A} {F : HasTop.Top U ⟶ A} (e : F (HasTop.top U) ≃ a) :
   F ≃[λ t => HasFunctors.byDef⁻¹ • e • HasCongrArg.congrArg F (topEq t)] elimFun a)



class HasBot (U : Universe.{u}) where
(B : U)
(elim (b : B) (A : U) : A)

namespace HasBot

  variable (U : Universe) [h : HasBot U]

  @[reducible] def Bot : U := h.B

end HasBot

class HasInternalBot (U : Universe.{u}) [HasIdentity.{u, iu} U] [HasInternalFunctors U]
  extends HasBot U where
(defElimFun (A : U) : B ⟶[λ b => HasBot.elim b A] A)

namespace HasInternalBot

  open HasBot

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasInternalBot U]

  def elimFun (A : U) : Bot U ⟶ A := HasInternalBot.defElimFun A

  def Not (A : U) : U := A ⟶ Bot U

end HasInternalBot

class HasClassicalLogic (U : Universe.{u}) [HasIdentity.{u, iu} U] [HasInternalFunctors U]
                        [HasInternalBot U] where
(byContradictionFun (A : U) : HasInternalBot.Not (HasInternalBot.Not A) ⟶ A)
