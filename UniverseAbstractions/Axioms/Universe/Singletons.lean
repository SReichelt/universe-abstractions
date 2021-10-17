import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u iu



class HasTop (U : Universe.{u}) [HasIdentity.{u, iu} U] where
(T : U)
(t : T)
(topEq (t' : T) : t' ≃ t)

namespace HasTop

  variable (U : Universe) [HasIdentity U] [h : HasTop U] 

  @[reducible] def Top : U     := h.T
  @[reducible] def top : Top U := h.t

  instance isSubsingleton : HasIdentity'.IsSubsingleton (Top U) :=
  ⟨λ a b => (h.topEq b)⁻¹ • h.topEq a⟩

end HasTop

-- Eliminating from `Top` should not require `SubLinearFunOp`, as conceptually, an instance of
-- `Top` does not hold any data. Therefore, we define a specialized version of `constFun`.

class HasInternalTop (U : Universe.{u}) [HasIdentity.{u, iu} U] [HasInternalFunctors U]
  extends HasTop U where
(defElimFun {A : U} (a : A) : T ⟶[λ _ => a] A)
(defElimFunFun (A : U) : A ⟶[λ a => defElimFun a] (T ⟶ A))

namespace HasInternalTop

  open HasTop

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasInternalTop U]

  @[reducible] def elimFun {A : U} (a : A) : Top U ⟶ A := defElimFun a
  @[reducible] def elimFunFun (A : U) : A ⟶ Top U ⟶ A := defElimFunFun A

end HasInternalTop



class HasBot (U : Universe.{u}) where
(B : U)
(elim (b : B) (A : U) : A)

namespace HasBot

  variable (U : Universe) [h : HasBot U]

  @[reducible] def Bot : U := h.B

end HasBot

class HasInternalBot (U : Universe.{u}) [HasIdentity.{u, iu} U] [HasInternalFunctors U]
  extends HasBot U where
(defElimFun (A : U) : HasBot.Bot U ⟶[λ b => HasBot.elim b A] A)

namespace HasInternalBot

  open HasBot

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasInternalBot U]

  def elimFun (A : U) : Bot U ⟶ A := HasInternalBot.defElimFun A

  def Not (A : U) : U := A ⟶ Bot U

end HasInternalBot

class HasClassicalLogic (U : Universe.{u}) [HasIdentity.{u, iu} U] [HasInternalFunctors U]
                        [HasInternalBot U] where
(byContradictionFun (A : U) : HasInternalBot.Not (HasInternalBot.Not A) ⟶ A)
