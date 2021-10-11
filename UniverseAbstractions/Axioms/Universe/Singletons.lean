-- TODO: Adapt to `HasIdentity`.
#exit 0



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

class HasEmbeddedTop (U : Universe.{u}) [HasIdentity.{u, iu} U] [HasEmbeddedFunctors U]
  extends HasTop U where
(defElimFun {A : U} (a : A) : T ⟶[λ _ => a] A)
(defElimFunFun (A : U) : A ⟶[λ a => defElimFun a] (T ⟶ A))

namespace HasEmbeddedTop

  open HasTop

  variable {U : Universe} [HasIdentity U] [HasEmbeddedFunctors U] [HasEmbeddedTop U]

  @[reducible] def elimFun {A : U} (a : A) : Top U ⟶ A := defElimFun a
  @[reducible] def elimFunFun (A : U) : A ⟶ Top U ⟶ A := defElimFunFun A

end HasEmbeddedTop



class HasBot (U : Universe.{u}) where
(B : U)
(elim (b : B) (A : U) : A)

namespace HasBot

  variable (U : Universe) [h : HasBot U]

  @[reducible] def Bot : U := h.B

end HasBot

class HasEmbeddedBot (U : Universe.{u}) [HasIdentity.{u, iu} U] [HasEmbeddedFunctors U]
  extends HasBot U where
(defElimFun (A : U) : HasBot.Bot U ⟶[λ b => HasBot.elim b A] A)

namespace HasEmbeddedBot

  open HasBot

  variable {U : Universe} [HasIdentity U] [HasEmbeddedFunctors U] [HasEmbeddedBot U]

  def elimFun (A : U) : Bot U ⟶ A := HasEmbeddedBot.defElimFun A

  def Not (A : U) : U := A ⟶ Bot U

end HasEmbeddedBot

class HasClassicalLogic (U : Universe.{u}) [HasIdentity.{u, iu} U] [HasEmbeddedFunctors U]
                        [HasEmbeddedBot U] where
(byContradictionFun (A : U) : HasEmbeddedBot.Not (HasEmbeddedBot.Not A) ⟶ A)
