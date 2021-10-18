import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v uv iu iv iuv



class HasProducts (U : Universe.{u}) (V : Universe.{v}) (UxV : outParam Universe.{uv}) :
  Type (max u v uv) where
(Prod                                  : U → V → UxV)
(intro {A : U} {B : V} (a : A) (b : B) : Prod A B)
(fst   {A : U} {B : V} (P : Prod A B)  : A)
(snd   {A : U} {B : V} (P : Prod A B)  : B)

namespace HasProducts

  infix:35 " ⊓ " => HasProducts.Prod
  
  class HasProductEq (U : Universe.{u}) (V : Universe.{v}) {UxV : Universe.{uv}}
                     [HasProducts U V UxV]
                     [HasIdentity.{u, iu} U] [HasIdentity.{v, iv} V] [HasIdentity.{uv, iuv} UxV] where
  (introEq {A : U} {B : V} (P : A ⊓ B)     : intro (fst P) (snd P) ≃ P)
  (fstEq   {A : U} {B : V} (a : A) (b : B) : fst (intro a b) ≃ a)
  (sndEq   {A : U} {B : V} (a : A) (b : B) : snd (intro a b) ≃ b)

end HasProducts



-- In many cases, the product of two universe instances is again an instance of the same universe.
--
-- Moreover, we would like to map in and out of products functorially. Introduction is simply given
-- by `A ⟶ B ⟶ A ⊓ B`, i.e. given an `A` and a `B`, we can construct their product. For
-- elimination, we take an indirect approach that works well with `HasLinearFunOp`,
-- `HasAffineFunOp`, and `HasFullFunOp`: If only `HasLinearFunOp` is given, it is both allowed and
-- required to always use both sides of a product; eliminating to either `A` or `B` requires
-- `constFun`.

class HasInternalProducts (U : Universe.{u}) [HasIdentity.{u, iu} U] [HasInternalFunctors U] extends
  HasProducts U U U where
(defIntroFun    {A : U} (a : A) (B : U)     : B ⟶[λ b => HasProducts.intro a b] A ⊓ B)
(defIntroFunFun (A B : U)                   : A ⟶[λ a => defIntroFun a B] (B ⟶ A ⊓ B))
(defElimFun     {A B C : U} (F : A ⟶ B ⟶ C) : A ⊓ B ⟶[λ P => F (HasProducts.fst P) (HasProducts.snd P)] C)
(defElimFunFun  (A B C : U)                 : (A ⟶ B ⟶ C) ⟶[λ F => defElimFun F] (A ⊓ B ⟶ C))

namespace HasInternalProducts

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasInternalProducts U]

  @[reducible] def introFun {A : U} (a : A) (B : U) : B ⟶ A ⊓ B := defIntroFun a B
  @[reducible] def introFunFun (A B : U) : A ⟶ B ⟶ A ⊓ B := defIntroFunFun A B

  @[reducible] def elimFun {A B C : U} (F : A ⟶ B ⟶ C) : A ⊓ B ⟶ C := defElimFun F
  @[reducible] def elimFunFun (A B C : U) : (A ⟶ B ⟶ C) ⟶ (A ⊓ B ⟶ C) := defElimFunFun A B C

end HasInternalProducts

class HasInternalProducts.HasProductExt (U : Universe.{u}) [HasIdentity.{u, iu} U]
                                        [HasInternalFunctors U] [HasLinearFunOp U]
                                        [HasInternalProducts U] extends
  HasProducts.HasProductEq U U where
(introEqExt (A B : U) :
   elimFun (introFunFun A B)
   ≃[λ P => HasFunctors.byDef⁻¹ • introEq P • (HasLinearFunOp.byDef₂ • HasFunctors.byDef)]
   HasLinearFunOp.idFun (A ⊓ B))
