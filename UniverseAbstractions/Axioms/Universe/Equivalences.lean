import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Singletons
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Lemmas.DerivedFunctors
import UniverseAbstractions.Lemmas.DerivedSingletonFunctors
import UniverseAbstractions.Lemmas.DerivedProductFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w w' w''



class HasEquivalenceCondition (U : Universe.{u}) (X : Universe.{v}) [HasFunctors U U X] :
  Type (max u v w) where
(IsEquiv {α β : U} : (α ⟶ β) → (β ⟶ α) → Sort w)

namespace HasEquivalenceCondition

  variable {U : Universe.{u}} {X : Universe.{v}} [HasFunctors U U X]
           [h : HasEquivalenceCondition.{u, v, w} U X]

  def DefEquiv (α β : U) (toFun : α ⟶ β) (invFun : β ⟶ α) := h.IsEquiv toFun invFun

  notation:20 α:21 " ⟷[" toFun:0 "," invFun:0 "] " β:21 => HasEquivalenceCondition.DefEquiv α β toFun invFun

  structure Equiv (α β : U) : Sort (max 1 u v w) where
  (toFun  : α ⟶ β)
  (invFun : β ⟶ α)
  (E      : α ⟷[toFun,invFun] β)

  infix:20 " ⟷' " => HasEquivalenceCondition.Equiv

  variable {α β : U}

  def toDefEquiv                                    (E : α ⟷' β)              : α ⟷[E.toFun,E.invFun] β := E.E
  def fromDefEquiv {toFun : α ⟶ β} {invFun : β ⟶ α} (E : α ⟷[toFun,invFun] β) : α ⟷'                  β := ⟨toFun, invFun, E⟩

  instance (E : α ⟷' β)                     : CoeDep (α ⟷' β)              E (α ⟷[E.toFun,E.invFun] β) := ⟨toDefEquiv E⟩
  instance {toFun : α ⟶ β} {invFun : β ⟶ α} : Coe    (α ⟷[toFun,invFun] β)   (α ⟷' β)                  := ⟨fromDefEquiv⟩

  @[simp] theorem fromToDefEquiv                                  (E : α ⟷' β)              : fromDefEquiv (toDefEquiv E) = E :=
  match E with | ⟨_, _, _⟩ => rfl
  @[simp] theorem toFromDefEquiv {toFun : α ⟶ β} {invFun : β ⟶ α} (E : α ⟷[toFun,invFun] β) : toDefEquiv (fromDefEquiv E) = E := rfl

end HasEquivalenceCondition



class HasEquivalences (U : Universe.{u}) (X : Universe.{v}) [HasFunctors U U X]
                      (Y : outParam Universe.{w})
  extends HasEquivalenceCondition.{u, v, w'} U X : Type (max u v w w') where
[embed (α β : U) : HasEmbeddedType.{w, max 1 u v w'} Y (α ⟷' β)]

namespace HasEquivalences

  variable {U X Y : Universe} [HasFunctors U U X] [h : HasEquivalences U X Y]

  instance hasEmbeddedType (α β : U) : HasEmbeddedType Y (α ⟷' β) := h.embed α β

  def Equiv (α β : U) : Y := HasEmbeddedType.EmbeddedType Y (α ⟷' β)
  infix:20 " ⟷ " => HasEquivalences.Equiv

  variable {α β : U}

  def toExternal   (E : α ⟷  β) : α ⟷' β := HasEmbeddedType.toExternal   Y E
  def fromExternal (E : α ⟷' β) : α ⟷  β := HasEmbeddedType.fromExternal Y E

  @[simp] theorem fromToExternal (E : α ⟷  β) : fromExternal (toExternal E) = E := HasEmbeddedType.fromToExternal Y E
  @[simp] theorem toFromExternal (E : α ⟷' β) : toExternal (fromExternal E) = E := HasEmbeddedType.toFromExternal Y E

  def toFun  (E : α ⟷ β) : α ⟶ β := (toExternal E).toFun
  def invFun (E : α ⟷ β) : β ⟶ α := (toExternal E).invFun

  @[simp] theorem toFromExternal.to  (E : α ⟷' β) : (toExternal (fromExternal E)).toFun  = E.toFun  :=
  congrArg HasEquivalenceCondition.Equiv.toFun  (toFromExternal E)
  @[simp] theorem toFromExternal.inv (E : α ⟷' β) : (toExternal (fromExternal E)).invFun = E.invFun :=
  congrArg HasEquivalenceCondition.Equiv.invFun (toFromExternal E)

  def fromDefEquiv {to : α ⟶ β} {inv : β ⟶ α} (E : α ⟷[to,inv] β) : α ⟷ β :=
  fromExternal (HasEquivalenceCondition.fromDefEquiv E)

  instance {to : α ⟶ β} {inv : β ⟶ α} : Coe (α ⟷[to,inv] β) ⌈α ⟷ β⌉ := ⟨fromDefEquiv⟩

  @[simp] theorem fromDefEquiv.to.eff  {to : α ⟶ β} {inv : β ⟶ α} (E : α ⟷[to,inv] β) :
    toFun  (fromDefEquiv E) = to  :=
  by simp [fromDefEquiv, toFun,  HasEquivalenceCondition.fromDefEquiv]
  @[simp] theorem fromDefEquiv.inv.eff {to : α ⟶ β} {inv : β ⟶ α} (E : α ⟷[to,inv] β) :
    invFun (fromDefEquiv E) = inv :=
  by simp [fromDefEquiv, invFun, HasEquivalenceCondition.fromDefEquiv]

end HasEquivalences



class HasIdEquiv (U X : Universe) [HasFunctors U U X] [HasIdFun U] [HasEquivalenceCondition U X] where
(defIdEquiv (α : U) : α ⟷[HasIdFun.idFun α, HasIdFun.idFun α] α)

namespace HasIdEquiv

  variable {U X : Universe} [HasFunctors U U X] [HasIdFun U]

  def idEquiv' [HasEquivalenceCondition U X] [HasIdEquiv U X] (α : U) : α ⟷' α := HasEquivalenceCondition.fromDefEquiv (defIdEquiv α)

  def idEquiv {Y : Universe} [HasEquivalences U X Y] [HasIdEquiv U X] (α : U) : α ⟷ α := HasEquivalences.fromExternal (idEquiv' α)

end HasIdEquiv

class HasInvEquiv' (U X : Universe) [HasFunctors U U X] [HasEquivalenceCondition U X] where
(defInvEquiv {α β : U} (E : α ⟷' β) : β ⟷[E.invFun, E.toFun] α)

namespace HasInvEquiv'

  variable {U X : Universe} [HasFunctors U U X] [HasEquivalenceCondition U X] [HasInvEquiv' U X]

  def invEquiv' {α β : U} (E : α ⟷' β) : β ⟷' α := HasEquivalenceCondition.fromDefEquiv (defInvEquiv E)

end HasInvEquiv'

class HasInvEquiv (U X Y : Universe) [HasFunctors U U X] [HasEquivalences U X Y] where
(defInvEquiv {α β : U} (E : α ⟷ β) : β ⟷[HasEquivalences.invFun E, HasEquivalences.toFun E] α)

namespace HasInvEquiv

  variable {U X Y : Universe} [HasFunctors U U X] [HasEquivalences U X Y] [HasInvEquiv U X Y]

  def invEquiv {α β : U} (E : α ⟷ β) : β ⟷ α := HasEquivalences.fromDefEquiv (defInvEquiv E)

  instance hasInvEquiv' : HasInvEquiv' U X :=
  ⟨λ E => HasEquivalences.toFromExternal E ▸ defInvEquiv (HasEquivalences.fromExternal E)⟩

end HasInvEquiv

class HasCompEquiv' (U X : Universe) [HasFunctors U U X] [HasCompFun U U U X X] [HasEquivalenceCondition U X] where
(defCompEquiv {α β γ : U} (E : α ⟷' β) (F : β ⟷' γ) : α ⟷[HasCompFun.compFun E.toFun F.toFun,
                                                          HasCompFun.compFun F.invFun E.invFun] γ)

namespace HasCompEquiv'

  variable {U X : Universe} [HasFunctors U U X] [HasCompFun U U U X X] [HasEquivalenceCondition U X] [HasCompEquiv' U X]

  def compEquiv' {α β γ : U} (E : α ⟷' β) (F : β ⟷' γ) : α ⟷' γ := HasEquivalenceCondition.fromDefEquiv (defCompEquiv E F)

end HasCompEquiv'

class HasCompEquiv (U X Y : Universe) [HasFunctors U U X] [HasCompFun U U U X X] [HasEquivalences U X Y] where
(defCompEquiv {α β γ : U} (E : α ⟷ β) (F : β ⟷ γ) : α ⟷[HasCompFun.compFun (HasEquivalences.toFun E) (HasEquivalences.toFun F),
                                                        HasCompFun.compFun (HasEquivalences.invFun F) (HasEquivalences.invFun E)] γ)

namespace HasCompEquiv

  variable {U X Y : Universe} [HasFunctors U U X] [HasCompFun U U U X X] [HasEquivalences U X Y] [HasCompEquiv U X Y]

  def compEquiv {α β γ : U} (E : α ⟷ β) (F : β ⟷ γ) : α ⟷ γ := HasEquivalences.fromDefEquiv (defCompEquiv E F)

  instance hasCompEquiv' : HasCompEquiv' U X :=
  ⟨λ E F => HasEquivalences.toFromExternal E ▸
            HasEquivalences.toFromExternal F ▸
            defCompEquiv (HasEquivalences.fromExternal E) (HasEquivalences.fromExternal F)⟩

end HasCompEquiv



class HasEmbeddedEquivalences (U : Universe.{u}) [HasEmbeddedFunctors.{u, w'} U] [HasEmbeddedProducts U]
  extends HasEquivalences.{u, u, u, w} U U U : Type (max u w w') where
(defElimFun (α β : U) : (α ⟷ β) ⟶[λ E => HasProducts.intro (HasEquivalences.toFun E) (HasEquivalences.invFun E)] (α ⟶ β) ⊓ (β ⟶ α))

namespace HasEmbeddedEquivalences

  variable {U : Universe} [HasEmbeddedFunctors U] [HasEmbeddedProducts U] [HasEmbeddedEquivalences U]

  @[reducible] def elimFun (α β : U) : (α ⟷ β) ⟶ (α ⟶ β) ⊓ (β ⟶ α) := defElimFun α β

end HasEmbeddedEquivalences



class HasEquivOp (U : Universe.{u}) [HasEmbeddedFunctors.{u, w'} U] [HasEmbeddedProducts.{u} U] [HasLinearFunOp U]
  extends HasEmbeddedEquivalences.{u, w} U : Type (max u w w') where
(defIdEquiv         (α : U)                             : α ⟷[HasLinearFunOp.idFun α, HasLinearFunOp.idFun α] α)
(defInvEquiv        {α β : U} (E : α ⟷ β)               : β ⟷[HasEquivalences.invFun E, HasEquivalences.toFun E] α)
(defInvEquivFun     (α β : U)                           : (α ⟷ β) ⟶[λ E => defInvEquiv E] (β ⟷ α))
(defCompEquiv       {α β γ : U} (E : α ⟷ β) (F : β ⟷ γ) : α ⟷[HasEquivalences.toFun F ⊙ HasEquivalences.toFun E, HasEquivalences.invFun E ⊙ HasEquivalences.invFun F] γ)
(defCompEquivFun    {α β : U} (E : α ⟷ β) (γ : U)       : (β ⟷ γ) ⟶[λ F => defCompEquiv E F] (α ⟷ γ))
(defCompEquivFunFun (α β γ : U)                         : (α ⟷ β) ⟶[λ E => defCompEquivFun E γ] ((β ⟷ γ) ⟶ (α ⟷ γ)))

namespace HasEquivOp

  variable {U : Universe.{u}} [HasEmbeddedFunctors U] [HasEmbeddedProducts U] [HasLinearFunOp U] [HasEquivOp U]

  instance hasIdEquiv : HasIdEquiv U U := ⟨defIdEquiv⟩

  @[reducible] def idEquiv (α : U) : α ⟷ α := defIdEquiv α

  instance hasInvEquiv : HasInvEquiv U U U := ⟨defInvEquiv⟩

  @[reducible] def invEquiv {α β : U} (E : α ⟷ β) : β ⟷ α := defInvEquiv E
  @[reducible] def invEquivFun (α β : U) : (α ⟷ β) ⟶ (β ⟷ α) := defInvEquivFun α β

  instance hasCompEquiv : HasCompEquiv U U U := ⟨defCompEquiv⟩

  @[reducible] def compEquiv {α β γ : U} (E : α ⟷ β) (F : β ⟷ γ) : α ⟷ γ := defCompEquiv E F
  @[reducible] def compEquivFun {α β : U} (E : α ⟷ β) (γ : U) : (β ⟷ γ) ⟶ (α ⟷ γ) := defCompEquivFun E γ
  @[reducible] def compEquivFunFun (α β γ : U) : (α ⟷ β) ⟶ (β ⟷ γ) ⟶ (α ⟷ γ) := defCompEquivFunFun α β γ

end HasEquivOp

class HasEquivOpEq (U : Universe.{u}) [HasEmbeddedFunctors.{u, w} U] [HasEmbeddedProducts.{u} U] [HasLinearFunOp U]
                   [HasEquivOp U] [hasIdFun : HasIdFun U] [hasCompFun : HasCompFun U U U U U]
                   [hasLinearFunOpEq : HasLinearFunOpEq U] [hasIdEquiv : HasIdEquiv U U]
                   [hasInvEquiv : HasInvEquiv U U U] [hasCompEquiv : HasCompEquiv U U U] where
(defIdEquivEq (α : U) : HasLinearFunOpEq.idFunEq α ▸ HasEquivOp.defIdEquiv α = HasIdEquiv.defIdEquiv α)
(defInvEquivEq {α β : U} (E : α ⟷ β) : HasEquivOp.defInvEquiv E = HasInvEquiv.defInvEquiv E)
(defCompEquivEq {α β γ : U} (E : α ⟷ β) (F : β ⟷ γ) :
   HasLinearFunOpEq.compFunEq (HasEquivalences.toFun E) (HasEquivalences.toFun F) ▸ 
   HasLinearFunOpEq.compFunEq (HasEquivalences.invFun F) (HasEquivalences.invFun E) ▸
   HasEquivOp.defCompEquiv E F =
   HasCompEquiv.defCompEquiv E F)

namespace HasEquivOpEq

  instance std (U : Universe.{u}) [HasEmbeddedFunctors.{u, w} U] [HasEmbeddedProducts.{u} U] [HasLinearFunOp U]
               [HasEquivOp U] : HasEquivOpEq U :=
  { defIdEquivEq   := λ _   => rfl,
    defInvEquivEq  := λ _   => rfl,
    defCompEquivEq := λ _ _ => rfl }

  variable {U : Universe.{u}} [HasEmbeddedFunctors.{u, w} U] [HasEmbeddedProducts.{u} U] [HasLinearFunOp U]
           [HasEquivOp U] [HasIdFun U] [HasCompFun U U U U U] [HasLinearFunOpEq U]
           [HasIdEquiv U U] [HasInvEquiv U U U] [HasCompEquiv U U U] [HasEquivOpEq U]

  -- TODO
  --def idEquivEq (α : U) : HasEquivOp.idEquiv α = HasIdEquiv.idEquiv α :=
  --Eq.simp_rec_prop (congrArg HasEquivalences.fromDefEquiv (defIdEquivEq α))

  def invEquivEq {α β : U} (E : α ⟷ β) : HasEquivOp.invEquiv E = HasInvEquiv.invEquiv E :=
  congrArg HasEquivalences.fromDefEquiv (defInvEquivEq E)

  -- TODO
  --def compEquivEq {α β γ : U} (E : α ⟷ β) (F : β ⟷ γ) : HasEquivOp.compEquiv E F = HasCompEquiv.compEquiv E F :=
  --Eq.simp_rec_prop (Eq.simp_rec_prop (congrArg HasEquivalences.fromDefEquiv (defCompEquivEq E F)))

end HasEquivOpEq



class HasLinearCommonEquivalences (U : Universe) [HasEmbeddedFunctors U] [HasLinearFunOp U]
                                  [HasEmbeddedTop U] [HasEmbeddedProducts U] [HasEquivOp U] where
(defFunDomainEquiv      {α β : U} (E : α ⟷ β) (γ : U) :
   (β ⟶ γ) ⟷[HasLinearFunOp.compFunFun (HasEquivalences.toFun  E) γ,
             HasLinearFunOp.compFunFun (HasEquivalences.invFun E) γ] (α ⟶ γ))
(defFunDomainEquivFun   (α β γ : U)                   :
   (α ⟷ β) ⟶[λ E => defFunDomainEquiv E γ] ((β ⟶ γ) ⟷ (α ⟶ γ)))
(defFunCodomainEquiv    {α β : U} (E : α ⟷ β) (γ : U) :
   (γ ⟶ α) ⟷[HasLinearFunOp.revCompFunFun γ (HasEquivalences.toFun  E),
             HasLinearFunOp.revCompFunFun γ (HasEquivalences.invFun E)] (γ ⟶ β))
(defFunCodomainEquivFun (α β γ : U)                   :
   (α ⟷ β) ⟶[λ E => defFunCodomainEquiv E γ] ((γ ⟶ α) ⟷ (γ ⟶ β)))
(defSwapFunFunEquiv     (α β γ : U)                   :
   (α ⟶ β ⟶ γ) ⟷[HasLinearFunOp.swapFunFunFun α β γ, HasLinearFunOp.swapFunFunFun β α γ] (β ⟶ α ⟶ γ))
(defTopElimEquiv        (α : U)                       :
   α ⟷[HasEmbeddedTop.elimFunFun α,
       HasEmbeddedTop.invElimFun α] (HasTop.Top U ⟶ α))
(defProdElimFunEquiv    (α β γ : U)                   :
   (α ⟶ β ⟶ γ) ⟷[HasEmbeddedProducts.elimFunFun α β γ,
                 HasEmbeddedProducts.invElimFunFunFun α β γ] (α ⊓ β ⟶ γ))
(defProdFstEquiv        {α β : U} (E : α ⟷ β) (γ : U) :
   α ⊓ γ ⟷[HasEmbeddedProducts.replaceFstFun (HasEquivalences.toFun  E) γ,
           HasEmbeddedProducts.replaceFstFun (HasEquivalences.invFun E) γ] β ⊓ γ)
(defProdFstEquivFun     (α β γ : U)                   :
   (α ⟷ β) ⟶[λ E => defProdFstEquiv E γ] (α ⊓ γ ⟷ β ⊓ γ))
(defProdSndEquiv        {α β : U} (E : α ⟷ β) (γ : U) :
   γ ⊓ α ⟷[HasEmbeddedProducts.replaceSndFun (HasEquivalences.toFun  E) γ,
           HasEmbeddedProducts.replaceSndFun (HasEquivalences.invFun E) γ] γ ⊓ β)
(defProdSndEquivFun     (α β γ : U)                   :
   (α ⟷ β) ⟶[λ E => defProdSndEquiv E γ] (γ ⊓ α ⟷ γ ⊓ β))
(defProdCommEquiv       (α β : U)                     :
   α ⊓ β ⟷[HasEmbeddedProducts.commFun α β, HasEmbeddedProducts.commFun β α] β ⊓ α)
(defProdAssocEquiv      (α β γ : U)                   :
   (α ⊓ β) ⊓ γ ⟷[HasEmbeddedProducts.assocLRFun α β γ, HasEmbeddedProducts.assocRLFun α β γ] α ⊓ (β ⊓ γ))
(defProdTopEquiv        (α : U)                       :
   α ⟷[HasEmbeddedProducts.prodTopIntroFun α,
       HasEmbeddedProducts.prodTopElimFun α] HasTop.Top U ⊓ α)
(defCompEquivEquiv      {α β : U} (E : α ⟷ β) (γ : U) :
   (β ⟷ γ) ⟷[HasEquivOp.compEquivFun E γ, HasEquivOp.compEquivFun (HasEquivOp.invEquiv E) γ] (α ⟷ γ))
(defCompEquivEquivFun   (α β γ : U)                   :
   (α ⟷ β) ⟶[λ E => defCompEquivEquiv E γ] ((β ⟷ γ) ⟷ (α ⟷ γ)))
(defInvEquivEquiv       (α β : U)                     :
   (α ⟷ β) ⟷[HasEquivOp.invEquivFun α β, HasEquivOp.invEquivFun β α] (β ⟷ α))

namespace HasLinearCommonEquivalences

  variable {U : Universe.{u}} [HasEmbeddedFunctors U] [HasLinearFunOp U] [HasEmbeddedTop U]
           [HasEmbeddedProducts U] [HasEquivOp U] [HasLinearCommonEquivalences U]

  @[reducible] def funDomainEquiv {α β : U} (E : α ⟷ β) (γ : U) : (β ⟶ γ) ⟷ (α ⟶ γ) := defFunDomainEquiv E γ
  @[reducible] def funDomainEquivFun (α β γ : U) : (α ⟷ β) ⟶ ((β ⟶ γ) ⟷ (α ⟶ γ)) := defFunDomainEquivFun α β γ
  @[reducible] def funCodomainEquiv {α β : U} (E : α ⟷ β) (γ : U) : (γ ⟶ α) ⟷ (γ ⟶ β) := defFunCodomainEquiv E γ
  @[reducible] def funCodomainEquivFun (α β γ : U) : (α ⟷ β) ⟶ ((γ ⟶ α) ⟷ (γ ⟶ β)) := defFunCodomainEquivFun α β γ
  @[reducible] def swapFunFunEquiv (α β γ : U) : (α ⟶ β ⟶ γ) ⟷ (β ⟶ α ⟶ γ) := defSwapFunFunEquiv α β γ

  @[reducible] def topElimEquiv (α : U) : α ⟷ (HasTop.Top U ⟶ α) := defTopElimEquiv α

  @[reducible] def prodElimFunEquiv (α β γ : U) : (α ⟶ β ⟶ γ) ⟷ (α ⊓ β ⟶ γ) := defProdElimFunEquiv α β γ
  @[reducible] def prodFstEquiv {α β : U} (E : α ⟷ β) (γ : U) : α ⊓ γ ⟷ β ⊓ γ := defProdFstEquiv E γ
  @[reducible] def prodFstEquivFun (α β γ : U) : (α ⟷ β) ⟶ (α ⊓ γ ⟷ β ⊓ γ) := defProdFstEquivFun α β γ
  @[reducible] def prodSndEquiv {α β : U} (E : α ⟷ β) (γ : U) : γ ⊓ α ⟷ γ ⊓ β := defProdSndEquiv E γ
  @[reducible] def prodSndEquivFun (α β γ : U) : (α ⟷ β) ⟶ (γ ⊓ α ⟷ γ ⊓ β) := defProdSndEquivFun α β γ
  @[reducible] def prodCommEquiv (α β : U) : α ⊓ β ⟷ β ⊓ α := defProdCommEquiv α β
  @[reducible] def prodAssocEquiv (α β γ : U) : (α ⊓ β) ⊓ γ ⟷ α ⊓ (β ⊓ γ) := defProdAssocEquiv α β γ
  @[reducible] def prodTopEquiv (α : U) : α ⟷ HasTop.Top U ⊓ α := defProdTopEquiv α

  @[reducible] def compEquivEquiv {α β : U} (E : α ⟷ β) (γ : U) : (β ⟷ γ) ⟷ (α ⟷ γ) := defCompEquivEquiv E γ
  @[reducible] def compEquivEquivFun (α β γ : U) : (α ⟷ β) ⟶ ((β ⟷ γ) ⟷ (α ⟷ γ)) := defCompEquivEquivFun α β γ
  @[reducible] def invEquivEquiv (α β : U) : (α ⟷ β) ⟷ (β ⟷ α) := defInvEquivEquiv α β

end HasLinearCommonEquivalences

class HasNonLinearCommonEquivalences (U : Universe) [HasFunOp U] [HasEmbeddedTop U]
                                     [HasEmbeddedProducts U] [HasEquivOp U] where
(defProdDistrEquiv (α β γ : U) :
   (α ⟶ β ⊓ γ) ⟷[HasEmbeddedProducts.distrFun α β γ,
                 HasEmbeddedProducts.invDistrFunFun α β γ] (α ⟶ β) ⊓ (α ⟶ γ))

namespace HasNonLinearCommonEquivalences

  variable {U : Universe} [HasFunOp U] [HasEmbeddedTop U] [HasEmbeddedProducts U]
           [HasEquivOp U] [HasNonLinearCommonEquivalences U]

  @[reducible] def prodDistrEquiv (α β γ : U) : (α ⟶ β ⊓ γ) ⟷ (α ⟶ β) ⊓ (α ⟶ γ):= defProdDistrEquiv α β γ

end HasNonLinearCommonEquivalences

class HasBotEquivalences (U : Universe) [HasEmbeddedFunctors U] [HasAffineFunOp U]
                         [HasEmbeddedTop U] [HasEmbeddedBot U] [HasEmbeddedProducts U]
                         [HasEquivOp U] where
(defBotNotTopEquiv         :
   HasBot.Bot U ⟷[HasEmbeddedBot.elimFun (HasEmbeddedBot.Not (HasTop.Top U)),
                  HasEmbeddedBot.notTopIntroFun] HasEmbeddedBot.Not (HasTop.Top U))
(defProdBotEquiv   (α : U) :
   HasBot.Bot U ⟷[HasEmbeddedBot.elimFun (HasBot.Bot U ⊓ α),
                  HasEmbeddedProducts.fstFun (HasBot.Bot U) α] HasBot.Bot U ⊓ α)
(defBotContraEquiv (α : U) :
   HasBot.Bot U ⟷[HasEmbeddedBot.elimFun (α ⊓ HasEmbeddedBot.Not α),
                  HasEmbeddedProducts.elimFun (HasEmbeddedBot.contraIntroFun α)] α ⊓ HasEmbeddedBot.Not α)

namespace HasBotEquivalences

  variable {U : Universe} [HasEmbeddedFunctors U] [HasAffineFunOp U] [HasEmbeddedTop U]
           [HasEmbeddedBot U] [HasEmbeddedProducts U] [HasEquivOp U] [HasBotEquivalences U]

  @[reducible] def botNotTopEquiv : HasBot.Bot U ⟷ HasEmbeddedBot.Not (HasTop.Top U) := defBotNotTopEquiv (U := U)
  @[reducible] def prodBotEquiv (α : U) : HasBot.Bot U ⟷ HasBot.Bot U ⊓ α := defProdBotEquiv α
  @[reducible] def botContraEquiv (α : U) : HasBot.Bot U ⟷ α ⊓ HasEmbeddedBot.Not α := defBotContraEquiv α

end HasBotEquivalences

class HasClassicalEquivalences (U : Universe) [HasEmbeddedFunctors U] [HasLinearFunOp U]
                               [HasEmbeddedBot U] [HasClassicalLogic U]
                               [HasEmbeddedProducts U] [HasEquivOp U] where
(defByContradictionEquiv (α : U) :
   α ⟷[HasEmbeddedBot.notNotFun α,
       HasClassicalLogic.byContradictionFun α] HasEmbeddedBot.Not (HasEmbeddedBot.Not α))

namespace HasClassicalEquivalences

  variable {U : Universe} [HasEmbeddedFunctors U] [HasLinearFunOp U] [HasEmbeddedBot U]
           [HasClassicalLogic U] [HasEmbeddedProducts U] [HasEquivOp U] [HasClassicalEquivalences U]

  @[reducible] def byContradictionEquiv (α : U) : α ⟷ HasEmbeddedBot.Not (HasEmbeddedBot.Not α) :=
  defByContradictionEquiv α

end HasClassicalEquivalences
