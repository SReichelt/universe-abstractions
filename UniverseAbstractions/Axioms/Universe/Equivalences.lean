import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Singletons
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Lemmas.DerivedFunctors
import UniverseAbstractions.Lemmas.DerivedSingletonFunctors
import UniverseAbstractions.Lemmas.DerivedProductFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w w'



class HasExternalEquivalence {U : Universe.{u}} {V : Universe.{v}} (α : U) (β : V)
                             [HasExternalFunctor.{u, v, w} α β] [HasExternalFunctor.{v, u, w} β α] where
(IsEquiv : (α ⟶' β) → (β ⟶' α) → Sort w')

namespace HasExternalEquivalence

  def DefEquiv {U : Universe.{u}} {V : Universe.{v}} (α : U) (β : V)
               [HasExternalFunctor.{u, v, w} α β] [HasExternalFunctor.{v, u, w} β α]
               [h : HasExternalEquivalence.{u, v, w, w'} α β] (toFun : α ⟶' β) (invFun : β ⟶' α) :=
  h.IsEquiv toFun invFun

  notation:20 α:21 " ⟷'[" toFun:0 "," invFun:0 "] " β:21 => HasExternalEquivalence.DefEquiv α β toFun invFun

  structure Equiv {U : Universe.{u}} {V : Universe.{v}} (α : U) (β : V)
                  [HasExternalFunctor.{u, v, w} α β] [HasExternalFunctor.{v, u, w} β α]
                  [HasExternalEquivalence.{u, v, w, w'} α β] : Sort (max 1 u v w w') where
  (toFun  : α ⟶' β)
  (invFun : β ⟶' α)
  (E      : α ⟷'[toFun,invFun] β)

  infix:20 " ⟷' " => HasExternalEquivalence.Equiv

  variable {U : Universe.{u}} {V : Universe.{v}} {α : U} {β : V}
           [HasExternalFunctor.{u, v, w} α β] [HasExternalFunctor.{v, u, w} β α]
           [HasExternalEquivalence.{u, v, w, w'} α β]

  def toDefEquiv                                      (E : α ⟷' β)               : α ⟷'[E.toFun,E.invFun] β := E.E
  def fromDefEquiv {toFun : α ⟶' β} {invFun : β ⟶' α} (E : α ⟷'[toFun,invFun] β) : α ⟷'                   β := ⟨toFun, invFun, E⟩

  instance (E : α ⟷' β)                       : CoeDep (α ⟷' β)               E (α ⟷'[E.toFun,E.invFun] β) := ⟨toDefEquiv E⟩
  instance {toFun : α ⟶' β} {invFun : β ⟶' α} : Coe    (α ⟷'[toFun,invFun] β)   (α ⟷' β)                   := ⟨fromDefEquiv⟩

  @[simp] theorem fromToDefEquiv                                    (E : α ⟷' β)               : fromDefEquiv (toDefEquiv E) = E :=
  match E with | ⟨_, _, _⟩ => rfl
  @[simp] theorem toFromDefEquiv {toFun : α ⟶' β} {invFun : β ⟶' α} (E : α ⟷'[toFun,invFun] β) : toDefEquiv (fromDefEquiv E) = E := rfl

end HasExternalEquivalence



class HasIdEquiv {U : Universe} (α : U) [HasExternalFunctor α α] [HasIdFun α] [HasExternalEquivalence α α] where
(defIdEquiv: α ⟷'[HasIdFun.idFun α, HasIdFun.idFun α] α)

namespace HasIdEquiv

  variable {U : Universe} (α : U) [HasExternalFunctor α α] [HasIdFun α] [HasExternalEquivalence α α] [HasIdEquiv α]

  def idEquiv : α ⟷' α := HasExternalEquivalence.fromDefEquiv defIdEquiv

end HasIdEquiv

class HasInvEquiv {U V : Universe} (α : U) (β : V) [HasExternalFunctor α β] [HasExternalFunctor β α]
                  [HasExternalEquivalence α β] [HasExternalEquivalence β α] where
(defInvEquiv (E : α ⟷' β) : β ⟷'[E.invFun, E.toFun] α)

class HasCompEquiv {U V W : Universe} (α : U) (β : V) (γ : W) 
                   [HasExternalFunctor α β] [HasExternalFunctor β γ] [HasExternalFunctor α γ]
                   [HasExternalFunctor β α] [HasExternalFunctor γ β] [HasExternalFunctor γ α]
                   [HasCompFun α β γ] [HasCompFun γ β α]
                   [HasExternalEquivalence α β] [HasExternalEquivalence β γ] [HasExternalEquivalence α γ] where
(defCompEquiv (E : α ⟷' β) (F : β ⟷' γ) : α ⟷'[F.toFun ⊙' E.toFun, E.invFun ⊙' F.invFun] γ)

namespace HasCompEquiv

  variable {U V W : Universe} {α : U} {β : V} {γ : W}
           [HasExternalFunctor α β] [HasExternalFunctor β γ] [HasExternalFunctor α γ]
           [HasExternalFunctor β α] [HasExternalFunctor γ β] [HasExternalFunctor γ α]
           [HasCompFun α β γ] [HasCompFun γ β α]
           [HasExternalEquivalence α β] [HasExternalEquivalence β γ] [HasExternalEquivalence α γ]
           [HasCompEquiv α β γ]

  def compEquiv (E : α ⟷' β) (F : β ⟷' γ) : α ⟷' γ := HasExternalEquivalence.fromDefEquiv (defCompEquiv E F)

end HasCompEquiv

namespace HasInvEquiv

  variable {U V : Universe} {α : U} {β : V} [HasExternalFunctor α β] [HasExternalFunctor β α]
           [HasExternalEquivalence α β] [HasExternalEquivalence β α] [HasInvEquiv α β]

  def invEquiv (E : α ⟷' β) : β ⟷' α := HasExternalEquivalence.fromDefEquiv (defInvEquiv E)

end HasInvEquiv



class HasEmbeddedEquivalence {U : Universe.{u}} [HasEmbeddedFunctors.{u, w} U] (α β : U) where
[hEquiv : HasExternalEquivalence.{u, u, w, w'} α β]
[hType  : HasEmbeddedType.{u, max 1 u w w'} U (α ⟷' β)]

class HasEmbeddedEquivalences (U : Universe.{u}) [HasEmbeddedFunctors.{u, w} U] where
[hasEquiv (α β : U) : HasEmbeddedEquivalence.{u, w, w'} α β]

namespace HasEmbeddedEquivalences

  variable {U : Universe} [HasEmbeddedFunctors U] [h : HasEmbeddedEquivalences U]

  instance hasExternalEquivalence (α β : U) : HasExternalEquivalence α β := (h.hasEquiv α β).hEquiv
  instance hasEmbeddedType        (α β : U) : HasEmbeddedType U (α ⟷' β) := (h.hasEquiv α β).hType

  def DefEquiv (α β : U) (toFun : α ⟶ β) (invFun : β ⟶ α) :=
  HasExternalEquivalence.DefEquiv α β (HasEmbeddedFunctors.toExternal toFun) (HasEmbeddedFunctors.toExternal invFun)

  notation:20 α:21 " ⟷[" toFun:0 "," invFun:0 "] " β:21 => HasEmbeddedEquivalences.DefEquiv α β toFun invFun

  def Equiv (α β : U) : U := HasEmbeddedType.EmbeddedType U (α ⟷' β)
  infix:20 " ⟷ " => HasEmbeddedEquivalences.Equiv

  variable {α β : U}

  def toExternal   (E : α ⟷  β) : α ⟷' β := HasEmbeddedType.toExternal   U E
  def fromExternal (E : α ⟷' β) : α ⟷  β := HasEmbeddedType.fromExternal U E

  @[simp] theorem fromToExternal (E : α ⟷  β) : fromExternal (toExternal E) = E := HasEmbeddedType.fromToExternal U E
  @[simp] theorem toFromExternal (E : α ⟷' β) : toExternal (fromExternal E) = E := HasEmbeddedType.toFromExternal U E

  def to  (E : α ⟷ β) (a : α) : β := (toExternal E).toFun  a
  def inv (E : α ⟷ β) (b : β) : α := (toExternal E).invFun b

  def toFun  (E : α ⟷ β) : α ⟶ β := HasEmbeddedFunctors.fromExternal (toExternal E).toFun
  def invFun (E : α ⟷ β) : β ⟶ α := HasEmbeddedFunctors.fromExternal (toExternal E).invFun

  @[simp] theorem toFun.eff  (E : α ⟷ β) (a : α) : (toFun  E) a = to  E a :=
  by apply HasEmbeddedFunctors.fromExternal.eff
  @[simp] theorem invFun.eff (E : α ⟷ β) (b : β) : (invFun E) b = inv E b :=
  by apply HasEmbeddedFunctors.fromExternal.eff

  @[simp] theorem toFun.extern  (E : α ⟷ β) : HasEmbeddedFunctors.toExternal (toFun E)  = (toExternal E).toFun :=
  HasEmbeddedFunctors.toFromExternal (toExternal E).toFun
  @[simp] theorem invFun.extern (E : α ⟷ β) : HasEmbeddedFunctors.toExternal (invFun E) = (toExternal E).invFun :=
  HasEmbeddedFunctors.toFromExternal (toExternal E).invFun

  @[simp] theorem toFromExternal.to  (E : α ⟷' β) : (toExternal (fromExternal E)).toFun  = E.toFun  :=
  congrArg HasExternalEquivalence.Equiv.toFun  (toFromExternal E)
  @[simp] theorem toFromExternal.inv (E : α ⟷' β) : (toExternal (fromExternal E)).invFun = E.invFun :=
  congrArg HasExternalEquivalence.Equiv.invFun (toFromExternal E)

  @[simp] theorem fromExternal.to.eff  (E : α ⟷' β) (a : α) : to  (fromExternal E) a = E.toFun  a :=
  congrFun (congrArg HasExternalFunctor.Fun.f (toFromExternal.to  E)) a
  @[simp] theorem fromExternal.inv.eff (E : α ⟷' β) (b : β) : inv (fromExternal E) b = E.invFun b :=
  congrFun (congrArg HasExternalFunctor.Fun.f (toFromExternal.inv E)) b

  def fromDefEquiv {to : α ⟶ β} {inv : β ⟶ α} (E : α ⟷[to,inv] β) : α ⟷ β :=
  fromExternal (HasExternalEquivalence.fromDefEquiv E)

  instance {to : α ⟶ β} {inv : β ⟶ α} : Coe (α ⟷[to,inv] β) ⌈α ⟷ β⌉ := ⟨fromDefEquiv⟩

  @[simp] theorem fromDefEquiv.to.eff  {to : α ⟶ β} {inv : β ⟶ α} (E : α ⟷[to,inv] β) :
    toFun  (fromDefEquiv E) = to  :=
  by simp [fromDefEquiv, toFun,  HasExternalEquivalence.fromDefEquiv]
  @[simp] theorem fromDefEquiv.inv.eff {to : α ⟶ β} {inv : β ⟶ α} (E : α ⟷[to,inv] β) :
    invFun (fromDefEquiv E) = inv :=
  by simp [fromDefEquiv, invFun, HasExternalEquivalence.fromDefEquiv]

end HasEmbeddedEquivalences



class HasFunctorialEquivalences (U : Universe.{u}) [HasEmbeddedFunctors.{u, w} U] [HasEmbeddedProducts.{u} U]
  extends HasEmbeddedEquivalences.{u, w, w'} U where
(defElimFun (α β : U) : (α ⟷ β) ⟶[λ E => HasEmbeddedProducts.intro (HasEmbeddedEquivalences.toFun E) (HasEmbeddedEquivalences.invFun E)] (α ⟶ β) ⊓ (β ⟶ α))

namespace HasFunctorialEquivalences

  variable {U : Universe} [HasEmbeddedFunctors U] [HasEmbeddedProducts U] [HasFunctorialEquivalences U]

  @[reducible] def elimFun (α β : U) : (α ⟷ β) ⟶ (α ⟶ β) ⊓ (β ⟶ α) := defElimFun α β

end HasFunctorialEquivalences



class HasEquivOp (U : Universe.{u}) [HasEmbeddedFunctors.{u, w} U] [HasEmbeddedProducts.{u} U] [HasLinearFunOp U]
  extends HasFunctorialEquivalences.{u, w, w'} U where
(defIdEquiv         (α : U)                             : α ⟷[HasLinearFunOp.idFun α, HasLinearFunOp.idFun α] α)
(defCompEquiv       {α β γ : U} (E : α ⟷ β) (F : β ⟷ γ) : α ⟷[HasEmbeddedEquivalences.toFun F ⊙ HasEmbeddedEquivalences.toFun E, HasEmbeddedEquivalences.invFun E ⊙ HasEmbeddedEquivalences.invFun F] γ)
(defCompEquivFun    {α β : U} (E : α ⟷ β) (γ : U)       : (β ⟷ γ) ⟶[λ F => defCompEquiv E F] (α ⟷ γ))
(defCompEquivFunFun (α β γ : U)                         : (α ⟷ β) ⟶[λ E => defCompEquivFun E γ] ((β ⟷ γ) ⟶ (α ⟷ γ)))
(defInvEquiv        {α β : U} (E : α ⟷ β)               : β ⟷[HasEmbeddedEquivalences.invFun E, HasEmbeddedEquivalences.toFun E] α)
(defInvEquivFun     (α β : U)                           : (α ⟷ β) ⟶[λ E => defInvEquiv E] (β ⟷ α))

namespace HasEquivOp

  variable {U : Universe.{u}} [HasEmbeddedFunctors U] [HasEmbeddedProducts U] [HasLinearFunOp U] [HasEquivOp U]

  instance (α : U) : HasIdEquiv α := ⟨HasEmbeddedFunctors.toFromExternal (HasIdFun.idFun α) ▸ defIdEquiv α⟩

  @[reducible] def idEquiv (α : U) : α ⟷ α := defIdEquiv α

  -- TODO
  --instance (α β γ : U) : HasCompEquiv α β γ :=
  --⟨λ E F => HasEmbeddedFunctors.toFromExternal (F.toFun  ⊙' E.toFun)  ▸
  --          HasEmbeddedFunctors.toFromExternal (E.invFun ⊙' F.invFun) ▸
  --          HasEmbeddedEquivalences.toFromExternal E ▸
  --          HasEmbeddedEquivalences.toFromExternal F ▸
  --          defCompEquiv (HasEmbeddedEquivalences.fromExternal E) (HasEmbeddedEquivalences.fromExternal F)⟩

  @[reducible] def compEquiv {α β γ : U} (E : α ⟷ β) (F : β ⟷ γ) : α ⟷ γ := defCompEquiv E F
  @[reducible] def compEquivFun {α β : U} (E : α ⟷ β) (γ : U) : (β ⟷ γ) ⟶ (α ⟷ γ) := defCompEquivFun E γ
  @[reducible] def compEquivFunFun (α β γ : U) : (α ⟷ β) ⟶ (β ⟷ γ) ⟶ (α ⟷ γ) := defCompEquivFunFun α β γ

  instance (α β : U) : HasInvEquiv α β :=
  ⟨λ E => HasEmbeddedFunctors.toFromExternal E.invFun ▸
          HasEmbeddedFunctors.toFromExternal E.toFun  ▸
          HasEmbeddedEquivalences.toFromExternal E ▸
          defInvEquiv (HasEmbeddedEquivalences.fromExternal E)⟩

  @[reducible] def invEquiv {α β : U} (E : α ⟷ β) : β ⟷ α := defInvEquiv E
  @[reducible] def invEquivFun (α β : U) : (α ⟷ β) ⟶ (β ⟷ α) := defInvEquivFun α β

end HasEquivOp



class HasLinearCommonEquivalences (U : Universe.{u}) [HasEmbeddedFunctors.{u, w} U] [HasLinearFunOp.{u, w} U]
                                  [HasFunctorialTop.{u, w} U] [HasFunctorialProducts.{u, w} U] [HasEquivOp.{u, w, w'} U] where
(defFunDomainEquiv      {α β : U} (E : α ⟷ β) (γ : U) :
   (β ⟶ γ) ⟷[HasLinearFunOp.compFunFun (HasEmbeddedEquivalences.toFun  E) γ,
             HasLinearFunOp.compFunFun (HasEmbeddedEquivalences.invFun E) γ] (α ⟶ γ))
(defFunDomainEquivFun   (α β γ : U)                   :
   (α ⟷ β) ⟶[λ E => defFunDomainEquiv E γ] ((β ⟶ γ) ⟷ (α ⟶ γ)))
(defFunCodomainEquiv    {α β : U} (E : α ⟷ β) (γ : U) :
   (γ ⟶ α) ⟷[HasLinearFunOp.revCompFunFun γ (HasEmbeddedEquivalences.toFun  E),
             HasLinearFunOp.revCompFunFun γ (HasEmbeddedEquivalences.invFun E)] (γ ⟶ β))
(defFunCodomainEquivFun (α β γ : U)                   :
   (α ⟷ β) ⟶[λ E => defFunCodomainEquiv E γ] ((γ ⟶ α) ⟷ (γ ⟶ β)))
(defSwapFunFunEquiv     (α β γ : U)                   :
   (α ⟶ β ⟶ γ) ⟷[HasLinearFunOp.swapFunFunFun α β γ, HasLinearFunOp.swapFunFunFun β α γ] (β ⟶ α ⟶ γ))
(defTopElimEquiv        (α : U)                       :
   α ⟷[HasFunctorialTop.elimFunFun α,
       HasFunctorialTop.invElimFun α] (HasEmbeddedTop.Top U ⟶ α))
(defProdElimFunEquiv    (α β γ : U)                   :
   (α ⟶ β ⟶ γ) ⟷[HasFunctorialProducts.elimFunFun α β γ,
                 HasFunctorialProducts.invElimFunFunFun α β γ] (α ⊓ β ⟶ γ))
(defProdFstEquiv        {α β : U} (E : α ⟷ β) (γ : U) :
   α ⊓ γ ⟷[HasFunctorialProducts.replaceFstFun (HasEmbeddedEquivalences.toFun  E) γ,
           HasFunctorialProducts.replaceFstFun (HasEmbeddedEquivalences.invFun E) γ] β ⊓ γ)
(defProdFstEquivFun     (α β γ : U)                   :
   (α ⟷ β) ⟶[λ E => defProdFstEquiv E γ] (α ⊓ γ ⟷ β ⊓ γ))
(defProdSndEquiv        {α β : U} (E : α ⟷ β) (γ : U) :
   γ ⊓ α ⟷[HasFunctorialProducts.replaceSndFun (HasEmbeddedEquivalences.toFun  E) γ,
           HasFunctorialProducts.replaceSndFun (HasEmbeddedEquivalences.invFun E) γ] γ ⊓ β)
(defProdSndEquivFun     (α β γ : U)                   :
   (α ⟷ β) ⟶[λ E => defProdSndEquiv E γ] (γ ⊓ α ⟷ γ ⊓ β))
(defProdCommEquiv       (α β : U)                     :
   α ⊓ β ⟷[HasFunctorialProducts.commFun α β, HasFunctorialProducts.commFun β α] β ⊓ α)
(defProdAssocEquiv      (α β γ : U)                   :
   (α ⊓ β) ⊓ γ ⟷[HasFunctorialProducts.assocLRFun α β γ, HasFunctorialProducts.assocRLFun α β γ] α ⊓ (β ⊓ γ))
(defProdTopEquiv        (α : U)                       :
   α ⟷[HasFunctorialProducts.prodTopIntroFun α,
       HasFunctorialProducts.prodTopElimFun α] HasEmbeddedTop.Top U ⊓ α)
(defCompEquivEquiv      {α β : U} (E : α ⟷ β) (γ : U) :
   (β ⟷ γ) ⟷[HasEquivOp.compEquivFun E γ, HasEquivOp.compEquivFun (HasEquivOp.invEquiv E) γ] (α ⟷ γ))
(defCompEquivEquivFun   (α β γ : U)                   :
   (α ⟷ β) ⟶[λ E => defCompEquivEquiv E γ] ((β ⟷ γ) ⟷ (α ⟷ γ)))
(defInvEquivEquiv       (α β : U)                     :
   (α ⟷ β) ⟷[HasEquivOp.invEquivFun α β, HasEquivOp.invEquivFun β α] (β ⟷ α))

namespace HasLinearCommonEquivalences

  variable {U : Universe.{u}} [HasEmbeddedFunctors U] [HasLinearFunOp U] [HasFunctorialTop U]
           [HasFunctorialProducts U] [HasEquivOp U] [HasLinearCommonEquivalences U]

  @[reducible] def funDomainEquiv {α β : U} (E : α ⟷ β) (γ : U) : (β ⟶ γ) ⟷ (α ⟶ γ) := defFunDomainEquiv E γ
  @[reducible] def funDomainEquivFun (α β γ : U) : (α ⟷ β) ⟶ ((β ⟶ γ) ⟷ (α ⟶ γ)) := defFunDomainEquivFun α β γ
  @[reducible] def funCodomainEquiv {α β : U} (E : α ⟷ β) (γ : U) : (γ ⟶ α) ⟷ (γ ⟶ β) := defFunCodomainEquiv E γ
  @[reducible] def funCodomainEquivFun (α β γ : U) : (α ⟷ β) ⟶ ((γ ⟶ α) ⟷ (γ ⟶ β)) := defFunCodomainEquivFun α β γ
  @[reducible] def swapFunFunEquiv (α β γ : U) : (α ⟶ β ⟶ γ) ⟷ (β ⟶ α ⟶ γ) := defSwapFunFunEquiv α β γ

  @[reducible] def topElimEquiv (α : U) : α ⟷ (HasEmbeddedTop.Top U ⟶ α) := defTopElimEquiv α

  @[reducible] def prodElimFunEquiv (α β γ : U) : (α ⟶ β ⟶ γ) ⟷ (α ⊓ β ⟶ γ) := defProdElimFunEquiv α β γ
  @[reducible] def prodFstEquiv {α β : U} (E : α ⟷ β) (γ : U) : α ⊓ γ ⟷ β ⊓ γ := defProdFstEquiv E γ
  @[reducible] def prodFstEquivFun (α β γ : U) : (α ⟷ β) ⟶ (α ⊓ γ ⟷ β ⊓ γ) := defProdFstEquivFun α β γ
  @[reducible] def prodSndEquiv {α β : U} (E : α ⟷ β) (γ : U) : γ ⊓ α ⟷ γ ⊓ β := defProdSndEquiv E γ
  @[reducible] def prodSndEquivFun (α β γ : U) : (α ⟷ β) ⟶ (γ ⊓ α ⟷ γ ⊓ β) := defProdSndEquivFun α β γ
  @[reducible] def prodCommEquiv (α β : U) : α ⊓ β ⟷ β ⊓ α := defProdCommEquiv α β
  @[reducible] def prodAssocEquiv (α β γ : U) : (α ⊓ β) ⊓ γ ⟷ α ⊓ (β ⊓ γ) := defProdAssocEquiv α β γ
  @[reducible] def prodTopEquiv (α : U) : α ⟷ HasEmbeddedTop.Top U ⊓ α := defProdTopEquiv α

  @[reducible] def compEquivEquiv {α β : U} (E : α ⟷ β) (γ : U) : (β ⟷ γ) ⟷ (α ⟷ γ) := defCompEquivEquiv E γ
  @[reducible] def compEquivEquivFun (α β γ : U) : (α ⟷ β) ⟶ ((β ⟷ γ) ⟷ (α ⟷ γ)) := defCompEquivEquivFun α β γ
  @[reducible] def invEquivEquiv (α β : U) : (α ⟷ β) ⟷ (β ⟷ α) := defInvEquivEquiv α β

end HasLinearCommonEquivalences

class HasNonLinearCommonEquivalences (U : Universe.{u}) [HasFunOp.{u, w} U] [HasFunctorialTop.{u, w} U]
                                     [HasFunctorialProducts.{u} U] [HasEquivOp.{u, w, w'} U] where
(defProdDistrEquiv (α β γ : U) :
   (α ⟶ β ⊓ γ) ⟷[HasFunctorialProducts.distrFun α β γ,
                 HasFunctorialProducts.invDistrFunFun α β γ] (α ⟶ β) ⊓ (α ⟶ γ))

namespace HasNonLinearCommonEquivalences

  variable {U : Universe.{u}} [HasFunOp U] [HasFunctorialTop U] [HasFunctorialProducts U]
           [HasEquivOp U] [HasNonLinearCommonEquivalences U]

  @[reducible] def prodDistrEquiv (α β γ : U) : (α ⟶ β ⊓ γ) ⟷ (α ⟶ β) ⊓ (α ⟶ γ):= defProdDistrEquiv α β γ

end HasNonLinearCommonEquivalences

class HasBotEquivalences (U : Universe.{u}) [HasEmbeddedFunctors.{u, w} U] [HasAffineFunOp.{u, w} U]
                         [HasFunctorialTop.{u, w} U] [HasFunctorialBot.{u, w} U]
                         [HasFunctorialProducts.{u} U] [HasEquivOp.{u, w, w'} U] where
(defBotNotTopEquiv         :
   HasEmbeddedBot.Bot U ⟷[HasFunctorialBot.elimFun (HasFunctorialBot.Not (HasEmbeddedTop.Top U)),
                          HasFunctorialBot.notTopIntroFun] HasFunctorialBot.Not (HasEmbeddedTop.Top U))
(defProdBotEquiv   (α : U) :
   HasEmbeddedBot.Bot U ⟷[HasFunctorialBot.elimFun (HasEmbeddedBot.Bot U ⊓ α),
                          HasFunctorialProducts.fstFun (HasEmbeddedBot.Bot U) α] HasEmbeddedBot.Bot U ⊓ α)
(defBotContraEquiv (α : U) :
   HasEmbeddedBot.Bot U ⟷[HasFunctorialBot.elimFun (α ⊓ HasFunctorialBot.Not α),
                          HasFunctorialProducts.elimFun (HasFunctorialBot.contraIntroFun α)] α ⊓ HasFunctorialBot.Not α)

namespace HasBotEquivalences

  variable {U : Universe.{u}} [HasEmbeddedFunctors U] [HasAffineFunOp U] [HasFunctorialTop U]
           [HasFunctorialBot U] [HasFunctorialProducts U] [HasEquivOp U] [HasBotEquivalences U]

  @[reducible] def botNotTopEquiv : HasEmbeddedBot.Bot U ⟷ HasFunctorialBot.Not (HasEmbeddedTop.Top U) := defBotNotTopEquiv (U := U)
  @[reducible] def prodBotEquiv (α : U) : HasEmbeddedBot.Bot U ⟷ HasEmbeddedBot.Bot U ⊓ α := defProdBotEquiv α
  @[reducible] def botContraEquiv (α : U) : HasEmbeddedBot.Bot U ⟷ α ⊓ HasFunctorialBot.Not α := defBotContraEquiv α

end HasBotEquivalences

class HasClassicalEquivalences (U : Universe.{u}) [HasEmbeddedFunctors.{u, w} U] [HasLinearFunOp.{u, w} U]
                               [HasFunctorialBot.{u, w} U] [HasClassicalLogic.{u, w} U]
                               [HasFunctorialProducts.{u} U] [HasEquivOp.{u, w, w'} U] where
(defByContradictionEquiv (α : U) :
   α ⟷[HasFunctorialBot.notNotFun α,
       HasClassicalLogic.byContradictionFun α] HasFunctorialBot.Not (HasFunctorialBot.Not α))

namespace HasClassicalEquivalences

  variable {U : Universe.{u}} [HasEmbeddedFunctors U] [HasLinearFunOp U] [HasFunctorialBot U]
           [HasClassicalLogic U] [HasFunctorialProducts U] [HasEquivOp U] [HasClassicalEquivalences U]

  @[reducible] def byContradictionEquiv (α : U) : α ⟷ HasFunctorialBot.Not (HasFunctorialBot.Not α) := defByContradictionEquiv α

end HasClassicalEquivalences
