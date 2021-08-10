import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors



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

class HasInvEquiv {U V : Universe} (α : U) (β : V) [HasExternalFunctor α β] [HasExternalFunctor β α]
                  [HasExternalEquivalence α β] [HasExternalEquivalence β α] where
(defInvEquiv (E : α ⟷' β) : β ⟷'[E.invFun, E.toFun] α)

namespace HasInvEquiv

  variable {U V : Universe} {α : U} {β : V} [HasExternalFunctor α β] [HasExternalFunctor β α]
           [HasExternalEquivalence α β] [HasExternalEquivalence β α] [HasInvEquiv α β]

  def invEquiv (E : α ⟷' β) : β ⟷' α := HasExternalEquivalence.fromDefEquiv (defInvEquiv E)

end HasInvEquiv



class HasEmbeddedEquivalence {U : Universe.{u}} [HasEmbeddedFunctors.{u, w} U] (α β : U) where
[hEquiv : HasExternalEquivalence.{u, u, w, w'} α β]
[hType  : HasEmbeddedType.{u, max 1 u w w'} U (α ⟷' β)]

class HasEmbeddedEquivalences (U : Universe.{u}) [HasEmbeddedFunctors.{u, w} U] where
[hasEquiv (α β : U) : HasEmbeddedEquivalence α β]

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



class HasFunctorialEquivalences (U : Universe.{u}) [HasEmbeddedFunctors.{u, w} U] extends HasEmbeddedEquivalences.{u, w, w'} U where
(defToFunFun  (α β : U) : (α ⟷ β) ⟶[λ E => HasEmbeddedEquivalences.toFun  E] (α ⟶ β))
(defInvFunFun (α β : U) : (α ⟷ β) ⟶[λ E => HasEmbeddedEquivalences.invFun E] (β ⟶ α))

namespace HasFunctorialEquivalences

  variable {U : Universe} [HasEmbeddedFunctors U] [HasFunctorialEquivalences U]

  @[reducible] def toFunFun  (α β : U) : (α ⟷ β) ⟶ (α ⟶ β) := defToFunFun  α β
  @[reducible] def invFunFun (α β : U) : (α ⟷ β) ⟶ (β ⟶ α) := defInvFunFun α β

end HasFunctorialEquivalences



class HasEquivOp (U : Universe.{u}) [HasEmbeddedFunctors.{u, w} U] [HasLinearFunOp U] extends HasFunctorialEquivalences.{u, w, w'} U where
(defIdEquiv         (α : U)                             : α ⟷[HasLinearFunOp.idFun α, HasLinearFunOp.idFun α] α)
(defCompEquiv       {α β γ : U} (E : α ⟷ β) (F : β ⟷ γ) : α ⟷[HasEmbeddedEquivalences.toFun F ⊙ HasEmbeddedEquivalences.toFun E, HasEmbeddedEquivalences.invFun E ⊙ HasEmbeddedEquivalences.invFun F] γ)
(defCompEquivFun    {α β : U} (E : α ⟷ β) (γ : U)       : (β ⟷ γ) ⟶[λ F => defCompEquiv E F] (α ⟷ γ))
(defCompEquivFunFun (α β γ : U)                         : (α ⟷ β) ⟶[λ E => defCompEquivFun E γ] ((β ⟷ γ) ⟶ (α ⟷ γ)))
(defInvEquiv        {α β : U} (E : α ⟷ β)               : β ⟷[HasEmbeddedEquivalences.invFun E, HasEmbeddedEquivalences.toFun E] α)
(defInvEquivFun     (α β : U)                           : (α ⟷ β) ⟶[λ E => defInvEquiv E] (β ⟷ α))
(defInvEquivEquiv   (α β : U)                           : (α ⟷ β) ⟷[defInvEquivFun α β, defInvEquivFun β α] (β ⟷ α))

namespace HasEquivOp

  variable {U : Universe.{u}} [HasEmbeddedFunctors U] [HasLinearFunOp U] [HasEquivOp U]

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
  @[reducible] def invEquivEquiv (α β : U) : (α ⟷ β) ⟷ (β ⟷ α) := defInvEquivEquiv α β

end HasEquivOp
