import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences
import UniverseAbstractions.Axioms.Universe.Properties

import UniverseAbstractions.Lemmas.LeanEq



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w w' w''



class HasDependentFunctoriality (U : Universe.{u}) (V : Universe.{v}) extends
  HasProperties.{u, v, w} U V : Type (max u v w w') where
(IsFun {α : U} {φ : HasProperties.Property α V} : HasProperties.Pi φ → Sort w')

namespace HasDependentFunctoriality

  variable {U : Universe.{u}} {V : Universe.{v}} [h : HasDependentFunctoriality.{u, v, w, w'} U V]

  def DefPi {α : U} (φ : HasProperties.Property α V) (f : HasProperties.Pi φ) := h.IsFun f
  notation:20 "Π[" f:0 "] " φ:21 => HasDependentFunctoriality.DefPi φ f

  structure Pi {α : U} (φ : HasProperties.Property α V) : Sort (max 1 u v w') where
  (f : HasProperties.Pi φ)
  (F : Π[f] φ)
  notation:20 "Π' " φ:21 => HasDependentFunctoriality.Pi φ

  variable {α : U} {φ : HasProperties.Property α V}

  instance coeDefPi (f : HasProperties.Pi φ) : CoeFun (Π[f] φ) (λ _ => HasProperties.Pi φ) := ⟨λ _ => f⟩
  instance coePi                             : CoeFun (Π'   φ) (λ _ => HasProperties.Pi φ) := ⟨Pi.f⟩

  def toDefPi                            (F : Π'   φ) : Π[F.f] φ := F.F
  def fromDefPi {f : HasProperties.Pi φ} (F : Π[f] φ) : Π'     φ := ⟨f, F⟩

  instance (F : Π' φ)               : CoeDep (Π'   φ) F (Π[F.f] φ) := ⟨toDefPi F⟩
  instance {f : HasProperties.Pi φ} : Coe    (Π[f] φ)   (Π'     φ) := ⟨fromDefPi⟩

  def castDefPi {f f' : HasProperties.Pi φ} (F : Π[f] φ) (h : ∀ a, f a = f' a) : Π[f'] φ :=
  have h₁ : f = f' := funext h;
  h₁ ▸ F

  @[simp] theorem fromCastDefPi {f f' : HasProperties.Pi φ} (F : Π[f] φ) (h : ∀ a, f a = f' a) :
    fromDefPi (castDefPi F h) = fromDefPi F :=
  Eq.simp_rec

  @[simp] theorem castCastDefPi {f f' : HasProperties.Pi φ} (F : Π[f] φ) (h : ∀ a, f a = f' a) :
    castDefPi (castDefPi F h) (λ a => Eq.symm (h a)) = F :=
  Eq.simp_rec_rec (ha := funext h)

  @[simp] theorem toDefPi.eff                            (F : Π'   φ) (a : α) : (toDefPi   F) a = F a := rfl
  @[simp] theorem fromDefPi.eff {f : HasProperties.Pi φ} (F : Π[f] φ) (a : α) : (fromDefPi F) a = F a := rfl

  @[simp] theorem fromToDefPi                          (F : Π'   φ) : fromDefPi (toDefPi F) = F :=
  match F with | ⟨_, _⟩ => rfl
  @[simp] theorem toFromDefPi {f : HasProperties.Pi φ} (F : Π[f] φ) : toDefPi (fromDefPi F) = F := rfl

end HasDependentFunctoriality



class HasDependentFunctors (U : Universe.{u}) (V : Universe.{v}) (X : outParam Universe.{w}) extends
  HasDependentFunctoriality.{u, v, w', w''} U V : Type (max u v w w' w'') where
[embed {α : U} (φ : HasProperties.Property α V) : HasEmbeddedType.{w, max 1 u v w''} X (Π' φ)]

namespace HasDependentFunctors

  variable {U V X : Universe} [h : HasDependentFunctors U V X]

  instance hasEmbeddedType {α : U} (φ : HasProperties.Property α V) : HasEmbeddedType X (Π' φ) :=
  h.embed φ

  def Pi {α : U} (φ : HasProperties.Property α V) : X := HasEmbeddedType.EmbeddedType X (Π' φ)
  notation:20 "Π " φ:21 => HasDependentFunctors.Pi φ

  variable {α : U} {φ : HasProperties.Property α V}

  def toExternal   (F : Π  φ) : Π' φ := HasEmbeddedType.toExternal   X F
  def fromExternal (F : Π' φ) : Π  φ := HasEmbeddedType.fromExternal X F

  def piCoe (F : Π φ) : HasProperties.Pi φ := (toExternal F).f
  instance coePi : CoeFun ⌈Π φ⌉ (λ _ => HasProperties.Pi φ) := ⟨piCoe⟩

  @[simp] theorem fromToExternal (F : Π  φ) : fromExternal (toExternal F) = F := HasEmbeddedType.fromToExternal X F
  @[simp] theorem toFromExternal (F : Π' φ) : toExternal (fromExternal F) = F := HasEmbeddedType.toFromExternal X F

  @[simp] theorem toExternal.eff   (F : Π  φ) (a : α) : (toExternal   F) a = F a := rfl
  @[simp] theorem fromExternal.eff (F : Π' φ) (a : α) : (fromExternal F) a = F a :=
  congrFun (congrArg HasDependentFunctoriality.Pi.f (toFromExternal F)) a

  def toDefPi                            (F : Π    φ) : Π[piCoe F] φ := HasDependentFunctoriality.toDefPi (toExternal F)
  def fromDefPi {f : HasProperties.Pi φ} (F : Π[f] φ) : Π φ          := fromExternal (HasDependentFunctoriality.fromDefPi F)
  instance {f : HasProperties.Pi φ} : Coe (Π[f] φ) ⌈Π φ⌉ := ⟨fromDefPi⟩

  @[simp] theorem fromCastDefPi {f f' : HasProperties.Pi φ} (F : Π[f] φ) (h : ∀ a, f a = f' a) :
    fromDefPi (HasDependentFunctoriality.castDefPi F h) = fromDefPi F :=
  congrArg fromExternal (HasDependentFunctoriality.fromCastDefPi F h)

  def toDefPi' (F : Π φ) {f : HasProperties.Pi φ} (h : ∀ a, F a = f a) : Π[f] φ :=
  HasDependentFunctoriality.castDefPi (toDefPi F) h

  theorem toDefPi'.eff (F : Π φ) {f : HasProperties.Pi φ} (h : ∀ a, F a = f a) (a : α) : (toDefPi' F h) a = F a :=
  Eq.symm (h a)

  @[simp] theorem toDefPi.eff                            (F : Π    φ) (a : α) : (toDefPi   F) a = F a := rfl
  @[simp] theorem fromDefPi.eff {f : HasProperties.Pi φ} (F : Π[f] φ) (a : α) : (fromDefPi F) a = F a :=
  fromExternal.eff (HasDependentFunctoriality.fromDefPi F) a

  @[simp] theorem fromToDefPi (F : Π φ) : fromDefPi (toDefPi F) = F :=
  Eq.trans (congrArg fromExternal (HasDependentFunctoriality.fromToDefPi (toExternal F))) (fromToExternal F)

  @[simp] theorem fromToDefPi' (F : Π φ) {f : HasProperties.Pi φ} (h : ∀ a, F a = f a) : fromDefPi (toDefPi' F h) = F :=
  Eq.trans (fromCastDefPi (toDefPi F) h) (fromToDefPi F)

  -- This is annoying to prove, and we don't need it at the moment.
  --@[simp] theorem toFromDefPi' {f : HasProperties.Pi φ} (F : Π[f] φ) : toDefPi' (fromDefPi F) (fromDefPi.eff F) = F :=
  --sorry

end HasDependentFunctors



class HasPiFunEquiv (U : Universe.{u}) (V : Universe.{v}) (X : Universe.{w}) (Y : Universe.{w'})
                    [HasDependentFunctors U V X] [HasFunctors U V X]
                    [HasFunctors X X Y] [HasEquivalenceCondition X Y] where
(defPiFun      {α : U} {β : V} (F : Π HasProperties.constProp α β) : α ⟶[λ a => F a] β)
(defPiFunFun   (α : U) (β : V)                                     : (Π HasProperties.constProp α β) ⟶[λ F => defPiFun F] (α ⟶ β))
(defFunPi      {α : U} {β : V} (F : α ⟶ β)                         : Π[λ a => F a] HasProperties.constProp α β)
(defFunPiFun   (α : U) (β : V)                                     : (α ⟶ β) ⟶[λ F => defFunPi F] (Π HasProperties.constProp α β))
(defPiFunEquiv (α : U) (β : V) : (Π HasProperties.constProp α β) ⟷[defPiFunFun α β, defFunPiFun α β] (α ⟶ β))

namespace HasPiFunEquiv

  variable {U V X Y Z : Universe} [HasDependentFunctors U V X] [HasFunctors U V X]
           [HasFunctors X X Y] [HasEquivalences X Y Z] [HasPiFunEquiv U V X Y]

  @[reducible] def piFun {α : U} {β : V} (F : Π HasProperties.constProp α β) : α ⟶ β := defPiFun (Y := Y) F
  @[reducible] def piFunFun (α : U) (β : V) : (Π HasProperties.constProp α β) ⟶ (α ⟶ β) := defPiFunFun α β
  @[reducible] def funPi {α : U} {β : V} (F : α ⟶ β) : Π HasProperties.constProp α β := defFunPi (Y := Y) F
  @[reducible] def funPiFun (α : U) (β : V) : (α ⟶ β) ⟶ Π HasProperties.constProp α β := defFunPiFun α β
  @[reducible] def piFunEquiv (α : U) (β : V) : (Π HasProperties.constProp α β) ⟷ (α ⟶ β) := defPiFunEquiv α β

end HasPiFunEquiv



class HasPiCompFunProp (U V W X Y : Universe) [HasFunctors U V X] [HasProperties V W]
                       [HasDependentFunctors U W Y] [h : HasProperties X Y] extends
  HasCompFunProp U V W X where
(piCompPropIsProp (α : U) {β : V} (φ : HasProperties.Property β W) :
   h.IsProp (λ F : α ⟶ β => Π HasCompFunProp.compProp F φ))

namespace HasPiCompFunProp

  variable {U V W X Y : Universe} [HasFunctors U V X] [HasProperties V W]
           [HasDependentFunctors U W Y] [HasProperties X Y] [HasPiCompFunProp U V W X Y]

  @[reducible] def piCompPropProp (α : U) {β : V} (φ : HasProperties.Property β W) :
    HasProperties.Property (α ⟶ β) Y :=
  ⟨piCompPropIsProp α φ⟩

end HasPiCompFunProp



class HasCompFunPi' (U V W : Universe) [HasFunctoriality U V] [HasDependentFunctoriality V W]
                    [HasDependentFunctoriality U W] [HasCompFunProp' U V W] where
(defCompFunPi {α : U} {β : V} {φ : HasProperties.Property β W} (F : α ⟶' β) (G : Π' φ) :
   Π[λ a => G (F a)] HasCompFunProp'.compProp' F φ)

namespace HasCompFunPi'

  variable {U V W : Universe} [HasFunctoriality U V] [HasDependentFunctoriality V W]
           [HasDependentFunctoriality U W] [HasCompFunProp' U V W] [HasCompFunPi' U V W]

  @[reducible] def compFunPi' {α : U} {β : V} {φ : HasProperties.Property β W} (F : α ⟶' β) (G : Π' φ) :
    Π' HasCompFunProp'.compProp' F φ :=
  defCompFunPi F G

end HasCompFunPi'

class HasCompFunPi (U V W X Y : Universe) [HasFunctors U V X] [HasDependentFunctors V W Y]
                   [HasDependentFunctoriality U W] [HasCompFunProp U V W X] where
(defCompFunPi {α : U} {β : V} {φ : HasProperties.Property β W} (F : α ⟶ β) (G : Π φ) :
   Π[λ a => G (F a)] HasCompFunProp.compProp F φ)

namespace HasCompFunPi

  variable {U V W X Y Z : Universe} [HasFunctors U V X] [HasDependentFunctors V W Y] [HasDependentFunctors U W Z]
           [HasCompFunProp U V W X] [HasCompFunPi U V W X Y]

  @[reducible] def compFunPi {α : U} {β : V} {φ : HasProperties.Property β W} (F : α ⟶ β) (G : Π φ) :
    Π HasCompFunProp.compProp F φ :=
  defCompFunPi F G

  -- TODO
  --instance hasCompFunPi' : HasCompFunPi' U V W :=
  --⟨λ F G => HasDependentFunctoriality.castDefPi (defCompFunPi (HasFunctors.fromExternal F) (HasDependentFunctors.fromExternal G))
  --                                              (λ _ => by simp)⟩

end HasCompFunPi

class HasCompFunPiPi (U : Universe) [HasEmbeddedFunctors U] [HasDependentFunctors U U U]
                     [HasPiCompFunProp U U U U U] extends
  HasCompFunPi U U U U U where
(defRevCompFunPiPi (α : U) {β : U} {φ : HasProperties.Property β U} (G : Π φ) :
   Π[λ F => HasCompFunPi.compFunPi F G] HasPiCompFunProp.piCompPropProp α φ)
(defRevCompFunPiPiFun (α : U) {β : U} (φ : HasProperties.Property β U) :
   (Π φ) ⟶[λ G => defRevCompFunPiPi α G] (Π HasPiCompFunProp.piCompPropProp α φ))

-- TODO: Since the "rev" versions work better than non-"rev" versions here, we should revise our
-- decision to declare forward composition as the default.

namespace HasCompFunPiPi

  variable {U : Universe} [HasEmbeddedFunctors U] [HasDependentFunctors U U U]
           [HasPiCompFunProp U U U U U] [HasCompFunPiPi U]

  @[reducible] def revCompFunPiPi (α : U) {β : U} {φ : HasProperties.Property β U} (G : Π φ) :
    Π HasPiCompFunProp.piCompPropProp α φ :=
  defRevCompFunPiPi α G

  @[reducible] def revCompFunPiPiFun (α : U) {β : U} (φ : HasProperties.Property β U) :
    (Π φ) ⟶ Π HasPiCompFunProp.piCompPropProp α φ :=
  defRevCompFunPiPiFun α φ

  -- TODO: implement this as a lemma, using a dependent version of `swapFunFun`.
  --def defCompFunPiFun {α β : U} (F : α ⟶ β) (φ : HasProperties.Property β U) :
  --  (Π φ) ⟶[λ G => HasCompFunPi.compFunPi F G] (Π HasCompFunProp.compProp F φ) :=
  --sorry

end HasCompFunPiPi



class HasConstFunPi (U V X : Universe) [HasFunctors U V X] [HasConstFun U V] [HasProperties V U]
                    [HasProperties V V] [HasDependentFunctoriality V X] [HasFunProp V U V X] where
(defConstFunPi {β : V} (φ : HasProperties.Property β U) :
   Π[λ c => HasConstFun.constFun (φ c) c] HasFunProp.outFunProp φ β)

namespace HasConstFunPi

  variable {U V X : Universe} [HasFunctors U V X] [HasConstFun U V] [HasProperties V U]
           [HasProperties V V] 

  @[reducible] def constFunPi' [HasDependentFunctoriality V X] [HasFunProp V U V X]
                               [HasConstFunPi U V X] {β : V} (φ : HasProperties.Property β U) :
    Π' HasFunProp.outFunProp φ β :=
  defConstFunPi φ

  @[reducible] def constFunPi {Y : Universe} [HasDependentFunctors V X Y] [HasFunProp V U V X]
                              [HasConstFunPi U V X] {β : V} (φ : HasProperties.Property β U) :
    Π HasFunProp.outFunProp φ β :=
  HasDependentFunctors.fromExternal (constFunPi' φ)

end HasConstFunPi



class HasPiAppFun (U V X Y : Universe) [HasDependentFunctors U V X] [HasFunctors X V Y]
                  [HasProperties U X] [HasDependentFunctoriality U Y] [HasFunProp U X V Y] where
(defAppFun {α : U} (a : α) (φ : HasProperties.Property α V) :
   (Π φ) ⟶[λ F => F a] (φ a))
(defAppFunPi {α : U} (φ : HasProperties.Property α V) :
   Π[λ a => HasFunctors.fromDefFun (defAppFun a φ)] HasFunProp.inFunProp (Π φ) φ)

namespace HasPiAppFun

  variable {U V X Y : Universe} [HasDependentFunctors U V X] [HasFunctors X V Y] [HasProperties U X]

  @[reducible] def appFun' [HasDependentFunctoriality U Y] [HasFunProp U X V Y] [HasPiAppFun U V X Y]
                           {α : U} (a : α) (φ : HasProperties.Property α V) :
    (Π φ) ⟶' φ a :=
  defAppFun a φ

  @[reducible] def appFun [HasDependentFunctoriality U Y] [HasFunProp U X V Y] [HasPiAppFun U V X Y]
                          {α : U} (a : α) (φ : HasProperties.Property α V) :
    (Π φ) ⟶ φ a :=
  HasFunctors.fromExternal (appFun' a φ)

  @[reducible] def appFunPi' [HasDependentFunctoriality U Y] [HasFunProp U X V Y] [HasPiAppFun U V X Y]
                             {α : U} (φ : HasProperties.Property α V) :
    Π' HasFunProp.inFunProp (Π φ) φ :=
  defAppFunPi φ

  @[reducible] def appFunPi {Z : Universe} [HasDependentFunctors U Y Z] [HasFunProp U X V Y]
                            [HasPiAppFun U V X Y]
                            {α : U} (φ : HasProperties.Property α V) :
    Π HasFunProp.inFunProp (Π φ) φ :=
  HasDependentFunctors.fromExternal (appFunPi' φ)

end HasPiAppFun



class HasDupPi (U V X Y : Universe) [HasDependentFunctors U V X] [HasFunctors U X Y] [HasFunctoriality Y X] where
(defDupPi    {α : U} {φ : HasProperties.Property α V} (F : α ⟶ Π φ) : Π[λ a => F a a] φ)
(defDupPiFun {α : U} (φ : HasProperties.Property α V)               : (α ⟶ Π φ) ⟶[λ F => defDupPi F] (Π φ))

namespace HasDupPi

  variable {U V X Y : Universe} [HasDependentFunctors U V X] [HasFunctors U X Y]

  @[reducible] def dupPi' [HasFunctoriality Y X] [HasDupPi U V X Y]
                          {α : U} {φ : HasProperties.Property α V} (F : α ⟶ Π φ) :
    Π' φ :=
  defDupPi F

  @[reducible] def dupPi [HasFunctoriality Y X] [HasDupPi U V X Y]
                         {α : U} {φ : HasProperties.Property α V} (F : α ⟶ Π φ) :
    Π φ :=
  HasDependentFunctors.fromExternal (dupPi' F)

  @[reducible] def dupPiFun' [HasFunctoriality Y X] [HasDupPi U V X Y]
                             {α : U} (φ : HasProperties.Property α V) :
    (α ⟶ Π φ) ⟶' Π φ :=
  defDupPiFun φ

  @[reducible] def dupPiFun {Z : Universe} [HasFunctors Y X Z] [HasDupPi U V X Y]
                            {α : U} (φ : HasProperties.Property α V) :
    (α ⟶ Π φ) ⟶ Π φ :=
  HasFunctors.fromExternal (dupPiFun' φ)

end HasDupPi
