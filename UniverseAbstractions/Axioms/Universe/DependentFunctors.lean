-- TODO: Adapt to `HasIdentity`.
#exit



import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences
import UniverseAbstractions.Axioms.Universe.Properties



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w w' w''



class HasDependentFunctoriality (U : Universe.{u}) (V : Universe.{v}) extends
  HasProperties.{u, v, w} U V : Type (max 1 u v w w') where
(IsFun {A : U} {φ : A ⟿ V} : HasProperties.Pi φ → Sort w')

namespace HasDependentFunctoriality

  variable {U : Universe.{u}} {V : Universe.{v}} [h : HasDependentFunctoriality.{u, v, w, w'} U V]

  def DefPi {A : U} (φ : A ⟿ V) (f : HasProperties.Pi φ) := h.IsFun f
  notation:20 "Π[" f:0 "] " φ:21 => HasDependentFunctoriality.DefPi φ f

  structure Pi {A : U} (φ : A ⟿ V) : Sort (max 1 u v w') where
  (f : HasProperties.Pi φ)
  (F : Π[f] φ)
  notation:20 "Π' " φ:21 => HasDependentFunctoriality.Pi φ

  variable {A : U} {φ : A ⟿ V}

  instance coeDefPi (f : HasProperties.Pi φ) : CoeFun (Π[f] φ) (λ _ => HasProperties.Pi φ) := ⟨λ _ => f⟩
  instance coePi                             : CoeFun (Π'   φ) (λ _ => HasProperties.Pi φ) := ⟨Pi.f⟩

  def toDefPi                            (F : Π'   φ) : Π[F.f] φ := F.F
  def fromDefPi {f : HasProperties.Pi φ} (F : Π[f] φ) : Π'     φ := ⟨f, F⟩

  instance (F : Π' φ)               : CoeDep (Π'   φ) F (Π[F.f] φ) := ⟨toDefPi F⟩
  instance {f : HasProperties.Pi φ} : Coe    (Π[f] φ)   (Π'     φ) := ⟨fromDefPi⟩

  theorem DefPi.ext {f f' : HasProperties.Pi φ} (h : ∀ a, f a = f' a) : (Π[f] φ) = (Π[f'] φ) :=
  congrArg (DefPi φ) (funext h)

  def castDefPi {f f' : HasProperties.Pi φ} (F : Π[f] φ) (h : ∀ a, f a = f' a) : Π[f'] φ :=
  cast (DefPi.ext h) F

  @[simp] theorem fromCastDefPi {f f' : HasProperties.Pi φ} (F : Π[f] φ) (h : ∀ a, f a = f' a) :
    fromDefPi (castDefPi F h) = fromDefPi F :=
  have h₁ : f = f' := funext h;
  by subst h₁; rfl

  @[simp] theorem castCastDefPi {f f' : HasProperties.Pi φ} (F : Π[f] φ) (h : ∀ a, f a = f' a) :
    castDefPi (castDefPi F h) (λ a => Eq.symm (h a)) = F :=
  have h₁ : f = f' := funext h;
  by subst h₁; rfl

  @[simp] theorem toDefPi.eff                            (F : Π'   φ) (a : A) : (toDefPi   F) a = F a := rfl
  @[simp] theorem fromDefPi.eff {f : HasProperties.Pi φ} (F : Π[f] φ) (a : A) : (fromDefPi F) a = F a := rfl

  @[simp] theorem fromToDefPi                          (F : Π'   φ) : fromDefPi (toDefPi F) = F :=
  match F with | ⟨_, _⟩ => rfl
  @[simp] theorem toFromDefPi {f : HasProperties.Pi φ} (F : Π[f] φ) : toDefPi (fromDefPi F) = F := rfl

  theorem Pi.Eq.eff {F F' : Π' φ} (h : F = F') (a : A) : F a = F' a := h ▸ rfl

  theorem toDefPi.congr {F F' : Π' φ} (h : F = F') :
    castDefPi (toDefPi F) (Pi.Eq.eff h) = toDefPi F' :=
  by subst h; rfl

end HasDependentFunctoriality



class HasDependentFunctors (U : Universe.{u}) (V : Universe.{v}) (UV : outParam Universe.{w}) extends
  HasDependentFunctoriality.{u, v, w', w''} U V : Type (max 1 u v w w' w'') where
[embed {A : U} (φ : A ⟿ V) : HasEmbeddedType.{w, max 1 u v w''} UV (Π' φ)]

namespace HasDependentFunctors

  variable {U V UV : Universe} [h : HasDependentFunctors U V UV]

  instance hasEmbeddedType {A : U} (φ : A ⟿ V) : HasEmbeddedType UV (Π' φ) :=
  h.embed φ

  def Pi {A : U} (φ : A ⟿ V) : UV := HasEmbeddedType.EmbeddedType UV (Π' φ)
  notation:20 "Π " φ:21 => HasDependentFunctors.Pi φ

  variable {A : U} {φ : A ⟿ V}

  def toExternal   (F : Π  φ) : Π' φ := HasEmbeddedType.toExternal   UV F
  def fromExternal (F : Π' φ) : Π  φ := HasEmbeddedType.fromExternal UV F

  def piCoe (F : Π φ) : HasProperties.Pi φ := (toExternal F).f
  instance coePi : CoeFun ⌈Π φ⌉ (λ _ => HasProperties.Pi φ) := ⟨piCoe⟩

  @[simp] theorem fromToExternal (F : Π  φ) : fromExternal (toExternal F) = F := HasEmbeddedType.fromToExternal UV F
  @[simp] theorem toFromExternal (F : Π' φ) : toExternal (fromExternal F) = F := HasEmbeddedType.toFromExternal UV F

  @[simp] theorem toExternal.eff   (F : Π  φ) (a : A) : (toExternal   F) a = F a := rfl
  @[simp] theorem fromExternal.eff (F : Π' φ) (a : A) : (fromExternal F) a = F a :=
  congrFun (congrArg HasDependentFunctoriality.Pi.f (toFromExternal F)) a

  def toDefPi                            (F : Π    φ) : Π[piCoe F] φ := HasDependentFunctoriality.toDefPi (toExternal F)
  def fromDefPi {f : HasProperties.Pi φ} (F : Π[f] φ) : Π φ          := fromExternal (HasDependentFunctoriality.fromDefPi F)
  instance {f : HasProperties.Pi φ} : Coe (Π[f] φ) ⌈Π φ⌉ := ⟨fromDefPi⟩

  @[simp] theorem fromCastDefPi {f f' : HasProperties.Pi φ} (F : Π[f] φ) (h : ∀ a, f a = f' a) :
    fromDefPi (HasDependentFunctoriality.castDefPi F h) = fromDefPi F :=
  congrArg fromExternal (HasDependentFunctoriality.fromCastDefPi F h)

  def toDefPi' (F : Π φ) {f : HasProperties.Pi φ} (h : ∀ a, F a = f a) : Π[f] φ :=
  HasDependentFunctoriality.castDefPi (toDefPi F) h

  theorem toDefPi'.eff (F : Π φ) {f : HasProperties.Pi φ} (h : ∀ a, F a = f a) (a : A) : (toDefPi' F h) a = F a :=
  Eq.symm (h a)

  @[simp] theorem toDefPi.eff                            (F : Π    φ) (a : A) : (toDefPi   F) a = F a := rfl
  @[simp] theorem fromDefPi.eff {f : HasProperties.Pi φ} (F : Π[f] φ) (a : A) : (fromDefPi F) a = F a :=
  fromExternal.eff (HasDependentFunctoriality.fromDefPi F) a

  @[simp] theorem fromToDefPi (F : Π φ) : fromDefPi (toDefPi F) = F :=
  Eq.trans (congrArg fromExternal (HasDependentFunctoriality.fromToDefPi (toExternal F))) (fromToExternal F)

  @[simp] theorem fromToDefPi' (F : Π φ) {f : HasProperties.Pi φ} (h : ∀ a, F a = f a) : fromDefPi (toDefPi' F h) = F :=
  Eq.trans (fromCastDefPi (toDefPi F) h) (fromToDefPi F)

  @[simp] theorem toFromDefPi' {f : HasProperties.Pi φ} (F : Π[f] φ) : toDefPi' (fromDefPi F) (fromDefPi.eff F) = F :=
  HasDependentFunctoriality.toDefPi.congr (toFromExternal (HasDependentFunctoriality.fromDefPi F))

  theorem toFromDefPi {f : HasProperties.Pi φ} (F : Π[f] φ) : toDefPi (fromDefPi F) ≅ F :=
  heq_of_eqRec_eq _ (toFromDefPi' F)

end HasDependentFunctors



class HasPiFunEquiv (U : Universe.{u}) (V : Universe.{v}) (UV : Universe.{w}) (UVUV : Universe.{w'})
                    [HasDependentFunctors U V UV] [HasFunctors U V UV]
                    [HasFunctors UV UV UVUV] [HasEquivalenceCondition UV UVUV] where
(defPiFun      {A : U} {B : V} (F : Π A{B}) : A ⟶[λ a => F a] B)
(defPiFunFun   (A : U) (B : V)              : (Π A{B}) ⟶[λ F => defPiFun F] (A ⟶ B))
(defFunPi      {A : U} {B : V} (F : A ⟶ B)  : Π[λ a => F a] A{B})
(defFunPiFun   (A : U) (B : V)              : (A ⟶ B) ⟶[λ F => defFunPi F] (Π A{B}))
(defPiFunEquiv (A : U) (B : V)              : (Π A{B}) ⟷[defPiFunFun A B, defFunPiFun A B] (A ⟶ B))

namespace HasPiFunEquiv

  variable {U V UV UVUV UV_UV : Universe} [HasDependentFunctors U V UV] [HasFunctors U V UV]
           [HasFunctors UV UV UVUV] [HasEquivalences UV UVUV UV_UV] [HasPiFunEquiv U V UV UVUV]

  @[reducible] def piFun {A : U} {B : V} (F : Π A{B}) : A ⟶ B := defPiFun (UVUV := UVUV) F
  @[reducible] def piFunFun (A : U) (B : V) : (Π A{B}) ⟶ (A ⟶ B) := defPiFunFun A B
  @[reducible] def funPi {A : U} {B : V} (F : A ⟶ B) : Π A{B} := defFunPi (UVUV := UVUV) F
  @[reducible] def funPiFun (A : U) (B : V) : (A ⟶ B) ⟶ Π A{B} := defFunPiFun A B
  @[reducible] def piFunEquiv (A : U) (B : V) : (Π A{B}) ⟷ (A ⟶ B) := defPiFunEquiv A B

end HasPiFunEquiv



class HasPiCompFunProp (U V W UV UW : Universe) [HasFunctors U V UV] [HasProperties V W]
                       [HasDependentFunctors U W UW] [HasProperties UV UW] extends
  HasCompFunProp U V W UV where
(defPiCompPropProp (A : U) {B : V} (φ : B ⟿ W) : (A ⟶ B) ⟿[λ F => Π HasCompFunProp.compProp F φ] UW)
(defPiCompPropConstEq (A : U) (B : V) (C : W) :
  defPiCompPropProp A B{C} = HasProperties.castDefProp (HasProperties.defConstProp (A ⟶ B) (Π A{C}))
                                                       (λ _ => by simp))

namespace HasPiCompFunProp

  variable {U V W UV UW : Universe} [HasFunctors U V UV] [HasProperties V W]
           [HasDependentFunctors U W UW] [HasProperties UV UW] [HasPiCompFunProp U V W UV UW]

  @[reducible] def piCompPropProp (A : U) {B : V} (φ : B ⟿ W) : (A ⟶ B) ⟿ UW := defPiCompPropProp A φ

  @[simp] theorem piCompPropConstEq (A : U) (B : V) (C : W) : piCompPropProp A B{C} = (A ⟶ B){Π A{C}} :=
  Eq.trans (congrArg HasProperties.fromDefProp (defPiCompPropConstEq A B C)) (HasProperties.fromCastDefProp _ _)

end HasPiCompFunProp



class HasCompFunPi' (U V W : Universe) [HasFunctoriality U V] [HasDependentFunctoriality V W]
                    [HasDependentFunctoriality U W] [HasCompFunProp' U V W] where
(defCompFunPi {A : U} {B : V} {φ : B ⟿ W} (F : A ⟶' B) (G : Π' φ) :
   Π[λ a => G (F a)] HasCompFunProp'.compProp F φ)

namespace HasCompFunPi'

  variable {U V W : Universe} [HasFunctoriality U V] [HasDependentFunctoriality V W]
           [HasDependentFunctoriality U W] [HasCompFunProp' U V W] [HasCompFunPi' U V W]

  @[reducible] def compFunPi' {A : U} {B : V} {φ : B ⟿ W} (F : A ⟶' B) (G : Π' φ) :
    Π' HasCompFunProp'.compProp F φ :=
  defCompFunPi F G

end HasCompFunPi'

class HasCompFunPi (U V W UV VW : Universe) [HasFunctors U V UV] [HasDependentFunctors V W VW]
                   [HasDependentFunctoriality U W] [HasCompFunProp U V W UV] where
(defCompFunPi {A : U} {B : V} {φ : B ⟿ W} (F : A ⟶ B) (G : Π φ) :
   Π[λ a => G (F a)] HasCompFunProp.compProp F φ)

namespace HasCompFunPi

  variable {U V W UV VW UW : Universe} [HasFunctors U V UV] [HasDependentFunctors V W VW] [HasDependentFunctors U W UW]
           [HasCompFunProp U V W UV] [HasCompFunPi U V W UV VW]

  @[reducible] def compFunPi {A : U} {B : V} {φ : B ⟿ W} (F : A ⟶ B) (G : Π φ) :
    Π HasCompFunProp.compProp F φ :=
  defCompFunPi F G

  -- TODO
  --instance hasCompFunPi' : HasCompFunPi' U V W :=
  --⟨λ F G => HasDependentFunctoriality.castDefPi (defCompFunPi (HasFunctors.fromExternal F) (HasDependentFunctors.fromExternal G))
  --                                              (λ _ => by simp)⟩

end HasCompFunPi

class HasCompFunPiPi (U : Universe) [HasInternalFunctors U] [HasDependentFunctors U U U]
                     [HasPiCompFunProp U U U U U] extends
  HasCompFunPi U U U U U where
(defRevCompFunPiPi (A : U) {B : U} {φ : B ⟿ U} (G : Π φ) :
   Π[λ F => HasCompFunPi.compFunPi F G] HasPiCompFunProp.piCompPropProp A φ)
(defRevCompFunPiPiFun (A : U) {B : U} (φ : B ⟿ U) :
   (Π φ) ⟶[λ G => defRevCompFunPiPi A G] (Π HasPiCompFunProp.piCompPropProp A φ))

-- TODO: Since the "rev" versions work better than non-"rev" versions here, we should revise our
-- decision to declare forward composition as the default.

namespace HasCompFunPiPi

  variable {U : Universe} [HasInternalFunctors U] [HasDependentFunctors U U U]
           [HasPiCompFunProp U U U U U] [HasCompFunPiPi U]

  @[reducible] def revCompFunPiPi (A : U) {B : U} {φ : B ⟿ U} (G : Π φ) :
    Π HasPiCompFunProp.piCompPropProp A φ :=
  defRevCompFunPiPi A G

  @[reducible] def revCompFunPiPiFun (A : U) {B : U} (φ : B ⟿ U) :
    (Π φ) ⟶ Π HasPiCompFunProp.piCompPropProp A φ :=
  defRevCompFunPiPiFun A φ

  -- TODO: implement this as a lemma, using a dependent version of `swapFunFun`.
  --def defCompFunPiFun {A B : U} (F : A ⟶ B) (φ : B ⟿ U) :
  --  (Π φ) ⟶[λ G => HasCompFunPi.compFunPi F G] (Π HasCompFunProp.compProp F φ) :=
  --sorry

end HasCompFunPiPi



class HasConstFunPi (U V UV : Universe) [HasFunctors U V UV] [HasConstFun U V] [HasProperties V U]
                    [HasProperties V V] [HasDependentFunctoriality V UV] [HasFunProp V U V UV] where
(defConstFunPi {B : V} (φ : B ⟿ U) :
   Π[λ b => HasConstFun.constFun (φ b) b] {φ ⟶ B{B}})

namespace HasConstFunPi

  variable {U V UV : Universe} [HasFunctors U V UV] [HasConstFun U V] [HasProperties V U]
           [HasProperties V V] 

  @[reducible] def constFunPi' [HasDependentFunctoriality V UV] [HasFunProp V U V UV]
                               [HasConstFunPi U V UV] {B : V} (φ : B ⟿ U) :
    Π' {φ ⟶ B{B}} :=
  defConstFunPi φ

  @[reducible] def constFunPi {VUV : Universe} [HasDependentFunctors V UV VUV] [HasFunProp V U V UV]
                              [HasConstFunPi U V UV] {B : V} (φ : B ⟿ U) :
    Π {φ ⟶ B{B}} :=
  HasDependentFunctors.fromExternal (constFunPi' φ)

end HasConstFunPi



class HasPiAppFun (U V UV UVV : Universe) [HasDependentFunctors U V UV] [HasFunctors UV V UVV]
                  [HasProperties U UV] [HasDependentFunctoriality U UVV] [HasFunProp U UV V UVV] where
(defAppFun   {A : U} (a : A) (φ : A ⟿ V) : (Π φ) ⟶[λ F => F a] (φ a))
(defAppFunPi {A : U}         (φ : A ⟿ V) : Π[λ a => HasFunctors.fromDefFun (defAppFun a φ)] {A{Π φ} ⟶ φ})

namespace HasPiAppFun

  variable {U V UV UVV : Universe} [HasDependentFunctors U V UV] [HasFunctors UV V UVV] [HasProperties U UV]

  @[reducible] def appFun' [HasDependentFunctoriality U UVV] [HasFunProp U UV V UVV] [HasPiAppFun U V UV UVV]
                           {A : U} (a : A) (φ : A ⟿ V) :
    (Π φ) ⟶' φ a :=
  defAppFun a φ

  @[reducible] def appFun [HasDependentFunctoriality U UVV] [HasFunProp U UV V UVV] [HasPiAppFun U V UV UVV]
                          {A : U} (a : A) (φ : A ⟿ V) :
    (Π φ) ⟶ φ a :=
  HasFunctors.fromExternal (appFun' a φ)

  @[reducible] def appFunPi' [HasDependentFunctoriality U UVV] [HasFunProp U UV V UVV] [HasPiAppFun U V UV UVV]
                             {A : U} (φ : A ⟿ V) :
    Π' {A{Π φ} ⟶ φ} :=
  defAppFunPi φ

  @[reducible] def appFunPi {UUVV : Universe} [HasDependentFunctors U UVV UUVV] [HasFunProp U UV V UVV]
                            [HasPiAppFun U V UV UVV]
                            {A : U} (φ : A ⟿ V) :
    Π {A{Π φ} ⟶ φ} :=
  HasDependentFunctors.fromExternal (appFunPi' φ)

end HasPiAppFun



class HasDupPi (U V UV UUV : Universe) [HasDependentFunctors U V UV] [HasFunctors U UV UUV] [HasFunctoriality UUV UV] where
(defDupPi    {A : U} {φ : A ⟿ V} (F : A ⟶ Π φ) : Π[λ a => F a a] φ)
(defDupPiFun {A : U} (φ : A ⟿ V)               : (A ⟶ Π φ) ⟶[λ F => defDupPi F] (Π φ))

namespace HasDupPi

  variable {U V UV UUV : Universe} [HasDependentFunctors U V UV] [HasFunctors U UV UUV]

  @[reducible] def dupPi' [HasFunctoriality UUV UV] [HasDupPi U V UV UUV]
                          {A : U} {φ : A ⟿ V} (F : A ⟶ Π φ) :
    Π' φ :=
  defDupPi F

  @[reducible] def dupPi [HasFunctoriality UUV UV] [HasDupPi U V UV UUV]
                         {A : U} {φ : A ⟿ V} (F : A ⟶ Π φ) :
    Π φ :=
  HasDependentFunctors.fromExternal (dupPi' F)

  @[reducible] def dupPiFun' [HasFunctoriality UUV UV] [HasDupPi U V UV UUV]
                             {A : U} (φ : A ⟿ V) :
    (A ⟶ Π φ) ⟶' Π φ :=
  defDupPiFun φ

  @[reducible] def dupPiFun {UUVUV : Universe} [HasFunctors UUV UV UUVUV] [HasDupPi U V UV UUV]
                            {A : U} (φ : A ⟿ V) :
    (A ⟶ Π φ) ⟶ Π φ :=
  HasFunctors.fromExternal (dupPiFun' φ)

end HasDupPi
