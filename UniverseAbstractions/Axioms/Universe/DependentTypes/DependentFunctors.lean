import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.DependentTypes.Properties



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v upv uv



class HasDependentFunctors (U : Universe.{u}) (V : Universe.{v})
                           {UpV : Universe.{upv}} [HasFunctors U {V} UpV]
                           (UV : outParam Universe.{uv}) where
(Pi    {A : U}               : (A ⟶ ⌊V⌋) → UV)
(apply {A : U} {φ : A ⟶ ⌊V⌋} : Pi φ → HasFunctors.Pi φ)

namespace HasDependentFunctors

  open MetaRelation

  notation:20 "Π " φ:21 => HasDependentFunctors.Pi φ

  instance coeFun {U V UpV UV : Universe} [HasFunctors U {V} UpV] [HasDependentFunctors U V UV]
                  {A : U} (φ : A ⟶ ⌊V⌋) :
    CoeFun ⌈Π φ⌉ (λ _ => HasFunctors.Pi φ) :=
  ⟨apply⟩

  variable {U V UpV UV : Universe} [HasFunctors U {V} UpV] [HasDependentFunctors U V UV]
           [HasIdentity V] 

  structure DefPi {A : U} (φ : A ⟶ ⌊V⌋) (f : HasFunctors.Pi φ) where
  (F           : Π φ)
  (eff (a : A) : F a ≃ f a)

  notation:20 "Π{" f:0 "} " φ:21 => HasDependentFunctors.DefPi φ f

  variable {A : U} {φ : A ⟶ ⌊V⌋}

  def toDefPi' (F : Π φ) {f : HasFunctors.Pi φ} (h : ∀ a, F a ≃ f a) : Π{f} φ := ⟨F, h⟩

  def toDefPi                          (F : Π    φ) : Π{apply F} φ := toDefPi' F (λ a => HasRefl.refl (F a))
  def fromDefPi {f : HasFunctors.Pi φ} (F : Π{f} φ) : Π          φ := F.F

  def byDef {f : HasFunctors.Pi φ} {F : Π{f} φ} {a : A} : (fromDefPi F) a ≃ f a := F.eff a

  @[simp] theorem fromToDefPi' (F : Π φ) {f : HasFunctors.Pi φ} (h : ∀ a, F a ≃ f a) :
    fromDefPi (toDefPi' F h) = F :=
  rfl
  @[simp] theorem fromToDefPi (F : Π φ) : fromDefPi (toDefPi F) = F := rfl

  @[simp] theorem toFromDefPi' {f : HasFunctors.Pi φ} (F : Π{f} φ) : toDefPi' (fromDefPi F) F.eff = F :=
  by induction F; rfl

  instance (F : Π φ)              : CoeDep (Π    φ) F (Π{apply F} φ) := ⟨toDefPi F⟩
  instance {f : HasFunctors.Pi φ} : Coe    (Π{f} φ)   (Π          φ) := ⟨fromDefPi⟩

  def castDefPi {f f' : HasFunctors.Pi φ} (F : Π{f} φ) (h : ∀ a, f a ≃ f' a) : Π{f'} φ :=
  ⟨F.F, λ a => h a • F.eff a⟩

  @[simp] theorem fromCastDefPi {f f' : HasFunctors.Pi φ} (F : Π{f} φ) (h : ∀ a, f a ≃ f' a) :
    fromDefPi (castDefPi F h) = fromDefPi F :=
  rfl

end HasDependentFunctors



class HasDependentCongrArg (U : Universe.{u}) (V : Universe.{v}) {UpV : Universe.{upv}}
                           [HasFunctors U {V} UpV] {UV : Universe.{uv}} [HasDependentFunctors U V UV]
                           [HasIdentity U] [HasTypeIdentity V] [HasCongrArg U {V}] where
(congrArg {A : U} {φ : A ⟶ ⌊V⌋} (F : Π φ) {a₁ a₂ : A} (e : a₁ ≃ a₂) :
   F a₁ ≃[HasCongrArg.propCongrArg φ e] F a₂)

#exit




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
   Π{λ a => G (F a)} HasCompFunProp'.compProp F φ)

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
   Π{λ a => G (F a)} HasCompFunProp.compProp F φ)

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
   Π{λ F => HasCompFunPi.compFunPi F G} HasPiCompFunProp.piCompPropProp A φ)
(defRevCompFunPiPiFun (A : U) {B : U} (φ : B ⟿ U) :
   (Π φ) ⟶{λ G => defRevCompFunPiPi A G} (Π HasPiCompFunProp.piCompPropProp A φ))

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
  --  (Π φ) ⟶{λ G => HasCompFunPi.compFunPi F G} (Π HasCompFunProp.compProp F φ) :=
  --sorry

end HasCompFunPiPi



class HasConstFunPi (U V UV : Universe) [HasFunctors U V UV] [HasConstFun U V] [HasProperties V U]
                    [HasProperties V V] [HasDependentFunctoriality V UV] [HasFunProp V U V UV] where
(defConstFunPi {B : V} (φ : B ⟿ U) :
   Π{λ b => HasConstFun.constFun (φ b) b} {φ ⟶ B{B}})

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
(defAppFun   {A : U} (a : A) (φ : A ⟿ V) : (Π φ) ⟶{λ F => F a} (φ a))
(defAppFunPi {A : U}         (φ : A ⟿ V) : Π{λ a => HasFunctors.fromDefFun (defAppFun a φ)} {A{Π φ} ⟶ φ})

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
(defDupPi    {A : U} {φ : A ⟿ V} (F : A ⟶ Π φ) : Π{λ a => F a a} φ)
(defDupPiFun {A : U} (φ : A ⟿ V)               : (A ⟶ Π φ) ⟶{λ F => defDupPi F} (Π φ))

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
