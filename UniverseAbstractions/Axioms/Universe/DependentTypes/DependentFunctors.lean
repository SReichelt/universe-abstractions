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
  notation:20 "Π{▻ " f:0 "} " φ:21 => HasDependentFunctors.DefPi φ (HasFunctors.castPiTo φ f (λ _ => HasFunctors.byDef))
  notation:20 "Π{" hTo:0 " ▻ " f:0 "} " φ:21 => HasDependentFunctors.DefPi φ (HasFunctors.castPiTo φ f (λ _ => hTo • HasFunctors.byDef))
  notation:20 "Π{" f:0 " ◅} " φ:21 => HasDependentFunctors.DefPi φ (HasFunctors.castPiInv φ f (λ _ => HasFunctors.byDef))
  notation:20 "Π{" f:0 " ◅ " hInv:0 "} " φ:21 => HasDependentFunctors.DefPi φ (HasFunctors.castPiInv φ f (λ _ => hInv • HasFunctors.byDef))
  notation:20 "Π{▻ " f:0 " ◅} " φ:21 => HasDependentFunctors.DefPi φ (HasFunctors.castPiTo φ (HasFunctors.castPiInv φ f (λ _ => HasFunctors.byDef)) (λ _ => HasFunctors.byDef))
  notation:20 "Π{" hTo:0 "▻ " f:0 " ◅} " φ:21 => HasDependentFunctors.DefPi φ (HasFunctors.castPiTo φ (HasFunctors.castPiInv φ f (λ _ => HasFunctors.byDef)) (λ _ => hTo • HasFunctors.byDef))
  notation:20 "Π{▻ " f:0 " ◅ " hInv:0 "} " φ:21 => HasDependentFunctors.DefPi φ (HasFunctors.castPiTo φ (HasFunctors.castPiInv φ f (λ _ => hInv • HasFunctors.byDef)) (λ _ => HasFunctors.byDef))
  notation:20 "Π{" hTo:0 "▻ " f:0 " ◅ " hInv:0 "} " φ:21 => HasDependentFunctors.DefPi φ (HasFunctors.castPiTo φ (HasFunctors.castPiInv φ f (λ _ => hInv • HasFunctors.byDef)) (λ _ => hTo • HasFunctors.byDef))

  variable {A : U} {φ : A ⟶ ⌊V⌋}

  def toDefPi' (F : Π φ) {f : HasFunctors.Pi φ} (h : ∀ a, F a ≃ f a) : Π{f} φ := ⟨F, h⟩

  def toDefPi                          (F : Π    φ) : Π{apply F} φ := toDefPi' F (λ a => HasRefl.refl (F a))
  def fromDefPi {f : HasFunctors.Pi φ} (F : Π{f} φ) : Π          φ := F.F

  def byDefPi {f : HasFunctors.Pi φ} {F : Π{f} φ} {a : A} : (fromDefPi F) a ≃ f a := F.eff a

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

namespace HasDependentCongrArg

  open HasFunctors DependentEquivalence HasDependentFunctors

  variable {U V UpV UV : Universe} [HasFunctors U {V} UpV] [HasDependentFunctors U V UV]
           [HasIdentity U] [HasTypeIdentity V] [HasCongrArg U {V}] [HasDependentCongrArg U V]

  def defCongrArg {A : U} {φ : A ⟶ ⌊V⌋} {f : HasFunctors.Pi φ} (F : Π{f} φ) {a₁ a₂ : A}
                  (e : a₁ ≃ a₂) :
    f a₁ ≃[HasCongrArg.propCongrArg φ e] f a₂ :=
  compDepInd (compIndDep byDefPi⁻¹ (congrArg (fromDefPi F) e)) byDefPi

  def byArgDef {X XU : Universe} [HasFunctors X U XU] {A : X} {B : U} {φ : B ⟶ ⌊V⌋}
               {f : A → B} {F : A ⟶{f} B} {G : Π φ} {a : A} :
    G ((fromDefFun F) a) ≃[HasCongrArg.propCongrArg φ byDef] G (f a) :=
  congrArg G byDef

end HasDependentCongrArg

class HasDependentCongrFun (U : Universe.{u}) (V : Universe.{v}) {UpV : Universe.{upv}}
                           [HasFunctors U {V} UpV] {UV : Universe.{uv}} [HasDependentFunctors U V UV]
                           [HasIdentity UV] [HasIdentity V] where
(congrFun {A : U} {φ : A ⟶ ⌊V⌋} {F₁ F₂ : Π φ} (h : F₁ ≃ F₂) (a : A) : F₁ a ≃ F₂ a)

namespace HasDependentCongrFun

  open HasDependentFunctors

  variable {U V UpV UV : Universe} [HasFunctors U {V} UpV] [HasDependentFunctors U V UV]
           [HasIdentity UV] [HasIdentity V] [HasDependentCongrFun U V]

  def defCongrFun {A : U} {φ : A ⟶ ⌊V⌋} {f₁ f₂ : HasFunctors.Pi φ} {F₁ : Π{f₁} φ} {F₂ : Π{f₂} φ}
                  (h : fromDefPi F₁ ≃ fromDefPi F₂) (a : A) :
    f₁ a ≃ f₂ a :=
  byDefPi • congrFun h a • byDefPi⁻¹

end HasDependentCongrFun



class HasFunctorialPiConstructor (U V : Universe) {UpV UV UpVpUV : Universe}
                                 [HasFunctors U {V} UpV] [HasDependentFunctors U V UV]
                                 [HasFunctors UpV {UV} UpVpUV] [HasIdentity {UV}] where
(defPiFun (A : U) : (A ⟶ ⌊V⌋) ⟶{λ φ => Π φ} ⌊UV⌋)

namespace HasFunctorialPiConstructor

  open HasFunctors HasCongrArg HasTypeIdentity

  section

    variable {U V UpV UV UpVpUV : Universe} [HasFunctors U {V} UpV] [HasDependentFunctors U V UV]
             [HasFunctors UpV {UV} UpVpUV]

    @[reducible] def piFun [HasIdentity {UV}] [HasFunctorialPiConstructor U V] (A : U) :
      (A ⟶ ⌊V⌋) ⟶ ⌊UV⌋ :=
    fromDefFun (defPiFun A)

    variable [HasIdentity UpV] [HasTypeIdentity UV] [HasFunctorialPiConstructor U V]
             [HasCongrArg UpV {UV}]

    def castPiTo  {A : U} {φ₁ φ₂ : A ⟶ ⌊V⌋} (E : φ₁ ≃ φ₂) (F : Π φ₁) : Π φ₂ :=
    castTo  (defCongrArg (defPiFun A) E) F
    def castPiInv {A : U} {φ₁ φ₂ : A ⟶ ⌊V⌋} (E : φ₁ ≃ φ₂) (F : Π φ₂) : Π φ₁ :=
    castInv (defCongrArg (defPiFun A) E) F

  end

  section

    variable {U V W VpW UVpW VW UpVW VpWpVW : Universe} [HasFunctors V {W} VpW]
             [HasFunctors U VpW UVpW] [HasDependentFunctors V W VW] [HasIdentity {VW}]
             [HasFunctors U {VW} UpVW] [HasFunctors VpW {VW} VpWpVW]
             [HasFunctorialPiConstructor V W] [HasCompFun U VpW {VW}]

    def defPiProp {A : U} {B : V} (φ : A ⟶ B ⟶ ⌊W⌋) : A ⟶{λ a => Π (φ a)} ⌊VW⌋ :=
    piFun B ⊙ φ
    ◄ byDef

    @[reducible] def piProp {A : U} {B : V} (φ : A ⟶ B ⟶ ⌊W⌋) : A ⟶ ⌊VW⌋ := defPiProp φ
    notation:20 "{Π} " φ:21 => HasFunctorialPiConstructor.piProp φ

  end

  section

    variable {U W : Universe} {UpW UpWpW : Universe} [HasFunctors U U U] [HasFunctors U {W} UpW]
             [HasDependentFunctors U W W] [HasIdentity {W}] [HasFunctors U UpW UpW]
             [HasFunctors UpW {W} UpWpW] [HasIdentity UpW] [HasCongrArg UpW {W}]
             [HasFunctorialPiConstructor U W] [HasRevCompFunFun U {W}] [HasCompFun U UpW {W}]

    def defPiCompFunProp (A : U) {B : U} (φ : B ⟶ ⌊W⌋) : (A ⟶ B) ⟶{λ F => Π (φ ⊙ F)} ⌊W⌋ :=
    piFun A ⊙ HasRevCompFunFun.revCompFunFun A φ
    ◄ HasInstanceEquivalences.trans byArgDef byDef

    @[reducible] def piCompFunProp (A : U) {B : U} (φ : B ⟶ ⌊W⌋) : (A ⟶ B) ⟶ ⌊W⌋ := defPiCompFunProp A φ

  end

end HasFunctorialPiConstructor



class HasCompFunPi (U V W : Universe) {UV VpW VW UpW UW : Universe} [HasFunctors U V UV]
                   [HasFunctors V {W} VpW] [HasDependentFunctors V W VW]
                   [HasFunctors U {W} UpW] [HasDependentFunctors U W UW]
                   [HasTypeIdentity W] [HasCompFun U V {W}] where
(defCompFunPi {A : U} {B : V} {φ : B ⟶ ⌊W⌋} (F : A ⟶ B) (G : Π φ) : Π{λ a => G (F a) ◅} (φ ⊙ F))

namespace HasCompFunPi

  variable {U V W UV VpW VW UpW UW : Universe} [HasFunctors U V UV] [HasFunctors V {W} VpW]
           [HasDependentFunctors V W VW] [HasFunctors U {W} UpW] [HasDependentFunctors U W UW]
           [HasTypeIdentity W] [HasCompFun U V {W}] [HasCompFunPi U V W]

  @[reducible] def compFunPi {A : U} {B : V} {φ : B ⟶ ⌊W⌋} (F : A ⟶ B) (G : Π φ) :
    Π (φ ⊙ F) :=
  defCompFunPi F G

end HasCompFunPi

class HasRevCompFunPiPi (U W : Universe) {UpW UpWpW : Universe} [HasTypeIdentity W] [HasFunctors U U U]
                        [HasFunctors U {W} UpW] [HasDependentFunctors U W W]
                        [HasFunctors U UpW UpW] [HasIdentity UpW] [HasFunctors UpW {W} UpWpW]
                        [HasCongrArg UpW {W}] [HasCompFun U UpW {⌈W⌉}]
                        [HasFunctorialPiConstructor U W] [HasRevCompFunFun U {W}] extends
  HasCompFunPi U U W where
(defRevCompFunPiPi (A : U) {B : U} {φ : B ⟶ ⌊W⌋} (G : Π φ) :
   Π{λ F => HasCompFunPi.compFunPi F G ◅} HasFunctorialPiConstructor.piCompFunProp A φ)
(defRevCompFunPiPiFun (A : U) {B : U} (φ : B ⟶ ⌊W⌋) :
   (Π φ) ⟶{λ G => defRevCompFunPiPi A G} (Π HasFunctorialPiConstructor.piCompFunProp A φ))

namespace HasRevCompFunPiPi

  variable {U W UpW UpWpW : Universe} [HasTypeIdentity W] [HasFunctors U U U] [HasFunctors U {W} UpW]
           [HasDependentFunctors U W W] [HasFunctors U UpW UpW] [HasIdentity UpW]
           [HasFunctors UpW {W} UpWpW] [HasCongrArg UpW {W}] [HasCompFun U UpW {⌈W⌉}]
           [HasFunctorialPiConstructor U W] [HasRevCompFunFun U {W}] [HasRevCompFunPiPi U W]

  @[reducible] def revCompFunPiPi (A : U) {B : U} {φ : B ⟶ ⌊W⌋} (G : Π φ) :
    Π HasFunctorialPiConstructor.piCompFunProp A φ :=
  defRevCompFunPiPi A G

  @[reducible] def revCompFunPiPiFun (A : U) {B : U} (φ : B ⟶ ⌊W⌋) :
    (Π φ) ⟶ Π HasFunctorialPiConstructor.piCompFunProp A φ :=
  defRevCompFunPiPiFun A φ

  -- TODO: Derive these.
  --def defCompFunPiFun {A B : U} (F : A ⟶ B) (φ : B ⟶ ⌊W⌋) :
  --  (Π φ) ⟶{λ G => HasCompFunPi.compFunPi F G} (Π (φ ⊙ F)) :=
  --sorry

  --def defCompFunPiFunPi [HasFunProp U W W] [HasConstFun U {W}] (A : U) {B : U} (φ : B ⟶ ⌊W⌋) :
  --  Π{λ F => defCompFunPiFun F φ} ({[A ⟶ B] Π φ} {⟶} HasFunctorialPiConstructor.piCompFunProp A φ) :=
  --sorry

end HasRevCompFunPiPi



class HasConstFunPi (U : Universe) {UpU : Universe} [HasTypeIdentity U] [HasFunctors U {U} UpU]
                    [HasDependentFunctors U U U] [HasConstFun U U] [HasConstFun U {U}]
                    [HasFunProp U U U] where
(defConstFunPi {B : U} (φ : B ⟶ ⌊U⌋) :
   Π{λ b => HasConstFun.constProp.invFun b B • HasConstFun.constFun (φ b) b ◅}
    (φ {⟶} {[B] B}))

namespace HasConstFunPi

  variable {U UpU : Universe} [HasTypeIdentity U] [HasFunctors U {U} UpU]
           [HasDependentFunctors U U U] [HasConstFun U U] [HasConstFun U {U}]
           [HasFunProp U U U] [HasConstFunPi U] 

  @[reducible] def constFunPi {B : U} (φ : B ⟶ ⌊U⌋) : Π (φ {⟶} {[B] B}) := defConstFunPi φ

end HasConstFunPi



class HasPiRevAppFun (U V : Universe) {UpV UV UVV : Universe} [HasIdentity V]
                     [HasFunctors U {V} UpV] [HasDependentFunctors U V UV]
                     [HasFunctors UV V UVV] where
(defRevAppFun {A : U} (a : A) (φ : A ⟶ ⌊V⌋) : (Π φ) ⟶{λ F => F a} (φ a))

namespace HasPiRevAppFun

  open HasCongrArg

  variable {U V UpV UV UVV : Universe} [HasIdentity V] [HasFunctors U {V} UpV]
           [HasDependentFunctors U V UV] [HasFunctors UV V UVV] [HasPiRevAppFun U V]

  @[reducible] def revAppFun {A : U} (a : A) (φ : A ⟶ ⌊V⌋) : (Π φ) ⟶ φ a := defRevAppFun a φ

  instance hasDependentCongrFun [HasIdentity UV] [HasCongrArg UV V] : HasDependentCongrFun U V :=
  ⟨λ {A φ F₁ F₂} h a => defCongrArg (defRevAppFun a φ) h⟩

end HasPiRevAppFun

class HasPiRevAppFunPi (U V : Universe) {UpV : Universe} [HasTypeIdentity V] [HasFunctors U {V} UpV]
                       [HasDependentFunctors U V V] [HasFunProp U V V] [HasConstFun U {V}] extends
  HasPiRevAppFun U V where
(defRevAppFunPi {A : U} (φ : A ⟶ ⌊V⌋) :
   Π{λ a => HasPiRevAppFun.revAppFun a φ • HasConstFun.constProp.toFun a (Π φ) ◅}
    ({[A] Π φ} {⟶} φ))

namespace HasPiRevAppFunPi

  variable {U V UpV : Universe} [HasTypeIdentity V] [HasFunctors U {V} UpV]
           [HasDependentFunctors U V V] [HasFunProp U V V] [HasConstFun U {V}]
           [HasPiRevAppFunPi U V]

  @[reducible] def revAppFunPi {A : U} (φ : A ⟶ ⌊V⌋) : Π ({[A] Π φ} {⟶} φ) := defRevAppFunPi φ

end HasPiRevAppFunPi



class HasDupPi (U V : Universe) {UpV UV UUV : Universe} [HasIdentity V]
               [HasFunctors U {V} UpV] [HasDependentFunctors U V UV] [HasFunctors U UV UUV] where
(defDupPi {A : U} {φ : A ⟶ ⌊V⌋} (F : A ⟶ Π φ) : Π{λ a => F a a} φ)

namespace HasDupPi

  variable {U V UpV UV UUV : Universe} [HasIdentity V] [HasFunctors U {V} UpV]
           [HasDependentFunctors U V UV] [HasFunctors U UV UUV] [HasDupPi U V]

  @[reducible] def dupPi {A : U} {φ : A ⟶ ⌊V⌋} (F : A ⟶ Π φ) : Π φ := defDupPi F

end HasDupPi

class HasDupPiFun (U V : Universe) {UpV : Universe} [HasIdentity U] [HasIdentity V]
                  [HasFunctors U {V} UpV] [HasDependentFunctors U V U]
                  [HasInternalFunctors U] extends
  HasDupPi U V where
(defDupPiFun {A : U} (φ : A ⟶ ⌊V⌋) : (A ⟶ Π φ) ⟶{λ F => defDupPi F} (Π φ))

namespace HasDupPiFun

  variable {U V UpV : Universe} [HasIdentity U] [HasIdentity V] [HasFunctors U {V} UpV]
           [HasDependentFunctors U V U] [HasInternalFunctors U] [HasDupPiFun U V]

  @[reducible] def dupPiFun {A : U} (φ : A ⟶ ⌊V⌋) : (A ⟶ Π φ) ⟶ Π φ := defDupPiFun φ

end HasDupPiFun
