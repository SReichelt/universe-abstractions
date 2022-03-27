import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.TypeConstructors
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

  open MetaRelation HasFunctors

  notation:20 "Π " φ:21 => HasDependentFunctors.Pi φ

  instance coeFun {U V UpV UV : Universe} [HasFunctors U {V} UpV] [HasDependentFunctors U V UV]
                  {A : U} (φ : A ⟶ ⌊V⌋) :
    CoeFun ⌈Π φ⌉ (λ _ => HasFunctors.Pi φ) :=
  ⟨apply⟩

  variable {U V UpV UV : Universe} [HasFunctors U {V} UpV] [HasDependentFunctors U V UV]
           [HasTypeIdentity V]

  structure DefPi [HasTypeIdentity V] {A : U} {p : A → V} (φ : A ⟶{p} ⌊V⌋) (f : ∀ a, p a) where
  (F           : Π (fromDefFun φ))
  (eff (a : A) : F a ≃[φ.eff a] f a)

  notation:20 "Π{" f:0 "} " φ:21 => HasDependentFunctors.DefPi φ f

  variable {A : U}

  def toDefPi' {p : A → V} {φ : A ⟶ ⌊V⌋} (F : Π φ) {f : ∀ a, p a} (hφ : ∀ a, φ a ≃ ⸤p a⸥)
               (hF : ∀ a, F a ≃[hφ a] f a) :
    Π{f} (toDefFun' φ hφ) :=
  ⟨F, hF⟩

  def toDefPi               {φ : A ⟶ ⌊V⌋}                   (F : Π    φ) : Π{apply F} (toDefFun   φ) :=
  toDefPi' F (λ a => HasRefl.refl (φ a)) (λ a => DependentEquivalence.refl (F a))
  def fromDefPi {p : A → V} {φ : A ⟶{p} ⌊V⌋} {f : ∀ a, p a} (F : Π{f} φ) : Π          (fromDefFun φ) :=
  F.F

  def byDefPi {p : A → V} {φ : A ⟶{p} ⌊V⌋} {f : ∀ a, p a} {F : Π{f} φ} {a : A} :
    (fromDefPi F) a ≃[φ.eff a] f a :=
  F.eff a

  @[simp] theorem fromToDefPi' {p : A → V} {φ : A ⟶ ⌊V⌋} (F : Π φ) {f : ∀ a, p a}
                               (hφ : ∀ a, φ a ≃ ⸤p a⸥) (hF : ∀ a, F a ≃[hφ a] f a) :
    fromDefPi (toDefPi' F hφ hF) = F :=
  rfl
  @[simp] theorem fromToDefPi {φ : A ⟶ ⌊V⌋} (F : Π φ) : fromDefPi (toDefPi F) = F := rfl

  --@[simp] theorem toFromDefPi' {p : A → V} {φ : A ⟶{p} ⌊V⌋} {f : ∀ a, p a} (F : Π{f} φ) :
  --  toFromDefFun' φ ▸ toDefPi' (fromDefPi F) φ.eff F.eff = F :=
  --sorry

  instance             {φ : A ⟶ ⌊V⌋}    (F : Π φ)      : CoeDep (Π    φ) F (Π{apply F} (toDefFun   φ)) := ⟨toDefPi F⟩
  instance {p : A → V} {φ : A ⟶{p} ⌊V⌋} {f : ∀ a, p a} : Coe    (Π{f} φ)   (Π          (fromDefFun φ)) := ⟨fromDefPi⟩

  def castDefPi {p : A → V} {φ : A ⟶{p} ⌊V⌋} {f f' : ∀ a, p a} (F : Π{f} φ) (h : ∀ a, f a ≃ f' a) : Π{f'} φ :=
  ⟨F.F, λ a => h a • F.eff a⟩

  @[simp] theorem fromCastDefPi {p : A → V} {φ : A ⟶{p} ⌊V⌋} {f f' : ∀ a, p a} (F : Π{f} φ) (h : ∀ a, f a ≃ f' a) :
    fromDefPi (castDefPi F h) = fromDefPi F :=
  rfl

end HasDependentFunctors



class HasDependentCongrArg (U : Universe.{u}) (V : Universe.{v}) {UpV : Universe.{upv}}
                           [HasFunctors U {V} UpV] {UV : Universe.{uv}} [HasDependentFunctors U V UV]
                           [HasIdentity U] [HasTypeIdentity V] [HasPropCongrArg U V] where
(piCongrArg {A : U} {φ : A ⟶ ⌊V⌋} (F : Π φ) {a₁ a₂ : A} (e : a₁ ≃ a₂) :
   F a₁ ≃[HasPropCongrArg.propCongrArg φ e] F a₂)

namespace HasDependentCongrArg

  open HasFunctors HasEquivalences DependentEquivalence HasTypeIdentity HasPropCongrArg HasDependentFunctors

  variable {U V UpV UV : Universe} [HasFunctors U {V} UpV] [HasDependentFunctors U V UV]
           [HasIdentity U] [HasTypeIdentity V] [HasPropCongrArg U V] [HasDependentCongrArg U V]

  def defPiCongrArg {A : U} {p : A → V} {φ : A ⟶{p} ⌊V⌋} {f : ∀ a, p a} (F : Π{f} φ) {a₁ a₂ : A}
                    (e : a₁ ≃ a₂) :
    f a₁ ≃[defPropCongrArg φ e] f a₂ :=
  byDefPi [•] piCongrArg (fromDefPi F) e [•] byDefPi[⁻¹]

  def byPiArgDef {X XU : Universe} [HasFunctors X U XU] {A : X} {B : U} {φ : B ⟶ ⌊V⌋}
               {f : A → B} {F : A ⟶{f} B} {G : Π φ} {a : A} :
    G ((fromDefFun F) a) ≃[propCongrArg φ byDef] G (f a) :=
  piCongrArg G byDef

end HasDependentCongrArg

class HasDependentCongrFun (U : Universe.{u}) (V : Universe.{v}) {UpV : Universe.{upv}}
                           [HasFunctors U {V} UpV] {UV : Universe.{uv}} [HasDependentFunctors U V UV]
                           [HasIdentity UV] [HasIdentity V] where
(piCongrFun {A : U} {φ : A ⟶ ⌊V⌋} {F₁ F₂ : Π φ} (h : F₁ ≃ F₂) (a : A) : F₁ a ≃ F₂ a)

namespace HasDependentCongrFun

  open HasCongrArg HasEquivalences HasDependentFunctors

  variable {U V UpV UV : Universe} [HasFunctors U {V} UpV] [HasDependentFunctors U V UV]
           [HasIdentity UV] [HasTypeIdentity V] [HasDependentCongrFun U V]

  def defCongrFun {A : U} {p : A → V} {φ : A ⟶{p} ⌊V⌋} {f₁ f₂ : ∀ a, p a} {F₁ : Π{f₁} φ} {F₂ : Π{f₂} φ}
                  (h : fromDefPi F₁ ≃ fromDefPi F₂) (a : A) :
    f₁ a ≃ f₂ a :=
  byDefPi • congrArg (toFun (φ.eff a)) (piCongrFun h a) • byDefPi⁻¹

end HasDependentCongrFun



namespace HasFunctors

  open HasLeftTypeFun HasCongrArg

  variable (U : Universe) {V W UV UVW UtUV UtUVW UVtUVW : Universe}
           [h₁ : HasFunctors U V UV] [h₂ : HasFunctors UV W UVW]
           [HasFunctors {U} {UV} UtUV] [HasFunctors {U} {UVW} UtUVW] [HasFunctors {UV} {UVW} UVtUVW]
           [HasIdentity {U}] [HasIdentity {UV}] [HasIdentity {UVW}]
           [HasLeftTypeFun h₁.Fun] [HasLeftTypeFun h₂.Fun]
           [HasCompFun {U} {UV} {UVW}] [HasCongrArg {UV} {UVW}]

  def defDependentTypeProp (B : V) (C : W) : ⌊U⌋ ⟶{λ A => (A ⟶ B) ⟶ C} ⌊UVW⌋ :=
  revTypeFun h₂.Fun C ⊙ revTypeFun h₁.Fun B
  ◄ byDefDef

  @[reducible] def dependentTypeProp (B : V) (C : W) : ⌊U⌋ ⟶ ⌊UVW⌋ :=
  defDependentTypeProp U B C

end HasFunctors



class HasDependentTypeFun {U V W UpV UpVtW : Universe} [HasFunctors U {V} UpV]
                          [HasFunctors UpV {W} UpVtW] [HasIdentity {W}]
                          (T : ∀ {A : U}, (A ⟶ ⌊V⌋) → W) where
(defTypeFun (A : U) : (A ⟶ ⌊V⌋) ⟶{T} ⌊W⌋)

namespace HasDependentTypeFun

  open HasFunctors HasCongrArg HasTypeIdentity

  variable {U V W UpV UpVtW : Universe} [HasFunctors U {V} UpV]
           (T : ∀ {A : U}, (A ⟶ ⌊V⌋) → W) [HasFunctors UpV {W} UpVtW]

  @[reducible] def typeFun [HasIdentity {W}] [h : HasDependentTypeFun T] (A : U) :
    (A ⟶ ⌊V⌋) ⟶ ⌊W⌋ :=
  h.defTypeFun A

  variable [HasIdentity UpV] [HasTypeIdentity W] [h : HasDependentTypeFun T]
           [HasCongrArg UpV {W}]

  def castInstPropTo  {A : U} {φ₁ φ₂ : A ⟶ ⌊V⌋} (E : φ₁ ≃ φ₂) (F : T φ₁) : T φ₂ :=
  castTo  (defCongrArg (h.defTypeFun A) E) F
  def castInstPropInv {A : U} {φ₁ φ₂ : A ⟶ ⌊V⌋} (E : φ₁ ≃ φ₂) (F : T φ₂) : T φ₁ :=
  castInv (defCongrArg (h.defTypeFun A) E) F

end HasDependentTypeFun

class HasDependentTypeFunPi {U V W UpV UpVtW UtUpVtW UpVtUpVtW UtUpV : Universe}
                            [h₁ : HasFunctors U {V} UpV] [h₂ : HasFunctors UpV {W} UpVtW] [HasIdentity {W}]
                            [HasFunctors {U} {UpVtW} UtUpVtW] [HasDependentFunctors {U} UpVtW UtUpVtW]
                            [HasFunctors {UpV} {UpVtW} UpVtUpVtW] [HasTypeIdentity UpVtW]
                            [HasFunctors {U} {UpV} UtUpV] [HasIdentity {UpV}] [HasPropCongrArg {UpV} UpVtW]
                            [HasLeftTypeFun h₁.Fun] [HasLeftTypeFun h₂.Fun] [HasCompFun {U} {UpV} {UpVtW}]
                            (T : ∀ {A : U}, (A ⟶ ⌊V⌋) → W) extends
  HasDependentTypeFun T where
(defTypeFunPi : Π{λ A => defTypeFun A} (HasFunctors.defDependentTypeProp U ⌊V⌋ ⌊W⌋))

namespace HasDependentTypeFunPi

  open HasFunctors HasCongrFun HasEquivalences HasTypeIdentity HasPropCongrArg HasDependentCongrArg HasDependentTypeFun

  variable {U V W UpV UpVtW UtUpVtW UpVtUpVtW UtUpV : Universe}
           [h₁ : HasFunctors U {V} UpV] [h₂ : HasFunctors UpV {W} UpVtW]
           [HasFunctors {U} {UpVtW} UtUpVtW] [HasDependentFunctors {U} UpVtW UtUpVtW]
           [HasFunctors {UpV} {UpVtW} UpVtUpVtW] [HasTypeIdentity UpVtW]
           [HasFunctors {U} {UpV} UtUpV] [HasTypeIdentity UpV] [HasPropCongrArg {UpV} UpVtW]
           [HasLeftTypeFun h₁.Fun] [HasLeftTypeFun h₂.Fun] [HasCompFun {U} {UpV} {UpVtW}]
           (T : ∀ {A : U}, (A ⟶ ⌊V⌋) → W)

  variable [HasTypeIdentity U] [HasIdentity {V}] [HasTypeIdentity W] [h : HasDependentTypeFunPi T]
           [HasCompFun U U {V}] [HasPropCongrArg {U} UpVtW] [HasDependentCongrArg {U} UpVtW]
           [HasCongrArg {U} {UpV}] [HasCongrFun UpV {W}]

  -- TODO: Can we prove this with `HasPropCongrArg` now?
  def baseEquiv {A₁ A₂ : U} {φ : A₁ ⟶ ⌊V⌋} (E : A₁ ⟷ A₂) : T φ ⟷ T (φ ⊙ invFun E) :=
  let H₁ : ((A₁ ⟶ ⌊V⌋) ⟶ ⌊W⌋) ⟷ ((A₂ ⟶ ⌊V⌋) ⟶ ⌊W⌋) := defPropCongrArg (defDependentTypeProp U ⌊V⌋ ⌊W⌋) E;
  let H₂ : typeFun T A₁ ≃[H₁] typeFun T A₂ := defPiCongrArg h.defTypeFunPi E;
  let H₃ : typeFun T A₁ ≃ inv H₁ (typeFun T A₂) := HasEquivalences.toInv H₂;
  let H₄ := congrFun H₃ φ • byDef⁻¹;
  let H₅ : T φ ⟷ (inv H₁ (typeFun T A₂)) φ := H₄;
  -- TODO (outdated?): To prove this, we need to construct type functors explicitly instead of asserting them as variables.
  let H₆ : HasLeftTypeFun.castInstTo h₁.Fun E φ ≃ φ ⊙ invFun E := sorry;
  let H₉ : T φ ⟷ T (φ ⊙ invFun E) := sorry;
  H₉

  def castInstBaseTo  {A₁ A₂ : U} {φ : A₁ ⟶ ⌊V⌋} (E : ⸤A₁⸥ ≃ ⸤A₂⸥) (F : T φ) : T (φ ⊙ invFun E) :=
  to (baseEquiv T E) F
  def castInstBaseInv {A₁ A₂ : U} {φ : A₂ ⟶ ⌊V⌋} (E : ⸤A₁⸥ ≃ ⸤A₂⸥) (F : T φ) : T (φ ⊙ toFun  E) :=
  sorry --to (baseEquiv T E⁻¹) F

end HasDependentTypeFunPi



namespace HasDependentFunctors

  open HasFunctors HasCongrArg HasDependentTypeFun

  section

    variable {U V W VpW UVpW VW UpVW VpWpVW : Universe} [HasFunctors V {W} VpW]
             [HasFunctors U VpW UVpW] [h : HasDependentFunctors V W VW] [HasIdentity {VW}]
             [HasFunctors U {VW} UpVW] [HasFunctors VpW {VW} VpWpVW]
             [HasDependentTypeFun h.Pi] [HasCompFun U VpW {VW}]

    def defPiProp {A : U} {B : V} (φ : A ⟶ B ⟶ ⌊W⌋) : A ⟶{λ a => Π (φ a)} ⌊VW⌋ :=
    typeFun h.Pi B ⊙ φ
    ◄ byDef

    @[reducible] def piProp {A : U} {B : V} (φ : A ⟶ B ⟶ ⌊W⌋) : A ⟶ ⌊VW⌋ := defPiProp φ
    notation:20 "{Π} " φ:21 => HasDependentFunctors.piProp φ

  end

  section

    variable {U W : Universe} {UpW UpWpW : Universe} [HasFunctors U U U] [HasFunctors U {W} UpW]
             [h : HasDependentFunctors U W W] [HasIdentity {W}] [HasFunctors U UpW UpW]
             [HasFunctors UpW {W} UpWpW] [HasIdentity UpW] [HasCongrArg UpW {W}]
             [HasDependentTypeFun h.Pi] [HasRevCompFunFun U {W}] [HasCompFun U UpW {W}]

    def defPiCompFunProp (A : U) {B : U} (φ : B ⟶ ⌊W⌋) : (A ⟶ B) ⟶{λ F => Π (φ ⊙ F)} ⌊W⌋ :=
    typeFun h.Pi A ⊙ HasRevCompFunFun.revCompFunFun A φ
    ◄ byDefDef

    @[reducible] def piCompFunProp (A : U) {B : U} (φ : B ⟶ ⌊W⌋) : (A ⟶ B) ⟶ ⌊W⌋ := defPiCompFunProp A φ

  end

end HasDependentFunctors



-- TODO: Most of these definitions probably need to be moved further into the dependent realm.
-- Or maybe define a dependent S combinator only?

class HasCompFunPi (U V W : Universe) {UV VpW VW UpW UW : Universe} [HasFunctors U V UV]
                   [HasFunctors V {W} VpW] [HasDependentFunctors V W VW]
                   [HasFunctors U {W} UpW] [HasDependentFunctors U W UW]
                   [HasTypeIdentity W] [HasCompFun U V {W}] where
(defCompFunPi {A : U} {B : V} {φ : B ⟶ ⌊W⌋} (F : A ⟶ B) (G : Π φ) : Π{λ a => G (F a)} HasCompFun.defCompFun F φ)

namespace HasCompFunPi

  variable {U V W UV VpW VW UpW UW : Universe} [HasFunctors U V UV] [HasFunctors V {W} VpW]
           [HasDependentFunctors V W VW] [HasFunctors U {W} UpW] [HasDependentFunctors U W UW]
           [HasTypeIdentity W] [HasCompFun U V {W}] [HasCompFunPi U V W]

  @[reducible] def compFunPi {A : U} {B : V} {φ : B ⟶ ⌊W⌋} (F : A ⟶ B) (G : Π φ) :
    Π (φ ⊙ F) :=
  defCompFunPi F G

end HasCompFunPi

class HasRevCompFunPiPi (U W : Universe) {UpW UpWpW : Universe} [HasTypeIdentity W] [HasFunctors U U U]
                        [HasFunctors U {W} UpW] [h : HasDependentFunctors U W W]
                        [HasFunctors U UpW UpW] [HasIdentity UpW] [HasFunctors UpW {W} UpWpW]
                        [HasCongrArg UpW {W}] [HasCompFun U UpW {⌈W⌉}]
                        [HasDependentTypeFun h.Pi] [HasRevCompFunFun U {W}] extends
  HasCompFunPi U U W where
(defRevCompFunPiPi (A : U) {B : U} {φ : B ⟶ ⌊W⌋} (G : Π φ) :
   Π{λ F => HasCompFunPi.compFunPi F G} HasDependentFunctors.defPiCompFunProp A φ)
(defRevCompFunPiPiFun (A : U) {B : U} (φ : B ⟶ ⌊W⌋) :
   (Π φ) ⟶{λ G => defRevCompFunPiPi A G} (Π HasDependentFunctors.piCompFunProp A φ))

namespace HasRevCompFunPiPi

  variable {U W UpW UpWpW : Universe} [HasTypeIdentity W] [HasFunctors U U U] [HasFunctors U {W} UpW]
           [h : HasDependentFunctors U W W] [HasFunctors U UpW UpW] [HasIdentity UpW]
           [HasFunctors UpW {W} UpWpW] [HasCongrArg UpW {W}] [HasCompFun U UpW {⌈W⌉}]
           [HasDependentTypeFun h.Pi] [HasRevCompFunFun U {W}] [HasRevCompFunPiPi U W]

  @[reducible] def revCompFunPiPi (A : U) {B : U} {φ : B ⟶ ⌊W⌋} (G : Π φ) :
    Π HasDependentFunctors.piCompFunProp A φ :=
  defRevCompFunPiPi A G

  @[reducible] def revCompFunPiPiFun (A : U) {B : U} (φ : B ⟶ ⌊W⌋) :
    (Π φ) ⟶ Π HasDependentFunctors.piCompFunProp A φ :=
  defRevCompFunPiPiFun A φ

  -- TODO: Derive these.
  --def defCompFunPiFun {A B : U} (F : A ⟶ B) (φ : B ⟶ ⌊W⌋) :
  --  (Π φ) ⟶{λ G => HasCompFunPi.compFunPi F G} (Π (φ ⊙ F)) :=
  --sorry

  --def defCompFunPiFunPi {WtW : Universe} [HasFunctors {W} {W} WtW] [HasRightTypeFun HasFunctors.Fun]
  --                      [HasCompFun U {W} {W}] (A : U) {B : U} (φ : B ⟶ ⌊W⌋) :
  --  Π{λ F => defCompFunPiFun F φ} ({Π φ ⟶} HasDependentFunctors.piCompFunProp A φ) :=
  --sorry

end HasRevCompFunPiPi



class HasConstFunPi (U : Universe) {UpU UtU : Universe} [h : HasTypeIdentity U]
                    [HasFunctors U {U} UpU] [HasDependentFunctors U U U] [HasConstFun U U]
                    [HasFunctors {U} {U} UtU] [HasLeftTypeFun h.hasInternalFunctors.Fun]
                    [HasCompFun U {U} {U}] where
(defConstFunPi {B : U} (φ : B ⟶ ⌊U⌋) : Π{λ b => HasConstFun.constFun (φ b) b} (HasFunctors.defLeftFunProp φ B))

namespace HasConstFunPi

  variable {U UpU UtU : Universe} [h : HasTypeIdentity U] [HasFunctors U {U} UpU]
           [HasDependentFunctors U U U] [HasConstFun U U] [HasFunctors {U} {U} UtU]
           [HasLeftTypeFun h.hasInternalFunctors.Fun] [HasCompFun U {U} {U}]
           [HasConstFunPi U]

  @[reducible] def constFunPi {B : U} (φ : B ⟶ ⌊U⌋) : Π (φ {⟶ B}) := defConstFunPi φ

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

class HasPiRevAppFunPi (U V : Universe) {UpV VtV : Universe} [h : HasTypeIdentity V]
                       [HasFunctors U {V} UpV] [HasDependentFunctors U V V] [HasFunctors {V} {V} VtV]
                       [HasRightTypeFun h.hasInternalFunctors.Fun] [HasCompFun U {V} {V}] extends
  HasPiRevAppFun U V where
(defRevAppFunPi {A : U} (φ : A ⟶ ⌊V⌋) : Π{λ a => HasPiRevAppFun.revAppFun a φ} (HasFunctors.defRightFunProp (Π φ) φ))

namespace HasPiRevAppFunPi

  variable {U V UpV VtV : Universe} [h : HasTypeIdentity V] [HasFunctors U {V} UpV]
           [HasDependentFunctors U V V] [HasFunctors {V} {V} VtV]
           [HasRightTypeFun h.hasInternalFunctors.Fun] [HasCompFun U {V} {V}]
           [HasPiRevAppFunPi U V]

  @[reducible] def revAppFunPi {A : U} (φ : A ⟶ ⌊V⌋) : Π ({Π φ ⟶} φ) := defRevAppFunPi φ

end HasPiRevAppFunPi



class HasDupPi (U V : Universe) {UpV UV UUV : Universe} [HasTypeIdentity V]
               [HasFunctors U {V} UpV] [HasDependentFunctors U V UV] [HasFunctors U UV UUV] where
(defDupPi {A : U} {φ : A ⟶ ⌊V⌋} (F : A ⟶ Π φ) : Π{λ a => F a a} (HasFunctors.toDefFun φ))

namespace HasDupPi

  open HasDependentFunctors

  variable {U V UpV UV UUV : Universe} [HasTypeIdentity V] [HasFunctors U {V} UpV]
           [HasDependentFunctors U V UV] [HasFunctors U UV UUV] [HasDupPi U V]

  @[reducible] def dupPi {A : U} {φ : A ⟶ ⌊V⌋} (F : A ⟶ Π φ) : Π φ := fromDefPi (defDupPi F)

end HasDupPi

class HasDupPiFun (U V : Universe) {UpV : Universe} [HasIdentity U] [HasTypeIdentity V]
                  [HasFunctors U {V} UpV] [HasDependentFunctors U V U]
                  [HasInternalFunctors U] extends
  HasDupPi U V where
(defDupPiFun {A : U} (φ : A ⟶ ⌊V⌋) : (A ⟶ Π φ) ⟶{λ F => HasDependentFunctors.fromDefPi (defDupPi F)} (Π φ))

namespace HasDupPiFun

  variable {U V UpV : Universe} [HasIdentity U] [HasTypeIdentity V] [HasFunctors U {V} UpV]
           [HasDependentFunctors U V U] [HasInternalFunctors U] [HasDupPiFun U V]

  @[reducible] def dupPiFun {A : U} (φ : A ⟶ ⌊V⌋) : (A ⟶ Π φ) ⟶ Π φ := defDupPiFun φ

end HasDupPiFun
