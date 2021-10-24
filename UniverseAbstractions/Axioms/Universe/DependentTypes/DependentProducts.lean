import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences
import UniverseAbstractions.Axioms.Universe.DependentTypes.Properties
import UniverseAbstractions.Axioms.Universe.DependentTypes.DependentFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v upv uv



class HasDependentProducts (U : Universe.{u}) (V : Universe.{v}) {UpV : Universe.{upv}}
                           [HasFunctors U {V} UpV] (UxV : outParam Universe.{uv}) where
(Sigma {A : U} (φ : A ⟶ ⌊V⌋)                       : UxV)
(intro {A : U} {φ : A ⟶ ⌊V⌋} (a : A) (b : ⌈⸥φ a⸤⌉) : Sigma φ)
(fst   {A : U} {φ : A ⟶ ⌊V⌋} (P : Sigma φ)         : A)
(snd   {A : U} {φ : A ⟶ ⌊V⌋} (P : Sigma φ)         : φ (fst P))

namespace HasDependentProducts

  open HasFunctors HasCongrArg

  notation:20 "Σ " φ:21 => HasDependentProducts.Sigma φ
  
  class HasDependentProductEq (U : Universe.{u}) (V : Universe.{v}) {UpV : Universe.{upv}}
                              [HasFunctors U {V} UpV] {UxV : Universe.{uv}}
                              [HasDependentProducts U V UxV] [HasIdentity U]
                              [HasTypeIdentity V] [HasCongrArg U {V}] [HasIdentity UxV] where
  (introEq {A : U} {φ : A ⟶ ⌊V⌋} (P : Σ φ)             : intro (fst P) (snd P) ≃ P)
  (fstEq   {A : U} {φ : A ⟶ ⌊V⌋} (a : A) (b : ⌈⸥φ a⸤⌉) : fst (intro a b) ≃ a)
  (sndEq   {A : U} {φ : A ⟶ ⌊V⌋} (a : A) (b : ⌈⸥φ a⸤⌉) : snd (intro a b) ≃[propCongrArg φ (fstEq a b)] b)

end HasDependentProducts



class HasFunctorialSigmaConstructor (U V : Universe) {UpV UV UpVpUV : Universe}
                                    [HasFunctors U {V} UpV] [HasDependentProducts U V UV]
                                    [HasFunctors UpV {UV} UpVpUV] [HasIdentity {UV}] where
(defSigmaFun (A : U) : (A ⟶ ⌊V⌋) ⟶{λ φ => Σ φ} ⌊UV⌋)

namespace HasFunctorialSigmaConstructor

  open HasFunctors HasCongrArg HasTypeIdentity

  section

    variable {U V UpV UV UpVpUV : Universe} [HasFunctors U {V} UpV] [HasDependentProducts U V UV]
             [HasFunctors UpV {UV} UpVpUV]

    @[reducible] def sigmaFun [HasIdentity {UV}] [HasFunctorialSigmaConstructor U V] (A : U) :
      (A ⟶ ⌊V⌋) ⟶ ⌊UV⌋ :=
    fromDefFun (defSigmaFun A)

    variable [HasIdentity UpV] [HasTypeIdentity UV] [HasFunctorialSigmaConstructor U V]
             [HasCongrArg UpV {UV}]

    def castSigmaTo  {A : U} {φ₁ φ₂ : A ⟶ ⌊V⌋} (E : φ₁ ≃ φ₂) (F : Σ φ₁) : Σ φ₂ :=
    castTo  (defCongrArg (defSigmaFun A) E) F
    def castSigmaInv {A : U} {φ₁ φ₂ : A ⟶ ⌊V⌋} (E : φ₁ ≃ φ₂) (F : Σ φ₂) : Σ φ₁ :=
    castInv (defCongrArg (defSigmaFun A) E) F

  end

  section

    variable {U V W VpW UVpW VW UpVW VpWpVW : Universe} [HasFunctors V {W} VpW]
             [HasFunctors U VpW UVpW] [HasDependentProducts V W VW] [HasIdentity {VW}]
             [HasFunctors U {VW} UpVW] [HasFunctors VpW {VW} VpWpVW]
             [HasFunctorialSigmaConstructor V W] [HasCompFun U VpW {VW}]

    def defSigmaProp {A : U} {B : V} (φ : A ⟶ B ⟶ ⌊W⌋) : A ⟶{λ a => Σ (φ a)} ⌊VW⌋ :=
    sigmaFun B ⊙ φ
    ◄ byDef

    @[reducible] def sigmaProp {A : U} {B : V} (φ : A ⟶ B ⟶ ⌊W⌋) : A ⟶ ⌊VW⌋ := defSigmaProp φ
    notation:20 "{Σ} " φ:21 => HasFunctorialSigmaConstructor.sigmaProp φ

  end

end HasFunctorialSigmaConstructor



class HasInternalDependentProducts (U : Universe.{u}) (V : Universe.{v}) {UpV : Universe.{upv}}
                                   [HasTypeIdentity V] [HasFunctors U {V} UpV] [HasConstFun U {V}]
                                   [HasDependentFunctors U V V] [HasFunProp U V V]
  extends HasDependentProducts U V V where
(defIntroFun   {A : U} (φ : A ⟶ ⌊V⌋) (a : A) :
   φ a ⟶{λ b => HasDependentProducts.intro a b} (Σ φ))
(defIntroFunPi {A : U} (φ : A ⟶ ⌊V⌋) :
   Π{λ a => HasConstFun.constProp.invFun a (Σ φ) • HasFunctors.fromDefFun (defIntroFun φ a) ◅}
    (φ {⟶} {[A] Σ φ}))
(defElimFun    {A : U} {φ : A ⟶ ⌊V⌋} {C : V} (F : Π (φ {⟶} {[A] C})) :
   (Σ φ)
   ⟶{λ P => HasFunctors.apply (HasConstFun.constProp.toFun (HasDependentProducts.fst P) C •
                               HasTypeIdentity.castTo (A := (φ {⟶} {[A] C}) (HasDependentProducts.fst P))
                                                      HasFunctors.byDef
                                                      (F (HasDependentProducts.fst P)))
                              (HasDependentProducts.snd P)}
   C)
(defElimFunFun {A : U} (φ : A ⟶ ⌊V⌋) (C : V) :
   (Π (φ {⟶} {[A] C})) ⟶{λ F => defElimFun F} ((Σ φ) ⟶ C))

namespace HasInternalDependentProducts

  variable {U V UpV : Universe} [HasTypeIdentity V] [HasFunctors U {V} UpV] [HasConstFun U {V}]
           [HasDependentFunctors U V V] [HasFunProp U V V] [HasInternalDependentProducts U V]

  @[reducible] def introFun {A : U} (φ : A ⟶ ⌊V⌋) (a : A) : φ a ⟶ Σ φ := defIntroFun φ a
  @[reducible] def introFunPi {A : U} (φ : A ⟶ ⌊V⌋) : Π (φ {⟶} {[A] Σ φ}) := defIntroFunPi φ
  @[reducible] def elimFun {A : U} {φ : A ⟶ ⌊V⌋} {C : V} (F : Π (φ {⟶} {[A] C})) : (Σ φ) ⟶ C := defElimFun F
  @[reducible] def elimFunFun {A : U} (φ : A ⟶ ⌊V⌋) (C : V) : (Π (φ {⟶} {[A] C})) ⟶ ((Σ φ) ⟶ C) := defElimFunFun φ C

end HasInternalDependentProducts



-- TODO: extensionality
