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

  open HasPropCongrArg

  notation:20 "Σ " φ:21 => HasDependentProducts.Sigma φ
  
  class HasDependentProductEq (U : Universe.{u}) (V : Universe.{v}) {UpV : Universe.{upv}}
                              [HasFunctors U {V} UpV] {UxV : Universe.{uv}}
                              [HasDependentProducts U V UxV] [HasIdentity U]
                              [HasTypeIdentity V] [HasPropCongrArg U V] [HasIdentity UxV] where
  (introEq {A : U} {φ : A ⟶ ⌊V⌋} (P : Σ φ)             : intro (fst P) (snd P) ≃ P)
  (fstEq   {A : U} {φ : A ⟶ ⌊V⌋} (a : A) (b : ⌈⸥φ a⸤⌉) : fst (intro a b) ≃ a)
  (sndEq   {A : U} {φ : A ⟶ ⌊V⌋} (a : A) (b : ⌈⸥φ a⸤⌉) : snd (intro a b) ≃[propCongrArg φ (fstEq a b)] b)

end HasDependentProducts



namespace HasDependentProducts

  open HasFunctors HasCongrArg HasDependentTypeFun

  section

    variable {U V W VpW UVpW VW UpVW VpWpVW : Universe} [HasFunctors V {W} VpW]
             [HasFunctors U VpW UVpW] [h : HasDependentProducts V W VW] [HasIdentity {VW}]
             [HasFunctors U {VW} UpVW] [HasFunctors VpW {VW} VpWpVW]
             [HasDependentTypeFun h.Sigma] [HasCompFun U VpW {VW}]

    def defSigmaProp {A : U} {B : V} (φ : A ⟶ B ⟶ ⌊W⌋) : A ⟶{λ a => Σ (φ a)} ⌊VW⌋ :=
    typeFun h.Sigma B ⊙ φ
    ◄ byDef

    @[reducible] def sigmaProp {A : U} {B : V} (φ : A ⟶ B ⟶ ⌊W⌋) : A ⟶ ⌊VW⌋ := defSigmaProp φ
    notation:20 "{Σ} " φ:21 => HasDependentProducts.sigmaProp φ

  end

  section

    variable {U W : Universe} {UpW UpWpW : Universe} [HasFunctors U U U] [HasFunctors U {W} UpW]
             [h : HasDependentProducts U W W] [HasIdentity {W}] [HasFunctors U UpW UpW]
             [HasFunctors UpW {W} UpWpW] [HasIdentity UpW] [HasCongrArg UpW {W}]
             [HasDependentTypeFun h.Sigma] [HasRevCompFunFun U {W}] [HasCompFun U UpW {W}]

    def defSigmaCompFunProp (A : U) {B : U} (φ : B ⟶ ⌊W⌋) : (A ⟶ B) ⟶{λ F => Σ (φ ⊙ F)} ⌊W⌋ :=
    typeFun h.Sigma A ⊙ HasRevCompFunFun.revCompFunFun A φ
    ◄ byDefDef

    @[reducible] def sigmaCompFunProp (A : U) {B : U} (φ : B ⟶ ⌊W⌋) : (A ⟶ B) ⟶ ⌊W⌋ := defSigmaCompFunProp A φ

  end

end HasDependentProducts



class HasInternalDependentProducts (U : Universe.{u}) (V : Universe.{v}) {UpV VtV : Universe}
                                   [h : HasTypeIdentity V] [HasFunctors U {V} UpV]
                                   [HasDependentFunctors U V V] [HasFunctors {V} {V} VtV]
                                   [HasLeftTypeFun h.hasInternalFunctors.Fun] [HasCompFun U {V} {V}]
  extends HasDependentProducts U V V where
-- TODO: Generic `DefFunPi` type to combine the two `intro`s?
(defIntroFun   {A : U} (φ : A ⟶ ⌊V⌋) (a : A) :
   φ a ⟶{λ b => HasDependentProducts.intro a b} (Σ φ))
(defIntroFunPi {A : U} (φ : A ⟶ ⌊V⌋) :
   Π{λ a => HasFunctors.fromDefFun (defIntroFun φ a)} (HasFunctors.defLeftFunProp φ (Σ φ)))
(defElimFun    {A : U} (φ : A ⟶ ⌊V⌋) (C : V) :
   (Π (φ {⟶ C}))
   ⟶
   (Σ φ)
   ⟶{λ F P => HasFunctors.apply (HasTypeIdentity.castTo (A := (φ {⟶ C}) (HasDependentProducts.fst P))
                                                        HasFunctors.byDef
                                                        (F (HasDependentProducts.fst P)))
                                (HasDependentProducts.snd P)}
   C)

namespace HasInternalDependentProducts

  variable {U V UpV VtV : Universe} [h : HasTypeIdentity V] [HasFunctors U {V} UpV]
           [HasDependentFunctors U V V] [HasFunctors {V} {V} VtV]
           [HasLeftTypeFun h.hasInternalFunctors.Fun] [HasCompFun U {V} {V}]
           [HasInternalDependentProducts U V]

  @[reducible] def introFun {A : U} (φ : A ⟶ ⌊V⌋) (a : A) : φ a ⟶ Σ φ := defIntroFun φ a
  @[reducible] def introFunPi {A : U} (φ : A ⟶ ⌊V⌋) : Π (φ {⟶ Σ φ}) := defIntroFunPi φ
  @[reducible] def elimFun {A : U} {φ : A ⟶ ⌊V⌋} {C : V} (F : Π (φ {⟶ C})) : (Σ φ) ⟶ C := (defElimFun φ C).defFun F
  @[reducible] def elimFunFun {A : U} (φ : A ⟶ ⌊V⌋) (C : V) : (Π (φ {⟶ C})) ⟶ ((Σ φ) ⟶ C) := defElimFun φ C

end HasInternalDependentProducts



-- TODO: extensionality
