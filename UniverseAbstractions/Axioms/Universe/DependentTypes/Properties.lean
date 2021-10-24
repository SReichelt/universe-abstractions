import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v uv



namespace HasFunctors

  open HasTypeIdentity

  variable {U : Universe.{u}} {V : Universe.{v}} {UpV : Universe} [HasFunctors U {V} UpV]
           {A : U} (φ : A ⟶ ⌊V⌋)

  def Pi    : Sort (imax u v)  := ∀  a, ⌈⸥φ a⸤⌉
  def Sigma : Sort (max 1 u v) := Σ' a, ⌈⸥φ a⸤⌉

  def castPiTo  [HasTypeIdentity V] {C : A → V} (f : ∀ a, C a) (h : ∀ a, ⸤C a⸥ ≃ φ a) : Pi φ :=
  λ a => castTo  (h a) (f a)
  def castPiInv [HasTypeIdentity V] {C : A → V} (f : ∀ a, C a) (h : ∀ a, φ a ≃ ⸤C a⸥) : Pi φ :=
  λ a => castInv (h a) (f a)

  class IsUniversal where
  (h : Pi φ)

  class IsInhabited where
  (h : Sigma φ)

end HasFunctors



namespace HasCongrArg

  open HasFunctors

  variable {U V UpV : Universe} [HasFunctors U {V} UpV] [HasIdentity U]
           [HasTypeIdentity V] [HasCongrArg U {V}]

  def propCongrArg {A : U} (φ : A ⟶ ⌊V⌋) {a₁ a₂ : A} (e : a₁ ≃ a₂) : ⸥φ a₁⸤ ⟷ ⸥φ a₂⸤ :=
  congrArg φ e

end HasCongrArg



namespace HasConstFun

  variable {U : Universe.{u}} {V : Universe.{v}} {UpV : Universe} [HasFunctors U {V} UpV]

  def constProp [HasIdentity {V}] [HasConstFun U {V}] (A : U) (B : V) : A ⟶ ⌊V⌋ :=
  constFun A ⸤B⸥
  notation "{[" A:0 "] " B:0 "}" => HasConstFun.constProp A B

  def constProp.eff [HasIdentity {V}] [HasConstFun U {V}] {A : U} (a : A) (B : V) :
    {[A] B} a ≃ ⸤B⸥ :=
  (defConstFun A ⸤B⸥).eff a

  variable [HasTypeIdentity V] [HasConstFun U {V}]

  def constProp.toFun  {A : U} (a : A) (B : V) : {[A] B} a ⟶ B :=
  HasEquivalences.toFun  (constProp.eff a B)
  def constProp.invFun {A : U} (a : A) (B : V) : B ⟶ {[A] B} a :=
  HasEquivalences.invFun (constProp.eff a B)

end HasConstFun



-- TODO: Replace these with functoriality of type constructors (and construct the properties via composition of functors).



class HasFunProp (U V W : Universe) {UpV UpW VW UpVW : Universe}
                 [HasFunctors U {V} UpV] [HasFunctors U {W} UpW] [HasFunctors V W VW]
                 [HasIdentity {VW}] [HasFunctors U {VW} UpVW] where
(defFunProp {A : U} (φ : A ⟶ ⌊V⌋) (ψ : A ⟶ ⌊W⌋) : A ⟶{λ a => φ a ⟶ ψ a} ⌊VW⌋)

namespace HasFunProp

  variable {U V W UpV UpW VW UpVW : Universe} [HasFunctors U {V} UpV] [HasFunctors U {W} UpW]
           [HasFunctors V W VW] [HasIdentity {VW}] [HasFunctors U {VW} UpVW]
           [HasFunProp U V W]

  @[reducible] def funProp {A : U} (φ : A ⟶ ⌊V⌋) (ψ : A ⟶ ⌊W⌋) : A ⟶ ⌊VW⌋ := defFunProp φ ψ
  infixr:20 " {⟶} " => HasFunProp.funProp

end HasFunProp



class HasProdProp (U V W : Universe) {UpV UpW VxW UpVxW : Universe}
                  [HasFunctors U {V} UpV] [HasFunctors U {W} UpW] [HasProducts V W VxW]
                  [HasIdentity {VxW}] [HasFunctors U {VxW} UpVxW] where
(defProdProp {A : U} (φ : A ⟶ ⌊V⌋) (ψ : A ⟶ ⌊W⌋) : A ⟶{λ a => φ a ⊓ ψ a} ⌊VxW⌋)

namespace HasProdProp

  variable {U V W UpV UpW VxW UpVxW : Universe} [HasFunctors U {V} UpV] [HasFunctors U {W} UpW]
           [HasProducts V W VxW] [HasIdentity {VxW}] [HasFunctors U {VxW} UpVxW]
           [HasProdProp U V W]

  @[reducible] def prodProp {A : U} (φ : A ⟶ ⌊V⌋) (ψ : A ⟶ ⌊W⌋) : A ⟶ ⌊VxW⌋ := defProdProp φ ψ
  infixr:35 " {⊓} " => HasProdProp.prodProp

end HasProdProp



class HasEquivProp (U V W : Universe) {UpV UpW VW WV V_W UpV_W : Universe}
                   [HasIdentity V] [HasIdentity W]
                   [HasFunctors U {V} UpV] [HasFunctors U {W} UpW]
                   [HasFunctors V W VW] [HasFunctors W V WV] [HasEquivalences V W V_W]
                   [HasIdentity {V_W}] [HasFunctors U {V_W} UpV_W] where
(defEquivProp {A : U} (φ : A ⟶ ⌊V⌋) (ψ : A ⟶ ⌊W⌋) : A ⟶{λ a => φ a ⟷ ψ a} ⌊V_W⌋)

namespace HasEquivProp

  variable {U V W UpV UpW VW WV V_W UpV_W : Universe} [HasIdentity V] [HasIdentity W]
           [HasFunctors U {V} UpV] [HasFunctors U {W} UpW]
           [HasFunctors V W VW] [HasFunctors W V WV] [HasEquivalences V W V_W]
           [HasIdentity {V_W}] [HasFunctors U {V_W} UpV_W] [HasEquivProp U V W]

  @[reducible] def equivProp {A : U} (φ : A ⟶ ⌊V⌋) (ψ : A ⟶ ⌊W⌋) : A ⟶ ⌊V_W⌋ := defEquivProp φ ψ
  infixr:20 " {⟷} " => HasEquivProp.equivProp

end HasEquivProp
