import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v uv



namespace HasFunctors

  variable {U : Universe.{u}} {V : Universe.{v}} {UpV : Universe} [HasFunctors U {V} UpV]

  def constProp [HasIdentity {V}] [HasConstFun U {V}] (A : U) (B : V) : A ⟶ ⌊V⌋ :=
  HasConstFun.constFun A B
  notation "{[" A:0 "] " B:0 "}" => HasFunctors.constProp A B

  variable {A : U} (φ : A ⟶ ⌊V⌋)

  def propType (a : A) : V := φ a
  notation "⌋" φ "⌊" => HasFunctors.propType φ

  def Pi    : Sort (imax u v)  := ∀  a, ⌋φ⌊ a
  def Sigma : Sort (max 1 u v) := Σ' a, ⌋φ⌊ a

  class IsUniversal where
  (h : Pi φ)

  class IsInhabited where
  (h : Sigma φ)

end HasFunctors



namespace HasCongrArg

  open HasFunctors

  variable {U V UpV : Universe} [HasFunctors U {V} UpV] [HasIdentity U]
           [HasTypeIdentity V] [HasCongrArg U {V}]

  def propCongrArg {A : U} (φ : A ⟶ ⌊V⌋) {a₁ a₂ : A} :
    a₁ ≃ a₂ → (⌋φ⌊ a₁ ⟷ ⌋φ⌊ a₂) :=
  congrArg φ

end HasCongrArg



class HasFunProp (U V W : Universe) {UpV UpW VW UpVW : Universe}
                 [HasFunctors U {V} UpV] [HasFunctors U {W} UpW] [HasFunctors V W VW]
                 [HasIdentity {VW}] [HasFunctors U {VW} UpVW] where
(defFunProp {A : U} (φ : A ⟶ ⌊V⌋) (ψ : A ⟶ ⌊W⌋) : A ⟶{λ a => φ a ⟶ ψ a} ⌊VW⌋)

namespace HasFunProp

  variable {U V W UpV UpW VW UpVW : Universe} [HasFunctors U {V} UpV] [HasFunctors U {W} UpW]
           [HasFunctors V W VW] [HasIdentity {VW}] [HasFunctors U {VW} UpVW]
           [HasFunProp U V W]

  @[reducible] def funProp {A : U} (φ : A ⟶ ⌊V⌋) (ψ : A ⟶ ⌊W⌋) : A ⟶ ⌊VW⌋ := defFunProp φ ψ
  notation "{" φ:50 " ⟶ " ψ:50 "}" => HasFunProp.funProp φ ψ

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
  notation "{" φ:50 " ⊓ " ψ:50 "}" =>  HasProdProp.prodProp φ ψ

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
  notation "{" φ:50 " ⟷ " ψ:50 "}" => HasEquivProp.equivProp φ ψ

end HasEquivProp
