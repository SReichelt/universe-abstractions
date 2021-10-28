import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences
import UniverseAbstractions.Axioms.Universe.TypeConstructors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v uv



namespace HasFunctors

  open HasTypeIdentity

  variable {U : Universe.{u}} {V : Universe.{v}} {UpV : Universe} [HasFunctors U {V} UpV]
           {A : U} (φ : A ⟶ ⌊V⌋)

  def Pi    : Sort (imax u v)  := ∀  a, ⌈⸥φ a⸤⌉
  def Sigma : Sort (max 1 u v) := Σ' a, ⌈⸥φ a⸤⌉

  def castPiTo  [HasTypeIdentity V] {p : A → V} (f : ∀ a, p a) (h : ∀ a, ⸤p a⸥ ≃ φ a) : Pi φ :=
  λ a => castTo  (h a) (f a)
  def castPiInv [HasTypeIdentity V] {p : A → V} (f : ∀ a, p a) (h : ∀ a, φ a ≃ ⸤p a⸥) : Pi φ :=
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

  def propCongrArg {A : U} (φ : A ⟶ ⌊V⌋) {a₁ a₂ : A} (e : a₁ ≃ a₂) : φ a₁ ⟷ φ a₂ :=
  congrArg φ e

  def defPropCongrArg {A : U} {p : A → V} (φ : A ⟶{p} ⌊V⌋) {a₁ a₂ : A} (e : a₁ ≃ a₂) :
    p a₁ ⟷ p a₂ :=
  defCongrArg φ e

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



namespace HasFunctors

  open HasCongrFun HasRightTypeFun HasLeftTypeFun HasTypeBiFun HasBiCompFun

  variable {U V W VW : Universe} [h : HasFunctors V W VW]

  section

    variable {VtVW UpV UpVW : Universe} [HasFunctors {V} {VW} VtVW]
             [HasIdentity {VW}] [HasLeftTypeFun h.Fun]
             [HasFunctors U {V} UpV] [HasFunctors U {VW} UpVW]
             [HasCompFun U {V} {VW}]

    def defLeftFunProp {A : U} (φ : A ⟶ ⌊V⌋) (C : W) : A ⟶{λ a => φ a ⟶ C} ⌊VW⌋ :=
    revTypeFun h.Fun C ⊙ φ
    ◄ byDef

    @[reducible] def leftFunProp {A : U} (φ : A ⟶ ⌊V⌋) (C : W) : A ⟶ ⌊VW⌋ := defLeftFunProp φ C
    notation:20 φ:21 " {⟶ " C:0 "}" => HasFunctors.leftFunProp φ C

  end

  section

    variable {WtVW UpW UpVW : Universe} [HasFunctors {W} {VW} WtVW]
             [HasIdentity {VW}] [HasRightTypeFun h.Fun]
             [HasFunctors U {W} UpW] [HasFunctors U {VW} UpVW]
             [HasCompFun U {W} {VW}]

    def defRightFunProp {A : U} (B : V) (ψ : A ⟶ ⌊W⌋) : A ⟶{λ a => B ⟶ ψ a} ⌊VW⌋ :=
    typeFun h.Fun B ⊙ ψ
    ◄ byDef

    @[reducible] def rightFunProp {A : U} (B : V) (ψ : A ⟶ ⌊W⌋) : A ⟶ ⌊VW⌋ := defRightFunProp B ψ
    notation:20 "{" B:0 "⟶} " ψ:21 => HasFunctors.rightFunProp B ψ

  end

  section

    variable {WtVW VtWtVW UpV UpW UpVW : Universe} [HasFunctors {W} {VW} WtVW]
             [HasFunctors {V} WtVW VtWtVW] [HasIdentity {VW}] [HasIdentity WtVW]
             [HasTypeBiFun h.Fun] [HasFunctors U {V} UpV] [HasFunctors U {W} UpW]
             [HasFunctors U {VW} UpVW] [HasBiCompFun U {V} {W} {VW}] [HasCongrFun {W} {VW}]

    def defFunProp {A : U} (φ : A ⟶ ⌊V⌋) (ψ : A ⟶ ⌊W⌋) : A ⟶{λ a => φ a ⟶ ψ a} ⌊VW⌋ :=
    biCompFun φ ψ (typeFunFun h.Fun)
    ◄ byDef₂

    @[reducible] def funProp {A : U} (φ : A ⟶ ⌊V⌋) (ψ : A ⟶ ⌊W⌋) : A ⟶ ⌊VW⌋ := defFunProp φ ψ
    infixr:20 " {⟶} " => HasFunctors.funProp

  end

end HasFunctors



namespace HasProducts

  open HasCongrFun HasRightTypeFun HasLeftTypeFun HasTypeBiFun HasBiCompFun

  variable {U V W VxW : Universe} [h : HasProducts V W VxW]

  -- TODO left, right

  section

    variable {WtVxW VtWtVxW UpV UpW UpVxW : Universe}
             [HasFunctors {W} {VxW} WtVxW] [HasFunctors {V} WtVxW VtWtVxW]
             [HasIdentity {VxW}] [HasIdentity WtVxW] [HasTypeBiFun h.Prod]
             [HasFunctors U {V} UpV] [HasFunctors U {W} UpW] [HasFunctors U {VxW} UpVxW]
             [HasBiCompFun U {V} {W} {VxW}] [HasCongrFun {W} {VxW}]

    def defProdProp {A : U} (φ : A ⟶ ⌊V⌋) (ψ : A ⟶ ⌊W⌋) : A ⟶{λ a => φ a ⊓ ψ a} ⌊VxW⌋ :=
    biCompFun φ ψ (typeFunFun h.Prod)
    ◄ byDef₂

    @[reducible] def prodProp {A : U} (φ : A ⟶ ⌊V⌋) (ψ : A ⟶ ⌊W⌋) : A ⟶ ⌊VxW⌋ := defProdProp φ ψ
    infixr:35 " {⊓} " => HasProducts.prodProp

  end

end HasProducts



namespace HasEquivalences

  open HasCongrFun HasRightTypeFun HasLeftTypeFun HasTypeBiFun HasBiCompFun

  variable {U V W VW WV V_W : Universe} [HasIdentity V] [HasIdentity W]
           [HasFunctors V W VW] [HasFunctors W V WV] [h : HasEquivalences V W V_W]

  -- TODO left, right

  section

    variable {WtV_W VtWtV_W UpV UpW UpV_W : Universe}
             [HasFunctors {W} {V_W} WtV_W] [HasFunctors {V} WtV_W VtWtV_W]
             [HasIdentity {V_W}] [HasIdentity WtV_W] [HasTypeBiFun h.Equiv]
             [HasFunctors U {V} UpV] [HasFunctors U {W} UpW] [HasFunctors U {V_W} UpV_W]
             [HasBiCompFun U {V} {W} {V_W}] [HasCongrFun {W} {V_W}]

    def defEquivProp {A : U} (φ : A ⟶ ⌊V⌋) (ψ : A ⟶ ⌊W⌋) : A ⟶{λ a => φ a ⟷ ψ a} ⌊V_W⌋ :=
    biCompFun φ ψ (typeFunFun h.Equiv)
    ◄ byDef₂

    @[reducible] def equivProp {A : U} (φ : A ⟶ ⌊V⌋) (ψ : A ⟶ ⌊W⌋) : A ⟶ ⌊V_W⌋ := defEquivProp φ ψ
    infixr:20 " {⟷} " => HasEquivalences.equivProp

  end

end HasEquivalences
