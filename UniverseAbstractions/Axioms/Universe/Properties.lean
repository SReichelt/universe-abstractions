import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences

import mathlib4_experiments.Data.Equiv.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w w'



-- We define a "`V`-valued property" on a type `α` to be a function yielding a type in `V` with an
-- additional condition, similarly to the definition of functoriality. If `V` is the universe
-- `prop`, this is just a regular property, or equivalently `Set α` in Lean.

class HasProperties (U : Universe.{u}) (V : Universe.{v}) : Type (max u v w) where
(IsProp       {α : U}         : (α → V) → Sort w)
(defConstProp (α : U) (β : V) : IsProp (Function.const ⌈α⌉ β))

namespace HasProperties

  def DefProp {U : Universe.{u}} (α : U) (V : Universe.{v}) [h : HasProperties.{u, v, w} U V]
              (p : α → V) :=
  h.IsProp p
  notation:20 α:21 " ⟿[" p:0 "] " V:21 => HasProperties.DefProp α V p

  structure Property {U : Universe.{u}} (α : U) (V : Universe.{v}) [HasProperties.{u, v, w} U V] :
    Type (max 1 u v w) where
  (p : α → V)
  (φ : α ⟿[p] V)

  infixr:20 " ⟿ " => HasProperties.Property

  variable {U : Universe.{u}} {V : Universe.{v}} [HasProperties U V]

  section Properties
  
    variable {α : U}

    instance coeDefProp (p : α → V) : CoeFun (α ⟿[p] V) (λ _ => α → V) := ⟨λ _ => p⟩
    instance coeProp                : CoeFun (α ⟿ V)    (λ _ => α → V) := ⟨Property.p⟩

    def toDefProp               (φ : α ⟿ V)    : α ⟿[φ.p] V := φ.φ
    def fromDefProp {p : α → V} (φ : α ⟿[p] V) : α ⟿      V := ⟨p, φ⟩

    instance (φ : α ⟿ V) : CoeDep (α ⟿ V) φ (α ⟿[φ.φ] V) := ⟨toDefProp φ⟩
    instance {p : α → V} : Coe (α ⟿[p] V) (α ⟿ V) := ⟨fromDefProp⟩

    theorem DefProp.ext {p p' : α → V} (h : ∀ a, p a = p' a) : (α ⟿[p] V) = (α ⟿[p'] V) :=
    congrArg (DefProp α V) (funext h)

    def castDefProp {p p' : α → V} (φ : α ⟿[p] V) (h : ∀ a, p a = p' a) : α ⟿[p'] V :=
    cast (DefProp.ext h) φ

    @[simp] theorem fromCastDefProp {p p' : α → V} (φ : α ⟿[p] V) (h : ∀ a, p a = p' a) :
      fromDefProp (castDefProp φ h) = fromDefProp φ :=
    have h₁ : p = p' := funext h;
    by subst h₁; rfl

    @[simp] theorem castCastDefProp {p p' : α → V} (φ : α ⟿[p] V) (h : ∀ a, p a = p' a) :
      castDefProp (castDefProp φ h) (λ a => Eq.symm (h a)) = φ :=
    have h₁ : p = p' := funext h;
    by subst h₁; rfl

    def toDefProp' (φ : α ⟿ V) {p : α → V} (h : ∀ a, φ a = p a) : α ⟿[p] V :=
    castDefProp (toDefProp φ) h

    @[simp] theorem toDefProp.eff               (φ : α ⟿ V)    (a : α) : (toDefProp   φ) a = φ a := rfl
    @[simp] theorem fromDefProp.eff {p : α → V} (φ : α ⟿[p] V) (a : α) : (fromDefProp φ) a = φ a := rfl

    @[simp] theorem fromToDefProp             (φ : α ⟿ V)    : fromDefProp (toDefProp φ) = φ :=
    match φ with | ⟨_, _⟩ => rfl
    @[simp] theorem toFromDefProp {p : α → V} (φ : α ⟿[p] V) : toDefProp (fromDefProp φ) = φ := rfl

    theorem Prop.Eq.eff {φ φ' : α ⟿ V} (h : φ = φ') (a : α) : φ a = φ' a := h ▸ rfl

    theorem toDefProp.congr {φ φ' : α ⟿ V} (h : φ = φ') :
      castDefProp (toDefProp φ) (Prop.Eq.eff h) = toDefProp φ' :=
    by subst h; rfl

    variable (φ : α ⟿ V)

    -- Universality and existence with respect to generalized properties are given by `∀` and `Σ'`.

    def Pi    : Sort (imax u v)  := ∀  a, ⌈φ a⌉
    def Sigma : Sort (max 1 u v) := Σ' a, ⌈φ a⌉

    class IsUniversal where
    (h : Pi φ)

    class IsInhabited where
    (h : Sigma φ)

  end Properties

  -- Given a type `β : V`, we can define a constant property that always yields this type. `Pi`
  -- applied to this property is just the type of functions from `α` to `β`, and `Sigma` applied to
  -- this property is just the product of `α` and `β`.

  def constProp (α : U) (β : V) : α ⟿ V := fromDefProp (defConstProp α β)

  namespace constProp

    notation:1023 α:1024 "{" β:0 "}" => HasProperties.constProp α β

    variable (α : U) (β : V)

    def piEquivFun : Pi α{β} ≃ (α → β) := Equiv.refl (α → β)

    def sigmaEquivProd : Sigma α{β} ≃ PProd ⌈α⌉ ⌈β⌉ :=
    { toFun    := λ s => ⟨s.fst, s.snd⟩,
      invFun   := λ p => ⟨p.fst, p.snd⟩,
      leftInv  := λ ⟨_, _⟩ => rfl,
      rightInv := λ ⟨_, _⟩ => rfl }

  end constProp

end HasProperties



class HasCompFunProp' (U V W : Universe) [HasFunctoriality U V] [HasProperties V W]
                      [HasProperties U W] where
(defCompProp {α : U} {β : V} (F : α ⟶' β) (φ : β ⟿ W) : α ⟿[λ a => φ (F a)] W)
(defCompConstEq {α : U} {β : V} (F : α ⟶' β) (γ : W) :
   defCompProp F β{γ} = HasProperties.defConstProp α γ)

namespace HasCompFunProp'

  variable {U V W : Universe} [HasFunctoriality U V] [HasProperties V W] [HasProperties U W]
           [HasCompFunProp' U V W]

  @[reducible] def compProp {α : U} {β : V} (F : α ⟶' β) (φ : β ⟿ W) : α ⟿ W := defCompProp F φ

  @[simp] theorem compConstEq {α : U} {β : V} (F : α ⟶' β) (γ : W) :
    compProp F β{γ} = α{γ} :=
  congrArg HasProperties.fromDefProp (defCompConstEq F γ)

end HasCompFunProp'

class HasCompFunProp (U V W X : Universe) [HasFunctors U V X] [HasProperties V W]
                     [HasProperties U W] where
(defCompProp {α : U} {β : V} (F : α ⟶ β) (φ : β ⟿ W) : α ⟿[λ a => φ (F a)] W)
(defCompConstEq {α : U} {β : V} (F : α ⟶ β) (γ : W) :
   defCompProp F β{γ} = HasProperties.defConstProp α γ)

namespace HasCompFunProp

  variable {U V W X : Universe} [HasFunctors U V X] [HasProperties V W] [HasProperties U W]
           [HasCompFunProp U V W X]

  @[reducible] def compProp {α : U} {β : V} (F : α ⟶ β) (φ : β ⟿ W) : α ⟿ W := defCompProp F φ

  @[simp] theorem compConstEq {α : U} {β : V} (F : α ⟶ β) (γ : W) :
    compProp F β{γ} = α{γ} :=
  congrArg HasProperties.fromDefProp (defCompConstEq F γ)

  instance hasCompFunProp' : HasCompFunProp' U V W :=
  { defCompProp    := λ F φ => HasProperties.castDefProp (defCompProp (HasFunctors.fromExternal F) φ)
                                                         (λ _ => by simp),
    defCompConstEq := λ F γ => defCompConstEq (HasFunctors.fromExternal F) γ }

end HasCompFunProp



class HasFunProp (U V W X : Universe) [HasProperties U V] [HasProperties U W] [HasFunctors V W X]
                 [HasProperties U X] where
(defFunProp {α : U} (φ : α ⟿ V) (ψ : α ⟿ W) : α ⟿[λ a => φ a ⟶ ψ a] X)
(defFunConstEq (α : U) (β : V) (γ : W) : defFunProp α{β} α{γ} = HasProperties.defConstProp α (β ⟶ γ))

namespace HasFunProp

  variable {U V W X : Universe} [HasProperties U V] [HasProperties U W] [HasFunctors V W X]
           [HasProperties U X] [HasFunProp U V W X]

  @[reducible] def funProp {α : U} (φ : α ⟿ V) (ψ : α ⟿ W) : α ⟿ X := defFunProp φ ψ
  notation "{" φ:50 " ⟶ " ψ:50 "}" => HasFunProp.funProp φ ψ

  @[simp] theorem funConstEq (α : U) (β : V) (γ : W) : {α{β} ⟶ α{γ}} = α{β ⟶ γ} :=
  congrArg HasProperties.fromDefProp (defFunConstEq α β γ)

end HasFunProp



class HasProdProp (U V W X : Universe) [HasProperties U V] [HasProperties U W] [HasProducts V W X]
                  [HasProperties U X] where
(defProdProp {α : U} (φ : α ⟿ V) (ψ : α ⟿ W) : α ⟿[λ a => φ a ⊓ ψ a] X)
(defProdConstEq (α : U) (β : V) (γ : W) : defProdProp α{β} α{γ} = HasProperties.defConstProp α (β ⊓ γ))

namespace HasProdProp

  variable {U V W X : Universe} [HasProperties U V] [HasProperties U W] [HasProducts V W X]
           [HasProperties U X] [HasProdProp U V W X]

  @[reducible] def prodProp {α : U} (φ : α ⟿ V) (ψ : α ⟿ W) : α ⟿ X := defProdProp φ ψ
  notation "{" φ:50 " ⊓ " ψ:50 "}" =>  HasProdProp.prodProp φ ψ

  @[simp] theorem prodConstEq (α : U) (β : V) (γ : W) : {α{β} ⊓ α{γ}} = α{β ⊓ γ} :=
  congrArg HasProperties.fromDefProp (defProdConstEq α β γ)

end HasProdProp



class HasEquivProp (U V X : Universe) [HasProperties U V] [HasEmbeddedFunctors V]
                   [HasEquivalences V V X] [HasProperties U X] where
(defEquivProp {α : U} (φ ψ : α ⟿ V) : α ⟿[λ a => φ a ⟷ ψ a] X)
(defEquivConstEq (α : U) (β γ : V) : defEquivProp α{β} α{γ} = HasProperties.defConstProp α (β ⟷ γ))

namespace HasEquivProp

  variable {U V X : Universe} [HasProperties U V] [HasEmbeddedFunctors V] [HasEquivalences V V X]
           [HasProperties U X] [HasEquivProp U V X]

  @[reducible] def equivProp {α : U} (φ ψ : α ⟿ V) : α ⟿ X := defEquivProp φ ψ
  notation "{" φ:50 " ⟷ " ψ:50 "}" => HasEquivProp.equivProp φ ψ

  @[simp] theorem equivConstEq (α : U) (β γ : V) : {α{β} ⟷ α{γ}} = α{β ⟷ γ} :=
  congrArg HasProperties.fromDefProp (defEquivConstEq α β γ)

end HasEquivProp
