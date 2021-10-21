-- TODO: Adapt to `HasIdentity`, use functors.
#exit



import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences

import mathlib4_experiments.Data.Equiv.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v uv



-- We define a "`V`-valued property" on a type `A` to be a functor into the singleton universe
-- `⌊V⌋`, i.e. a function yielding a type in `V` with an additional condition.
-- A `prop`-valued property is just a regular property, or equivalently `Set A` in Lean.

class HasProperties (U : Universe.{u}) (V : Universe.{v}) [HasIdentity V]
                    (UV : outParam Universe.{uv}) extends
  HasFunctors U ⌉V⌈ UV, HasConstFun U ⌉V⌈

#exit

namespace HasProperties

  def DefProp {U : Universe.{u}} (A : U) (V : Universe.{v}) [h : HasProperties.{u, v, w} U V]
              (p : A → V) :=
  h.IsProp p
  notation:20 A:21 " ⟿[" p:0 "] " V:21 => HasProperties.DefProp A V p

  structure Property {U : Universe.{u}} (A : U) (V : Universe.{v}) [HasProperties.{u, v, w} U V] :
    Type (max 1 u v w) where
  (p : A → V)
  (φ : A ⟿[p] V)

  infixr:20 " ⟿ " => HasProperties.Property

  variable {U : Universe.{u}} {V : Universe.{v}} [HasProperties U V]

  section Properties
  
    variable {A : U}

    instance coeDefProp (p : A → V) : CoeFun (A ⟿[p] V) (λ _ => A → V) := ⟨λ _ => p⟩
    instance coeProp                : CoeFun (A ⟿ V)    (λ _ => A → V) := ⟨Property.p⟩

    def toDefProp               (φ : A ⟿ V)    : A ⟿[φ.p] V := φ.φ
    def fromDefProp {p : A → V} (φ : A ⟿[p] V) : A ⟿      V := ⟨p, φ⟩

    instance (φ : A ⟿ V) : CoeDep (A ⟿ V) φ (A ⟿[φ.φ] V) := ⟨toDefProp φ⟩
    instance {p : A → V} : Coe (A ⟿[p] V) (A ⟿ V) := ⟨fromDefProp⟩

    theorem DefProp.ext {p p' : A → V} (h : ∀ a, p a = p' a) : (A ⟿[p] V) = (A ⟿[p'] V) :=
    congrArg (DefProp A V) (funext h)

    def castDefProp {p p' : A → V} (φ : A ⟿[p] V) (h : ∀ a, p a = p' a) : A ⟿[p'] V :=
    cast (DefProp.ext h) φ

    @[simp] theorem fromCastDefProp {p p' : A → V} (φ : A ⟿[p] V) (h : ∀ a, p a = p' a) :
      fromDefProp (castDefProp φ h) = fromDefProp φ :=
    have h₁ : p = p' := funext h;
    by subst h₁; rfl

    @[simp] theorem castCastDefProp {p p' : A → V} (φ : A ⟿[p] V) (h : ∀ a, p a = p' a) :
      castDefProp (castDefProp φ h) (λ a => Eq.symm (h a)) = φ :=
    have h₁ : p = p' := funext h;
    by subst h₁; rfl

    def toDefProp' (φ : A ⟿ V) {p : A → V} (h : ∀ a, φ a = p a) : A ⟿[p] V :=
    castDefProp (toDefProp φ) h

    @[simp] theorem toDefProp.eff               (φ : A ⟿ V)    (a : A) : (toDefProp   φ) a = φ a := rfl
    @[simp] theorem fromDefProp.eff {p : A → V} (φ : A ⟿[p] V) (a : A) : (fromDefProp φ) a = φ a := rfl

    @[simp] theorem fromToDefProp             (φ : A ⟿ V)    : fromDefProp (toDefProp φ) = φ :=
    match φ with | ⟨_, _⟩ => rfl
    @[simp] theorem toFromDefProp {p : A → V} (φ : A ⟿[p] V) : toDefProp (fromDefProp φ) = φ := rfl

    theorem Prop.Eq.eff {φ φ' : A ⟿ V} (h : φ = φ') (a : A) : φ a = φ' a := h ▸ rfl

    theorem toDefProp.congr {φ φ' : A ⟿ V} (h : φ = φ') :
      castDefProp (toDefProp φ) (Prop.Eq.eff h) = toDefProp φ' :=
    by subst h; rfl

    variable (φ : A ⟿ V)

    -- Universality and existence with respect to generalized properties are given by `∀` and `Σ'`.

    def Pi    : Sort (imax u v)  := ∀  a, ⌈φ a⌉
    def Sigma : Sort (max 1 u v) := Σ' a, ⌈φ a⌉

    class IsUniversal where
    (h : Pi φ)

    class IsInhabited where
    (h : Sigma φ)

  end Properties

  #exit

  -- Given a type `B : V`, we can define a constant property that always yields this type. `Pi`
  -- applied to this property is just the type of functions from `A` to `B`, and `Sigma` applied to
  -- this property is just the product of `A` and `B`.

  def constProp (A : U) (B : V) : A ⟿ V := fromDefProp (defConstProp A B)

  namespace constProp

    notation:1023 A:1024 "{" B:0 "}" => HasProperties.constProp A B

    variable (A : U) (B : V)

    def piEquivFun : Pi A{B} ≃ (A → B) := Equiv.refl (A → B)

    def sigmaEquivProd : Sigma A{B} ≃ PProd ⌈A⌉ ⌈B⌉ :=
    { toFun    := λ s => ⟨s.fst, s.snd⟩,
      invFun   := λ p => ⟨p.fst, p.snd⟩,
      leftInv  := λ ⟨_, _⟩ => rfl,
      rightInv := λ ⟨_, _⟩ => rfl }

  end constProp

end HasProperties



class HasCompFunProp' (U V W : Universe) [HasFunctoriality U V] [HasProperties V W]
                      [HasProperties U W] where
(defCompProp {A : U} {B : V} (F : A ⟶' B) (φ : B ⟿ W) : A ⟿[λ a => φ (F a)] W)
(defCompConstEq {A : U} {B : V} (F : A ⟶' B) (C : W) :
   defCompProp F B{C} = HasProperties.defConstProp A C)

namespace HasCompFunProp'

  variable {U V W : Universe} [HasFunctoriality U V] [HasProperties V W] [HasProperties U W]
           [HasCompFunProp' U V W]

  @[reducible] def compProp {A : U} {B : V} (F : A ⟶' B) (φ : B ⟿ W) : A ⟿ W := defCompProp F φ

  @[simp] theorem compConstEq {A : U} {B : V} (F : A ⟶' B) (C : W) :
    compProp F B{C} = A{C} :=
  congrArg HasProperties.fromDefProp (defCompConstEq F C)

end HasCompFunProp'

class HasCompFunProp (U V W UV : Universe) [HasFunctors U V UV] [HasProperties V W]
                     [HasProperties U W] where
(defCompProp {A : U} {B : V} (F : A ⟶ B) (φ : B ⟿ W) : A ⟿[λ a => φ (F a)] W)
(defCompConstEq {A : U} {B : V} (F : A ⟶ B) (C : W) :
   defCompProp F B{C} = HasProperties.defConstProp A C)

namespace HasCompFunProp

  variable {U V W UV : Universe} [HasFunctors U V UV] [HasProperties V W] [HasProperties U W]
           [HasCompFunProp U V W UV]

  @[reducible] def compProp {A : U} {B : V} (F : A ⟶ B) (φ : B ⟿ W) : A ⟿ W := defCompProp F φ

  @[simp] theorem compConstEq {A : U} {B : V} (F : A ⟶ B) (C : W) :
    compProp F B{C} = A{C} :=
  congrArg HasProperties.fromDefProp (defCompConstEq F C)

  instance hasCompFunProp' : HasCompFunProp' U V W :=
  { defCompProp    := λ F φ => HasProperties.castDefProp (defCompProp (HasFunctors.fromExternal F) φ)
                                                         (λ _ => by simp),
    defCompConstEq := λ F C => defCompConstEq (HasFunctors.fromExternal F) C }

end HasCompFunProp



class HasFunProp (U V W VW : Universe) [HasProperties U V] [HasProperties U W] [HasFunctors V W VW]
                 [HasProperties U VW] where
(defFunProp {A : U} (φ : A ⟿ V) (ψ : A ⟿ W) : A ⟿[λ a => φ a ⟶ ψ a] VW)
(defFunConstEq (A : U) (B : V) (C : W) : defFunProp A{B} A{C} = HasProperties.defConstProp A (B ⟶ C))

namespace HasFunProp

  variable {U V W VW : Universe} [HasProperties U V] [HasProperties U W] [HasFunctors V W VW]
           [HasProperties U VW] [HasFunProp U V W VW]

  @[reducible] def funProp {A : U} (φ : A ⟿ V) (ψ : A ⟿ W) : A ⟿ VW := defFunProp φ ψ
  notation "{" φ:50 " ⟶ " ψ:50 "}" => HasFunProp.funProp φ ψ

  @[simp] theorem funConstEq (A : U) (B : V) (C : W) : {A{B} ⟶ A{C}} = A{B ⟶ C} :=
  congrArg HasProperties.fromDefProp (defFunConstEq A B C)

end HasFunProp



class HasProdProp (U V W VxW : Universe) [HasProperties U V] [HasProperties U W] [HasProducts V W VxW]
                  [HasProperties U VxW] where
(defProdProp {A : U} (φ : A ⟿ V) (ψ : A ⟿ W) : A ⟿[λ a => φ a ⊓ ψ a] VxW)
(defProdConstEq (A : U) (B : V) (C : W) : defProdProp A{B} A{C} = HasProperties.defConstProp A (B ⊓ C))

namespace HasProdProp

  variable {U V W VxW : Universe} [HasProperties U V] [HasProperties U W] [HasProducts V W VxW]
           [HasProperties U VxW] [HasProdProp U V W VxW]

  @[reducible] def prodProp {A : U} (φ : A ⟿ V) (ψ : A ⟿ W) : A ⟿ VxW := defProdProp φ ψ
  notation "{" φ:50 " ⊓ " ψ:50 "}" =>  HasProdProp.prodProp φ ψ

  @[simp] theorem prodConstEq (A : U) (B : V) (C : W) : {A{B} ⊓ A{C}} = A{B ⊓ C} :=
  congrArg HasProperties.fromDefProp (defProdConstEq A B C)

end HasProdProp



class HasEquivProp (U V V_V : Universe) [HasProperties U V] [HasInternalFunctors V]
                   [HasEquivalences V V V_V] [HasProperties U V_V] where
(defEquivProp {A : U} (φ ψ : A ⟿ V) : A ⟿[λ a => φ a ⟷ ψ a] V_V)
(defEquivConstEq (A : U) (B C : V) : defEquivProp A{B} A{C} = HasProperties.defConstProp A (B ⟷ C))

namespace HasEquivProp

  variable {U V V_V : Universe} [HasProperties U V] [HasInternalFunctors V] [HasEquivalences V V V_V]
           [HasProperties U V_V] [HasEquivProp U V V_V]

  @[reducible] def equivProp {A : U} (φ ψ : A ⟿ V) : A ⟿ V_V := defEquivProp φ ψ
  notation "{" φ:50 " ⟷ " ψ:50 "}" => HasEquivProp.equivProp φ ψ

  @[simp] theorem equivConstEq (A : U) (B C : V) : {A{B} ⟷ A{C}} = A{B ⟷ C} :=
  congrArg HasProperties.fromDefProp (defEquivConstEq A B C)

end HasEquivProp
