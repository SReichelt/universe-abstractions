-- TODO: Adapt to `HasIdentity`:
-- Add type classes to "upgrade" a meta-relation to a relation,
-- and especially to upgrade instance equivalences to an equality-like recursor
-- (see `IsIdentity` below).
#exit



import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences
import UniverseAbstractions.Axioms.Universe.DependentTypes.Properties
import UniverseAbstractions.Axioms.Universe.DependentTypes.DependentFunctors
import UniverseAbstractions.Axioms.Universe.DependentTypes.DependentProducts
import UniverseAbstractions.Lemmas.DerivedFunctors
import UniverseAbstractions.Lemmas.DerivedProductFunctors
import UniverseAbstractions.Notation



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w w' w''



class HasRelations (U : Universe.{u}) [HasFunOp.{u, w} U] [HasInternalProducts.{u, w} U]
                   (V : Universe.{v}) extends
  HasDependentFunctors.{u, v, v, w', w''} U V V : Type (max 1 u v w w' w'')

namespace HasRelations

  open HasProducts HasInternalProducts HasCompFunProp'

  variable {U : Universe.{u}} [HasFunOp.{u, w} U] [HasInternalProducts.{u, w} U]

  def relMap {V : Universe.{v}} [HasRelations.{u, v, w, w', w''} U V] {A : U} (r : A ⊓ A → V) :
    A → A → V :=
  λ a b => r (intro a b)

  def propMap {V : Universe.{v}} [HasRelations.{u, v, w, w', w''} U V] {A : U} (r : A → A → V) :
    A ⊓ A → V :=
  λ P => r (fst P) (snd P)

  def DefRel (A : U) (V : Universe.{v}) [HasRelations.{u, v, w, w', w''} U V] (r : A → A → V) :=
  A ⊓ A ⟿[propMap r] V
  notation:20 A:21 " ⤐[" r:0 "] " V:21 => HasRelations.DefRel A V r

  def Relation (A : U) (V : Universe.{v}) [HasRelations.{u, v, w, w', w''} U V] := A ⊓ A ⟶ ⌊V⌋
  infixr:20 " ⤐ " => HasRelations.Relation

  variable {V : Universe} [HasRelations U V] {A : U}

  instance coeRel : CoeFun (A ⤐ V) (λ _ => A → A → V) := ⟨λ θ => relMap θ.p⟩

  def defExtractABFun : (A ⊓ A) ⊓ A ⟶{λ P => intro (fst (fst P)) (snd (fst P))} A ⊓ A :=
  fstFun (A ⊓ A) A
  ◄ λ _ => by simp

  def defExtractBCFun : (A ⊓ A) ⊓ A ⟶{λ P => intro (snd (fst P)) (snd P)} A ⊓ A :=
  elim₃LFun (HasSubLinearFunOp.constFun A (introFunFun A A))
  ◄ λ _ => by simp [elim₃LFun]

  def defExtractACFun : (A ⊓ A) ⊓ A ⟶{λ P => intro (fst (fst P)) (snd P)} A ⊓ A :=
  elim₃LFun (HasLinearFunOp.swapFunFun (HasSubLinearFunOp.constFun A (introFunFun A A)))
  ◄ λ _ => by simp [elim₃LFun]

  @[reducible] def extractABFun' : (A ⊓ A) ⊓ A ⟶' A ⊓ A := HasFunctoriality.fromDefFun defExtractABFun
  @[reducible] def extractBCFun' : (A ⊓ A) ⊓ A ⟶' A ⊓ A := HasFunctoriality.fromDefFun defExtractBCFun
  @[reducible] def extractACFun' : (A ⊓ A) ⊓ A ⟶' A ⊓ A := HasFunctoriality.fromDefFun defExtractACFun

  variable [HasCompFunProp' U U V] (θ : A ⤐ V)

  class HasRefl where
  (reflPi : Π compProp (dupIntroFun' A) θ)

  def HasRefl.refl [HasRefl θ] (a : A) : θ a a := reflPi a

  variable [HasInternalFunctors V] [HasFunProp U V V V]

  class HasTrans where
  (transPi : Π {compProp extractABFun' θ ⟶ {compProp extractBCFun' θ ⟶ compProp extractACFun' θ}})

  @[simp] theorem simp_extractAB (a b c : A) :
    let P := intro₃L a b c;
    θ (fst (fst P)) (snd (fst P)) = θ a b :=
  by simp

  @[simp] theorem simp_extractBC (a b c : A) :
    let P := intro₃L a b c;
    θ (snd (fst P)) (snd P) = θ b c :=
  by simp

  @[simp] theorem simp_extractAC (a b c : A) :
    let P := intro₃L a b c;
    θ (fst (fst P)) (snd P) = θ a c :=
  by simp

  def HasTrans.trans [HasTrans θ] (a b c : A) : θ a b ⟶ θ b c ⟶ θ a c :=
  simp_extractAB θ a b c ▸ simp_extractBC θ a b c ▸ simp_extractAC θ a b c ▸ transPi (intro₃L a b c)

  class IsPreorder extends HasRefl θ, HasTrans θ

  variable [HasInternalProducts V] [HasInternalEquivalences V] [HasEquivProp U V V]

  class HasSymm where
  (symmPi : Π {θ ⟶ compProp (commFun' A A) θ})

  @[simp] theorem simp_swap (a b : A) :
    let P := intro a b;
    θ (snd P) (fst P) = θ b a :=
  by simp

  def HasSymm.symm [HasSymm θ] (a b : A) : θ a b ⟶ θ b a :=
  simp_swap θ a b ▸ symmPi (intro a b)

  class HasTransEquiv [HasTrans θ] [HasSymm θ] where
  (defTransEquiv    {a b : A} (f : θ a b) (c : A) :
      θ b c ⟷{HasTrans.trans θ a b c f, HasTrans.trans θ b a c (HasSymm.symm θ a b f)} θ a c)
  (defTransEquivFun (a b c : A)                   :
      θ a b ⟶{λ f => HasEquivalences.fromDefEquiv (defTransEquiv f c)} (θ b c ⟷ θ a c))

  class HasSymmEquiv [HasSymm θ] where
  (defSymmEquiv (a b : A) : θ a b ⟷{HasSymm.symm θ a b, HasSymm.symm θ b a} θ b a)

  class IsEquivalence extends IsPreorder θ, HasSymm θ, HasTransEquiv θ

  def substRel (φ : A ⟶ ⌊V⌋) : A ⤐ V :=
  {compProp (fstFun' A A) φ ⟷ compProp (sndFun' A A) φ}

  @[simp] theorem simp_subst_refl (φ : A ⟶ ⌊V⌋) :
    compProp (dupIntroFun' A) (substRel φ) = {φ ⟷ φ} :=
  sorry

  class HasIdEquivPi (φ : A ⟶ ⌊V⌋) where
  [hasIdFun   : HasIdFun V]
  [hasIdEquiv : HasIdEquiv V V]
  (F          : Π{λ a => HasIdEquiv.idEquiv (φ a)} {φ ⟷ φ})

  instance substRel.hasRefl (φ : A ⟶ ⌊V⌋) [h : HasIdEquivPi φ] :
    HasRefl (substRel φ) :=
  ⟨simp_subst_refl φ ▸ h.F⟩

  class IsSubstitution extends HasRefl θ where
  (substPi (φ : A ⟶ ⌊V⌋) [HasIdEquivPi φ] : Π {θ ⟶ substRel φ})

  @[simp] theorem simp_apply_fst (φ : A ⟶ ⌊V⌋) (a b : A) :
    φ (fst (intro a b)) = φ a :=
  by simp

  @[simp] theorem simp_apply_snd (φ : A ⟶ ⌊V⌋) (a b : A) :
    φ (snd (intro a b)) = φ b :=
  by simp

  def IsSubstitution.subst [IsSubstitution θ] (φ : A ⟶ ⌊V⌋) [HasIdEquivPi φ] (a b : A) :
    θ a b ⟶ (φ a ⟷ φ b) :=
  simp_apply_fst φ a b ▸ simp_apply_snd φ a b ▸ substPi φ (intro a b)

  class IsIdentity extends HasRefl θ where
  (elimPi (ξ : A ⤐ V) [HasRefl ξ] : Π {θ ⟶ ξ})

  namespace IsIdentity

    variable [IsIdentity θ]

    def elim (ξ : A ⤐ V) [HasRefl ξ] (a b : A) : θ a b ⟶ ξ a b :=
    elimPi ξ (HasProducts.intro a b)

    instance isSubstitution : IsSubstitution θ :=
    { substPi := λ φ => elimPi (substRel φ) }

  end IsIdentity

end HasRelations
