-- TODO: Adapt to `HasIdentity`.
#exit



import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences
import UniverseAbstractions.Axioms.Universe.Properties
import UniverseAbstractions.Axioms.Universe.DependentFunctors
import UniverseAbstractions.Axioms.Universe.DependentProducts
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

  def Relation (A : U) (V : Universe.{v}) [HasRelations.{u, v, w, w', w''} U V] := A ⊓ A ⟿ V
  infixr:20 " ⤐ " => HasRelations.Relation

  variable {V : Universe} [HasRelations U V] {A : U}

  instance coeRel : CoeFun (A ⤐ V) (λ _ => A → A → V) := ⟨λ θ => relMap θ.p⟩

  section

    def defExtractABFun : (A ⊓ A) ⊓ A ⟶[λ P => intro (fst (fst P)) (snd (fst P))] A ⊓ A :=
    fstFun (A ⊓ A) A
    ◄ λ _ => by simp

    def defExtractBCFun : (A ⊓ A) ⊓ A ⟶[λ P => intro (snd (fst P)) (snd P)] A ⊓ A :=
    elim₃LFun (HasSubLinearFunOp.constFun A (introFunFun A A))
    ◄ λ _ => by simp [elim₃LFun]

    def defExtractACFun : (A ⊓ A) ⊓ A ⟶[λ P => intro (fst (fst P)) (snd P)] A ⊓ A :=
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
       θ b c ⟷[HasTrans.trans θ a b c f, HasTrans.trans θ b a c (HasSymm.symm θ a b f)] θ a c)
    (defTransEquivFun (a b c : A)                   :
       θ a b ⟶[λ f => HasEquivalences.fromDefEquiv (defTransEquiv f c)] (θ b c ⟷ θ a c))

    class HasSymmEquiv [HasSymm θ] where
    (defSymmEquiv (a b : A) : θ a b ⟷[HasSymm.symm θ a b, HasSymm.symm θ b a] θ b a)

    class IsEquivalence extends IsPreorder θ, HasSymm θ, HasTransEquiv θ
  
    def substRel (φ : A ⟿ V) : A ⤐ V :=
    {compProp (fstFun' A A) φ ⟷ compProp (sndFun' A A) φ}

    @[simp] theorem simp_subst_refl (φ : A ⟿ V) :
      compProp (dupIntroFun' A) (substRel φ) = {φ ⟷ φ} :=
    sorry

    class HasIdEquivPi (φ : A ⟿ V) where
    [hasIdFun   : HasIdFun V]
    [hasIdEquiv : HasIdEquiv V V]
    (F          : Π[λ a => HasIdEquiv.idEquiv (φ a)] {φ ⟷ φ})

    instance substRel.hasRefl (φ : A ⟿ V) [h : HasIdEquivPi φ] :
      HasRefl (substRel φ) :=
    ⟨simp_subst_refl φ ▸ h.F⟩

    class IsSubstitution extends HasRefl θ where
    (substPi (φ : A ⟿ V) [HasIdEquivPi φ] : Π {θ ⟶ substRel φ})

    @[simp] theorem simp_apply_fst (φ : A ⟿ V) (a b : A) :
      φ (fst (intro a b)) = φ a :=
    by simp

    @[simp] theorem simp_apply_snd (φ : A ⟿ V) (a b : A) :
      φ (snd (intro a b)) = φ b :=
    by simp

    def IsSubstitution.subst [IsSubstitution θ] (φ : A ⟿ V) [HasIdEquivPi φ] (a b : A) :
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

  end

  #exit

  def HasTrans.revTrans {θ : A ⤐ V} [HasInternalFunctors V] [HasLinearFunOp V] [h : HasTrans θ]
                        {a b c : A} : θ b c ⟶ θ a b ⟶ θ a c :=
  HasLinearFunOp.swapFunFun h.trans

  @[simp] theorem HasTrans.revTrans.eff {θ : A ⤐ V} [HasInternalFunctors V] [HasLinearFunOp V] [h : HasTrans θ]
                                        {a b c : A} (g : θ b c) (f : θ a b) :
    h.revTrans g f = h.trans f g :=
  by apply HasLinearFunOp.swapFunFun.effEff

  def HasTrans.trans' {θ : A ⤐ V} [HasInternalFunctors V] [h : HasTrans θ]
                      {a b c : A} (f : θ a b) (g : θ b c) : θ a c := h.trans f g

  def HasSymm.symm' {θ : A ⤐ V} [HasInternalFunctors V] [HasInternalEquivalences V] [h : HasSymm θ]
                    {a b : A} (f : θ a b) : θ b a := HasInternalEquivalences.to h.symm f

  -- When reasoning about instances of `θ a b`, we would like to write `trans` as composition, `refl` as
  -- identity, and `symm` as inverse.
  -- Note that `θ` can be inferred from `f : θ a b` by elaboration.

  section Notation

    @[reducible] def revComp {θ : A ⤐ V} [HasInternalFunctors V] [h : HasTrans θ] {a b c : A} (g : θ b c) (f : θ a b) : θ a c := h.trans' f g
    infixr:90 " • " => revComp

    @[reducible] def ident (θ : A ⤐ V) [h : HasRefl θ] (a : A) : θ a a := h.refl a

    @[reducible] def inv {θ : A ⤐ V} [HasInternalFunctors V] [HasInternalEquivalences V] [h : HasSymm θ] {a b : A} (f : θ a b) : θ b a := h.symm' f
    postfix:max "⁻¹" => inv

  end Notation

  def ConstRel (B : V) : A ⤐ V := λ _ _ => B

  namespace ConstRel
  
    variable (B : V)

    instance hasRefl (c : B) : HasRefl (ConstRel (A := A) B) := ⟨λ _ => c⟩

    variable [HasInternalFunctors V] [HasAffineFunOp V]

    instance hasTrans : HasTrans (ConstRel (A := A) B) := ⟨HasSubLinearFunOp.constFun B (HasLinearFunOp.idFun B)⟩
    instance isPreorder (c : B) : IsPreorder (ConstRel (A := A) B) := { toHasRefl := hasRefl B c }

    variable [HasEquivOp V]

    instance hasSymm : HasSymm (ConstRel (A := A) B) := ⟨HasEquivOp.idEquiv B⟩
    instance isEquivalence (c : B) : IsEquivalence (ConstRel (A := A) B) := { toHasRefl := hasRefl B c }

    --@[simp] theorem symmEq  {a₁ a₂    : A} (c : B) : (hasSymm  (A := A) B).symm'  (a := a₁) (b := a₂)           c   = c :=
    --HasLinearFunOp.idFun.eff B c
    --@[simp] theorem transEq {a₁ a₂ a₃ : A} (c : B) : (hasTrans (A := A) B).trans' (a := a₁) (b := a₂) (c := a₃) c c = c :=
    --let h₁ := congrArg HasInternalFunctors.funCoe (HasAffineFunOp.constFun.eff B (HasLinearFunOp.idFun B) c);
    --Eq.trans (congrFun h₁ c) (HasLinearFunOp.idFun.eff B c)

  end ConstRel

end HasRelations



-- We can attach products, arrows, and/or equivalences to a given sort, in the form of generalized
-- relations satisfying appropriate properties.

section AttachedRelations

  variable {U : Universe.{u}} (A : U) (V : Universe.{v}) [HasInternalFunctors V]

  class HasArrows where
  (Arrow      : A ⤐ V)
  [isPreorder : IsPreorder Arrow]

  namespace HasArrows
    variable [h : HasArrows A V]
    instance arrowPreorder : IsPreorder h.Arrow := h.isPreorder
    instance hasArrow : HasArrow A A := ⟨h.Arrow⟩
    instance : HasInstances (HasArrow.C A A) := Universe.instInst V
    instance : IsPreorder (@HasArrow.Arrow A A (hasArrow A V)) := h.isPreorder
  end HasArrows

  variable [HasInternalEquivalences V]

  class HasEquivalences where
  (Equiv   : A ⤐ V)
  [isEquiv : IsEquivalence Equiv]

  namespace HasEquivalences
    variable [h : HasEquivalences A V]
    instance equivEquivalence : IsEquivalence h.Equiv := h.isEquiv
    instance hasEquivalence : HasEquivalence A A := ⟨h.Equiv⟩
    instance : HasInstances (HasEquivalence.C A A) := Universe.instInst V
    instance : IsEquivalence (@HasEquivalence.Equiv A A (hasEquivalence A V)) := h.isEquiv
  end HasEquivalences

  class HasProducts where
  (Product : A ⤐ V)
  [hasSymm : HasSymm Product]

  namespace HasProducts
    variable [h : HasProducts A V]
    instance productSymm : HasSymm h.Product := h.hasSymm
    instance hasProduct : HasProduct A A := ⟨h.Product⟩
    instance : HasInstances (HasProduct.C A A) := Universe.instInst V
    instance : HasSymm (@HasProduct.Product A A (hasProduct A V)) := h.hasSymm
  end HasProducts

end AttachedRelations
