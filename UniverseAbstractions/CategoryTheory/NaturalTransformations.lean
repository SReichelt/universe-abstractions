import UniverseAbstractions.CategoryTheory.Basic
import UniverseAbstractions.CategoryTheory.Functors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u uu v vv w ww iw iww



namespace CategoryTheory

  open MetaRelation MetaFunctor MetaQuantification HasTransFun HasSymmFun
       IsAssociative IsCategoricalPreorder IsTransFunctor
       HasCatProp HasCatProp.Category HasFunProp HasFunProp.Functor
       HasFunctors HasCongrArg HasCongrFun HasLinearFunOp HasNonLinearFunOp

  structure NatDesc {U : Universe.{u, uu}} {V : Universe.{v, vv}} {W : Universe.{w, ww}}
                    [IsHomUniverse.{w, ww, iw, iww} W] [HasCatProp U W] [HasCatProp V W]
                    {A : Category U W} {B : Category V W} [hFunProp : HasFunProp A B]
                    (F G : A ⮕ B) :
    Sort (max 1 u w iw) where
  (η     : MetaQuantification (Hom B) F.φ G.φ)
  [isNat : IsNatural (preFun F) (preFun G) η]

  namespace NatDesc

    variable {U V W : Universe} [IsHomUniverse W] [HasCatProp U W] [HasCatProp V W]
             {A : Category U W} {B : Category V W} [hFunProp : HasFunProp A B]

    def StrictNaturality {φ : A → B} (F G : hFunProp.Fun φ) :=
    ∀ {a b : A} (f : a ⇾ b), mapHom ⟨F⟩ f ≃'{φ a ⇾ φ b} mapHom ⟨G⟩ f

    def strict {φ : A → B} {F G : hFunProp.Fun φ} (hEq : StrictNaturality F G) : NatDesc ⟨F⟩ ⟨G⟩ :=
    { η     := λ a => idHom (φ a),
      isNat := IsNatural.fromEq (hFunProp.desc F).F (hFunProp.desc G).F hEq }

    section

      variable {F G : A ⮕ B} (η : NatDesc F G)

      instance : IsNatural (preFun F) (preFun G) η.η := η.isNat

    end

    def refl (F : A ⮕ B) : NatDesc F F := ⟨MetaQuantification.refl (Hom B) F.φ⟩

    def trans {F G H : A ⮕ B} (η : NatDesc F G) (ε : NatDesc G H) : NatDesc F H :=
    ⟨MetaQuantification.trans (Hom B) η.η ε.η⟩

  end NatDesc



  class HasNatRel {U : Universe.{u, uu}} {V : Universe.{v, vv}} {W : Universe.{w, ww}}
                  [IsHomUniverse.{w, ww, iw, iww} W] [HasCatProp U W] [HasCatProp V W]
                  (A : Category U W) (B : Category V W) [hFunProp : HasFunProp A B] where
  (Nat                             : MetaRelation (A ⮕ B) W)
  (desc {F G : A ⮕ B}              : Nat F G → NatDesc F G)
  (defNatFun (F G : A ⮕ B) (a : A) : Nat F G ⟶{λ η => (desc η).η a} (F a ⇾ G a))

  namespace HasNatRel

    open HasFunctors HasFunProp HasFunProp.Functor

    variable {U V W : Universe} [IsHomUniverse W] [HasCatProp U W] [HasCatProp V W]

    section

      variable {A : Category U W} {B : Category V W} [hFunProp : HasFunProp A B]
               [h : HasNatRel A B]

      @[reducible] def nat {F G : A ⮕ B} (η : h.Nat F G) (a : A) : F a ⇾ G a :=
      (h.desc η).η a

      @[reducible] def natFun (F G : A ⮕ B) (a : A) : h.Nat F G ⟶ (F a ⇾ G a) :=
      h.defNatFun F G a

      section

        variable {F G : A ⮕ B}

        instance (η : h.Nat F G) (a : A) : IsFunApp (h.Nat F G) (nat η a) :=
        { F := natFun F G a,
          a := η,
          e := byDef }

        def natCongrArg {η₁ η₂ : h.Nat F G} (e : η₁ ≃ η₂) (a : A) : nat η₁ a ≃ nat η₂ a :=
        defCongrArg (h.defNatFun F G a) e

        def naturality (η : h.Nat F G) {a b : A} (f : a ⇾ b) :
          nat η b • mapHom F f ≃ mapHom G f • nat η a :=
        (h.desc η).isNat.nat f

        structure DefNat (desc : NatDesc F G) where
        (η             : h.Nat F G)
        (natEq (a : A) : nat η a ≃ desc.η a)

        def byNatDef {desc : NatDesc F G} {η : DefNat desc} {a : A} : nat η.η a ≃ desc.η a :=
        η.natEq a

        def NatEquiv (η₁ η₂ : h.Nat F G) (hNat : ∀ a, nat η₁ a ≃ nat η₂ a) := η₁ ≃ η₂

        def DefNatEquiv {desc₁ desc₂ : NatDesc F G} (η₁ : DefNat desc₁)
                        (η₂ : DefNat desc₂) (hNat : ∀ a, desc₁.η a ≃ desc₂.η a) :=
        NatEquiv η₁.η η₂.η (λ a => byNatDef⁻¹ • hNat a • byNatDef)

      end

      section

        variable {φ : A → B} {F G : hFunProp.Fun φ}

        def StrictDefNat (hEq : NatDesc.StrictNaturality F G) := DefNat (NatDesc.strict hEq)

        def byStrictNatDef {hEq : NatDesc.StrictNaturality F G} {η : StrictDefNat hEq} {a : A} :
          nat η.η a ≃ idHom (φ a) :=
        byNatDef

      end

    end

    class HasTrivialNaturalityCondition (A : Category U W) (B : Category V W)
                                        [hFunProp : HasFunProp A B] [h : HasNatRel A B] where
    (nat {F G : A ⮕ B} (desc : NatDesc F G) : DefNat desc)

    namespace HasTrivialNaturalityCondition

      variable {A : Category U W} {B : Category V W} [HasFunProp A B] [HasNatRel A B]
               [h : HasTrivialNaturalityCondition A B]

      def defNat {F G : A ⮕ B} {desc : NatDesc F G} : DefNat desc := h.nat desc

    end HasTrivialNaturalityCondition

    class HasTrivialNatEquiv (A : Category U W) (B : Category V W) [hFunProp : HasFunProp A B]
                             [h : HasNatRel A B] where
    (equiv {F G : A ⮕ B} (η₁ η₂ : h.Nat F G) (hNat : ∀ a, nat η₁ a ≃ nat η₂ a) :
       NatEquiv η₁ η₂ hNat)

    namespace HasTrivialNatEquiv

      variable {A : Category U W} {B : Category V W} [HasFunProp A B] [hNatRel : HasNatRel A B]
               [h : HasTrivialNatEquiv A B]

      def natEquiv {F G : A ⮕ B} {η₁ η₂ : hNatRel.Nat F G} {hNat : ∀ a, nat η₁ a ≃ nat η₂ a} :
        NatEquiv η₁ η₂ hNat :=
      h.equiv η₁ η₂ hNat

    end HasTrivialNatEquiv

  end HasNatRel

  class HasNatOp {U : Universe.{u, uu}} {V : Universe.{v, vv}} {W : Universe.{w, ww}}
                 [IsHomUniverse.{w, ww, iw, iww} W] [HasCatProp U W] [HasCatProp V W]
                 (A : Category U W) (B : Category V W) [hFunProp : HasFunProp A B] extends
    HasNatRel A B where
  (defRefl (F : A ⮕ B) : HasNatRel.DefNat (NatDesc.refl F))
  (defTrans {F G H : A ⮕ B} (η : Nat F G) (ε : Nat G H) :
     HasNatRel.DefNat (NatDesc.trans (desc η) (desc ε)))

  namespace HasNatOp

    open HasFunProp HasFunProp.Functor HasNatRel

    variable {U V W : Universe} [IsHomUniverse W] [HasCatProp U W] [HasCatProp V W]

    section

      variable (A : Category U W) (B : Category V W) [HasFunProp A B]

      instance trivial [HasNatRel A B] [HasTrivialNaturalityCondition A B] : HasNatOp A B :=
      { defRefl  := λ _   => HasTrivialNaturalityCondition.defNat,
        defTrans := λ _ _ => HasTrivialNaturalityCondition.defNat }

      variable [h : HasNatOp A B]

      instance natIsPreorder : IsPreorder h.Nat :=
      { refl  := λ F   => (h.defRefl F).η,
        trans := λ η ε => (h.defTrans η ε).η }

    end

    section

      variable {A : Category U W} {B : Category V W} [HasFunProp A B] [h : HasNatOp A B]

      def natReflEq (F : A ⮕ B) (a : A) :
        nat (HasRefl.refl F) a ≃ idHom (F a) :=
      byNatDef

      def natTransEq {F G H : A ⮕ B} (η : h.Nat F G) (ε : h.Nat G H) (a : A) :
        nat (ε • η) a ≃ nat ε a • nat η a :=
      byNatDef

      def natAssoc {F G H I : A ⮕ B} (η : h.Nat F G) (ε : h.Nat G H) (θ : h.Nat H I) (a : A) :
        nat ((θ • ε) • η) a ≃ nat (θ • (ε • η)) a :=
      (congrArgTransRight (natTransEq η ε a) (nat θ a) •
       natTransEq (ε • η) θ a)⁻¹ •
      assoc (nat η a) (nat ε a) (nat θ a) •
      (congrArgTransLeft (nat η a) (natTransEq ε θ a) •
       natTransEq η (θ • ε) a)

      def natRightId {F G : A ⮕ B} (η : h.Nat F G) (a : A) :
        nat (η • HasRefl.refl F) a ≃ nat η a :=
      cancelRightId (natReflEq F a) (nat η a) •
      natTransEq (HasRefl.refl F) η a

      def natLeftId {F G : A ⮕ B} (η : h.Nat F G) (a : A) :
        nat (HasRefl.refl G • η) a ≃ nat η a :=
      cancelLeftId (nat η a) (natReflEq G a) •
      natTransEq η (HasRefl.refl G) a

    end

  end HasNatOp

  class HasNatOpEquiv {U : Universe.{u, uu}} {V : Universe.{v, vv}} {W : Universe.{w, ww}}
                      [IsHomUniverse.{w, ww, iw, iww} W] [HasCatProp U W] [HasCatProp V W]
                      (A : Category U W) (B : Category V W) [hFunProp : HasFunProp A B] extends
    HasNatOp A B where
  (assoc {F G H I : A ⮕ B} (η : Nat F G) (ε : Nat G H) (θ : Nat H I) :
     HasNatRel.NatEquiv ((θ • ε) • η) (θ • (ε • η)) (HasNatOp.natAssoc η ε θ))
  (rightId {F G : A ⮕ B} (η : Nat F G) :
     HasNatRel.NatEquiv (η • HasRefl.refl F) η (HasNatOp.natRightId η))
  (leftId {F G : A ⮕ B} (η : Nat F G) :
     HasNatRel.NatEquiv (HasRefl.refl G • η) η (HasNatOp.natLeftId η))

  namespace HasNatOpEquiv

    open HasNatRel HasNatOp

    variable {U V W : Universe} [IsHomUniverse W] [HasCatProp U W] [HasCatProp V W]
             (A : Category U W) (B : Category V W) [HasFunProp A B]

    instance trivial [HasNatOp A B] [HasTrivialNatEquiv A B] : HasNatOpEquiv A B :=
    { assoc   := λ _ _ _ => HasTrivialNatEquiv.natEquiv,
      rightId := λ _     => HasTrivialNatEquiv.natEquiv,
      leftId  := λ _     => HasTrivialNatEquiv.natEquiv }

    variable [h : HasNatOpEquiv A B]

    instance natIsCategoricalPreorder : IsCategoricalPreorder h.Nat :=
    { assoc   := h.assoc,
      leftId  := h.leftId,
      rightId := h.rightId }

  end HasNatOpEquiv

  section

    variable {U : Universe.{u, uu}} {V : Universe.{v, vv}} {W : Universe.{w, ww}} [IsHomUniverse W]
             [HasCatProp U W] [HasCatProp V W] (A : Category U W) (B : Category V W)
             [HasFunProp A B]

    def natRel [h : HasNatRel A B] : BundledRelation sort.{max 1 u v w} W := ⟨A ⮕ B, h.Nat⟩

    def funCatDesc [h : HasNatOpEquiv A B] [natHasTransFun : HasTransFun h.Nat] :
      CatDesc (natRel A B) :=
    { homIsPreorder            := HasNatOp.natIsPreorder A B,
      homHasTransFun           := natHasTransFun,
      homIsCategoricalPreorder := HasNatOpEquiv.natIsCategoricalPreorder A B }

  end

  class HasNaturality {U : Universe.{u, uu}} {V : Universe.{v, vv}} {W : Universe.{w, ww}}
                      [IsHomUniverse.{w, ww, iw, iww} W] [HasCatProp U W] [HasCatProp V W]
                      [hFunCat : HasCatProp sort.{max 1 u v w} W]
                      (A : Category U W) (B : Category V W) [hFun : HasFunProp A B] extends
    HasNatOpEquiv A B where
  [natHasTransFun : HasTransFun Nat]
  (defFunCat : DefCat (funCatDesc A B))

  namespace HasNaturality

    open HasFunProp HasFunProp.Functor HasNatRel HasNatOp

    section

      variable {U : Universe.{u, uu}} {V : Universe.{v, vv}} {W : Universe.{w, ww}}
               [IsHomUniverse W] [HasCatProp U W] [HasCatProp V W]
               [HasCatProp sort.{max 1 u v w} W]

      section

        variable (A : Category U W) (B : Category V W) [HasFunProp A B] [h : HasNaturality A B]

        instance : HasTransFun h.Nat := h.natHasTransFun

        def funCat : Category sort.{max 1 u v w} W := DefCat.toCategory h.defFunCat
        infixr:20 " ⮕' " => CategoryTheory.HasNaturality.funCat

        instance : CoeFun (A ⮕' B) (λ _ => A → B) := HasFunProp.Functor.coeFun

      end

      section

        variable {A : Category U W} {B : Category V W} [HasFunProp A B] [h : HasNaturality A B]

        def natReflEq' (F : A ⮕' B) (a : A) :
          nat (idHom F) a ≃' idHom (F a) :=
        natReflEq F a • natCongrArg (DefCat.catReflEq F) a

        def natTransEq' {F G H : A ⮕' B} (η : F ⇾ G) (ε : G ⇾ H) (a : A) :
          nat (compHom η ε) a ≃' nat ε a • nat η a :=
        natTransEq η ε a • natCongrArg (DefCat.catTransEq η ε) a

        variable {F G : A ⮕' B}

        def natHalfInv {η : F ⇾ G} {ε : G ⇾ F} (e : HalfInv η ε) (a : A) :
          HalfInv (nat η a) (nat ε a) :=
        natReflEq' F a • natCongrArg e a • (natTransEq' η ε a)⁻¹

        instance natIsInv (η : F ⇾ G) (ε : G ⇾ F) [isInv : IsInv η ε] (a : A) :
          IsInv (nat η a) (nat ε a) :=
        { leftInv  := natHalfInv isInv.leftInv  a,
          rightInv := natHalfInv isInv.rightInv a }

        def natIsoDesc (η : IsoDesc F G) (a : A) : IsoDesc (F a) (G a) :=
        { toHom  := nat η.toHom  a,
          invHom := nat η.invHom a,
          isInv  := natIsInv η.toHom η.invHom (isInv := η.isInv) a }

      end

    end

  end HasNaturality



  structure NatIsoDesc {U : Universe.{u, uu}} {V : Universe.{v, vv}} {W : Universe.{w, ww}}
                       [IsHomUniverse.{w, ww, iw, iww} W] [HasCatProp U W] [HasCatProp V W]
                       {A : Category U W} {B : Category V W} [hBIso : HasIsomorphisms B]
                       [hFunProp : HasFunProp A B] (F G : A ⮕ B) :
    Sort (max 1 u w iw) where
  -- Note: `isInvNat` is redundant (see `construct`), but we include it anyway because in strict
  -- cases, it contains a much simpler term.
  (η        : MetaQuantification hBIso.Iso F.φ G.φ)
  [isToNat  : IsNatural (preFun F) (preFun G) (λ a => HasIsoRel.toHom  (η a))]
  [isInvNat : IsNatural (preFun G) (preFun F) (λ a => HasIsoRel.invHom (η a))]

  namespace NatIsoDesc

    open HasIsoRel HasIsoOp HasIsomorphisms HasIsoPreFun HasIsoFun HasNatRel HasNatOp HasNaturality

    variable {U : Universe.{u, uu}} {V : Universe.{v, vv}} {W : Universe.{w, ww}}
             [IsHomUniverse W]

    section

      variable [HasCatProp U W] [HasCatProp V W] {A : Category U W} {B : Category V W}
               [hBIso : HasIsomorphisms B] [hFunProp : HasFunProp A B]

      -- It would be nice if we could just use the corresponding code from `Meta.lean` here.
      -- However, we are in the special situation that only terms involving `η` are invertible,
      -- but `mapHom F f` and `mapHom G f` are not. The code in `Meta.lean` currently cannot deal
      -- with this; all operations that involve invertible elements ultimately rely on `HasSymm` for
      -- the entire relation.

      def construct {F G : A ⮕ B} (η : MetaQuantification hBIso.Iso F.φ G.φ)
                    [isToNat : IsNatural (preFun F) (preFun G) (λ a => HasIsoRel.toHom (η a))] :
        NatIsoDesc F G :=
      { η        := η,
        isToNat  := isToNat,
        isInvNat := { nat := λ {a b} f => (cancelLeftId (mapHom F f • invHom (η a)) (leftInv (η b)) •
                                           (assoc (mapHom F f • invHom (η a)) (toHom (η b)) (invHom (η b)))⁻¹) •
                                          congrArgTransRight (assoc (invHom (η a)) (mapHom F f) (toHom (η b)))
                                                             (invHom (η b)) •
                                          assoc (invHom (η a)) (toHom (η b) • mapHom F f) (invHom (η b)) •
                                          congrArgTransLeft (invHom (η a))
                                                            (congrArgTransRight (isToNat.nat f)⁻¹
                                                                                (invHom (η b)) •
                                                             assoc (toHom (η a)) (mapHom G f) (invHom (η b))) •
                                          (cancelRightId (rightInv (η a)) (invHom (η b) • mapHom G f) •
                                           assoc (invHom (η a)) (toHom (η a)) (invHom (η b) • mapHom G f))⁻¹ } }

      def strict {φ : A → B} {F G : hFunProp.Fun φ} (hEq : NatDesc.StrictNaturality F G) :
        NatIsoDesc ⟨F⟩ ⟨G⟩ :=
      { η        := λ a => idIso (φ a),
        isToNat  := { nat := λ {a b} f => (cancelRightId (toHomReflEq (φ a)) (mapHom ⟨G⟩ f))⁻¹ •
                                          hEq f •
                                          cancelLeftId (mapHom ⟨F⟩ f) (toHomReflEq (φ b)) }
        isInvNat := { nat := λ {a b} f => (cancelRightId (invHomReflEq (φ a)) (mapHom ⟨F⟩ f))⁻¹ •
                                          (hEq f)⁻¹ •
                                          cancelLeftId (mapHom ⟨G⟩ f) (invHomReflEq (φ b)) }, }

      def refl (F : A ⮕ B) : NatIsoDesc F F :=
      { η        := MetaQuantification.refl hBIso.Iso F.φ,
        isToNat  := { nat := λ {a b} f => (cancelRightId (toHomReflEq (F a)) (mapHom F f))⁻¹ •
                                          cancelLeftId (mapHom F f) (toHomReflEq (F b)) },
        isInvNat := { nat := λ {a b} f => (cancelRightId (invHomReflEq (F a)) (mapHom F f))⁻¹ •
                                          cancelLeftId (mapHom F f) (invHomReflEq (F b)) } }

      def symm {F G : A ⮕ B} (η : NatIsoDesc F G) : NatIsoDesc G F :=
      { η        := MetaQuantification.symm hBIso.Iso η.η,
        isToNat  := { nat := λ {a b} f => (congrArgTransRight (toHomSymmEq (η.η a)) (mapHom F f))⁻¹ •
                                          η.isInvNat.nat f •
                                          congrArgTransLeft (mapHom G f) (toHomSymmEq (η.η b)) },
        isInvNat := { nat := λ {a b} f => (congrArgTransRight (invHomSymmEq (η.η a)) (mapHom G f))⁻¹ •
                                          η.isToNat.nat f •
                                          congrArgTransLeft (mapHom F f) (invHomSymmEq (η.η b)) } }

      def trans {F G H : A ⮕ B} (η : NatIsoDesc F G) (ε : NatIsoDesc G H) : NatIsoDesc F H :=
      { η        := MetaQuantification.trans hBIso.Iso η.η ε.η,
        isToNat  := { nat := λ {a b} f => (congrArgTransRight (toHomTransEq (η.η a) (ε.η a)) (mapHom H f))⁻¹ •
                                          (IsNatural.trans _ _ (hη := η.isToNat) (hε := ε.isToNat)).nat f •
                                          congrArgTransLeft (mapHom F f) (toHomTransEq (η.η b) (ε.η b)) },
        isInvNat := { nat := λ {a b} f => (congrArgTransRight (invHomTransEq (η.η a) (ε.η a)) (mapHom F f))⁻¹ •
                                          (IsNatural.trans _ _ (hη := ε.isInvNat) (hε := η.isInvNat)).nat f •
                                          congrArgTransLeft (mapHom H f) (invHomTransEq (η.η b) (ε.η b)) } }

      variable {F G : A ⮕ B} (η : NatIsoDesc F G)

      @[reducible] def natIso    (a : A) : F a ⇿ G a := η.η a
      @[reducible] def natToHom  (a : A) : F a ⇾ G a := toHom  (natIso η a)
      @[reducible] def natInvHom (a : A) : G a ⇾ F a := invHom (natIso η a)

      def toNatDesc : NatDesc F G :=
      { η     := natToHom η,
        isNat := η.isToNat }

      def invNatDesc : NatDesc G F :=
      { η     := natInvHom η,
        isNat := η.isInvNat }

      structure IsoDescBuilder [hNatOp : HasNatOp A B] where
      (defToNat  : DefNat (toNatDesc  η))
      (defInvNat : DefNat (invNatDesc η))
      (leftInv   : NatEquiv (defInvNat.η • defToNat.η) (HasRefl.refl F)
                            (λ a => (natReflEq F a)⁻¹ •
                                    leftInv (η.η a) •
                                    congrArgTrans byNatDef byNatDef •
                                    natTransEq defToNat.η defInvNat.η a))
      (rightInv  : NatEquiv (defToNat.η • defInvNat.η) (HasRefl.refl G)
                            (λ b => (natReflEq G b)⁻¹ •
                                    rightInv (η.η b) •
                                    congrArgTrans byNatDef byNatDef •
                                    natTransEq defInvNat.η defToNat.η b))

      namespace IsoDescBuilder

        variable [HasCatProp sort.{max 1 u v w} W] [hNat : HasNaturality A B] (e : IsoDescBuilder η)

        def isoDesc : IsoDesc (A := A ⮕' B) F G :=
        { toHom  := e.defToNat.η,
          invHom := e.defInvNat.η,
          isInv  := { leftInv  := (DefCat.catReflEq (A := hNat.defFunCat) F)⁻¹ •
                                  e.leftInv •
                                  DefCat.catTransEq (A := hNat.defFunCat) e.defToNat.η e.defInvNat.η,
                      rightInv := (DefCat.catReflEq (A := hNat.defFunCat) G)⁻¹ •
                                  e.rightInv •
                                  DefCat.catTransEq (A := hNat.defFunCat) e.defInvNat.η e.defToNat.η } }

      end IsoDescBuilder

    end

    section

      variable [IsCatUniverse U W] [IsCatUniverse V W] [IsFunUniverse U V W]
               {A : Category U W} {B : Category V W} {F G : A ⮕ B} (η : NatIsoDesc F G)

      def isoNaturality {a b : A} (e : a ⇿ b) :
        natIso η b • mapIso F e ≃' mapIso G e • natIso η a :=
      toHomInj ((congrArgTransLeft (natToHom η a) (toHomComm G e) •
                 toHomTransEq (natIso η a) (mapIso G e))⁻¹ •
                η.isToNat.nat (toHom e) •
                (congrArgTransRight (toHomComm F e) (natToHom η b) •
                 toHomTransEq (mapIso F e) (natIso η b)))

      instance natIso.isNat :
        IsNatural (preFun (isoFunctor F)) (preFun (isoFunctor G)) (natIso η) :=
      ⟨λ {a b} e => (congrArgTransLeft (natIso η a) (mapIsoEq G e) •
                     DefCat.catTransEq (A := defIsoCat) (natIso η a) (mapIso' G e))⁻¹ •
                    isoNaturality η e •
                    (congrArgTransRight (mapIsoEq F e) (natIso η b) •
                     DefCat.catTransEq (A := defIsoCat) (mapIso' F e) (natIso η b))⟩

      def toIsoNatDesc : NatDesc (isoFunctor F) (isoFunctor G) :=
      { η     := natIso       η,
        isNat := natIso.isNat η }

    end

  end NatIsoDesc



  class HasIsoNat {U : Universe.{u, uu}} {V : Universe.{v, vv}} {W : Universe.{w, ww}}
                  [IsHomUniverse.{w, ww, iw, iww} W] [IsCatUniverse U W] [IsCatUniverse V W]
                  [IsSortCatUniverse.{max 1 u v w} W] {A : Category U W} {B : Category V W}
                  [hFun : HasFunProp A B] [hNat : HasNaturality A B] (F G : A ⮕' B) where
  (defNatIso (η : F ⇿ G) (a : A) : HasIsoRel.DefIso (HasNaturality.natIsoDesc (HasIsoRel.desc η) a))
  (defNatIsoFun (a : A) : (F ⇿ G) ⟶{λ η => (defNatIso η a).e} (F a ⇿ G a))

  namespace HasIsoNat

    open HasIsoRel HasIsoOp HasIsoPreFun HasNatRel

    variable {U : Universe.{u, uu}} {V : Universe.{v, vv}} {W : Universe.{w}} [IsHomUniverse W]
             [IsCatUniverse U W] [IsCatUniverse V W] [IsSortCatUniverse.{max 1 u v w} W]
             {A : Category U W} {B : Category V W} [HasFunProp A B] [HasNaturality A B]

    def natIso {F G : A ⮕' B} [h : HasIsoNat F G] (η : F ⇿ G) (a : A) : F a ⇿ G a :=
    (h.defNatIso η a).e

    @[reducible] def natIsoFun (F G : A ⮕' B) [h : HasIsoNat F G] (a : A) :
      (F ⇿ G) ⟶ (F a ⇿ G a) :=
    fromDefFun (h.defNatIsoFun a)

    section

      variable {F G : A ⮕' B} [h : HasIsoNat F G]

      instance (η : F ⇿ G) (a : A) : IsFunApp (F ⇿ G) (natIso η a) :=
      { F := natIsoFun F G a,
        a := η,
        e := byDef }

      def natIsoCongrArg {η₁ η₂ : F ⇿ G} (e : η₁ ≃ η₂) (a : A) :
        natIso η₁ a ≃ natIso η₂ a :=
      defCongrArg (h.defNatIsoFun a) e

      def natIsoToHomComm (η : F ⇿ G) (a : A) :
        toHom (natIso η a) ≃' nat (toHom η) a :=
      byToDef

      def natIsoInvHomComm (η : F ⇿ G) (a : A) :
        invHom (natIso η a) ≃' nat (invHom η) a :=
      byInvDef

      def natIsoEq {η₁ η₂ : F ⇿ G} {a : A} :
        nat (toHom η₁) a ≃ nat (toHom η₂) a → natIso η₁ a ≃ natIso η₂ a :=
      λ e => toHomInj ((natIsoToHomComm η₂ a)⁻¹ • e • natIsoToHomComm η₁ a)

      def natIsoDesc (η : F ⇿ G) : NatIsoDesc F G :=
      { η        := natIso η,
        isToNat  := { nat := λ {a b} f => congrArgTransRight (natIsoToHomComm η a)⁻¹ (mapHom G f) •
                                          naturality (toHom η) f •
                                          congrArgTransLeft (mapHom F f) (natIsoToHomComm η b) },
        isInvNat := { nat := λ {a b} f => congrArgTransRight (natIsoInvHomComm η a)⁻¹ (mapHom F f) •
                                          naturality (invHom η) f •
                                          congrArgTransLeft (mapHom G f) (natIsoInvHomComm η b) } }

      structure DefNatIso (desc : NatIsoDesc F G) where
      (η             : F ⇿ G)
      (natEq (a : A) : natIso η a ≃ NatIsoDesc.natIso desc a)

      section

        variable {desc : NatIsoDesc F G} {η : DefNatIso desc} {a : A}

        def byNatIsoDef : natIso η.η a ≃ NatIsoDesc.natIso desc a := η.natEq a

        def byNatIsoToHomDef  : nat (toHom  η.η) a ≃' NatIsoDesc.natToHom  desc a :=
        toHomCongrArg  byNatIsoDef • (natIsoToHomComm  η.η a)⁻¹

        def byNatIsoInvHomDef : nat (invHom η.η) a ≃' NatIsoDesc.natInvHom desc a :=
        invHomCongrArg byNatIsoDef • (natIsoInvHomComm η.η a)⁻¹

      end

    end

    section

      variable {φ : A → B} {F G : HasFunProp.Fun φ} [h : HasIsoNat ⟨F⟩ ⟨G⟩]

      def StrictDefNatIso (hEq : NatDesc.StrictNaturality F G) := DefNatIso (NatIsoDesc.strict hEq)

      variable {hEq : NatDesc.StrictNaturality F G} {η : StrictDefNatIso hEq} {a : A}

      def byStrictNatIsoDef : natIso η.η a ≃ idIso (φ a) := byNatIsoDef

      def byStrictNatIsoToHomDef  : nat (toHom  η.η) a ≃ idHom (φ a) :=
      toHomReflEq  (φ a) • byNatIsoToHomDef

      def byStrictNatIsoInvHomDef : nat (invHom η.η) a ≃ idHom (φ a) :=
      invHomReflEq (φ a) • byNatIsoInvHomDef

    end

  end HasIsoNat

  class HasIsoNaturality {U : Universe.{u, uu}} {V : Universe.{v, vv}} {W : Universe.{w, ww}}
                         [IsHomUniverse.{w, ww, iw, iww} W] [IsCatUniverse U W] [IsCatUniverse V W]
                         [IsSortCatUniverse.{max 1 u v w} W] [IsFunUniverse U V W]
                         (A : Category U W) (B : Category V W) extends
    HasNaturality A B where
  [hasIsoNat (F G : A ⮕' B) : HasIsoNat F G]

  namespace HasIsoNaturality

    open HasIsoRel HasIsoOp HasIsomorphisms HasIsoPreFun HasNatRel HasNaturality HasIsoNat

    variable {U : Universe.{u, uu}} {V : Universe.{v, vv}} {W : Universe.{w}} [IsHomUniverse W]
             [IsCatUniverse U W] [IsCatUniverse V W] [IsSortCatUniverse.{max 1 u v w} W]
             [IsFunUniverse U V W]

    section

      variable {A : Category U W} {B : Category V W} [h : HasIsoNaturality A B]

      instance (F G : A ⮕' B) : HasIsoNat F G := h.hasIsoNat F G

      def natIsoReflEq (F : A ⮕' B) (a : A) : natIso (idIso F) a ≃ idIso (F a) :=
      toHomInj ((toHomReflEq (F a))⁻¹ •
                natReflEq' F a •
                (natCongrArg (toHomReflEq F) a •
                 natIsoToHomComm (idIso F) a))

      def natIsoSymmEq {F G : A ⮕' B} (η : F ⇿ G) (a : A) : natIso η⁻¹ a ≃ (natIso η a)⁻¹ :=
      toHomInj ((natIsoInvHomComm η a •
                 toHomSymmEq (natIso η a))⁻¹ •
                (natCongrArg (toHomSymmEq η) a •
                 natIsoToHomComm η⁻¹ a))

      def natIsoTransEq {F G H : A ⮕' B} (η : F ⇿ G) (ε : G ⇿ H) (a : A) :
        natIso (ε • η) a ≃ natIso ε a • natIso η a :=
      toHomInj ((congrArgTrans (natIsoToHomComm η a) (natIsoToHomComm ε a) •
                 toHomTransEq (natIso η a) (natIso ε a))⁻¹ •
                natTransEq' (toHom η) (toHom ε) a •
                (natCongrArg (toHomTransEq η ε) a •
                 natIsoToHomComm (ε • η) a))

    end

    class HasTrivialIsoNaturalityCondition (A : Category U W) (B : Category V W)
                                           [h : HasIsoNaturality A B] where
    (natIso {F G : A ⮕' B} (desc : NatIsoDesc F G) : DefNatIso desc)

    namespace HasTrivialIsoNaturalityCondition

      variable {A : Category U W} {B : Category V W} [HasIsoNaturality A B]
               [h : HasTrivialIsoNaturalityCondition A B]

      def defNatIso {F G : A ⮕' B} {desc : NatIsoDesc F G} : DefNatIso desc := h.natIso desc

    end HasTrivialIsoNaturalityCondition

  end HasIsoNaturality



  class IsNatUniverse (U : Universe.{u, uu}) (V : Universe.{v, vv}) (W : Universe.{w, ww})
                      [IsHomUniverse.{w, ww, iw, iww} W] [IsCatUniverse U W] [IsCatUniverse V W]
                      [hFunCatUniv : IsSortCatUniverse.{max 1 u v w} W] [IsFunUniverse U V W] where
  [hasNat (A : Category U W) (B : Category V W) : HasIsoNaturality A B]

  namespace IsNatUniverse

    open HasIsoPreFun HasNaturality HasIsoNat

    section

      variable {U : Universe.{u, uu}} {V : Universe.{v, vv}} {W : Universe.{w}} [IsHomUniverse W]
               [IsCatUniverse U W] [IsCatUniverse V W] [IsSortCatUniverse.{max 1 u v w} W]
               [IsFunUniverse U V W] [h : IsNatUniverse U V W]

      instance (A : Category U W) (B : Category V W) : HasIsoNaturality A B :=
      h.hasNat A B

    end

    section

      variable (U : Universe.{u, uu}) (V : Universe.{v, vv}) (W : Universe.{w, ww}) [IsHomUniverse W]
               [IsCatUniverse U W] [IsCatUniverse V W] [IsSortCatUniverse.{max 1 u v w} W]
               [IsFunUniverse U V W] [h : IsNatUniverse U V W]

      instance hasFunctors : HasFunctors (univ U W) (univ V W) (univ sort.{max 1 u v w} W) :=
      { Fun   := λ A B => A ⮕' B,
        apply := Functor.φ }

      instance hasCongrArg : HasCongrArg (univ U W) (univ V W) := ⟨λ {_ _} F {_ _} e => mapIso F e⟩
      instance hasCongrFun : HasCongrFun (univ U W) (univ V W) := ⟨λ e a => natIso e a⟩

    end
  
  end IsNatUniverse

  class IsSortNatUniverse (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw, iww} W] extends
    IsSortCatUniverse.{max 1 u w} W, IsSortFunUniverse.{max 1 u w, max 1 u w} W,
    IsNatUniverse sort.{max 1 u w} sort.{max 1 u w} W

  namespace IsSortNatUniverse

    variable (W : Universe.{w, ww}) [IsHomUniverse W] [h : IsSortNatUniverse.{u} W]

    @[reducible] def univ : Universe.{max 1 u w, max (max 1 u w + 1) ww} :=
    IsSortCatUniverse.univ.{max 1 u w} W

    instance hasInternalFunctors : HasInternalFunctors (univ.{u} W) := ⟨⟩

    class HasTrivialNaturalIsomorphisms where
    [hasTrivialNatEquiv (A B : Category sort.{max 1 u w} W) : HasNatRel.HasTrivialNatEquiv A B]
    [hasTrivialIsoNat   (A B : Category sort.{max 1 u w} W) : HasIsoNaturality.HasTrivialIsoNaturalityCondition A B]

    namespace HasTrivialNaturalIsomorphisms

      variable [h : HasTrivialNaturalIsomorphisms W]

      instance (A B : Category sort.{max 1 u w} W) : HasNatRel.HasTrivialNatEquiv A B                      := h.hasTrivialNatEquiv A B
      instance (A B : Category sort.{max 1 u w} W) : HasIsoNaturality.HasTrivialIsoNaturalityCondition A B := h.hasTrivialIsoNat A B

    end HasTrivialNaturalIsomorphisms

  end IsSortNatUniverse

end CategoryTheory
