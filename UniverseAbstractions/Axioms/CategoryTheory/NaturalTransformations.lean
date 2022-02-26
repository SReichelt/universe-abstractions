import UniverseAbstractions.Axioms.CategoryTheory.Basic
import UniverseAbstractions.Axioms.CategoryTheory.Functors



set_option autoBoundImplicitLocal false
set_option synthInstance.maxHeartbeats 2000
--set_option pp.universes true

universe u u' u'' u''' v w ww iw iww



namespace CategoryTheory

  open MetaRelation MetaFunctor MetaQuantification HasTransFun HasSymmFun
       IsAssociative IsCategoricalPreorder IsTransFunctor
       HasCatProp HasCatProp.Category HasFunProp HasFunProp.Functor
       HasFunctors HasCongrArg HasCongrFun HasLinearFunOp HasNonLinearFunOp

  structure NatDesc {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]
                    [HasCatProp.{u} W] [HasCatProp.{v} W] {A : Category.{u} W} {B : Category.{v} W}
                    [hFunProp : HasFunProp A B] (F G : A ⮕ B) :
    Sort (max 1 u w iw) where
  (η     : MetaQuantification (Hom B) F.φ G.φ)
  [isNat : IsNatural (preFun F) (preFun G) η]

  namespace NatDesc

    variable {W : Universe} [IsHomUniverse W] [HasCatProp.{u} W] [HasCatProp.{v} W]
             {A : Category.{u} W} {B : Category.{v} W} [hFunProp : HasFunProp A B]

    def StrictNaturality {φ : A → B} (F G : hFunProp.Fun φ) :=
    ∀ {a b : A} (f : a ⇾ b), HasInstanceEquivalences.Rel (φ a ⇾ φ b) (mapHom ⟨F⟩ f) (mapHom ⟨G⟩ f)

    def strict {φ : A → B} {F G : hFunProp.Fun φ} (hEq : StrictNaturality F G) : NatDesc ⟨F⟩ ⟨G⟩ :=
    { η     := λ a => idHom (φ a),
      isNat := IsNatural.fromEq (hFunProp.desc F).F (hFunProp.desc G).F hEq }

    section

      variable {F G : A ⮕ B} (η : NatDesc F G)

      instance : IsNatural (preFun F) (preFun G) η.η := η.isNat

    end

    def refl (F : A ⮕ B) : NatDesc F F := ⟨MetaQuantification.refl (Hom B) F.φ⟩

    def trans {F G H : A ⮕ B} (η : NatDesc F G) (ε : NatDesc G H) :
      NatDesc F H :=
    ⟨MetaQuantification.trans (Hom B) η.η ε.η⟩

  end NatDesc

  class HasNatRel {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]
                  [HasCatProp.{u} W] [HasCatProp.{v} W] (A : Category.{u} W) (B : Category.{v} W)
                  [hFunProp : HasFunProp A B] where
  (Nat                             : MetaRelation (A ⮕ B) W)
  (desc {F G : A ⮕ B}              : Nat F G → NatDesc F G)
  (defNatFun (F G : A ⮕ B) (a : A) : Nat F G ⟶{λ η => (desc η).η a} (F a ⇾ G a))

  namespace HasNatRel

    open HasFunctors HasFunProp HasFunProp.Functor

    variable {W : Universe} [IsHomUniverse W] [HasCatProp.{u} W] [HasCatProp.{v} W]

    def natRel (A : Category.{u} W) (B : Category.{v} W) [HasFunProp A B] [h : HasNatRel A B] :
      BundledRelation W :=
    ⟨h.Nat⟩

    section

      variable {A : Category.{u} W} {B : Category.{v} W} [hFunProp : HasFunProp A B]
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
        defCongrArg (defNatFun F G a) e

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

      def byStrictNatDef {φ : A → B} {F G : hFunProp.Fun φ} {hEq : NatDesc.StrictNaturality F G}
                         {η : DefNat (NatDesc.strict hEq)} {a : A} :
        nat η.η a ≃ idHom (φ a) :=
      byNatDef

    end

    class HasTrivialNaturalityCondition (A : Category.{u} W) (B : Category.{v} W)
                                        [hFunProp : HasFunProp A B] [h : HasNatRel A B] where
    (nat {F G : A ⮕ B} (desc : NatDesc F G) : DefNat desc)

    namespace HasTrivialNaturalityCondition

      variable {A : Category.{u} W} {B : Category.{v} W} [HasFunProp A B] [HasNatRel A B]
               [h : HasTrivialNaturalityCondition A B]

      def defNat {F G : A ⮕ B} {desc : NatDesc F G} : DefNat desc := h.nat desc

    end HasTrivialNaturalityCondition

    class HasTrivialNatEquiv (A : Category.{u} W) (B : Category.{v} W) [hFunProp : HasFunProp A B]
                             [h : HasNatRel A B] where
    (equiv {F G : A ⮕ B} (η₁ η₂ : h.Nat F G) (hNat : ∀ a, nat η₁ a ≃ nat η₂ a) :
       NatEquiv η₁ η₂ hNat)

    namespace HasTrivialNatEquiv

      variable {A : Category.{u} W} {B : Category.{v} W} [HasFunProp A B] [hNatRel : HasNatRel A B]
               [h : HasTrivialNatEquiv A B]

      def natEquiv {F G : A ⮕ B} {η₁ η₂ : hNatRel.Nat F G} {hNat : ∀ a, nat η₁ a ≃ nat η₂ a} :
        NatEquiv η₁ η₂ hNat :=
      h.equiv η₁ η₂ hNat

    end HasTrivialNatEquiv

  end HasNatRel

  class HasNatOp {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]
                 [HasCatProp.{u} W] [HasCatProp.{v} W] (A : Category.{u} W) (B : Category.{v} W)
                 [hFunProp : HasFunProp A B] extends
    HasNatRel A B where
  (defRefl (F : A ⮕ B) : HasNatRel.DefNat (NatDesc.refl F))
  (defTrans {F G H : A ⮕ B} (η : Nat F G) (ε : Nat G H) :
     HasNatRel.DefNat (NatDesc.trans (desc η) (desc ε)))

  namespace HasNatOp

    open HasFunProp HasFunProp.Functor HasNatRel

    variable {W : Universe} [IsHomUniverse W] [HasCatProp.{u} W] [HasCatProp.{v} W]

    section

      variable (A : Category.{u} W) (B : Category.{v} W) [HasFunProp A B]

      instance trivial [HasNatRel A B] [HasTrivialNaturalityCondition A B] : HasNatOp A B :=
      { defRefl  := λ _   => HasTrivialNaturalityCondition.defNat,
        defTrans := λ _ _ => HasTrivialNaturalityCondition.defNat }

      variable [h : HasNatOp A B]

      instance natIsPreorder : IsPreorder h.Nat :=
      { refl  := λ F   => (h.defRefl F).η,
        trans := λ η ε => (h.defTrans η ε).η }

    end

    section

      variable {A : Category.{u} W} {B : Category.{v} W} [HasFunProp A B] [h : HasNatOp A B]

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

  class HasNatOpEquiv {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]
                      [HasCatProp.{u} W] [HasCatProp.{v} W] (A : Category.{u} W) (B : Category.{v} W)
                      [hFunProp : HasFunProp A B] extends
    HasNatOp A B where
  (assoc {F G H I : A ⮕ B} (η : Nat F G) (ε : Nat G H) (θ : Nat H I) :
     HasNatRel.NatEquiv ((θ • ε) • η) (θ • (ε • η)) (HasNatOp.natAssoc η ε θ))
  (rightId {F G : A ⮕ B} (η : Nat F G) :
     HasNatRel.NatEquiv (η • HasRefl.refl F) η (HasNatOp.natRightId η))
  (leftId {F G : A ⮕ B} (η : Nat F G) :
     HasNatRel.NatEquiv (HasRefl.refl G • η) η (HasNatOp.natLeftId η))

  namespace HasNatOpEquiv

    open HasNatRel

    variable {W : Universe} [IsHomUniverse W] [HasCatProp.{u} W] [HasCatProp.{v} W]
             (A : Category.{u} W) (B : Category.{v} W) [HasFunProp A B] [HasFunProp A B]

    instance trivial [HasNatOp A B] [HasTrivialNatEquiv A B] : HasNatOpEquiv A B :=
    { assoc   := λ _ _ _ => HasTrivialNatEquiv.natEquiv,
      rightId := λ _     => HasTrivialNatEquiv.natEquiv,
      leftId  := λ _     => HasTrivialNatEquiv.natEquiv }

    variable [h : HasNatOpEquiv A B]

    instance natIsCategoricalPreorder : IsCategoricalPreorder h.Nat :=
    { assoc   := h.assoc,
      leftId  := h.leftId,
      rightId := h.rightId }

    def funCatDesc [natHasTransFun : HasTransFun h.Nat] : CatDesc (natRel A B) :=
    { homIsPreorder            := HasNatOp.natIsPreorder A B,
      homHasTransFun           := natHasTransFun,
      homIsCategoricalPreorder := natIsCategoricalPreorder A B }

  end HasNatOpEquiv

  class HasNaturality {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]
                      [HasCatProp.{u} W] [HasCatProp.{v} W] [hFunCat : HasCatProp.{max 1 u v w} W]
                      (A : Category.{u} W) (B : Category.{v} W) [hFunProp : HasFunProp A B] extends
    HasNatOpEquiv A B where
  [natHasTransFun : HasTransFun Nat]
  (defFunCat : DefCat (HasNatOpEquiv.funCatDesc A B))

  namespace HasNaturality

    open HasFunProp HasFunProp.Functor HasNatRel HasNatOp

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]

    section

      variable [HasCatProp.{u} W] [HasCatProp.{v} W] [hFunCat : HasCatProp.{max 1 u v w} W]
               (A : Category.{u} W) (B : Category.{v} W) [HasFunProp A B] [h : HasNaturality A B]

      instance : HasTransFun h.Nat := h.natHasTransFun

      def funCat : Category.{max 1 u v w} W := HasCatProp.DefCat.toCategory h.defFunCat
      infixr:20 " ⮕' " => CategoryTheory.HasNaturality.funCat

      instance : CoeFun (A ⮕' B) (λ _ => A → B) := HasFunProp.Functor.coeFun

    end

    section

      variable [HasCatProp.{u} W] [HasCatProp.{v} W] [hFunCat : HasCatProp.{max 1 u v w} W]
               {A : Category.{u} W} {B : Category.{v} W} [HasFunProp A B] [h : HasNaturality A B]

      def natReflEq' (F : A ⮕' B) (a : A) :
        nat (idHom F) a ≃ idHom (F a) :=
      natReflEq F a • natCongrArg (DefCat.catReflEq F) a

      def natTransEq' {F G H : A ⮕' B} (η : F ⇾ G) (ε : G ⇾ H) (a : A) :
        nat (compHom η ε) a ≃ nat ε a • nat η a :=
      natTransEq η ε a • natCongrArg (DefCat.catTransEq η ε) a

    end

    section

      variable [HasCatProp.{u} W] [HasCatProp.{u'} W] [HasCatProp.{u''} W]
               {A : Category.{u} W} {B : Category.{u'} W} {C : Category.{u''} W}
               [hFunBC : HasFunProp B C]

      structure FunFunDesc (F : A → (B ⮕ C)) where
      (natDesc {a₁ a₂ : A} : (a₁ ⇾ a₂) → NatDesc (F a₁) (F a₂))
      (natDescReflEq (a : A) (b : B) : (natDesc (idHom a)).η b ≃ idHom ((F a) b))
      (natDescTransEq {a₁ a₂ a₃ : A} (f : a₁ ⇾ a₂) (g : a₂ ⇾ a₃) (b : B) :
         (natDesc (g • f)).η b ≃ (natDesc g).η b • (natDesc f).η b)

      variable [HasCatProp.{max 1 u' u'' w} W] [hNatBC : HasNaturality B C] {F : A → (B ⮕' C)}

      structure DefFunFunBaseBase (desc : FunFunDesc F) where
      (defNat {a₁ a₂ : A} (f : a₁ ⇾ a₂) : DefNat (desc.natDesc f))
      (natReflEq (a : A) :
         DefNatEquiv (defNat (idHom a)) (HasNatOp.defRefl (F a))
                     (desc.natDescReflEq a))
      (natTransEq {a₁ a₂ a₃ : A} (f : a₁ ⇾ a₂) (g : a₂ ⇾ a₃) :
         DefNatEquiv (defNat (g • f)) (HasNatOp.defTrans (defNat f).η (defNat g).η)
                     (λ b => (congrArgTrans byNatDef byNatDef)⁻¹ •
                             desc.natDescTransEq f g b))

      structure DefFunFunBase (desc : FunFunDesc F) extends DefFunFunBaseBase desc where
      (defNatFun (a₁ a₂ : A) : (a₁ ⇾ a₂) ⟶{λ f => (defNat f).η} (F a₁ ⇾ F a₂))

      namespace DefFunFunBase

        variable {desc : FunFunDesc F} (G : DefFunFunBase desc)

        @[reducible] def natFun (a₁ a₂ : A) : (a₁ ⇾ a₂) ⟶ (F a₁ ⇾ F a₂) :=
        G.defNatFun a₁ a₂

        def natPreFun : PreFunctor (Hom A) (Hom (B ⮕' C)) F := ⟨natFun G⟩

        instance : IsPreorderFunctor (natPreFun G) :=
        { reflEq  := λ a   => (DefCat.catReflEq (F a))⁻¹ • G.natReflEq a • byDef,
          transEq := λ f g => (DefCat.catTransEq (A := hNatBC.defFunCat) (G.defNat f).η (G.defNat g).η •
                               congrArgTrans byDef byDef)⁻¹ •
                              G.natTransEq f g •
                              byDef }

        def funDesc : FunDesc F := ⟨natPreFun G⟩

      end DefFunFunBase

      structure DefFunFun [hFunABC : HasFunProp A (B ⮕' C)] (desc : FunFunDesc F) extends
        DefFunFunBase desc, DefFun (DefFunFunBase.funDesc toDefFunFunBase)

      namespace DefFunFun

        variable [HasFunProp A (B ⮕' C)] {desc : FunFunDesc F}

        def trivial (G : DefFunFunBase desc) [HasTrivialFunctorialityCondition A (B ⮕' C)] :
          DefFunFun desc :=
        { toDefFunFunBase := G,
          toDefFun        := HasTrivialFunctorialityCondition.defFun }

        def toFunctor (G : DefFunFun desc) : A ⮕ B ⮕' C := DefFun.toFunctor G.toDefFun

        def byFunFunDefNat {G : DefFunFun desc} {a₁ a₂ : A} {f : a₁ ⇾ a₂} :
          mapHom (toFunctor G) f ≃' (G.defNat f).η :=
        DefFun.byMapHomDef

        def byFunFunDef {G : DefFunFun desc} {a₁ a₂ : A} {f : a₁ ⇾ a₂} {b : B} :
          nat (mapHom (toFunctor G) f) b ≃' (desc.natDesc f).η b :=
        byNatDef • natCongrArg byFunFunDefNat b

      end DefFunFun

    end

    section

      variable [HasCatProp.{u} W] [HasCatProp.{u'} W] [HasCatProp.{u''} W]
               [HasCatProp.{max 1 u' u'' w} W]
               {A : Category.{u} W} {B : Category.{u'} W} {C : Category.{u''} W} [hFunBC : HasFunProp B C]
               [hNatBC : HasNaturality B C] [hFunABC : HasFunProp A (B ⮕' C)]

      structure NatNatDesc (F G : A ⮕ B ⮕' C) (η : ∀ a, F a ⇾ G a) where
      (natEq {a₁ a₂ : A} (f : a₁ ⇾ a₂) (b : B) :
         nat (η a₂) b • nat (mapHom F f) b ≃ nat (mapHom G f) b • nat (η a₁) b)

      namespace NatNatDesc

        def StrictNaturality₂ {φ : A → B → C} {F' G' : ∀ a, hFunBC.Fun (φ a)}
                              (F : hFunABC.Fun (λ a => ⟨F' a⟩)) (G : hFunABC.Fun (λ a => ⟨G' a⟩)) :=
        ∀ {a₁ a₂ : A} (f : a₁ ⇾ a₂) (b : B),
          HasInstanceEquivalences.Rel (φ a₁ b ⇾ φ a₂ b) (nat (mapHom ⟨F⟩ f) b) (nat (mapHom ⟨G⟩ f) b)

        def strict {φ : A → B → C} {F' G' : ∀ a, hFunBC.Fun (φ a)}
                   {hEq : ∀ a, NatDesc.StrictNaturality (F' a) (G' a)}
                   {η : ∀ a, DefNat (NatDesc.strict (hEq a))}
                   {F : hFunABC.Fun (λ a => ⟨F' a⟩)} {G : hFunABC.Fun (λ a => ⟨G' a⟩)}
                   (hNatEq : StrictNaturality₂ F G) :
          NatNatDesc ⟨F⟩ ⟨G⟩ (λ a => (η a).η) :=
        { natEq := λ {a₁ a₂} f b => (cancelRightId (byStrictNatDef (hEq := hEq a₁))
                                                   (nat (mapHom ⟨G⟩ f) b))⁻¹ •
                                    hNatEq f b •
                                    cancelLeftId (nat (mapHom ⟨F⟩ f) b)
                                                 (byStrictNatDef (hEq := hEq a₂)) }

      end NatNatDesc

      section

        variable {F G : A ⮕ B ⮕' C} {η : ∀ a, F a ⇾ G a}

        structure DefNatNatBase (desc : NatNatDesc F G η) where
        (natEquiv {a₁ a₂ : A} (f : a₁ ⇾ a₂) :
           NatEquiv (compHom (mapHom F f) (η a₂)) (compHom (η a₁) (mapHom G f))
                    (λ b => (natTransEq' (η a₁) (mapHom G f) b)⁻¹ •
                            desc.natEq f b •
                            natTransEq' (mapHom F f) (η a₂) b))

        namespace DefNatNatBase

          def trivial {desc : NatNatDesc F G η} [HasTrivialNatEquiv B C] : DefNatNatBase desc :=
          { natEquiv := λ _ => HasTrivialNatEquiv.natEquiv }

          variable {desc : NatNatDesc F G η} (ε : DefNatNatBase desc)

          def natDesc : NatDesc F G :=
          { η     := η,
            isNat := ⟨ε.natEquiv⟩ }

        end DefNatNatBase

        structure DefNatNat [HasCatProp.{max 1 u u' u'' w} W] [hNatABC : HasNaturality A (B ⮕' C)]
                            (desc : NatNatDesc F G η) extends
          DefNatNatBase desc, DefNat (DefNatNatBase.natDesc toDefNatNatBase)

        namespace DefNatNat

          variable [HasCatProp.{max 1 u u' u'' w} W] [HasNaturality A (B ⮕' C)]
                  {desc : NatNatDesc F G η}

          def trivial (ε : DefNatNatBase desc) [HasTrivialNaturalityCondition A (B ⮕' C)] :
            DefNatNat desc :=
          { toDefNatNatBase := ε,
            toDefNat        := HasTrivialNaturalityCondition.defNat }

        end DefNatNat

      end

      def byStrictNatNatDef [HasCatProp.{max 1 u u' u'' w} W] [hNatABC : HasNaturality A (B ⮕' C)]
                            {φ : A → B → C} {F' G' : ∀ a, hFunBC.Fun (φ a)}
                            {hEq : ∀ a, NatDesc.StrictNaturality (F' a) (G' a)}
                            {η' : ∀ a, DefNat (NatDesc.strict (hEq a))}
                            {F : hFunABC.Fun (λ a => ⟨F' a⟩)} {G : hFunABC.Fun (λ a => ⟨G' a⟩)}
                            {hNatEq : NatNatDesc.StrictNaturality₂ F G}
                            {η : DefNatNat (NatNatDesc.strict (η := η') hNatEq)} {a : A} {b : B} :
        nat (nat η.η a) b ≃ idHom (φ a b) :=
      byNatDef • natCongrArg (byNatDef (η := η.toDefNat)) b

    end

    section

      variable [HasCatProp.{u} W] [HasCatProp.{u'} W] [HasCatProp.{u''} W] [HasCatProp.{u'''} W]
               [HasCatProp.{max 1 u'' u''' w} W]
               {A : Category.{u} W} {B : Category.{u'} W} {C : Category.{u''} W} {D : Category.{u'''} W}
               [hFunCD : HasFunProp C D] [hNatCD : HasNaturality C D]
               [hFunBCD : HasFunProp B (C ⮕' D)]

      structure FunFunFunDesc (F : A → (B ⮕ C ⮕' D)) where
      (revFunFunDesc (b : B) : FunFunDesc (λ a => (F a) b))
      (natNatDesc {a₁ a₂ : A} (f : a₁ ⇾ a₂) (G : ∀ b, DefFunFunBaseBase (revFunFunDesc b)) :
         NatNatDesc (F a₁) (F a₂) (λ b => ((G b).defNat f).η))

      variable [HasCatProp.{max 1 u' u'' u''' w} W] [hNatBCD : HasNaturality B (C ⮕' D)]
               {F : A → (B ⮕' C ⮕' D)}

      structure DefFunFunFunBase (desc : FunFunFunDesc F) where
      (defRevFunFun (b : B) : DefFunFunBaseBase (desc.revFunFunDesc b))
      (defNatNat {a₁ a₂ : A} (f : a₁ ⇾ a₂) : DefNatNatBase (desc.natNatDesc f defRevFunFun))

      namespace DefFunFunFunBase

        variable {desc : FunFunFunDesc F} (G : DefFunFunFunBase desc)

        def funFunDesc : FunFunDesc F :=
        { natDesc        := λ f     => DefNatNatBase.natDesc (G.defNatNat f),
          natDescReflEq  := λ a   b => (DefCat.catReflEq ((F a) b))⁻¹ •
                                       (G.defRevFunFun b).natReflEq a,
          natDescTransEq := λ f g b => (DefCat.catTransEq (A := hNatCD.defFunCat)
                                                          ((G.defRevFunFun b).defNat f).η
                                                          ((G.defRevFunFun b).defNat g).η)⁻¹ •
                                       (G.defRevFunFun b).natTransEq f g }

      end DefFunFunFunBase

      structure DefFunFunFun [hFunABCD : HasFunProp A (B ⮕' C ⮕' D)] (desc : FunFunFunDesc F) extends
        DefFunFunFunBase desc, DefFunFun (DefFunFunFunBase.funFunDesc toDefFunFunFunBase)

      namespace DefFunFunFun

        variable [hFunABCD : HasFunProp A (B ⮕' C ⮕' D)] {desc : FunFunFunDesc F}

        def trivial (G : DefFunFunFunBase desc) (H : DefFunFunBase (DefFunFunFunBase.funFunDesc G))
                    [HasTrivialFunctorialityCondition A (B ⮕' C ⮕' D)] :
          DefFunFunFun desc :=
        { toDefFunFunFunBase := G,
          toDefFunFun        := DefFunFun.trivial H }

        def toFunctor (G : DefFunFunFun desc) : A ⮕ B ⮕' C ⮕' D := DefFunFun.toFunctor G.toDefFunFun

        def byFunFunFunDefNat {G : DefFunFunFun desc} {a₁ a₂ : A} {f : a₁ ⇾ a₂} {b : B} :
          nat (mapHom (toFunctor G) f) b ≃' (G.funFunDesc.natDesc f).η b :=
        DefFunFun.byFunFunDef

        def byFunFunFunDef {G : DefFunFunFun desc} {a₁ a₂ : A} {f : a₁ ⇾ a₂} {b : B} {c : C} :
          nat (nat (mapHom (toFunctor G) f) b) c ≃' ((desc.revFunFunDesc b).natDesc f).η c :=
        byNatDef • natCongrArg byFunFunFunDefNat c

      end DefFunFunFun

    end

    section

      variable [HasCatProp.{u} W] [HasCatProp.{u'} W] [HasCatProp.{u''} W] [HasCatProp.{u'''} W]
               [HasCatProp.{max 1 u' u'' u''' w} W] [HasCatProp.{max 1 u'' u''' w} W]
               {A : Category.{u} W} {B : Category.{u'} W} {C : Category.{u''} W} {D : Category.{u'''} W}
               [hFunCD : HasFunProp C D] [hNatCD : HasNaturality C D] [hFunBCD : HasFunProp B (C ⮕' D)]
               [hNatBCD : HasNaturality B (C ⮕' D)] [hFunABCD : HasFunProp A (B ⮕' C ⮕' D)]

      structure NatNatNatDesc (F G : A ⮕ B ⮕' C ⮕' D) (η : ∀ a, F a ⇾ G a) where
      (natNatEq {a₁ a₂ : A} (f : a₁ ⇾ a₂) (b : B) (c : C) :
         nat (nat (η a₂) b) c • nat (nat (mapHom F f) b) c ≃ nat (nat (mapHom G f) b) c • nat (nat (η a₁) b) c)

      namespace NatNatNatDesc

        def StrictNaturality₃ {φ : A → B → C → D} {F'' G'' : ∀ a b, hFunCD.Fun (φ a b)}
                              {F' : ∀ a, hFunBCD.Fun (λ b => ⟨F'' a b⟩)}
                              {G' : ∀ a, hFunBCD.Fun (λ b => ⟨G'' a b⟩)}
                              (F : hFunABCD.Fun (λ a => ⟨F' a⟩)) (G : hFunABCD.Fun (λ a => ⟨G' a⟩)) :=
        ∀ {a₁ a₂ : A} (f : a₁ ⇾ a₂) (b : B) (c : C),
          HasInstanceEquivalences.Rel (φ a₁ b c ⇾ φ a₂ b c) (nat (nat (mapHom ⟨F⟩ f) b) c)
                                                            (nat (nat (mapHom ⟨G⟩ f) b) c)

        def strict {φ : A → B → C → D} {F'' G'' : ∀ a b, hFunCD.Fun (φ a b)}
                   {hEq : ∀ a b, NatDesc.StrictNaturality (F'' a b) (G'' a b)}
                   {η' : ∀ a b, DefNat (NatDesc.strict (hEq a b))}
                   {F' : ∀ a, hFunBCD.Fun (λ b => ⟨F'' a b⟩)}
                   {G' : ∀ a, hFunBCD.Fun (λ b => ⟨G'' a b⟩)}
                   {hNatEq : ∀ a, NatNatDesc.StrictNaturality₂ (F' a) (G' a)}
                   {η : ∀ a, DefNatNat (NatNatDesc.strict (η := η' a) (hNatEq a))}
                   {F : hFunABCD.Fun (λ a => ⟨F' a⟩)} {G : hFunABCD.Fun (λ a => ⟨G' a⟩)}
                   (hNatNatEq : StrictNaturality₃ F G) :
          NatNatNatDesc ⟨F⟩ ⟨G⟩ (λ a => (η a).η) :=
        { natNatEq := λ {a₁ a₂} f b c => (cancelRightId (byStrictNatNatDef (hNatEq := hNatEq a₁))
                                                        (nat (nat (mapHom ⟨G⟩ f) b) c))⁻¹ •
                                         hNatNatEq f b c •
                                         cancelLeftId (nat (nat (mapHom ⟨F⟩ f) b) c)
                                                      (byStrictNatNatDef (hNatEq := hNatEq a₂)) }

      end NatNatNatDesc

      variable {F G : A ⮕ B ⮕' C ⮕' D} {η : ∀ a, F a ⇾ G a}

      structure DefNatNatNatBase (desc : NatNatNatDesc F G η) where
      (natNatEquiv {a₁ a₂ : A} (f : a₁ ⇾ a₂) (b : B) :
         NatEquiv (compHom (nat (mapHom F f) b) (nat (η a₂) b)) (compHom (nat (η a₁) b) (nat (mapHom G f) b))
                  (λ c => (natTransEq' (nat (η a₁) b) (nat (mapHom G f) b) c)⁻¹ •
                          desc.natNatEq f b c •
                          natTransEq' (nat (mapHom F f) b) (nat (η a₂) b) c))

      namespace DefNatNatNatBase

        def trivial {desc : NatNatNatDesc F G η} [HasTrivialNatEquiv C D] : DefNatNatNatBase desc :=
        { natNatEquiv := λ _ _ => HasTrivialNatEquiv.natEquiv }

        variable {desc : NatNatNatDesc F G η} (ε : DefNatNatNatBase desc)

        def natNatDesc : NatNatDesc F G η :=
        { natEq := ε.natNatEquiv }

      end DefNatNatNatBase

      structure DefNatNatNat [HasCatProp.{max 1 u u' u'' u''' w} W] [hNatABC : HasNaturality A (B ⮕' C ⮕' D)]
                          (desc : NatNatNatDesc F G η) extends
        DefNatNatNatBase desc, DefNatNat (DefNatNatNatBase.natNatDesc toDefNatNatNatBase)

      namespace DefNatNatNat

        variable [HasCatProp.{max 1 u u' u'' u''' w} W] [HasNaturality A (B ⮕' C ⮕' D)]
                 {desc : NatNatNatDesc F G η}

        def trivial (ε : DefNatNatNatBase desc) (θ : DefNatNatBase (DefNatNatNatBase.natNatDesc ε))
                    [HasTrivialNaturalityCondition A (B ⮕' C ⮕' D)] :
          DefNatNatNat desc :=
        { toDefNatNatNatBase := ε,
          toDefNatNat        := DefNatNat.trivial θ }

      end DefNatNatNat

    end

    section

      variable [HasCatProp.{u} W] [HasCatProp.{v} W] [HasCatProp.{max 1 u v w} W]
               {A : Category.{u} W} (a : A) (B : Category.{v} W) [HasFunProp A B]
               [h : HasNaturality A B]

      def revApp (F : A ⮕' B) : B := F a

      def revAppPreFun : PreFunctor (Hom (A ⮕' B)) (Hom B) (revApp a B) :=
      ⟨λ F₁ F₂ => natFun F₁ F₂ a⟩

      instance : IsPreorderFunctor (revAppPreFun a B) :=
      { reflEq  := λ F   => natReflEq' F a • byDef,
        transEq := λ η ε => (congrArgTrans byDef byDef)⁻¹ •
                            natTransEq' η ε a •
                            byDef }

      def revAppFunDesc : FunDesc (revApp a B) := ⟨revAppPreFun a B⟩

    end

    class HasRevAppFun [HasCatProp.{u} W] [HasCatProp.{v} W] [HasCatProp.{max 1 u v w} W]
                       (A : Category.{u} W) (B : Category.{v} W) [hFunAB : HasFunProp A B]
                       [hNatAB : HasNaturality A B] [hFunABB : HasFunProp (A ⮕' B) B] where
    (defRevAppFun (a : A) : HasFunProp.DefFun (revAppFunDesc a B))

    namespace HasRevAppFun

      variable [HasCatProp.{u} W] [HasCatProp.{v} W] [HasCatProp.{max 1 u v w} W]
               (A : Category.{u} W) (B : Category.{v} W) [HasFunProp A B] [hNatAB : HasNaturality A B]
               [HasFunProp (A ⮕' B) B] [h : HasRevAppFun A B]

      def revAppFun (a : A) : (A ⮕' B) ⮕ B := DefFun.toFunctor (h.defRevAppFun a)

      def mapRevNat {a₁ a₂ : A} (f : a₁ ⇾ a₂) :
        MetaQuantification (Hom B) (revApp a₁ B) (revApp a₂ B) :=
      λ F => mapHom F f

      instance mapRevNat.isNat {a₁ a₂ : A} (f : a₁ ⇾ a₂) :
        IsNatural (preFun (revAppFun A B a₁)) (preFun (revAppFun A B a₂)) (mapRevNat A B f) :=
      ⟨λ {F₁ F₂} η => (naturality η f •
                       congrArgTransLeft (mapHom F₁ f)
                                         (DefFun.byMapHomDef (φ := revApp a₂ B)))⁻¹ •
                      congrArgTransRight (DefFun.byMapHomDef (φ := revApp a₁ B))
                                         (mapHom F₂ f)⟩

      def revAppNatDesc {a₁ a₂ : A} (f : a₁ ⇾ a₂) :
        NatDesc (revAppFun A B a₁) (revAppFun A B a₂) :=
      { η     := mapRevNat       A B f,
        isNat := mapRevNat.isNat A B f }

      def revAppFunFunDesc : FunFunDesc (revAppFun A B) :=
      { natDesc        := revAppNatDesc A B,
        natDescReflEq  := λ a   F => Functor.reflEq  F a,
        natDescTransEq := λ f g F => Functor.transEq F f g }

    end HasRevAppFun

    class HasRevAppFunFun [HasCatProp.{u} W] [HasCatProp.{v} W] [HasCatProp.{max 1 u v w} W]
                          (A : Category.{u} W) (B : Category.{v} W) [hFunAB : HasFunProp A B]
                          [hNatAB : HasNaturality A B] [hFunABB : HasFunProp (A ⮕' B) B]
                          [hNatABB : HasNaturality (A ⮕' B) B]
                          [hFunAABB : HasFunProp A ((A ⮕' B) ⮕' B)] extends
      HasRevAppFun A B where
    (defRevAppFunFun : DefFunFun (HasRevAppFun.revAppFunFunDesc A B))

    namespace HasRevAppFunFun

      variable [HasCatProp.{u} W] [HasCatProp.{v} W] [HasCatProp.{max 1 u v w} W]
               (A : Category.{u} W) (B : Category.{v} W) [HasFunProp A B] [HasNaturality A B]
               [HasFunProp (A ⮕' B) B] [HasNaturality (A ⮕' B) B] [HasFunProp A ((A ⮕' B) ⮕' B)]
               [h : HasRevAppFunFun A B]

      def revAppFunFun : A ⮕ (A ⮕' B) ⮕' B := DefFunFun.toFunctor h.defRevAppFunFun

    end HasRevAppFunFun

    section

      variable [HasCatProp.{u} W] [HasCatProp.{u'} W] [HasCatProp.{u''} W]
               (A : Category.{u} W) (B : Category.{u'} W) (C : Category.{u''} W) [HasFunProp A B]
               [HasFunProp B C] [HasFunProp A C] [h : HasCompFun A B C]

      section

        variable [HasCatProp.{max 1 u' u'' w} W] [hNatBC : HasNaturality B C] (F : A ⮕ B)

        def mapCompNat {G₁ G₂ : B ⮕' C} (η : G₁ ⇾ G₂) :
          MetaQuantification (Hom C) (G₁.φ ∘ F.φ) (G₂.φ ∘ F.φ) :=
        λ a => nat η (F a)

        instance mapCompNat.isNat {G₁ G₂ : B ⮕' C} (η : G₁ ⇾ G₂) :
          IsNatural (preFun (G₁ ⭗ F)) (preFun (G₂ ⭗ F)) (mapCompNat A B C F η) :=
        ⟨λ {a₁ a₂} f => (congrArgTransLeft (mapCompNat A B C F η a₁)
                                           (DefFun.byMapHomDef (φ := G₂.φ ∘ F.φ)))⁻¹ •
                        naturality η (mapHom F f) •
                        congrArgTransRight (DefFun.byMapHomDef (φ := G₁.φ ∘ F.φ))
                                           (mapCompNat A B C F η a₂)⟩

        def compNatDesc {G₁ G₂ : B ⮕' C} (η : G₁ ⇾ G₂) :
          NatDesc (G₁ ⭗ F) (G₂ ⭗ F) :=
        { η     := mapCompNat       A B C F η,
          isNat := mapCompNat.isNat A B C F η }

        def compFunFunDesc : FunFunDesc (λ G : B ⮕' C => G ⭗ F) :=
        { natDesc        := compNatDesc A B C F,
          natDescReflEq  := λ G   a => natReflEq'  G   (F a),
          natDescTransEq := λ η ε a => natTransEq' η ε (F a) }

      end

      section

        variable [HasCatProp.{max 1 u u' w} W] [hNatAB : HasNaturality A B] (G : B ⮕ C)

        def mapRevCompNat {F₁ F₂ : A ⮕' B} (η : F₁ ⇾ F₂) :
          MetaQuantification (Hom C) (G.φ ∘ F₁.φ) (G.φ ∘ F₂.φ) :=
        λ a => mapHom G (nat η a)

        instance mapRevCompNat.isNat {F₁ F₂ : A ⮕' B} (η : F₁ ⇾ F₂) :
          IsNatural (preFun (G ⭗ F₁)) (preFun (G ⭗ F₂)) (mapRevCompNat A B C G η) :=
        ⟨λ {a₁ a₂} f => (congrArgTransLeft (mapRevCompNat A B C G η a₁)
                                           (DefFun.byMapHomDef (φ := G.φ ∘ F₂.φ)))⁻¹ •
                        Functor.transEq G (nat η a₁) (mapHom F₂ f) •
                        mapHomCongrArg G (naturality η f) •
                        (Functor.transEq G (mapHom F₁ f) (nat η a₂))⁻¹ •
                        congrArgTransRight (DefFun.byMapHomDef (φ := G.φ ∘ F₁.φ))
                                           (mapRevCompNat A B C G η a₂)⟩

        def revCompNatDesc {F₁ F₂ : A ⮕' B} (η : F₁ ⇾ F₂) :
          NatDesc (G ⭗ F₁) (G ⭗ F₂) :=
        { η     := mapRevCompNat       A B C G η,
          isNat := mapRevCompNat.isNat A B C G η }

        def revCompFunFunDesc : FunFunDesc (λ F : A ⮕' B => G ⭗ F) :=
        { natDesc        := revCompNatDesc A B C G,
          natDescReflEq  := λ F   a => Functor.reflEq G (F a) •
                                       mapHomCongrArg G (natReflEq' F a),
          natDescTransEq := λ η ε a => Functor.transEq G (nat η a) (nat ε a) •
                                       mapHomCongrArg G (natTransEq' η ε a) }

      end

    end

    class HasCompFunFun [HasCatProp.{u} W] [HasCatProp.{u'} W] [HasCatProp.{u''} W]
                        [HasCatProp.{max 1 u u'' w} W] [HasCatProp.{max 1 u' u'' w} W]
                        (A : Category.{u} W) (B : Category.{u'} W) (C : Category.{u''} W)
                        [hFunAB : HasFunProp A B] [hFunBC : HasFunProp B C]
                        [hFunAC : HasFunProp A C] [hNatBC : HasNaturality B C]
                        [hNatAC : HasNaturality A C] [hFunBCAC : HasFunProp (B ⮕' C) (A ⮕' C)]
                        [h : HasCompFun A B C] where
    (defCompFunFun (F : A ⮕ B) : DefFunFun (compFunFunDesc A B C F))

    namespace HasCompFunFun

      variable [HasCatProp.{u} W] [HasCatProp.{u'} W] [HasCatProp.{u''} W]
               [HasCatProp.{max 1 u u' w} W] [HasCatProp.{max 1 u u'' w} W]
               [HasCatProp.{max 1 u' u'' w} W]
               (A : Category.{u} W) (B : Category.{u'} W) (C : Category.{u''} W) [HasFunProp A B]
               [HasFunProp B C] [HasFunProp A C] [HasNaturality B C]
               [HasNaturality A C] [HasFunProp (B ⮕' C) (A ⮕' C)] [HasCompFun A B C]
               [h : HasCompFunFun A B C]

      def compFunFun (F : A ⮕ B) : (B ⮕' C) ⮕ (A ⮕' C) := DefFunFun.toFunctor (h.defCompFunFun F)

      def compFunFunFunDesc [HasNaturality A B] : FunFunFunDesc (λ F : A ⮕' B => compFunFun A B C F) :=
      { revFunFunDesc := revCompFunFunDesc A B C,
        natNatDesc    := λ η _ => { natEq := λ ε a => (naturality ε (nat η a) •
                                                       congrArgTrans byNatDef DefFunFun.byFunFunDef)⁻¹ •
                                                      congrArgTrans DefFunFun.byFunFunDef byNatDef } }

    end HasCompFunFun

    class HasCompFunFunFun [HasCatProp.{u} W] [HasCatProp.{u'} W] [HasCatProp.{u''} W]
                           [HasCatProp.{max 1 u u' w} W] [HasCatProp.{max 1 u u'' w} W]
                           [HasCatProp.{max 1 u' u'' w} W] [HasCatProp.{max 1 u u' u'' w} W]
                           (A : Category.{u} W) (B : Category.{u'} W) (C : Category.{u''} W)
                           [hFunAB : HasFunProp A B] [hFunBC : HasFunProp B C]
                           [hFunAC : HasFunProp A C] [hNatAB : HasNaturality A B]
                           [hNatBC : HasNaturality B C] [hNatAC : HasNaturality A C]
                           [hFunBCAC : HasFunProp (B ⮕' C) (A ⮕' C)]
                           [hNatBCAC : HasNaturality (B ⮕' C) (A ⮕' C)]
                           [hFunABBCAC : HasFunProp (A ⮕' B) ((B ⮕' C) ⮕' (A ⮕' C))]
                           [h : HasCompFun A B C] extends
      HasCompFunFun A B C where
    (defCompFunFunFun : DefFunFunFun (HasCompFunFun.compFunFunFunDesc A B C))

    namespace HasCompFunFunFun

      variable [HasCatProp.{u} W] [HasCatProp.{u'} W] [HasCatProp.{u''} W]
               [HasCatProp.{max 1 u u' w} W] [HasCatProp.{max 1 u u'' w} W]
               [HasCatProp.{max 1 u' u'' w} W] [HasCatProp.{max 1 u u' u'' w} W]
               (A : Category.{u} W) (B : Category.{u'} W) (C : Category.{u''} W) [HasFunProp A B]
               [HasFunProp B C] [HasFunProp A C] [HasNaturality A B] [HasNaturality B C]
               [HasNaturality A C] [HasFunProp (B ⮕' C) (A ⮕' C)]
               [HasNaturality (B ⮕' C) (A ⮕' C)] [HasFunProp (A ⮕' B) ((B ⮕' C) ⮕' (A ⮕' C))]
               [HasCompFun A B C] [h : HasCompFunFunFun A B C]

      def compFunFunFun : (A ⮕' B) ⮕ (B ⮕' C) ⮕' (A ⮕' C) := DefFunFunFun.toFunctor h.defCompFunFunFun

    end HasCompFunFunFun

    section

      open HasFunProp.HasConstFun

      variable [HasSubLinearFunOp W] [HasCatProp.{u} W] [HasCatProp.{v} W]
               (A : Category.{u} W) (B : Category.{v} W) [HasFunProp A B] [h : HasConstFun A B]

      def mapConstNat {b₁ b₂ : B} (g : b₁ ⇾ b₂) :
        MetaQuantification (Hom B) (Function.const A b₁) (Function.const A b₂) :=
      λ _ => g

      instance mapConstNat.isNat {b₁ b₂ : B} (g : b₁ ⇾ b₂) :
        IsNatural (preFun (constFun A b₁)) (preFun (constFun A b₂)) (mapConstNat A B g) :=
      ⟨λ _ => (leftId g •
               congrArgTransLeft g (DefFun.byMapHomDef (φ := Function.const A b₂)))⁻¹ •
              (rightId g •
               congrArgTransRight (DefFun.byMapHomDef (φ := Function.const A b₁)) g)⟩

      def constNatDesc {b₁ b₂ : B} (g : b₁ ⇾ b₂) : NatDesc (constFun A b₁) (constFun A b₂) :=
      { η     := mapConstNat       A B g,
        isNat := mapConstNat.isNat A B g }

      def constFunFunDesc : FunFunDesc (λ b : B => constFun A b) :=
      { natDesc        := constNatDesc A B,
        natDescReflEq  := λ b   _ => HasInstanceEquivalences.refl (idHom b),
        natDescTransEq := λ f g _ => HasInstanceEquivalences.refl (g • f) }

    end

    class HasConstFunFun [HasSubLinearFunOp W] [HasCatProp.{u} W] [HasCatProp.{v} W]
                         [HasCatProp.{max 1 u v w} W] (A : Category.{u} W) (B : Category.{v} W)
                         [hFunAB : HasFunProp A B] [hNatAB : HasNaturality A B]
                         [hFunBAB : HasFunProp B (A ⮕' B)] [h : HasConstFun A B] where
    (defConstFunFun : DefFunFun (constFunFunDesc A B))

    namespace HasConstFunFun

      variable [HasSubLinearFunOp W] [HasCatProp.{u} W] [HasCatProp.{v} W] [HasCatProp.{max 1 u v w} W]
               (A : Category.{u} W) (B : Category.{v} W) [HasFunProp A B] [HasNaturality A B]
               [HasFunProp B (A ⮕' B)] [HasConstFun A B] [h : HasConstFunFun A B]

      def constFunFun : B ⮕ (A ⮕' B) := DefFunFun.toFunctor h.defConstFunFun

    end HasConstFunFun

    section

      variable [HasNonLinearFunOp W] [HasCatProp.{u} W] [HasCatProp.{v} W] [HasCatProp.{max 1 u v w} W]
               {A : Category.{u} W} {B : Category.{v} W} [HasFunProp A B] [HasNaturality A B]
               [HasFunProp A (A ⮕' B)] (F : A ⮕ A ⮕' B)

      @[reducible] def dup (a : A) : B := (F a) a

      @[reducible] def mapDupHom {a₁ a₂ : A} (f : a₁ ⇾ a₂) : dup F a₁ ⇾ dup F a₂ :=
      mapHom (F a₂) f • nat (mapHom F f) a₁

      @[reducible] def mapDupHom' {a₁ a₂ : A} (f : a₁ ⇾ a₂) : dup F a₁ ⇾ dup F a₂ :=
      nat (mapHom F f) a₂ • mapHom (F a₁) f

      def mapDupHomEq {a₁ a₂ : A} (f : a₁ ⇾ a₂) : mapDupHom' F f ≃ mapDupHom F f :=
      naturality (mapHom F f) f

      def defMapDupHomArg (a₁ a₂ : A) :
        (a₁ ⇾ a₂)
        ⟶{λ f => transFun (Hom B) (nat (mapHom F f) a₁) (dup F a₂)}
        (((F a₂) a₁ ⇾ dup F a₂) ⟶ (dup F a₁ ⇾ dup F a₂)) :=
      transFunFun (Hom B) (dup F a₁) ((F a₂) a₁) (dup F a₂) •
      natFun (F a₁) (F a₂) a₁ •
      (preFun F).baseFun a₁ a₂
      ◄ byDefDef • byArgDef

      def defMapDupHomFun (a₁ a₂ : A) : (a₁ ⇾ a₂) ⟶{λ f => mapDupHom F f} (dup F a₁ ⇾ dup F a₂) :=
      substFun ((preFun (F a₂)).baseFun a₁ a₂) (defMapDupHomArg F a₁ a₂)
      ◄ byDef (F := HasTransFun.defTransFun _ _) • byFunDef

      @[reducible] def mapDupHomFun (a₁ a₂ : A) : (a₁ ⇾ a₂) ⟶ (dup F a₁ ⇾ dup F a₂) :=
      defMapDupHomFun F a₁ a₂

      def mapDupHomPreFun : PreFunctor (Hom A) (Hom B) (dup F) := ⟨mapDupHomFun F⟩

      instance mapDupHomPreFun.isPreorderFunctor : IsPreorderFunctor (mapDupHomPreFun F) :=
      { reflEq  := λ a => idId (dup F a) •
                          congrArgTrans (natReflEq' (F a) a •
                                         natCongrArg (Functor.reflEq F a) a)
                                        (Functor.reflEq (F a) a) •
                          byDef (F := defMapDupHomFun F a a),
        transEq := λ {a₁ a₂ a₃} f g => (congrArgTrans (byDef (F := defMapDupHomFun F a₁ a₂))
                                                      (byDef (F := defMapDupHomFun F a₂ a₃)))⁻¹ •
                                       assoc (nat (mapHom F f) a₁) (mapHom (F a₂) f) (mapDupHom F g) •
                                       defCongrArg (defTransFun (nat (mapHom F f) a₁) (dup F a₃))
                                                   ((assoc (mapHom (F a₂) f)
                                                           (nat (mapHom F g) a₂)
                                                           (mapHom (F a₃) g))⁻¹ •
                                                    defCongrArg (defRevTransFun (Hom B) ((F a₂) a₁)
                                                                                        (mapHom (F a₃) g))
                                                                (naturality (mapHom F g) f)⁻¹ •
                                                    assoc (nat (mapHom F g) a₁)
                                                          (mapHom (F a₃) f)
                                                          (mapHom (F a₃) g)) •
                                       (assoc (nat (mapHom F f) a₁) (nat (mapHom F g) a₁)
                                              (mapHom (F a₃) g • mapHom (F a₃) f))⁻¹ •
                                       congrArgTrans (natTransEq' (mapHom F f) (mapHom F g) a₁ •
                                                      natCongrArg (Functor.transEq F f g) a₁)
                                                     (Functor.transEq (F a₃) f g) •
                                       byDef (F := defMapDupHomFun F a₁ a₃) }

      def dupFunDesc : FunDesc (dup F) := ⟨mapDupHomPreFun F⟩

    end

    class HasDupFun [HasNonLinearFunOp W] [HasCatProp.{u} W] [HasCatProp.{v} W]
                    [HasCatProp.{max 1 u v w} W] (A : Category.{u} W) (B : Category.{v} W)
                    [hFunAB : HasFunProp A B] [hNatAB : HasNaturality A B]
                    [hFunAAB : HasFunProp A (A ⮕' B)] where
    (defDupFun (F : A ⮕ A ⮕' B) : HasFunProp.DefFun (dupFunDesc F))

    namespace HasDupFun

      variable [HasNonLinearFunOp W] [HasCatProp.{u} W] [HasCatProp.{v} W] [HasCatProp.{max 1 u v w} W]
               (A : Category.{u} W) (B : Category.{v} W) [HasFunProp A B] [HasNaturality A B]
               [HasFunProp A (A ⮕' B)] [h : HasDupFun A B]

      def dupFun (F : A ⮕ A ⮕' B) : A ⮕ B := DefFun.toFunctor (h.defDupFun F)

      variable [hNatAAB : HasNaturality A (A ⮕' B)]

      def mapDupNat {F₁ F₂ : A ⮕' A ⮕' B} (η : F₁ ⇾ F₂) :
        MetaQuantification (Hom B) (dup F₁) (dup F₂) :=
      λ a => nat (nat η a) a

      instance mapDupNat.isNat {F₁ F₂ : A ⮕' A ⮕' B} (η : F₁ ⇾ F₂) :
        IsNatural (preFun (dupFun A B F₁)) (preFun (dupFun A B F₂)) (mapDupNat A B η) :=
      ⟨λ {a₁ a₂} f => congrArgTransLeft (mapDupNat A B η a₁) (DefFun.byMapHomDef (φ := dup F₂))⁻¹ •
                      (assoc (mapDupNat A B η a₁) (nat (mapHom F₂ f) a₁) (mapHom (F₂ a₂) f))⁻¹ •
                      congrArgTransRight (natTransEq' (nat η a₁) (mapHom F₂ f) a₁ •
                                          natCongrArg (naturality η f) a₁ •
                                          (natTransEq' (mapHom F₁ f) (nat η a₂) a₁)⁻¹)
                                         (mapHom (F₂ a₂) f) •
                      assoc (nat (mapHom F₁ f) a₁) (nat (nat η a₂) a₁) (mapHom (F₂ a₂) f) •
                      congrArgTransLeft (nat (mapHom F₁ f) a₁)
                                        (naturality (nat η a₂) f) •
                      (assoc (nat (mapHom F₁ f) a₁) (mapHom (F₁ a₂) f) (mapDupNat A B η a₂))⁻¹ •
                      congrArgTransRight (DefFun.byMapHomDef (φ := dup F₁)) (mapDupNat A B η a₂)⟩

      def dupNatDesc {F₁ F₂ : A ⮕' A ⮕' B} (η : F₁ ⇾ F₂) :
        NatDesc (dupFun A B F₁) (dupFun A B F₂) :=
      { η     := mapDupNat       A B η,
        isNat := mapDupNat.isNat A B η }

      def dupFunFunDesc : FunFunDesc (λ F : A ⮕' A ⮕' B => dupFun A B F) :=
      { natDesc        := dupNatDesc A B,
        natDescReflEq  := λ F   a => natReflEq' (F a) a •
                                     natCongrArg (natReflEq' F a) a,
        natDescTransEq := λ η ε a => natTransEq' (nat η a) (nat ε a) a •
                                     natCongrArg (natTransEq' η ε a) a }

    end HasDupFun

    class HasDupFunFun [HasNonLinearFunOp W] [HasCatProp.{u} W] [HasCatProp.{v} W]
                       [HasCatProp.{max 1 u v w} W] (A : Category.{u} W) (B : Category.{v} W)
                       [hFunAB : HasFunProp A B] [hNatAB : HasNaturality A B]
                       [hFunAAB : HasFunProp A (A ⮕' B)] [hNatAAB : HasNaturality A (A ⮕' B)]
                       [hFunAABAB : HasFunProp (A ⮕' A ⮕' B) (A ⮕' B)] extends
      HasDupFun A B where
    (defDupFunFun : DefFunFun (HasDupFun.dupFunFunDesc A B))

    namespace HasDupFunFun

      variable [HasNonLinearFunOp W] [HasCatProp.{u} W] [HasCatProp.{v} W] [HasCatProp.{max 1 u v w} W]
               (A : Category.{u} W) (B : Category.{v} W) [HasFunProp A B] [HasNaturality A B]
               [HasFunProp A (A ⮕' B)] [HasNaturality A (A ⮕' B)] [HasFunProp (A ⮕' A ⮕' B) (A ⮕' B)]
               [h : HasDupFunFun A B]

      def dupFunFun : (A ⮕' A ⮕' B) ⮕ (A ⮕' B) := DefFunFun.toFunctor h.defDupFunFun

    end HasDupFunFun

  end HasNaturality



  class IsNatUniverse (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw, iww} W]
                      [hCatUniv : IsCatUniverse.{u} W] [hFunUniv : IsFunUniverse.{u} W] where
  [hasNat (A B : Category W) : HasNaturality A B]

  namespace IsNatUniverse

    open IsCatUniverse HasFunProp

    section

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W] [IsCatUniverse.{u} W]
               [IsFunUniverse.{u} W] [h : IsNatUniverse.{u} W]

      instance (A B : Category W) : HasNaturality A B := h.hasNat A B

      instance hasFunctors : HasFunctors (univ W) (univ W) (univ W) :=
      { Fun   := λ A B => A ⮕' B,
        apply := Functor.φ }

    end

    class HasLinearFunctors (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw, iww} W]
                            [hCatUniv : IsCatUniverse.{u} W] [hFunUniv : IsFunUniverse.{u} W]
                            [hFunLin : IsFunUniverse.HasLinearFunctors W]
                            [hNatUniv : IsNatUniverse.{u} W] where
    [hasRevAppFunFun (A B : Category W) : HasNaturality.HasRevAppFunFun A B (hFunABB := hFunUniv.hasFun (A ⮕' B) B)]
    [hasCompFunFunFun (A B C : Category W) : HasNaturality.HasCompFunFunFun A B C]

    namespace HasLinearFunctors

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W] [IsCatUniverse.{u} W]
               [IsFunUniverse.{u} W] [IsFunUniverse.HasLinearFunctors W] [IsNatUniverse.{u} W]
               [h : HasLinearFunctors W]

      instance (A B : univ W) : HasNaturality.HasRevAppFunFun A B := h.hasRevAppFunFun A B
      instance (A B C : univ W) : HasNaturality.HasCompFunFunFun A B C := h.hasCompFunFunFun A B C

      def idFun (A : univ W) : A ⟶ A := IsFunUniverse.HasLinearFunctors.idFun A

      def revAppFun {A : univ W} (a : A) (B : univ W) : (A ⟶ B) ⟶ B :=
      HasNaturality.HasRevAppFun.revAppFun A B a

      def revAppFunFun (A B : univ W) : A ⟶ (A ⟶ B) ⟶ B :=
      HasNaturality.HasRevAppFunFun.revAppFunFun A B

      def compFun {A B C : univ W} (F : A ⟶ B) (G : B ⟶ C) : A ⟶ C :=
      IsFunUniverse.HasLinearFunctors.compFun F G

      def compFunFun {A B : univ W} (F : A ⟶ B) (C : univ W) : (B ⟶ C) ⟶ (A ⟶ C) :=
      HasNaturality.HasCompFunFun.compFunFun A B C F

      def compFunFunFun (A B C : univ W) : (A ⟶ B) ⟶ (B ⟶ C) ⟶ (A ⟶ C) :=
      HasNaturality.HasCompFunFunFun.compFunFunFun A B C

    end HasLinearFunctors

    class HasAffineFunctors (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw, iww} W] [HasSubLinearFunOp W]
                            [hCatUniv : IsCatUniverse.{u} W] [hFunUniv : IsFunUniverse.{u} W]
                            [hFunAff : IsFunUniverse.HasAffineFunctors W]
                            [hNatUniv : IsNatUniverse.{u} W] extends
      HasLinearFunctors W where
    [hasConstFunFun (A B : Category W) : HasNaturality.HasConstFunFun A B]

    namespace HasAffineFunctors

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W] [HasSubLinearFunOp W]
               [IsCatUniverse.{u} W] [IsFunUniverse.{u} W] [IsFunUniverse.HasAffineFunctors W]
               [IsNatUniverse.{u} W] [h : HasAffineFunctors W]

      instance (A B : univ W) : HasNaturality.HasConstFunFun A B := h.hasConstFunFun A B

      def constFun (A : univ W) {B : univ W} (b : B) : A ⟶ B :=
      IsFunUniverse.HasAffineFunctors.constFun A b

      def constFunFun (A B : univ W) : B ⟶ (A ⟶ B) :=
      HasNaturality.HasConstFunFun.constFunFun A B

    end HasAffineFunctors

    class HasFullFunctors (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw, iww} W]
                          [HasSubLinearFunOp W] [HasNonLinearFunOp W]
                          [hCatUniv : IsCatUniverse.{u} W] [hFunUniv : IsFunUniverse.{u} W]
                          [hFunAff : IsFunUniverse.HasAffineFunctors W]
                          [hNatUniv : IsNatUniverse.{u} W] extends
      HasAffineFunctors W where
    [hasDupFunFun (A B : Category W) : HasNaturality.HasDupFunFun A B]

    namespace HasFullFunctors

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W] [HasSubLinearFunOp W]
               [HasNonLinearFunOp W] [IsCatUniverse.{u} W] [IsFunUniverse.{u} W]
               [IsFunUniverse.HasAffineFunctors W] [IsNatUniverse.{u} W] [h : HasFullFunctors W]

      instance (A B : univ W) : HasNaturality.HasDupFunFun A B := h.hasDupFunFun A B

      def dupFun {A B : univ W} (F : A ⟶ A ⟶ B) : A ⟶ B :=
      HasNaturality.HasDupFun.dupFun A B F

      def dupFunFun (A B : univ W) : (A ⟶ A ⟶ B) ⟶ (A ⟶ B) :=
      HasNaturality.HasDupFunFun.dupFunFun A B

    end HasFullFunctors

  end IsNatUniverse

end CategoryTheory
