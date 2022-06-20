import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations
import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations.AttachedRelations
import UniverseAbstractions.Universes.Layer1.Meta.Tactics.Functoriality

import UniverseAbstractions.Universes.Helpers



namespace UniverseAbstractions.Layer1

set_option autoImplicit false

open Universe HasFunctors Helpers

universe u u' u'' v w w'



namespace Prerelation

  variable {V : Universe} [HasLinearLogic V]


  class HasPiType {α : Sort u} (P : α → V) where
    defPiType : DefType V (∀ a, P a)
    defApplyFun (a : α) : defPiType ⥤{λ F => defPiType.elim F a} P a

  namespace HasPiType

    variable {α : Sort u}

    @[reducible] def Pi (P : α → V) [h : HasPiType P] : V := h.defPiType

    @[reducible] def apply {P : α → V} [h : HasPiType P] (F : Pi P) (a : α) : P a :=
      (h.defPiType.elim F) a

    @[reducible] def applyFun (P : α → V) [h : HasPiType P] (a : α) : Pi P ⟶ P a :=
      (h.defApplyFun a).inst

    instance apply.isFunApp {P : α → V} [h : HasPiType P] {F : Pi P} {a : α} :
        IsFunApp (Pi P) (apply F a) :=
      ⟨applyFun P a, F⟩

    instance coeFun (P : α → V) [HasPiType P] : CoeFun (Pi P) (λ _ => ∀ a, P a) := ⟨apply⟩

    def DefPi (P : α → V) [h : HasPiType P] (f : ∀ a, P a) := DefType.DefInst h.defPiType f

    class HasConstPi (B : V) [HasPiType (Function.const α B)] where
      defConstPi (b : B) : DefPi (Function.const α B) (Function.const α b)
      defConstPiFun : B ⥤{λ b => (defConstPi b).inst} Pi (Function.const α B)

    class HasCompPi {ω : Sort w} (P : α → V) [HasPiType P] (l : ω → α) [hl : HasPiType (P ∘ l)] where
      defCompPi (F : Pi P) : DefPi (P ∘ l) (λ a => F (l a))
      defCompPiFun : Pi P ⥤{λ F => (defCompPi F).inst} Pi (P ∘ l)

  end HasPiType

  class HasPiType₂ {α : Sort u} {β : Sort u'} (P : α → β → V) where
    app (a : α) : HasPiType (P a)
    toHasPiType : HasPiType (λ a => HasPiType.Pi (P a))

  namespace HasPiType₂

    section

      variable {α : Sort u} {β : Sort u'}

      instance (P : α → β → V) [h : HasPiType₂ P] (a : α) : HasPiType (P a) := h.app a

      instance (P : α → β → V) [h : HasPiType₂ P] : HasPiType (λ a => HasPiType.Pi (P a)) :=
        h.toHasPiType

      @[reducible] def Pi₂ (P : α → β → V) [h : HasPiType₂ P] : V :=
        HasPiType.Pi (λ a => HasPiType.Pi (P a))

      @[reducible] def apply₂ {P : α → β → V} [h : HasPiType₂ P] (F : Pi₂ P) (a : α) (b : β) :
          P a b :=
        F a b

      def defApplyFun₂ (P : α → β → V) [h : HasPiType₂ P] (a : α) (b : β) :
          Pi₂ P ⥤{λ F => apply₂ F a b} P a b :=
        by functoriality

      @[reducible] def applyFun₂ (P : α → β → V) [h : HasPiType₂ P] (a : α) (b : β) :
          Pi₂ P ⟶ P a b :=
        (defApplyFun₂ P a b).inst

      instance apply₂.isFunApp {P : α → β → V} [h : HasPiType₂ P] {F : Pi₂ P} {a : α} {b : β} :
          IsFunApp (Pi₂ P) (apply₂ F a b) :=
        ⟨applyFun₂ P a b, F⟩

      structure DefPi₂ (P : α → β → V) [h : HasPiType₂ P] (f : ∀ a b, P a b) where
        app (a : α) : HasPiType.DefPi (P a) (f a)
        toDefPi : HasPiType.DefPi (λ a => HasPiType.Pi (P a)) (λ a => (app a).inst)

      @[reducible] def DefPi₂.inst {P : α → β → V} [HasPiType₂ P] {f : ∀ a b, P a b}
                                   (F : DefPi₂ P f) :
          Pi₂ P :=
        F.toDefPi.inst

      class HasSwapPi₂ {P : α → β → V} [h : HasPiType₂ P] [HasPiType₂ (λ b a => P a b)] where
        defSwapPi (F : Pi₂ P) : DefPi₂ (λ b a => P a b) (λ b a => F a b)
        defSwapPiFun : Pi₂ P ⥤{λ F => (defSwapPi F).inst} Pi₂ (λ b a => P a b)

      class HasCompPi₂ {ω : Sort w} {ω' : Sort w'} (P : α → β → V) [HasPiType₂ P] (l : ω → α)
                       (l' : ω' → β) [hl : HasPiType₂ (λ a b => P (l a) (l' b))] where
        defCompPi (F : Pi₂ P) : DefPi₂ (λ a b => P (l a) (l' b)) (λ a b => F (l a) (l' b))
        defCompPiFun : Pi₂ P ⥤{λ F => (defCompPi F).inst} Pi₂ (λ a b => P (l a) (l' b))

    end

    section

      variable {α : Sort u}
      
      def isFull {R : Prerelation α V} [HasPiType₂ R] (F : Pi₂ R) : IsFull R := ⟨apply₂ F⟩

      -- Some clarification is needed on the following points:
      -- * It seems the property `λ a => R a a` forms the basis of naturality: At the next higher
      --   layer, we can demand that every `η : Π a, R a a` must satisfy
      --   `∀ {a b} (f : R a b), f • η a ≃ η b • f`. (This requires `R` to be transitive.)
      -- * The generic natural transformation `η : Π a, S (φ a) (ψ a)` can be regarded as a special
      --   case of this with `R a b := S (φ a) (ψ b)`, except that transitivity of `S` does not
      --   imply transitivity of `R`.

      class HasDupPi (R : Prerelation α V) [HasPiType₂ R] [HasPiType (λ a => R a a)] where
        defDupPi (F : Pi₂ R) : HasPiType.DefPi (λ a => R a a) (λ a => F a a)
        defDupPiFun : Pi₂ R ⥤{λ F => (defDupPi F).inst} HasPiType.Pi (λ a => R a a)

      namespace HasDupPi

        @[reducible] def dupPi {R : Prerelation α V} [HasPiType₂ R] [HasPiType (λ a => R a a)]
                               [h : HasDupPi R] (F : Pi₂ R) :
            HasPiType.Pi (λ a => R a a) :=
          (h.defDupPi F).inst

        variable (R : Prerelation α V) [HasPiType₂ R] [HasPiType (λ a => R a a)] [h : HasDupPi R]

        @[reducible] def dupPiFun : Pi₂ R ⟶ HasPiType.Pi (λ a => R a a) := h.defDupPiFun.inst

        instance dupPi.isFunApp {F : Pi₂ R} : IsFunApp (Pi₂ R) (dupPi F) := ⟨dupPiFun R, F⟩

      end HasDupPi

    end

  end HasPiType₂


  class HasImplType {α : Sort u} (R S : Prerelation α V) extends
    HasPiType₂ (implication R S)

  namespace HasImplType

    variable {α : Sort u}

    @[reducible] def Impl (R S : Prerelation α V) [h : HasImplType R S] : V :=
      HasPiType₂.Pi₂ (implication R S)

    namespace Impl

      @[reducible] def applyFun₂ (R S : Prerelation α V) [HasImplType R S] (a₁ a₂ : α) :
          Impl R S ⟶ R a₁ a₂ ⟶ S a₁ a₂ :=
        HasPiType₂.applyFun₂ (implication R S) a₁ a₂

      variable {R S : Prerelation α V} [HasImplType R S] (F : Impl R S)

      def impl : Implication R S := HasPiType₂.isFull F

      @[reducible] def applyFun (a₁ a₂ : α) : R a₁ a₂ ⟶ S a₁ a₂ := (impl F).inst a₁ a₂
      @[reducible] def apply {a₁ a₂ : α} (f : R a₁ a₂) : S a₁ a₂ := (applyFun F a₁ a₂) f

    end Impl

    def DefImpl (R S : Prerelation α V) [HasImplType R S] (i : Implication R S) :=
      HasPiType₂.DefPi₂ (implication R S) i.inst

    class HasIdImpl (R : Prerelation α V) [HasImplType R R] where
      defIdImpl : DefImpl R R (Implication.idImpl R)

    class HasConstImpl [HasSubLinearLogic V] (R : Prerelation α V) (C : V) (c : C)
                       [HasImplType R (unitRelation α C)] where
      defConstImpl : DefImpl R (unitRelation α C) (Implication.constImpl R c)

    class HasCompImpl {R S T : Prerelation α V} [HasImplType R S] [HasImplType S T] [HasImplType R T]
                      where
      defCompImpl (F : Impl R S) (G : Impl S T) :
        DefImpl R T (Implication.compImpl (Impl.impl F) (Impl.impl G))
      defCompImplFun₂ : Impl R S ⥤ Impl S T ⥤{λ F G => (defCompImpl F G).inst} Impl R T

    class HasSymmImpl (R : Prerelation α V) [HasSymm R] [HasImplType R (opposite R)] where
      defSymmImpl : DefImpl R (opposite R) (Implication.symmImpl R)

  end HasImplType


  class HasFunType {α : Sort u} {β : Sort u'} (R : Prerelation α V) (S : Prerelation β V)
                   (φ : α → β) extends
    HasImplType R (lift S φ)

  namespace HasFunType

    section

      variable {α : Sort u} {β : Sort u'}

      @[reducible] def Fun (R : Prerelation α V) (S : Prerelation β V) (φ : α → β)
                           [h : HasFunType R S φ] : V :=
        HasImplType.Impl R (lift S φ)














#exit

  @[reducible] def funImplRel {α : Sort u} {β : Sort u'} (R : Prerelation α V) (S : Prerelation β V)
                              (φ : α → β) :
      Prerelation α V :=
    implication R (lift S φ)

  class HasFunType {α : Sort u} {β : Sort u'} (R : Prerelation α V) (S : Prerelation β V)
                   (φ : α → β) extends
    HasPiType₂ (funImplRel R S φ)

  namespace HasFunType

    section

      variable {α : Sort u} {β : Sort u'}

      @[reducible] def Fun (R : Prerelation α V) (S : Prerelation β V) (φ : α → β)
                           [h : HasFunType R S φ] : V :=
        HasPiType₂.Pi₂ (funImplRel R S φ)

      @[reducible] def applyFun₂ (R : Prerelation α V) (S : Prerelation β V) (φ : α → β)
                                 [HasFunType R S φ] (a₁ a₂ : α) :
          Fun R S φ ⟶ R a₁ a₂ ⟶ S (φ a₁) (φ a₂) :=
        HasPiType₂.applyFun₂ (funImplRel R S φ) a₁ a₂

      namespace Fun

        variable {R : Prerelation α V} {S : Prerelation β V} {φ : α → β} [HasFunType R S φ]
                 (F : Fun R S φ)

        def impl : Implication R (lift S φ) := HasPiType₂.isFull F

        @[reducible] def applyFun (a₁ a₂ : α) : R a₁ a₂ ⟶ S (φ a₁) (φ a₂) := (impl F).inst a₁ a₂
        @[reducible] def apply {a₁ a₂ : α} (f : R a₁ a₂) : S (φ a₁) (φ a₂) := (applyFun F a₁ a₂) f

        instance applyFun.isFunApp {a₁ a₂ : α} : IsFunApp (Fun R S φ) (applyFun F a₁ a₂) :=
          ⟨applyFun₂ R S φ a₁ a₂, F⟩

      end Fun

      def DefFun (R : Prerelation α V) (S : Prerelation β V) (φ : α → β) [HasFunType R S φ]
                 (i : Implication R (lift S φ)) :=
        HasPiType₂.DefPi₂ (funImplRel R S φ) i.inst

    end

    class HasIdFun {α : Sort u} (R : Prerelation α V) [HasFunType R R id] where
      defIdFun : DefFun R R id (Implication.idImpl R)

    class HasConstFun {α : Sort u} {β : Sort u'} [HasSubLinearLogic V] (R : Prerelation α V)
                      (S : Prerelation β V) [hS : HasRefl S] (c : β)
                      [HasFunType R S (Function.const α c)] where
      defConstFun : DefFun R S (Function.const α c) (Implication.constImpl R (hS.refl c))

    class HasCompFun {α : Sort u} {β : Sort u'} {γ : Sort u''} {R : Prerelation α V}
                     {S : Prerelation β V} {T : Prerelation γ V} (φ : α → β) (ψ : β → γ)
                     [HasFunType R S φ] [HasFunType S T ψ] [HasFunType R T (ψ ∘ φ)] where
      defCompFun (F : Fun R S φ) (G : Fun S T ψ) :
        DefFun R T (ψ ∘ φ) (Implication.compImpl (Fun.impl F) (Implication.lift (Fun.impl G) φ))
      defCompFunFun₂ : Fun R S φ ⟶ Fun S T ψ ⥤{λ F G => (defCompFun F G).inst} Fun R T (ψ ∘ φ)

    class HasSymmFun {α : Sort u} (R : Prerelation α V) [HasSymm R]
                     [HasFunType R (opposite R) id] where
      defSymmFun : DefFun R (opposite R) id (Implication.symmImpl R)

    structure DepFun {α : Sort u} {β : Sort u'} {γ : Sort u''} (S : Prerelation β V)
                     (T : Prerelation γ V) (φ : α → β → γ) [∀ a, HasFunType S T (φ a)] where
      {a : α}
      F : HasFunType.Fun S T (φ a)

  end HasFunType


  def natProp {α : Sort u} {β : Sort u'} {γ : Sort u''} {S : Prerelation β V} {T : Prerelation γ V}
              {φ : α → β → γ} [∀ a, HasFunType S T (φ a)] (F G : HasFunType.DepFun S T φ) :
      β → V :=
    λ b => T (φ F.a b) (φ G.a b)

  class HasNatType {α : Sort u} {β : Sort u'} {γ : Sort u''} (S : Prerelation β V)
                   (T : Prerelation γ V) (φ : α → β → γ) [∀ a, HasFunType S T (φ a)] where
    hNat (F G : HasFunType.DepFun S T φ) : HasPiType (natProp F G)

  namespace HasNatType

    section

      variable {α : Sort u} {β : Sort u'} {γ : Sort u''} {S : Prerelation β V} {T : Prerelation γ V}
               {φ : α → β → γ} [∀ a, HasFunType S T (φ a)] [h : HasNatType S T φ]

      instance (F G : HasFunType.DepFun S T φ) : HasPiType (natProp F G) := h.hNat F G

      @[reducible] def Nat (F G : HasFunType.DepFun S T φ) : V := HasPiType.Pi (natProp F G)

      def DefNat (F G : HasFunType.DepFun S T φ) (η : ∀ b, T (φ F.a b) (φ G.a b)) :=
        HasPiType.DefPi (natProp F G) η

    end

    section

      variable {α : Sort u} {β : Sort u'} {γ : Sort u''} (S : Prerelation β V) (T : Prerelation γ V)
               (φ : α → β → γ) [∀ a, HasFunType S T (φ a)] [h : HasNatType S T φ]

      class IsFullNat [hT : IsFull T] where
        defNat (F G : HasFunType.DepFun S T φ) : DefNat F G (λ b => hT.inst (φ F.a b) (φ G.a b))

      class HasReflNat [hT : HasRefl T] where
        defReflNat (F : HasFunType.DepFun S T φ) : DefNat F F (λ b => hT.refl (φ F.a b))

      class HasSymmNat [hT : HasSymm T] where
        defSymmNat {F G : HasFunType.DepFun S T φ} (η : Nat F G) : DefNat G F (λ b => (η b)⁻¹)
        defSymmNatFun (F G : HasFunType.DepFun S T φ) :
          Nat F G ⥤{λ η => (defSymmNat η).inst} Nat G F

      class HasTransNat [hT : HasTrans T] where
        defTransNat {F G H : HasFunType.DepFun S T φ} (η : Nat F G) (ε : Nat G H) :
          DefNat F H (λ b => ε b • η b)
        defRevTransNatFun₂ (F G H : HasFunType.DepFun S T φ) :
          Nat G H ⟶ Nat F G ⥤{λ ε η => (defTransNat η ε).inst} Nat F H

      class IsPreorderNat    [IsPreorder    T] extends HasReflNat S T φ, HasTransNat S T φ
      class IsEquivalenceNat [IsEquivalence T] extends IsPreorderNat S T φ, HasSymmNat S T φ

      @[reducible] def natRel : Prerelation (HasFunType.DepFun S T φ) V := Nat

      namespace natRel

        instance isFull [IsFull T] [h : IsFullNat S T φ] : IsFull (natRel S T φ) :=
          ⟨λ a₁ a₂ => (h.defNat a₁ a₂).inst⟩

        instance hasRefl [HasRefl T] [h : HasReflNat S T φ] : HasRefl (natRel S T φ) :=
          ⟨λ a => (h.defReflNat a).inst⟩

        instance hasSymm [HasSymm T] [h : HasSymmNat S T φ] : HasSymm (natRel S T φ) :=
          ⟨λ a₁ a₂ => (h.defSymmNatFun a₁ a₂).inst⟩

        instance hasTrans [HasTrans T] [h : HasTransNat S T φ] : HasTrans (natRel S T φ) :=
          ⟨λ a₁ a₂ a₃ => (h.defRevTransNatFun₂ a₁ a₂ a₃).inst⟩

        instance isPreorder    [IsPreorder    T] [IsPreorderNat    S T φ] : IsPreorder    (natRel S T φ) := ⟨⟩
        instance isEquivalence [IsEquivalence T] [IsEquivalenceNat S T φ] : IsEquivalence (natRel S T φ) := ⟨⟩

      end natRel

    end

  end HasNatType


  class HasFunNat {α : Sort u} {β : Sort u'} {γ : Sort u''} {R : Prerelation α V}
                  {S : Prerelation β V} {T : Prerelation γ V} {φ : α → β → γ}
                  [∀ a, HasFunType S T (φ a)] (F : ∀ a, HasFunType.Fun S T (φ a))
                  [HasNatType S T φ] [HasFunType R (HasNatType.natRel S T φ) (λ a => ⟨F a⟩)]
                  (G : HasFunType.Fun R (HasNatType.natRel S T φ) (λ a => ⟨F a⟩)) where
    defNat {a₁ a₂ : α} (f : R a₁ a₂) :
      HasNatType.DefNat ⟨F a₁⟩ ⟨F a₂⟩ (λ b => (HasFunType.Fun.apply G f) b)
    defNatFun (a₁ a₂ : α) : R a₁ a₂ ⥤{λ f => (defNat f).inst} HasNatType.Nat ⟨F a₁⟩ ⟨F a₂⟩

  class HasDepFunType {α : Sort u} {β : Sort u'} {γ : Sort u''} (R : Prerelation α V)
                      {S : Prerelation β V} {T : Prerelation γ V} {φ : α → β → γ}
                      [∀ a, HasFunType S T (φ a)] (F : ∀ a, HasFunType.Fun S T (φ a))
                      [HasNatType S T φ] where
    hFunType : HasFunType R (HasNatType.natRel S T φ) (λ a => ⟨F a⟩)
    hFunNat (G : HasFunType.Fun R (HasNatType.natRel S T φ) (λ a => ⟨F a⟩)) : HasFunNat F G

  namespace HasDepFunType

    variable {α : Sort u} {β : Sort u'} {γ : Sort u''} (R : Prerelation α V) (S : Prerelation β V)
             (T : Prerelation γ V) (φ : α → β → γ) [∀ a, HasFunType S T (φ a)]
             (F : ∀ a, HasFunType.Fun S T (φ a)) [HasNatType S T φ] [h : HasDepFunType R F]

    instance : HasFunType R (HasNatType.natRel S T φ) (λ a => ⟨F a⟩) := h.hFunType

  end HasDepFunType



-- Π a b₁ b₂, T (φ a b₁) (φ a b₂)   -->nat   Π a₁ a₂ b₁ b₂, T (φ a₁ b₁) (φ a₂ b₂)


  def depImplRel₂ {α : Sort u} {β : Sort u'} {γ : Sort u''} (R : Prerelation α V)
                  (S : Prerelation β V) (T : Prerelation γ V) (φ : α → β → γ) :
      Prerelation α V :=
    λ a₁ a₂ => R a₁ a₂ ⟶ HasPiType₂.Pi₂ (λ b₁ b₂ => S b₁ b₂ ⟶ T (φ a₁ b₁) (φ a₂ b₂))


#exit
  class HasFunType₂ {α : Sort u} {β : Sort u'} {γ : Sort u''} (R : Prerelation α V)
                    (S : Prerelation β V) (T : Prerelation γ V) (φ : α → β → γ) where
    app (a : α) : HasFunType S T (φ a)
    hAppPiType : HasPiType (λ a => HasFunType.Fun S T (φ a))
    hNatType : HasNatType S T φ
    hDepFunType (F : HasPiType.Pi (λ a => HasFunType.Fun S T (φ a))) :
      HasDepFunType R (HasPiType.apply F)
    -- TODO: We essentially reuse the Pi type as a functor type. Is this a good idea?
    funImpl (F : HasPiType.Pi (λ a => HasFunType.Fun S T (φ a))) :
      HasFunType.Fun R (HasNatType.natRel S T φ) (λ a => ⟨F a⟩)

  namespace HasFunType₂

    section

      variable {α : Sort u} {β : Sort u'} {γ : Sort u''}

      section

        variable (R : Prerelation α V) (S : Prerelation β V) (T : Prerelation γ V) (φ : α → β → γ)
                 [h : HasFunType₂ R S T φ]

        instance (a : α) : HasFunType S T (φ a) := h.app (R := R) a
        instance : HasPiType (λ a => HasFunType.Fun S T (φ a)) := h.hAppPiType
        instance : HasNatType S T φ := h.hNatType

        instance (F : HasPiType.Pi (λ a => HasFunType.Fun S T (φ a))) :
            HasDepFunType R (HasPiType.apply F) :=
          h.hDepFunType F

      end

      def Fun₂ (R : Prerelation α V) (S : Prerelation β V) (T : Prerelation γ V)
               (φ : α → β → γ) [HasFunType₂ R S T φ] : V :=
        HasFunType.Fun R (HasNatType.natRel S T φ) (λ a => ⟨F a⟩)

      namespace Fun₂

        variable {R : Prerelation α V} {S : Prerelation β V} {T : Prerelation γ V} {φ : α → β → γ}
                 [HasFunType₂ R S T φ] (F : Fun₂ R S T φ)

        @[reducible] def applyFun (a₁ a₂ : α) (b₁ b₂ : β) :
            R a₁ a₂ ⟶ S b₁ b₂ ⟶ T (φ a₁ b₁) (φ a₂ b₂) :=
          _

        @[reducible] def apply {a₁ a₂ : α} (f : R a₁ a₂) {b₁ b₂ : β} (g : S b₁ b₂) :
            T (φ a₁ b₁) (φ a₂ b₂) :=
          _

      end Fun₂

    end

  end HasFunType₂


#exit

  @[reducible] def Functor {α : Sort u} {β : Sort u'} (R : Prerelation α V) (S : Prerelation β V)
                           (φ : α → β) :=
    Implication R (lift S φ)

  namespace Functor

    @[reducible] def idFun {α : Sort u} (R : Prerelation α V) : Functor R R id :=
      Implication.idImpl R

    @[reducible] def constFun {α : Sort u} {β : Sort u'} [HasSubLinearLogic V] (R : Prerelation α V)
                              (S : Prerelation β V) [hS : HasRefl S] (c : β) :
        Functor R S (Function.const α c) :=
      Implication.constImpl R (hS.refl c)

    @[reducible] def compFun {α : Sort u} {β : Sort u'} {γ : Sort u''} {R : Prerelation α V}
                             {S : Prerelation β V} {T : Prerelation γ V} {φ : α → β} {ψ : β → γ}
                             (F : Functor R S φ) (G : Functor S T ψ) :
        Functor R T (ψ ∘ φ) :=
      Implication.compImpl F (Implication.lift G φ)

    def symmFun {α : Sort u} (R : Prerelation α V) [HasSymm R] :
        Functor R (Prerelation.opposite R) id :=
      Implication.symmImpl R

  end Functor

  def Functor₂ {α : Sort u} {β : Sort u'} {γ : Sort u''} (R : Prerelation α V) (S : Prerelation β V)
               (T : Prerelation γ V) (φ : α → β → γ) :=
    AbstractBiFun (Functor S T) (Functor R T) φ

  namespace Functor₂

    section

      variable {α : Sort u} {β : Sort u'} {γ : Sort u''} {R : Prerelation α V} {S : Prerelation β V}
               {T : Prerelation γ V} [HasTrans T] {φ : α → β → γ} (F : Functor₂ R S T φ)

      @[reducible] def apply {a₁ a₂ : α} {b₁ b₂ : β} (f : R a₁ a₂) (g : S b₁ b₂) :
          T (φ a₁ b₁) (φ a₂ b₂) :=
        (F.app a₂) g • (F.app₂ b₁) f

      @[reducible] def apply' {a₁ a₂ : α} {b₁ b₂ : β} (f : R a₁ a₂) (g : S b₁ b₂) :
          T (φ a₁ b₁) (φ a₂ b₂) :=
        (F.app₂ b₂) f • (F.app a₁) g

      @[reducible] def applyFun {a₁ a₂ : α} (f : R a₁ a₂) (b₁ b₂ : β) :
          S b₁ b₂ ⟶ T (φ a₁ b₁) (φ a₂ b₂) :=
        Λ g => apply F f g

      @[reducible] def applyFun' {a₁ a₂ : α} (f : R a₁ a₂) (b₁ b₂ : β) :
          S b₁ b₂ ⟶ T (φ a₁ b₁) (φ a₂ b₂) :=
        Λ g => apply' F f g

      @[reducible] def applyFun₂ (a₁ a₂ : α) (b₁ b₂ : β) :
          R a₁ a₂ ⟶ S b₁ b₂ ⟶ T (φ a₁ b₁) (φ a₂ b₂) :=
        Λ f => applyFun F f b₁ b₂

      @[reducible] def applyFun₂' (a₁ a₂ : α) (b₁ b₂ : β) :
          R a₁ a₂ ⟶ S b₁ b₂ ⟶ T (φ a₁ b₁) (φ a₂ b₂) :=
        Λ f => applyFun' F f b₁ b₂

      instance apply.isFunApp {a₁ a₂ : α} {b₁ b₂ : β} {f : R a₁ a₂} {g : S b₁ b₂} :
          IsFunApp (S b₁ b₂) (apply F f g) :=
        ⟨applyFun F f b₁ b₂, g⟩

      instance apply'.isFunApp {a₁ a₂ : α} {b₁ b₂ : β} {f : R a₁ a₂} {g : S b₁ b₂} :
          IsFunApp (S b₁ b₂) (apply' F f g) :=
        ⟨applyFun' F f b₁ b₂, g⟩

      instance applyFun.isFunApp {a₁ a₂ : α} {b₁ b₂ : β} {f : R a₁ a₂} :
          IsFunApp (R a₁ a₂) (applyFun F f b₁ b₂) :=
        ⟨applyFun₂ F a₁ a₂ b₁ b₂, f⟩

      instance applyFun'.isFunApp {a₁ a₂ : α} {b₁ b₂ : β} {f : R a₁ a₂} :
          IsFunApp (R a₁ a₂) (applyFun' F f b₁ b₂) :=
        ⟨applyFun₂' F a₁ a₂ b₁ b₂, f⟩

    end

    @[reducible] def swapFun₂ {α : Sort u} {β : Sort u'} {γ : Sort u''} {R : Prerelation α V}
                              {S : Prerelation β V} {T : Prerelation γ V} {φ : α → β → γ}
                              (F : Functor₂ R S T φ) :
        Functor₂ S R T (λ b a => φ a b) :=
      AbstractBiFun.swap F

    @[reducible] def dupFun {α : Sort u} {β : Sort u'} [HasNonLinearLogic V] {R : Prerelation α V}
                            {S : Prerelation β V} [HasTrans S] {φ : α → α → β}
                            (F : Functor₂ R R S φ) :
        Functor R S (λ a => φ a a) where
      inst a b := HasDupFun.dupFun (applyFun₂ F a b a b)

    @[reducible] def substFun {α : Sort u} {β : Sort u'} {γ : Sort u''} [HasNonLinearLogic V]
                              {R : Prerelation α V} {S : Prerelation β V} {T : Prerelation γ V}
                              [HasTrans T] {φ : α → β} {ψ : α → β → γ} (F : Functor R S φ)
                              (G : Functor₂ R S T ψ) :
        Functor R T (λ a => ψ a (φ a)) where
      inst a b := HasSubstFun.substFun (F.inst a b) (applyFun₂ G a b (φ a) (φ b))

    def homFun₂ {α : Sort u} (R : Prerelation α V) [HasTrans R] :
        Functor₂ (opposite R) R (funRel V) R where
      app  a := ⟨λ b₁ b₂ => HasTrans.revTransFun₂ a b₁ b₂⟩
      app₂ b := ⟨λ a₁ a₂ => HasTrans.transFun₂ a₂ a₁ b⟩

  end Functor₂


  structure DefIsoInst {α : Sort u} (Hom Iso : Prerelation α V) {a b : α} (toHom : Hom a b)
                       (invHom : Hom b a) where
    inst : Iso a b

  class IsIsoRelBase {α : Sort u} (Hom Iso : Prerelation α V) where
    to  : Implication Iso Hom
    inv : Implication Iso (opposite Hom)

  class IsIsoRel {α : Sort u} (Hom Iso : Prerelation α V) [hR : IsPreorder Hom] extends
      IsIsoRelBase Hom Iso where
    defRefl (a : α) : DefIsoInst Hom Iso (hR.refl a) (hR.refl a)
    defSymm {a b : α} (e : Iso a b) : DefIsoInst Hom Iso (inv e) (to e)
    defSymmFun (a b : α) : Iso a b ⥤{λ e => (defSymm e).inst} Iso b a
    defTrans {a b c : α} (e : Iso a b) (f : Iso b c) :
      DefIsoInst Hom Iso (to f • to e) (inv e • inv f)
    defRevTransFun₂ (a b c : α) : Iso b c ⟶ Iso a b ⥤{λ f e => (defTrans e f).inst} Iso a c

  namespace IsIsoRel

    section

      variable {α : Sort u} (Hom Iso : Prerelation α V) [IsPreorder Hom] [h : IsIsoRel Hom Iso]

      instance isEquivalence : IsEquivalence Iso where
        refl         a     := (h.defRefl a).inst
        symmFun      a b   := (h.defSymmFun a b).inst
        revTransFun₂ a b c := (h.defRevTransFun₂ a b c).inst

    end

    section

      variable {α : Sort u} {β : Sort u'} {R : Prerelation α V} {S : Prerelation β V} [IsPreorder S]
               {φ : α → β}

      section

        variable [IsEquivalence R] (SIso : Prerelation β V) [hS : IsIsoRel S SIso]

        class IsIsoFunctor (F : Functor R S φ) where
          defIsoCongrArg {a b : α} (e : R a b) : DefIsoInst S SIso (F e) (F e⁻¹)
          defIsoCongrArgFun (a b : α) :
            R a b ⥤{λ e => (defIsoCongrArg e).inst} SIso (φ a) (φ b)
  
        namespace IsIsoFunctor

          variable (F : Functor R S φ) [h : IsIsoFunctor SIso F]

          @[reducible] def isoCongrArg {a b : α} (e : R a b) : SIso (φ a) (φ b) :=
            (h.defIsoCongrArg e).inst

          @[reducible] def isoCongrArgFun (a b : α) : R a b ⟶ SIso (φ a) (φ b) :=
            (h.defIsoCongrArgFun a b).inst

          instance isoCongrArg.isFunApp {a b : α} {e : R a b} :
              IsFunApp (R a b) (isoCongrArg SIso F e) :=
            ⟨isoCongrArgFun SIso F a b, e⟩

          def toFunctor : Functor R SIso φ := ⟨isoCongrArgFun SIso F⟩

        end IsIsoFunctor

      end

      section

        variable [IsPreorder R] (RIso : Prerelation α V) [hR : IsIsoRel R RIso]

        def Functor.covariant (F : Functor R S φ) : Functor RIso S φ :=
          Implication.compImpl hR.to F
        def Functor.contravariant (F : Functor (opposite R) S φ) : Functor RIso S φ :=
          Implication.compImpl hR.inv F

        variable (SIso : Prerelation β V) [hS : IsIsoRel S SIso]

        class IsCovariantFunctor (F : Functor R S φ) extends
          IsIsoFunctor SIso (Functor.covariant RIso F)
  
        namespace IsCovariantFunctor

          variable (F : Functor R S φ) [h : IsCovariantFunctor RIso SIso F]

          @[reducible] def isoCongrArg {a b : α} (e : RIso a b) : SIso (φ a) (φ b) :=
            IsIsoFunctor.isoCongrArg SIso (Functor.covariant RIso F) e

          @[reducible] def isoCongrArgFun (a b : α) : RIso a b ⟶ SIso (φ a) (φ b) :=
            IsIsoFunctor.isoCongrArgFun SIso (Functor.covariant RIso F) a b

          -- This seems to cause a type class loop; I'm not sure why.
          --instance isoCongrArg.isFunApp {a b : α} {e : RIso a b} :
          --    IsFunApp (RIso a b) (isoCongrArg RIso SIso F e) :=
          --  ⟨isoCongrArgFun RIso SIso F a b, e⟩

          @[reducible] def toFunctor : Functor RIso SIso φ :=
            IsIsoFunctor.toFunctor SIso (Functor.covariant RIso F)

        end IsCovariantFunctor

        class IsContravariantFunctor (F : Functor (opposite R) S φ) extends
          IsIsoFunctor SIso (Functor.contravariant RIso F)

        namespace IsContravariantFunctor

          variable (F : Functor (opposite R) S φ) [h : IsContravariantFunctor RIso SIso F]

          @[reducible] def isoCongrArg {a b : α} (e : RIso a b) : SIso (φ a) (φ b) :=
            IsIsoFunctor.isoCongrArg SIso (Functor.contravariant RIso F) e

          @[reducible] def isoCongrArgFun (a b : α) : RIso a b ⟶ SIso (φ a) (φ b) :=
            IsIsoFunctor.isoCongrArgFun SIso (Functor.contravariant RIso F) a b

          -- This seems to cause a type class loop; I'm not sure why.
          --instance isoCongrArg.isFunApp {a b : α} {e : RIso a b} :
          --    IsFunApp (RIso a b) (isoCongrArg RIso SIso F e) :=
          --  ⟨isoCongrArgFun RIso SIso F a b, e⟩

          @[reducible] def toFunctor : Functor RIso SIso φ :=
            IsIsoFunctor.toFunctor SIso (Functor.contravariant RIso F)

        end IsContravariantFunctor

      end

    end

    section

      variable {α : Sort u} {β : Sort u'} {γ : Sort u''} {R : Prerelation α V} {S : Prerelation β V}
               {T : Prerelation γ V} [IsPreorder T] {φ : α → β → γ}

      section

        variable [IsEquivalence R] [IsEquivalence S] (TIso : Prerelation γ V) [hT : IsIsoRel T TIso]

        class IsIsoFunctor₂ (F : Functor₂ R S T φ) where
          app  (a : α) : IsIsoFunctor TIso (F.app  a)
          app₂ (b : β) : IsIsoFunctor TIso (F.app₂ b)
  
        namespace IsIsoFunctor₂

          open IsIsoFunctor

          variable (F : Functor₂ R S T φ) [h : IsIsoFunctor₂ TIso F]

          instance (a : α) : IsIsoFunctor TIso (F.app  a) := h.app  a
          instance (b : β) : IsIsoFunctor TIso (F.app₂ b) := h.app₂ b

          @[reducible] def isoCongrArg₂ {a₁ a₂ : α} {b₁ b₂ : β} (e : R a₁ a₂) (f : S b₁ b₂) :
              TIso (φ a₁ b₁) (φ a₂ b₂) :=
            isoCongrArg TIso (F.app a₂) f • isoCongrArg TIso (F.app₂ b₁) e

          @[reducible] def isoCongrArg₂' {a₁ a₂ : α} {b₁ b₂ : β} (e : R a₁ a₂) (f : S b₁ b₂) :
              TIso (φ a₁ b₁) (φ a₂ b₂) :=
            isoCongrArg TIso (F.app₂ b₂) e • isoCongrArg TIso (F.app a₁) f

          @[reducible] def isoCongrArg₂Fun {a₁ a₂ : α} (e : R a₁ a₂) (b₁ b₂ : β) :
              S b₁ b₂ ⟶ TIso (φ a₁ b₁) (φ a₂ b₂) :=
            Λ f => isoCongrArg₂ TIso F e f

          @[reducible] def isoCongrArg₂Fun' {a₁ a₂ : α} (e : R a₁ a₂) (b₁ b₂ : β) :
              S b₁ b₂ ⟶ TIso (φ a₁ b₁) (φ a₂ b₂) :=
            Λ f => isoCongrArg₂' TIso F e f

          @[reducible] def isoCongrArg₂Fun₂ (a₁ a₂ : α) (b₁ b₂ : β) :
              R a₁ a₂ ⟶ S b₁ b₂ ⟶ TIso (φ a₁ b₁) (φ a₂ b₂) :=
            Λ e => isoCongrArg₂Fun TIso F e b₁ b₂

          @[reducible] def isoCongrArg₂Fun₂' (a₁ a₂ : α) (b₁ b₂ : β) :
              R a₁ a₂ ⟶ S b₁ b₂ ⟶ TIso (φ a₁ b₁) (φ a₂ b₂) :=
            Λ e => isoCongrArg₂Fun' TIso F e b₁ b₂

          instance isoCongrArg₂.isFunApp {a₁ a₂ : α} {b₁ b₂ : β} {e : R a₁ a₂} {f : S b₁ b₂} :
              IsFunApp (S b₁ b₂) (isoCongrArg₂ TIso F e f) :=
            ⟨isoCongrArg₂Fun TIso F e b₁ b₂, f⟩

          instance isoCongrArg₂'.isFunApp {a₁ a₂ : α} {b₁ b₂ : β} {e : R a₁ a₂} {f : S b₁ b₂} :
              IsFunApp (S b₁ b₂) (isoCongrArg₂' TIso F e f) :=
            ⟨isoCongrArg₂Fun' TIso F e b₁ b₂, f⟩

          instance isoCongrArg₂Fun.isFunApp {a₁ a₂ : α} {b₁ b₂ : β} {e : R a₁ a₂} :
              IsFunApp (R a₁ a₂) (isoCongrArg₂Fun TIso F e b₁ b₂) :=
            ⟨isoCongrArg₂Fun₂ TIso F a₁ a₂ b₁ b₂, e⟩

          instance isoCongrArg₂Fun'.isFunApp {a₁ a₂ : α} {b₁ b₂ : β} {e : R a₁ a₂} :
              IsFunApp (R a₁ a₂) (isoCongrArg₂Fun' TIso F e b₁ b₂) :=
            ⟨isoCongrArg₂Fun₂' TIso F a₁ a₂ b₁ b₂, e⟩

          def toFunctor₂ : Functor₂ R S TIso φ where
            app  a := toFunctor TIso (F.app  a)
            app₂ b := toFunctor TIso (F.app₂ b)

        end IsIsoFunctor₂

      end

    end

  end IsIsoRel

end Prerelation
