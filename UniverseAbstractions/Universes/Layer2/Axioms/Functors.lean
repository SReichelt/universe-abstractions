import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedFunctors
import UniverseAbstractions.Universes.Layer1.Meta.Tactics.Functoriality

import UniverseAbstractions.Universes.Layer2.Axioms.Universes



namespace UniverseAbstractions.Layer2

set_option autoBoundImplicitLocal false

open Universe Layer1.HasFunctors Layer1.HasLinearLogic Layer1.HasSubLinearLogic
     Layer1.HasNonLinearLogic Layer1.Prerelation



-- We deviate slightly from the writeup by starting with `congrArg` and `congrFun` and using them
-- to include proofs in functor descriptions.
class HasFunctors (U : Universe) extends Layer1.HasFunctors U where
(congrArgFun {A B : U} (F : A ⟶ B) (a b : A) : a ≃ b ⟶ F a ≃ F b)
(congrFunFun {A B : U} (F G : A ⟶ B) (a : A) : F ≃ G ⟶ F a ≃ G a)

namespace HasFunctors

  variable {U : Universe} [h : HasFunctors U]

  instance (A B : U) : CoeFun (Layer1.HasInstances.Inst (I := U) (A ⟶ B)) (λ _ => A → B) :=
  Layer1.HasFunctors.coeFun A B

  @[reducible] def congrArg {A B : U} (F : A ⟶ B) {a b : A} (e : a ≃ b) : F a ≃ F b :=
  (congrArgFun F a b) e

  @[reducible] def congrFun {A B : U} {F G : A ⟶ B} (e : F ≃ G) (a : A) : F a ≃ G a :=
  (congrFunFun F G a) e

  @[reducible] def congrFun₂ {A B C : U} {F G : A ⟶ B ⟶ C} (e : F ≃ G) (a : A) (b : B) :
    F a b ≃ G a b :=
  congrFun (congrFun e a) b

  @[reducible] def congrFun₃ {A B C D : U} {F G : A ⟶ B ⟶ C ⟶ D} (e : F ≃ G) (a : A) (b : B) (c : C) :
    F a b c ≃ G a b c :=
  congrFun₂ (congrFun e a) b c

  @[reducible] def congrFun₄ {A B C D E : U} {F G : A ⟶ B ⟶ C ⟶ D ⟶ E} (e : F ≃ G)
                             (a : A) (b : B) (c : C) (d : D) :
    F a b c d ≃ G a b c d :=
  congrFun₃ (congrFun e a) b c d

  def congr {A B : U} {F G : A ⟶ B} (eFG : F ≃ G) {a b : A} (eab : a ≃ b) : F a ≃ G b :=
  congrArg G eab • congrFun eFG a

  def congr' {A B : U} {F G : A ⟶ B} (eFG : F ≃ G) {a b : A} (eab : a ≃ b) : F a ≃ G b :=
  congrFun eFG b • congrArg F eab

  @[reducible] def congrArg₂ {A B C : U} (F : A ⟶ B ⟶ C) {a₁ a₂ : A} (ea : a₁ ≃ a₂) {b₁ b₂ : B}
                             (eb : b₁ ≃ b₂) :
    F a₁ b₁ ≃ F a₂ b₂ :=
  congr (congrArg F ea) eb

  @[reducible] def congrArg₃ {A B C D : U} (F : A ⟶ B ⟶ C ⟶ D) {a₁ a₂ : A} (ea : a₁ ≃ a₂)
                             {b₁ b₂ : B} (eb : b₁ ≃ b₂) {c₁ c₂ : C} (ec : c₁ ≃ c₂) :
    F a₁ b₁ c₁ ≃ F a₂ b₂ c₂ :=
  congr (congrArg₂ F ea eb) ec

  @[reducible] def congrArg₄ {A B C D E : U} (F : A ⟶ B ⟶ C ⟶ D ⟶ E) {a₁ a₂ : A} (ea : a₁ ≃ a₂)
                             {b₁ b₂ : B} (eb : b₁ ≃ b₂) {c₁ c₂ : C} (ec : c₁ ≃ c₂) {d₁ d₂ : D}
                             (ed : d₁ ≃ d₂) :
    F a₁ b₁ c₁ d₁ ≃ F a₂ b₂ c₂ d₂ :=
  congr (congrArg₃ F ea eb ec) ed


  namespace DefFun

    section

      variable {A B : U} {f : A → B}

      class DefEq (F : A ⟶{f} B) where
      (e (a : A) : F.F a ≃ f a)

      def DefEq.cast {g : A → B} (hfg : ∀ a, f a ≃ g a) {F : A ⟶{f} B} (defEq : DefEq F) :
        DefEq (DefFun.cast (g := g) F) :=
      ⟨λ a => hfg a • defEq.e a⟩

      def byDef {F : A ⟶{f} B} [defEq : DefEq F] {a : A} : F.F a ≃ f a := defEq.e a

    end

    instance defAppFun.defEq {A B : U} (F : A ⟶ B) : DefEq (DefFun.defAppFun F) :=
    ⟨λ a => InstEq.refl (F a)⟩

  end DefFun

  namespace DefFun₂

    section

      variable {A B C : U} {f : A → B → C}

      class DefEq (F : A ⟶ B ⟶{f} C) where
      (app (a : A) : DefFun.DefEq (F.app a))
      (toDefFun    : DefFun.DefEq F.toDefFun)

      def DefEq.e {F : A ⟶ B ⟶{f} C} (defEq : DefEq F) (a : A) (b : B) : F.F a b ≃ f a b :=
      (defEq.app a).e b • congrFun (defEq.toDefFun.e a) b

      def DefEq.cast {g : A → B → C} (hfg : ∀ a b, f a b ≃ g a b) {F : A ⟶ B ⟶{f} C}
                     (defEq : DefEq F) :
        DefEq (DefFun₂.cast (g := g) F) :=
      ⟨λ a => DefFun.DefEq.cast (hfg a) (defEq.app a), defEq.toDefFun⟩

      section

        variable (F : A ⟶ B ⟶{f} C) [defEq : DefEq F]

        instance (a : A) : DefFun.DefEq (F.app a) := defEq.app a
        instance : DefFun.DefEq (F.toDefFun) := defEq.toDefFun

        def app.congr {a₁ a₂ : A} (e : a₁ ≃ a₂) :
          (F.app a₁).F ≃ (F.app a₂).F :=
        defEq.toDefFun.e a₂ • congrArg F.F e • (defEq.toDefFun.e a₁)⁻¹

      end

      def byDef {F : A ⟶ B ⟶{f} C} [defEq : DefEq F] {a : A} {b : B} : F.F a b ≃ f a b :=
      defEq.e a b

    end

    instance defAppFun.defEq {A B C : U} (F : A ⟶ B ⟶ C) : DefEq (DefFun₂.defAppFun F) :=
    ⟨λ a => DefFun.defAppFun.defEq (F a),
     ⟨λ a => InstEq.refl (F a)⟩⟩

  end DefFun₂

  namespace DefFun₃

    section

      variable {A B C D : U} {f : A → B → C → D}

      class DefEq (F : A ⟶ B ⟶ C ⟶{f} D) where
      (app (a : A) : DefFun₂.DefEq (F.app a))
      (toDefFun    : DefFun.DefEq F.toDefFun)

      def DefEq.e {F : A ⟶ B ⟶ C ⟶{f} D} (defEq : DefEq F) (a : A) (b : B) (c : C) :
        F.F a b c ≃ f a b c :=
      (defEq.app a).e b c • congrFun₂ (defEq.toDefFun.e a) b c

      def DefEq.cast {g : A → B → C → D} (hfg : ∀ a b c, f a b c ≃ g a b c) {F : A ⟶ B ⟶ C ⟶{f} D}
                     (defEq : DefEq F) :
        DefEq (DefFun₃.cast (g := g) F) :=
      ⟨λ a => DefFun₂.DefEq.cast (hfg a) (defEq.app a), defEq.toDefFun⟩

      section

        variable (F : A ⟶ B ⟶ C ⟶{f} D) [defEq : DefEq F]

        instance (a : A) : DefFun₂.DefEq (F.app a) := defEq.app a
        instance : DefFun.DefEq (F.toDefFun) := defEq.toDefFun

        def app.congr {a₁ a₂ : A} (e : a₁ ≃ a₂) : (F.app a₁).F ≃ (F.app a₂).F :=
        defEq.toDefFun.e a₂ • congrArg F.F e • (defEq.toDefFun.e a₁)⁻¹

        def app.congrApp {a₁ a₂ : A} (e : a₁ ≃ a₂) (b : B) :
          ((F.app a₁).app b).F ≃ ((F.app a₂).app b).F :=
        (defEq.app a₂).toDefFun.e b • congrFun (app.congr F e) b • ((defEq.app a₁).toDefFun.e b)⁻¹

      end

      def byDef {F : A ⟶ B ⟶ C ⟶{f} D} [defEq : DefEq F] {a : A} {b : B} {c : C} :
        F.F a b c ≃ f a b c :=
      defEq.e a b c

    end

    instance defAppFun.defEq {A B C D : U} (F : A ⟶ B ⟶ C ⟶ D) : DefEq (DefFun₃.defAppFun F) :=
    ⟨λ a => DefFun₂.defAppFun.defEq (F a),
     ⟨λ a => InstEq.refl (F a)⟩⟩

  end DefFun₃


  structure CongrProof {A B : U} (f : A → B) where
  (congr : ∀ a₁ a₂, a₁ ≃ a₂ ⟶ f a₁ ≃ f a₂)

  def CongrProof.apply {A B : U} (F : A ⟶ B) : CongrProof (apply F) := ⟨congrArgFun F⟩

  structure DefFunEx (A B : U) (f : A → B) (hf : CongrProof f) extends
    DefFun A B f where
  (defEq : DefFun.DefEq toDefFun)

  namespace DefFunEx

    notation:20 A:21 " ⟶{" f:0 ", " hf:0 "} " B:21 => HasFunctors.DefFunEx A B f hf

    section

      variable {A B : U} {f : A → B} {hf : CongrProof f}

      instance (F : A ⟶{f, hf} B) : DefFun.DefEq F.toDefFun := F.defEq

      def cast {g : A → B} {hg : CongrProof g} (hfg : ∀ a, f a ≃ g a) (F : A ⟶{f, hf} B) :
        A ⟶{g, hg} B :=
      ⟨DefFun.cast F.toDefFun, DefFun.DefEq.cast hfg F.defEq⟩
      infix:60 " ► " => HasFunctors.DefFunEx.cast

      -- An equivalence of two functors that are known to map all values equivalently.
      -- This is the type underlying the `Π` notation where the body is an equivalence.
      structure FunEquiv (F G : A ⟶{f, hf} B) where
      (e : F.F ≃ G.F)

      infix:25 " {≃} " => HasFunctors.DefFunEx.FunEquiv

    end

    def defAppFun {A B : U} (F : A ⟶ B) : A ⟶{apply F, CongrProof.apply F} B :=
    ⟨DefFun.defAppFun F, DefFun.defAppFun.defEq F⟩

  end DefFunEx

  structure CongrProof₂ {A B C : U} (f : A → B → C) where
  (app  (a : A) : CongrProof (f a))
  (app₂ (b : B) : CongrProof (λ a => f a b))

  def CongrProof₂.apply {A B C : U} (F : A ⟶ B ⟶ C) : CongrProof₂ (apply₂ F) :=
  ⟨λ a => CongrProof.apply (F a),
    λ b => ⟨λ a₁ a₂ => Λ e => congrFun (congrArg F e) b⟩⟩

  structure DefFunEx₂ (A B C : U) (f : A → B → C) (hf : CongrProof₂ f) extends
    DefFun₂ A B C f where
  (defEq : DefFun₂.DefEq toDefFun₂)

  namespace DefFunEx₂

    notation:20 A:21 " ⟶ " B:21 " ⟶{" f:0 ", " hf:0 "} " C:21 =>
    HasFunctors.DefFunEx₂ A B C f hf

    section

      variable {A B C : U} {f : A → B → C} {hf : CongrProof₂ f}

      instance (F : A ⟶ B ⟶{f, hf} C) : DefFun₂.DefEq F.toDefFun₂ := F.defEq

      def cast {g : A → B → C} {hg : CongrProof₂ g} (hfg : ∀ a b, f a b ≃ g a b)
               (F : A ⟶ B ⟶{f, hf} C) :
        A ⟶ B ⟶{g, hg} C :=
      ⟨DefFun₂.cast F.toDefFun₂, DefFun₂.DefEq.cast hfg F.defEq⟩
      infix:60 " ►► " => HasFunctors.DefFunEx₂.cast

      def appEx (F : A ⟶ B ⟶{f, hf} C) (a : A) : B ⟶{f a, hf.app a} C := ⟨F.app a, F.defEq.app a⟩

      def toDefFunEx (F : A ⟶ B ⟶{f, hf} C) :
        A ⟶{λ a => (F.appEx a).F, ⟨λ a₁ a₂ => Λ e => DefFun₂.app.congr F.toDefFun₂ e⟩} (B ⟶ C) :=
      ⟨F.toDefFun, F.defEq.toDefFun⟩

      structure FunEquiv (F G : A ⟶ B ⟶{f, hf} C) where
      (app (a : A) : F.appEx a {≃} G.appEx a)
      (toFunEquiv : (λ a => (app a).e) ► F.toDefFunEx {≃} G.toDefFunEx)

      infix:25 " {{≃}} " => HasFunctors.DefFunEx₂.FunEquiv

      @[reducible] def FunEquiv.e {F G : A ⟶ B ⟶{f, hf} C} (e : F {{≃}} G) : F.F ≃ G.F :=
      e.toFunEquiv.e

    end

    def defAppFun {A B C : U} (F : A ⟶ B ⟶ C) : A ⟶ B ⟶{apply₂ F, CongrProof₂.apply F} C :=
    ⟨DefFun₂.defAppFun F, DefFun₂.defAppFun.defEq F⟩

  end DefFunEx₂

  structure CongrProof₃ {A B C D : U} (f : A → B → C → D) where
  (app  (a : A)         : CongrProof₂ (f a))
  (app₃ (b : B) (c : C) : CongrProof (λ a => f a b c))

  def CongrProof₃.apply {A B C D : U} (F : A ⟶ B ⟶ C ⟶ D) : CongrProof₃ (apply₃ F) :=
  ⟨λ a   => CongrProof₂.apply (F a),
    λ b c => ⟨λ a₁ a₂ => Λ e => congrFun₂ (congrArg F e) b c⟩⟩

  structure DefFunEx₃ (A B C D : U) (f : A → B → C → D) (hf : CongrProof₃ f) extends
    DefFun₃ A B C D f where
  (defEq : DefFun₃.DefEq toDefFun₃)

  namespace DefFunEx₃

    notation:20 A:21 " ⟶ " B:21 " ⟶ " C:21 " ⟶{" f:0 ", " hf:0 "} " D:21 =>
    HasFunctors.DefFunEx₃ A B C D f hf

    section

      variable {A B C D : U} {f : A → B → C → D} {hf : CongrProof₃ f}

      instance (F :  A ⟶ B ⟶ C ⟶{f, hf} D) : DefFun₃.DefEq F.toDefFun₃ := F.defEq

      def cast {g : A → B → C → D} {hg : CongrProof₃ g} (hfg : ∀ a b c, f a b c ≃ g a b c)
               (F : A ⟶ B ⟶ C ⟶{f, hf} D) :
        A ⟶ B ⟶ C ⟶{g, hg} D :=
      ⟨DefFun₃.cast F.toDefFun₃, DefFun₃.DefEq.cast hfg F.defEq⟩
      infix:60 " ►►► " => HasFunctors.DefFunEx₃.cast

      def appEx (F : A ⟶ B ⟶ C ⟶{f, hf} D) (a : A) : B ⟶ C ⟶{f a, hf.app a} D :=
      ⟨F.app a, F.defEq.app a⟩

      def toDefFunEx (F : A ⟶ B ⟶ C ⟶{f, hf} D) :
        A ⟶{λ a => (F.appEx a).F, ⟨λ a₁ a₂ => Λ e => DefFun₃.app.congr F.toDefFun₃ e⟩} (B ⟶ C ⟶ D) :=
      ⟨F.toDefFun, F.defEq.toDefFun⟩

      structure FunEquiv (F G : A ⟶ B ⟶ C ⟶{f, hf} D) where
      (app (a : A) : F.appEx a {{≃}} G.appEx a)
      (toFunEquiv : (λ a => (app a).e) ► F.toDefFunEx {≃} G.toDefFunEx)

      infix:25 " {{{≃}}} " => HasFunctors.DefFunEx₃.FunEquiv

      @[reducible] def FunEquiv.e {F G : A ⟶ B ⟶ C ⟶{f, hf} D} (e : F {{{≃}}} G) : F.F ≃ G.F :=
      e.toFunEquiv.e

    end

    def defAppFun {A B C D : U} (F : A ⟶ B ⟶ C ⟶ D) : A ⟶ B ⟶ C ⟶{apply₃ F, CongrProof₃.apply F} D :=
    ⟨DefFun₃.defAppFun F, DefFun₃.defAppFun.defEq F⟩

  end DefFunEx₃

  -- TODO `DefFun₄`

end HasFunctors

open HasFunctors



class HasLinearLogic (U : Universe) [HasFunctors U] where
(defIdFun (A : U) : A ⟶{id, ⟨λ a₁ a₂ => idFun (a₁ ≃ a₂)⟩} A)
(defRevAppFun₂ (A B : U) :
   A ⟶ (A ⟶ B) ⟶{λ a F => F a,
                 ⟨λ a => ⟨λ F₁ F₂ => congrFunFun F₁ F₂ a⟩,
                  λ F => ⟨λ a₁ a₂ => congrArgFun F a₁ a₂⟩⟩} B)
(defCompFun₃ (A B C : U) :
   (A ⟶ B) ⟶ (B ⟶ C) ⟶ A ⟶{λ F G a => G (F a),
                           ⟨λ F => ⟨λ G => ⟨λ a₁ a₂ => congrArgFun G (F a₁) (F a₂) ⊙
                                                       congrArgFun F a₁ a₂⟩,
                                    λ a => ⟨λ G₁ G₂ => congrFunFun G₁ G₂ (F a)⟩⟩,
                            λ G a => ⟨λ F₁ F₂ => congrArgFun G (F₁ a) (F₂ a) ⊙
                                                 congrFunFun F₁ F₂ a⟩⟩} C)

namespace HasLinearLogic

  instance layer1 (U : Universe) [HasFunctors U] [HasLinearLogic U] : Layer1.HasLinearLogic U :=
  { defIdFun      := λ A     => (defIdFun      A).toDefFun,
    defRevAppFun₂ := λ A B   => (defRevAppFun₂ A B).toDefFun₂,
    defCompFun₃   := λ A B C => (defCompFun₃   A B C).toDefFun₃ }

  variable {U : Universe} [HasFunctors U] [HasLinearLogic U]

  instance (A : U) : DefFun.DefEq (Layer1.HasLinearLogic.defIdFun A) := (defIdFun A).defEq
  instance (A B : U) : DefFun₂.DefEq (Layer1.HasLinearLogic.defRevAppFun₂ A B) := (defRevAppFun₂ A B).defEq
  instance (A B C : U) : DefFun₃.DefEq (Layer1.HasLinearLogic.defCompFun₃ A B C) := (defCompFun₃ A B C).defEq

  @[reducible] def revAppFun.congrArg {A : U} {a₁ a₂ : A} (e : a₁ ≃ a₂) (B : U) :
    revAppFun a₁ B ≃ revAppFun a₂ B :=
  DefFun₂.app.congr (defRevAppFun₂ A B).toDefFun₂ e

  @[reducible] def compFun.congrArgRight {A B C : U} {F₁ F₂ : A ⟶ B} (e : F₁ ≃ F₂) (G : B ⟶ C) :
    G ⊙ F₁ ≃ G ⊙ F₂ :=
  DefFun₃.app.congrApp (defCompFun₃ A B C).toDefFun₃ e G

  @[reducible] def compFun.congrArgLeft {A B C : U} (F : A ⟶ B) {G₁ G₂ : B ⟶ C} (e : G₁ ≃ G₂) :
    G₁ ⊙ F ≃ G₂ ⊙ F :=
  DefFun₂.app.congr ((defCompFun₃ A B C).app F) e

  @[reducible] def compFun₂.congrArg {A B : U} {F₁ F₂ : A ⟶ B} (e : F₁ ≃ F₂) (C : U) :
    compFun₂ F₁ C ≃ compFun₂ F₂ C :=
  DefFun₃.app.congr (defCompFun₃ A B C).toDefFun₃ e

end HasLinearLogic


class HasSubLinearLogic (U : Universe) [HasFunctors U] [Layer1.HasSubLinearLogic U.V] where
(defConstFun₂ (A B : U) :
   B ⟶ A ⟶{λ b a => b,
           ⟨λ b => ⟨λ a₁ a₂ => constFun (a₁ ≃ a₂) (InstEq.refl b)⟩,
            λ a => ⟨λ b₁ b₂ => idFun (b₁ ≃ b₂)⟩⟩} B)

namespace HasSubLinearLogic

  instance layer1 (U : Universe) [HasFunctors U] [Layer1.HasSubLinearLogic U.V]
                  [HasSubLinearLogic U] :
    Layer1.HasSubLinearLogic U :=
  { defConstFun₂ := λ A B => (defConstFun₂ A B).toDefFun₂ }

  variable {U : Universe} [HasFunctors U] [Layer1.HasSubLinearLogic U.V] [HasSubLinearLogic U]

  instance (A B : U) : DefFun₂.DefEq (Layer1.HasSubLinearLogic.defConstFun₂ A B) := (defConstFun₂ A B).defEq

  @[reducible] def constFun.congrArg (A : U) {B : U} {b₁ b₂ : B} (e : b₁ ≃ b₂) :
    constFun A b₁ ≃ constFun A b₂ :=
  DefFun₂.app.congr (defConstFun₂ A B).toDefFun₂ e

end HasSubLinearLogic

class HasAffineLogic (U : Universe) [HasFunctors U] [Layer1.HasSubLinearLogic U.V] extends
  HasLinearLogic U, HasSubLinearLogic U

instance HasAffineLogic.layer1 (U : Universe) [HasFunctors U] [Layer1.HasSubLinearLogic U.V]
                               [HasAffineLogic U] :
  Layer1.HasAffineLogic U :=
⟨⟩


class HasNonLinearLogic (U : Universe) [HasFunctors U] [Layer1.HasNonLinearLogic U.V] where
(defDupFun₂ (A B : U) :
   (A ⟶ A ⟶ B) ⟶ A ⟶{λ F a => F a a,
                     ⟨λ F => ⟨λ a₁ a₂ => Λ e => congrArg₂ F e e⟩,
                      λ a => ⟨λ F₁ F₂ => Λ e => congrFun₂ e a a⟩⟩} B)

namespace HasNonLinearLogic

  instance layer1 (U : Universe) [HasFunctors U] [Layer1.HasNonLinearLogic U.V]
                  [HasNonLinearLogic U] :
    Layer1.HasNonLinearLogic U :=
  { defDupFun₂ := λ A B => (defDupFun₂ A B).toDefFun₂ }

  variable {U : Universe} [HasFunctors U] [Layer1.HasNonLinearLogic U.V] [HasNonLinearLogic U]

  instance (A B : U) : DefFun₂.DefEq (Layer1.HasNonLinearLogic.defDupFun₂ A B) := (defDupFun₂ A B).defEq

  @[reducible] def dupFun.congrArg {A B : U} {F₁ F₂ : A ⟶ A ⟶ B} (e : F₁ ≃ F₂) :
    dupFun F₁ ≃ dupFun F₂ :=
  DefFun₂.app.congr (defDupFun₂ A B).toDefFun₂ e

end HasNonLinearLogic

class HasFullLogic (U : Universe) [HasFunctors U] [Layer1.HasSubLinearLogic U.V]
                   [Layer1.HasNonLinearLogic U.V] extends
  HasAffineLogic U, HasNonLinearLogic U

instance HasFullLogic.layer1 (U : Universe) [HasFunctors U] [Layer1.HasSubLinearLogic U.V]
                             [Layer1.HasNonLinearLogic U.V] [HasFullLogic U] :
  Layer1.HasFullLogic U :=
⟨⟩
