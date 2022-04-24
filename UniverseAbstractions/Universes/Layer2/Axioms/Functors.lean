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
  let _ : IsEquivalence (InstEq (A := B)) := inferInstance
  congrArg G eab • congrFun eFG a

  def congr' {A B : U} {F G : A ⟶ B} (eFG : F ≃ G) {a b : A} (eab : a ≃ b) : F a ≃ G b :=
  let _ : IsEquivalence (InstEq (A := B)) := inferInstance
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

  section DefFun

    structure CongrProof {A B : U} (f : A → B) where
    (congr : ∀ a₁ a₂, a₁ ≃ a₂ ⟶ f a₁ ≃ f a₂)

    def CongrProof.apply {A B : U} (F : A ⟶ B) : CongrProof (apply F) := ⟨congrArgFun F⟩

    structure DefFun (A B : U) (f : A → B) (hf : CongrProof f) where
    (F : A ⟶ B)
    (e (a : A) : F a ≃ f a)

    namespace DefFun

      notation:20 A:21 " ⟶{" f:0 ", " hf:0 "} " B:21 => HasFunctors.DefFun A B f hf

      variable {A B : U}
      
      section

        variable {f : A → B} {hf : CongrProof f}

        instance : Coe (A ⟶{f, hf} B) (A ⟶{f} B) := ⟨λ F => ⟨F.F⟩⟩

        def byDef {F : A ⟶{f, hf} B} {a : A} : F.F a ≃ f a := F.e a

        def cast {g : A → B} {hg : CongrProof g} (hfg : ∀ a, f a ≃ g a) (F : A ⟶{f, hf} B) :
          A ⟶{g, hg} B :=
        ⟨F.F, λ a => hfg a • F.e a⟩

        infix:60 " ► " => HasFunctors.DefFun.cast

        -- An equivalence of two functors that are known to map all values equivalently.
        -- This is the type underlying the `Π` notation where the body is an equivalence.
        structure FunEquiv (F G : A ⟶{f, hf} B) where
        (e : F.F ≃ G.F)

        infix:25 " {≃} " => HasFunctors.DefFun.FunEquiv

      end

      def defAppFun (F : A ⟶ B) : A ⟶{apply F, CongrProof.apply F} B :=
      ⟨F, λ a => InstEq.refl (F a)⟩

      def defAppFun.funEquiv {F G : A ⟶ B} (e : F ≃ G) :
        congrFun e ► defAppFun F {≃} defAppFun G :=
      ⟨e⟩

    end DefFun

    structure CongrProof₂ {A B C : U} (f : A → B → C) where
    (app  (a : A) : CongrProof (f a))
    (app₂ (b : B) : CongrProof (λ a => f a b))

    def CongrProof₂.apply {A B C : U} (F : A ⟶ B ⟶ C) : CongrProof₂ (apply₂ F) :=
    ⟨λ a => CongrProof.apply (F a),
     λ b => ⟨λ a₁ a₂ => Λ e => congrFun (congrArg F e) b⟩⟩

    structure DefFun₂ (A B C : U) (f : A → B → C) (hf : CongrProof₂ f) where
    (app (a : A) : B ⟶{f a, hf.app a} C)
    (defAppCongrArg {a₁ a₂ : A} (ea : a₁ ≃ a₂) :
       (λ b => ((hf.app₂ b).congr a₁ a₂) ea) ► app a₁ {≃} app a₂)
    (defAppCongrArgFun (a₁ a₂ : A) :
       a₁ ≃ a₂ ⟶{λ ea => (defAppCongrArg ea).e} (app a₁).F ≃ (app a₂).F)
    (toDefFun : A ⟶{λ a => (app a).F, ⟨λ a₁ a₂ => (defAppCongrArgFun a₁ a₂).F⟩} (B ⟶ C))

    namespace DefFun₂

      notation:20 A:21 " ⟶ " B:21 " ⟶{" f:0 ", " hf:0 "} " C:21 =>
      HasFunctors.DefFun₂ A B C f hf

      variable {A B C : U}

      section

        variable {f : A → B → C} {hf : CongrProof₂ f}

        instance : Coe (A ⟶ B ⟶{f, hf} C) (A ⟶ B ⟶{f} C) := ⟨λ F => ⟨λ a => F.app a, F.toDefFun⟩⟩

        @[reducible] def F {F : A ⟶ B ⟶{f, hf} C} : A ⟶ B ⟶ C := F.toDefFun.F

        @[reducible] def appCongrArg (F : A ⟶ B ⟶{f, hf} C) {a₁ a₂ : A} (ea : a₁ ≃ a₂) :
          (F.app a₁).F ≃ (F.app a₂).F :=
        (F.defAppCongrArg ea).e

        @[reducible] def appCongrArgFun (F : A ⟶ B ⟶{f, hf} C) (a₁ a₂ : A) :
          a₁ ≃ a₂ ⟶ (F.app a₁).F ≃ (F.app a₂).F :=
        (F.defAppCongrArgFun a₁ a₂).F

        instance appCongrArg.isFunApp {F : A ⟶ B ⟶{f, hf} C} {a₁ a₂ : A} {ea : a₁ ≃ a₂} :
          IsFunApp (a₁ ≃ a₂) (appCongrArg F ea) :=
        ⟨appCongrArgFun F a₁ a₂, ea⟩

        def byDef {F : A ⟶ B ⟶{f, hf} C} {a : A} {b : B} : F.F a b ≃ f a b :=
        DefFun.byDef • congrFun DefFun.byDef b

        def cast {g : A → B → C} {hg : CongrProof₂ g} (hfg : ∀ a b, f a b ≃ g a b)
                 (F : A ⟶ B ⟶{f, hf} C) :
          A ⟶ B ⟶{g, hg} C :=
        ⟨λ a => hfg a ► F.app a,
         λ ea => ⟨appCongrArg F ea⟩,
         λ a₁ a₂ => ⟨appCongrArgFun F a₁ a₂⟩,
         F.toDefFun⟩

        infix:60 " ►► " => HasFunctors.DefFun₂.cast

        structure FunEquiv (F G : A ⟶ B ⟶{f, hf} C) where
        (app (a : A) : F.app a {≃} G.app a)
        (toFunEquiv : (λ a => (app a).e) ► F.toDefFun {≃} G.toDefFun)

        infix:25 " {{≃}} " => HasFunctors.DefFun₂.FunEquiv

        @[reducible] def FunEquiv.e {F G : A ⟶ B ⟶{f, hf} C} (e : F {{≃}} G) : F.F ≃ G.F :=
        e.toFunEquiv.e

      end

      def defAppFun (F : A ⟶ B ⟶ C) : A ⟶ B ⟶{apply₂ F, CongrProof₂.apply F} C :=
      ⟨λ a => DefFun.defAppFun (F a),
       λ ea => ⟨congrArg F ea⟩,
       λ a₁ a₂ => ⟨congrArgFun F a₁ a₂⟩,
       DefFun.defAppFun F⟩

      def defAppFun.funEquiv {F G : A ⟶ B ⟶ C} (e : F ≃ G) :
        congrFun₂ e ►► defAppFun F {{≃}} defAppFun G :=
      ⟨λ a => DefFun.defAppFun.funEquiv (congrFun e a), DefFun.defAppFun.funEquiv e⟩

    end DefFun₂

    structure CongrProof₃ {A B C D : U} (f : A → B → C → D) where
    (app  (a : A)         : CongrProof₂ (f a))
    (app₃ (b : B) (c : C) : CongrProof (λ a => f a b c))

    def CongrProof₃.apply {A B C D : U} (F : A ⟶ B ⟶ C ⟶ D) : CongrProof₃ (apply₃ F) :=
    ⟨λ a   => CongrProof₂.apply (F a),
     λ b c => ⟨λ a₁ a₂ => Λ e => congrFun₂ (congrArg F e) b c⟩⟩

    structure DefFun₃ (A B C D : U) (f : A → B → C → D) (hf : CongrProof₃ f) where
    (app (a : A) : B ⟶ C ⟶{f a, hf.app a} D)
    (defAppCongrArg₂ {a₁ a₂ : A} (ea : a₁ ≃ a₂) :
       (λ b c => ((hf.app₃ b c).congr a₁ a₂) ea) ►► app a₁ {{≃}} app a₂)
    (defAppCongrArgFun (a₁ a₂ : A) :
       a₁ ≃ a₂ ⟶{λ ea => (defAppCongrArg₂ ea).e} (app a₁).F ≃ (app a₂).F)
    (toDefFun : A ⟶{λ a => (app a).F, ⟨λ a₁ a₂ => (defAppCongrArgFun a₁ a₂).F⟩} (B ⟶ C ⟶ D))

    namespace DefFun₃

      notation:20 A:21 " ⟶ " B:21 " ⟶ " C:21 " ⟶{" f:0 ", " hf:0 "} " D:21 =>
      HasFunctors.DefFun₃ A B C D f hf

      variable {A B C D : U}

      section

        variable {f : A → B → C → D} {hf : CongrProof₃ f}

        instance : Coe (A ⟶ B ⟶ C ⟶{f, hf} D) (A ⟶ B ⟶ C ⟶{f} D) :=
        ⟨λ F => ⟨λ a => F.app a, F.toDefFun⟩⟩

        @[reducible] def F {F : A ⟶ B ⟶ C ⟶{f, hf} D} : A ⟶ B ⟶ C ⟶ D := F.toDefFun.F

        @[reducible] def appCongrArg' (F : A ⟶ B ⟶ C ⟶{f, hf} D) {a₁ a₂ : A} (ea : a₁ ≃ a₂) (b : B) :
          ((F.app a₁).app b).F ≃ ((F.app a₂).app b).F :=
        ((F.defAppCongrArg₂ ea).app b).e

        @[reducible] def appCongrArg (F : A ⟶ B ⟶ C ⟶{f, hf} D) {a₁ a₂ : A} (ea : a₁ ≃ a₂) :
          (F.app a₁).F ≃ (F.app a₂).F :=
        (F.defAppCongrArg₂ ea).e

        @[reducible] def appCongrArgFun (F : A ⟶ B ⟶ C ⟶{f, hf} D) (a₁ a₂ : A) :
          a₁ ≃ a₂ ⟶ (F.app a₁).F ≃ (F.app a₂).F :=
        (F.defAppCongrArgFun a₁ a₂).F

        instance appCongrArg.isFunApp {F : A ⟶ B ⟶ C ⟶{f, hf} D} {a₁ a₂ : A} {ea : a₁ ≃ a₂} :
          IsFunApp (a₁ ≃ a₂) (appCongrArg F ea) :=
        ⟨appCongrArgFun F a₁ a₂, ea⟩

        def byDef {F : A ⟶ B ⟶ C ⟶{f, hf} D} {a : A} {b : B} {c : C} : F.F a b c ≃ f a b c :=
        DefFun₂.byDef • congrFun₂ DefFun.byDef b c

        def cast {g : A → B → C → D} {hg : CongrProof₃ g} (hfg : ∀ a b c, f a b c ≃ g a b c)
                 (F : A ⟶ B ⟶ C ⟶{f, hf} D) :
          A ⟶ B ⟶ C ⟶{g, hg} D :=
        ⟨λ a => hfg a ►► F.app a,
         λ ea => ⟨λ b => ⟨appCongrArg' F ea b⟩, ⟨appCongrArg F ea⟩⟩,
         λ a₁ a₂ => ⟨appCongrArgFun F a₁ a₂⟩,
         F.toDefFun⟩

        infix:60 " ►►► " => HasFunctors.DefFun₃.cast

        structure FunEquiv (F G : A ⟶ B ⟶ C ⟶{f, hf} D) where
        (app (a : A) : F.app a {{≃}} G.app a)
        (toFunEquiv : (λ a => (app a).e) ► F.toDefFun {≃} G.toDefFun)

        infix:25 " {{{≃}}} " => HasFunctors.DefFun₃.FunEquiv

        @[reducible] def FunEquiv.e {F G : A ⟶ B ⟶ C ⟶{f, hf} D} (e : F {{{≃}}} G) : F.F ≃ G.F :=
        e.toFunEquiv.e

      end

      def defAppFun (F : A ⟶ B ⟶ C ⟶ D) : A ⟶ B ⟶ C ⟶{apply₃ F, CongrProof₃.apply F} D :=
      ⟨λ a => DefFun₂.defAppFun (F a),
       λ ea => ⟨λ b => ⟨congrFun (congrArg F ea) b⟩, ⟨congrArg F ea⟩⟩,
       λ a₁ a₂ => ⟨congrArgFun F a₁ a₂⟩,
       DefFun.defAppFun F⟩

      def defAppFun.funEquiv {F G : A ⟶ B ⟶ C ⟶ D} (e : F ≃ G) :
        congrFun₃ e ►►► defAppFun F {{{≃}}} defAppFun G :=
      ⟨λ a => DefFun₂.defAppFun.funEquiv (congrFun e a), DefFun.defAppFun.funEquiv e⟩

    end DefFun₃

    -- TODO `DefFun₄`

  end DefFun

end HasFunctors

open HasFunctors



-- TODO: Why do we need to write `apply` here?
class HasLinearLogic (U : Universe) [HasFunctors U] where
(defIdFun (A : U) : A ⟶{id, ⟨λ a₁ a₂ => idFun (a₁ ≃ a₂)⟩} A)
(defRevAppFun₂ (A B : U) :
   A ⟶ (A ⟶ B) ⟶{λ a F => apply F a,
                 ⟨λ a => ⟨λ F₁ F₂ => congrFunFun F₁ F₂ a⟩,
                  λ F => ⟨λ a₁ a₂ => congrArgFun F a₁ a₂⟩⟩} B)
(defCompFun₃ (A B C : U) :
   (A ⟶ B) ⟶ (B ⟶ C) ⟶ A ⟶{λ F G a => apply G (apply F a),
                           ⟨λ F => ⟨λ G => ⟨λ a₁ a₂ => congrArgFun G (apply F a₁) (apply F a₂) ⊙
                                                       congrArgFun F a₁ a₂⟩,
                                    λ a => ⟨λ G₁ G₂ => congrFunFun G₁ G₂ (apply F a)⟩⟩,
                            λ G a => ⟨λ F₁ F₂ => congrArgFun G (apply F₁ a) (apply F₂ a) ⊙
                                                 congrFunFun F₁ F₂ a⟩⟩} C)

namespace HasLinearLogic

  variable (U : Universe) [HasFunctors U] [HasLinearLogic U]

  instance layer1 : Layer1.HasLinearLogic U :=
  { defIdFun      := λ A     => defIdFun      A,
    defRevAppFun₂ := λ A B   => defRevAppFun₂ A B,
    defCompFun₃   := λ A B C => defCompFun₃   A B C }

  def revAppFun.congrArg {A : U} {a₁ a₂ : A} (e : a₁ ≃ a₂) (B : U) :
    revAppFun a₁ B ≃ revAppFun a₂ B :=
  DefFun₂.appCongrArg (defRevAppFun₂ A B) e

  def compFun.congrArgRight {A B C : U} {F₁ F₂ : A ⟶ B} (e : F₁ ≃ F₂) (G : B ⟶ C) :
    G ⊙ F₁ ≃ G ⊙ F₂ :=
  DefFun₃.appCongrArg' (defCompFun₃ A B C) e G

  def compFun.congrArgLeft {A B C : U} (F : A ⟶ B) {G₁ G₂ : B ⟶ C} (e : G₁ ≃ G₂) :
    G₁ ⊙ F ≃ G₂ ⊙ F :=
  DefFun₂.appCongrArg ((defCompFun₃ A B C).app F) e

  def compFun₂.congrArg {A B : U} {F₁ F₂ : A ⟶ B} (e : F₁ ≃ F₂) (C : U) :
    compFun₂ F₁ C ≃ compFun₂ F₂ C :=
  DefFun₃.appCongrArg (defCompFun₃ A B C) e

end HasLinearLogic


class HasSubLinearLogic (U : Universe) [HasFunctors U] [Layer1.HasSubLinearLogic U.V] where
(defConstFun₂ (A B : U) :
   B ⟶ A ⟶{λ b a => b,
           ⟨λ b => ⟨λ a₁ a₂ => constFun (a₁ ≃ a₂) (InstEq.refl b)⟩,
            λ a => ⟨λ b₁ b₂ => idFun (b₁ ≃ b₂)⟩⟩} B)

namespace HasSubLinearLogic

  variable (U : Universe) [HasFunctors U] [Layer1.HasSubLinearLogic U.V] [HasSubLinearLogic U]

  instance layer1 : Layer1.HasSubLinearLogic U :=
  { defConstFun₂ := λ A B => defConstFun₂ A B }

end HasSubLinearLogic

class HasAffineLogic (U : Universe) [HasFunctors U] [Layer1.HasSubLinearLogic U.V] extends
  HasLinearLogic U, HasSubLinearLogic U

instance HasAffineLogic.layer1 (U : Universe) [HasFunctors U] [Layer1.HasSubLinearLogic U.V]
                               [HasAffineLogic U] :
  Layer1.HasAffineLogic U :=
⟨⟩


class HasNonLinearLogic (U : Universe) [HasFunctors U] [Layer1.HasNonLinearLogic U.V] where
(defDupFun₂ (A B : U) :
   (A ⟶ A ⟶ B) ⟶ A ⟶{λ F a => apply₂ F a a,
                     ⟨λ F => ⟨λ a₁ a₂ => Λ e => congrArg₂ F e e⟩,
                      λ a => ⟨λ F₁ F₂ => Λ e => congrFun₂ e a a⟩⟩} B)

namespace HasNonLinearLogic

  variable (U : Universe) [HasFunctors U] [Layer1.HasNonLinearLogic U.V] [HasNonLinearLogic U]

  instance layer1 : Layer1.HasNonLinearLogic U :=
  { defDupFun₂ := λ A B => defDupFun₂ A B }

end HasNonLinearLogic

class HasFullLogic (U : Universe) [HasFunctors U] [Layer1.HasSubLinearLogic U.V]
                   [Layer1.HasNonLinearLogic U.V] extends
  HasAffineLogic U, HasNonLinearLogic U

instance HasFullLogic.layer1 (U : Universe) [HasFunctors U] [Layer1.HasSubLinearLogic U.V]
                             [Layer1.HasNonLinearLogic U.V] [HasFullLogic U] :
  Layer1.HasFullLogic U :=
⟨⟩
