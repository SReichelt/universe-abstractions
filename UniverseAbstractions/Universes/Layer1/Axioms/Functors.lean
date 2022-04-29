import UniverseAbstractions.Universes.Layer1.Axioms.Universes



namespace UniverseAbstractions.Layer1

set_option autoBoundImplicitLocal false



-- Functors at layer 1 are just functions which are used to encode implication (i.e. we disregard
-- all information about concrete instances).

class HasFunctors (U : Universe) where
(Fun             : U → U → U)
(apply {A B : U} : (Fun A B) → (A → B))

namespace HasFunctors

  infixr:20 " ⟶ " => HasFunctors.Fun

  variable {U : Universe} [h : HasFunctors U]

  instance coeFun (A B : U) : CoeFun (A ⟶ B) (λ _ => A → B) := ⟨h.apply⟩

  @[reducible] def apply₂ {A B C     : U} (F : A ⟶ B ⟶ C)         (a : A) (b : B)                 : C := F a b
  @[reducible] def apply₃ {A B C D   : U} (F : A ⟶ B ⟶ C ⟶ D)     (a : A) (b : B) (c : C)         : D := F a b c
  @[reducible] def apply₄ {A B C D E : U} (F : A ⟶ B ⟶ C ⟶ D ⟶ E) (a : A) (b : B) (c : C) (d : D) : E := F a b c d

  -- Helper classes for the `functoriality` tactic.
  section Helpers

    class IsFunApp (A : outParam U) {B : U} (b : B) where
    (F : A ⟶ B)
    (a : A)

    instance (priority := low) IsFunApp.refl {A B : U} {F : A ⟶ B} {a : A} : IsFunApp A (F a) :=
    ⟨F, a⟩

    class IsFunApp₂ (A B : outParam U) {C : U} (c : C) where
    (F : A ⟶ B ⟶ C)
    (a : A)
    (b : B)

    namespace IsFunApp₂

      variable {A B C : U}

      instance (priority := low) refl {F : A ⟶ B ⟶ C} {a : A} {b : B} : IsFunApp₂ A B (F a b) :=
      ⟨F, a, b⟩

      def isFunApp {c : C} [hApp : IsFunApp₂ A B c] : IsFunApp B c :=
      ⟨apply hApp.F hApp.a, hApp.b⟩

    end IsFunApp₂

    class IsFunApp₃ (A B C : outParam U) {D : U} (d : D) where
    (F : A ⟶ B ⟶ C ⟶ D)
    (a : A)
    (b : B)
    (c : C)

    namespace IsFunApp₃

      variable {A B C D : U}

      instance (priority := low) refl {F : A ⟶ B ⟶ C ⟶ D} {a : A} {b : B} {c : C} :
        IsFunApp₃ A B C (F a b c) :=
      ⟨F, a, b, c⟩

      def isFunApp₂ {d : D} [hApp : IsFunApp₃ A B C d] : IsFunApp₂ B C d :=
      ⟨apply hApp.F hApp.a, hApp.b, hApp.c⟩

      def isFunApp {d : D} [hApp : IsFunApp₃ A B C d] : IsFunApp C d :=
      let _ : IsFunApp₂ B C d := isFunApp₂
      IsFunApp₂.isFunApp

    end IsFunApp₃

    class IsFunApp₄ (A B C D : outParam U) {E : U} (e : E) where
    (F : A ⟶ B ⟶ C ⟶ D ⟶ E)
    (a : A)
    (b : B)
    (c : C)
    (d : D)

    namespace IsFunApp₄

      variable {A B C D E : U}

      instance (priority := low) refl {F : A ⟶ B ⟶ C ⟶ D ⟶ E} {a : A} {b : B} {c : C} {d : D} :
        IsFunApp₄ A B C D (F a b c d) :=
      ⟨F, a, b, c, d⟩

      def isFunApp₃ {e : E} [hApp : IsFunApp₄ A B C D e] : IsFunApp₃ B C D e :=
      ⟨apply hApp.F hApp.a, hApp.b, hApp.c, hApp.d⟩

      def isFunApp₂ {e : E} [hApp : IsFunApp₄ A B C D e] : IsFunApp₂ C D e :=
      let _ : IsFunApp₃ B C D e := isFunApp₃
      IsFunApp₃.isFunApp₂

      def isFunApp {e : E} [hApp : IsFunApp₄ A B C D e] : IsFunApp D e :=
      let _ : IsFunApp₂ C D e := isFunApp₂
      IsFunApp₂.isFunApp

    end IsFunApp₄

    class IsFunApp₂' (A₁ A₂ : outParam U) {B : U} (b : B) extends
      IsFunApp A₂ b where
    (h₂ : IsFunApp A₁ b)

    class IsFunApp₃' (A₁ A₂ A₃ : outParam U) {B : U} (b : B) extends
      IsFunApp₂' A₂ A₃ b where
    (h₃ : IsFunApp A₁ b)

    class IsFunApp₄' (A₁ A₂ A₃ A₄ : outParam U) {B : U} (b : B) extends
      IsFunApp₃' A₂ A₃ A₄ b where
    (h₄ : IsFunApp A₁ b)

  end Helpers

  -- A `DefFun` is a functor that additionally incorporates a concrete function in its type. In
  -- layer 1, that function is essentially just a proof that the implication holds.
  section DefFun

    structure DefFun (A B : U) (f : A → B) where
    (F : A ⟶ B)

    namespace DefFun

      notation:20 A:21 " ⟶{" f:0 "} " B:21 => HasFunctors.DefFun A B f

      variable {A B : U}

      def isFunApp {f : A → B} (F : A ⟶{f} B) {a : A} : IsFunApp A (f a) := ⟨F.F, a⟩

      def cast {f g : A → B} (F : A ⟶{f} B) : A ⟶{g} B := ⟨F.F⟩

      def defAppFun (F : A ⟶ B) : A ⟶{apply F} B := ⟨F⟩

    end DefFun

    structure DefFun₂ (A B C : U) (f : A → B → C) where
    (app (a : A) : B ⟶{f a} C)
    (toDefFun : A ⟶{λ a => (app a).F} (B ⟶ C))

    namespace DefFun₂

      notation:20 A:21 " ⟶ " B:21 " ⟶{" f:0 "} " C:21 => HasFunctors.DefFun₂ A B C f

      variable {A B C : U}

      @[reducible] def F {f : A → B → C} (F : A ⟶ B ⟶{f} C) : A ⟶ B ⟶ C :=
      F.toDefFun.F

      def isFunApp₂ {f : A → B → C} (F : A ⟶ B ⟶{f} C) {a : A} {b : B} :
        IsFunApp₂ A B (f a b) :=
      ⟨F.F, a, b⟩

      def cast {f g : A → B → C} (F : A ⟶ B ⟶{f} C) : A ⟶ B ⟶{g} C :=
      ⟨λ a => DefFun.cast (F.app a), DefFun.cast F.toDefFun⟩

      def defAppFun (F : A ⟶ B ⟶ C) : A ⟶ B ⟶{apply₂ F} C :=
      ⟨λ a => DefFun.defAppFun (F a), DefFun.defAppFun F⟩

    end DefFun₂

    structure DefFun₃ (A B C D : U) (f : A → B → C → D) where
    (app (a : A) : B ⟶ C ⟶{f a} D)
    (toDefFun : A ⟶{λ a => (app a).F} (B ⟶ C ⟶ D))

    namespace DefFun₃

      notation:20 A:21 " ⟶ " B:21 " ⟶ " C:21 " ⟶{" f:0 "} " D:21 => HasFunctors.DefFun₃ A B C D f

      variable {A B C D : U}

      @[reducible] def F {f : A → B → C → D} (F : A ⟶ B ⟶ C ⟶{f} D) :
        A ⟶ B ⟶ C ⟶ D :=
      F.toDefFun.F

      def isFunApp₃ {f : A → B → C → D} (F : A ⟶ B ⟶ C ⟶{f} D) {a : A} {b : B} {c : C} :
        IsFunApp₃ A B C (f a b c) :=
      ⟨F.F, a, b, c⟩

      def cast {f g : A → B → C → D} (F : A ⟶ B ⟶ C ⟶{f} D) : A ⟶ B ⟶ C ⟶{g} D :=
      ⟨λ a => DefFun₂.cast (F.app a), DefFun.cast F.toDefFun⟩

      def defAppFun (F : A ⟶ B ⟶ C ⟶ D) : A ⟶ B ⟶ C ⟶{apply₃ F} D :=
      ⟨λ a => DefFun₂.defAppFun (F a), DefFun.defAppFun F⟩

    end DefFun₃

    structure DefFun₄ (A B C D E : U) (f : A → B → C → D → E) where
    (app (a : A) : B ⟶ C ⟶ D ⟶{f a} E)
    (toDefFun : A ⟶{λ a => (app a).F} (B ⟶ C ⟶ D ⟶ E))

    namespace DefFun₄

      notation:20 A:21 " ⟶ " B:21 " ⟶ " C:21 " ⟶ " D:21 " ⟶{" f:0 "} " E:21 => HasFunctors.DefFun₄ A B C D E f

      variable {A B C D E : U}

      @[reducible] def F {f : A → B → C → D → E} (F : A ⟶ B ⟶ C ⟶ D ⟶{f} E) : A ⟶ B ⟶ C ⟶ D ⟶ E :=
      F.toDefFun.F

      def isFunApp₄ {f : A → B → C → D → E} (F : A ⟶ B ⟶ C ⟶ D ⟶{f} E) {a : A} {b : B} {c : C} {d : D} :
        IsFunApp₄ A B C D (f a b c d) :=
      ⟨F.F, a, b, c, d⟩

      def cast {f g : A → B → C → D → E} (F : A ⟶ B ⟶ C ⟶ D ⟶{f} E) : A ⟶ B ⟶ C ⟶ D ⟶{g} E :=
      ⟨λ a => DefFun₃.cast (F.app a), DefFun.cast F.toDefFun⟩

      def defAppFun (F : A ⟶ B ⟶ C ⟶ D ⟶ E) : A ⟶ B ⟶ C ⟶ D ⟶{apply₄ F} E :=
      ⟨λ a => DefFun₃.defAppFun (F a), DefFun.defAppFun F⟩

    end DefFun₄

  end DefFun

end HasFunctors

open HasFunctors



class HasLinearLogic (U : Universe) [HasFunctors U] where
(defIdFun      (A     : U) : A ⟶{id} A)
(defRevAppFun₂ (A B   : U) : A ⟶ (A ⟶ B) ⟶{λ a F => F a} B)
(defCompFun₃   (A B C : U) : (A ⟶ B) ⟶ (B ⟶ C) ⟶ A ⟶{λ F G a => G (F a)} C)

namespace HasLinearLogic

  variable {U : Universe} [HasFunctors U] [HasLinearLogic U]

  @[reducible] def idFun (A : U) : A ⟶ A := (defIdFun A).F

  @[reducible] def defAppFun₂ (A B : U) : (A ⟶ B) ⟶ A ⟶{λ F a => F a} B :=
  ⟨DefFun.defAppFun, defIdFun (A ⟶ B)⟩

  @[reducible] def appFun {A B : U} (F : A ⟶ B) : A ⟶ B := ((defAppFun₂ A B).app F).F
  @[reducible] def appFun₂ (A B : U) : (A ⟶ B) ⟶ A ⟶ B := (defAppFun₂ A B).F

  instance appFun.isFunApp {A B : U} {F : A ⟶ B} : IsFunApp (A ⟶ B) (appFun F) := ⟨appFun₂ A B, F⟩

  @[reducible] def revAppFun {A : U} (a : A) (B : U) : (A ⟶ B) ⟶ B := ((defRevAppFun₂ A B).app a).F
  @[reducible] def revAppFun₂ (A B : U) : A ⟶ (A ⟶ B) ⟶ B := (defRevAppFun₂ A B).F

  instance revAppFun.isFunApp {A B : U} {a : A} : IsFunApp A (revAppFun a B) := ⟨revAppFun₂ A B, a⟩

  @[reducible] def compFun {A B C : U} (F : A ⟶ B) (G : B ⟶ C) : A ⟶ C :=
  (((defCompFun₃ A B C).app F).app G).F
  @[reducible] def compFun₂ {A B : U} (F : A ⟶ B) (C : U) : (B ⟶ C) ⟶ (A ⟶ C) :=
  ((defCompFun₃ A B C).app F).F
  @[reducible] def compFun₃ (A B C : U) : (A ⟶ B) ⟶ (B ⟶ C) ⟶ (A ⟶ C) :=
  (defCompFun₃ A B C).F
  notation:90 G:91 " ⊙ " F:90 => HasLinearLogic.compFun F G

  instance compFun.isFunApp {A B C : U} {F : A ⟶ B} {G : B ⟶ C} : IsFunApp (B ⟶ C) (compFun F G) :=
  ⟨compFun₂ F C, G⟩

  instance compFun.isFunApp₂ {A B C : U} {F : A ⟶ B} {G : B ⟶ C} :
    IsFunApp₂ (A ⟶ B) (B ⟶ C) (compFun F G) :=
  ⟨compFun₃ A B C, F, G⟩

  instance compFun₂.isFunApp {A B C : U} {F : A ⟶ B} : IsFunApp (A ⟶ B) (compFun₂ F C) :=
  ⟨compFun₃ A B C, F⟩

end HasLinearLogic


class HasSubLinearLogic (U : Universe) [HasFunctors U] where
(defConstFun₂ (A B : U) : B ⟶ A ⟶{λ b a => b} B)

namespace HasSubLinearLogic

  variable {U : Universe} [HasFunctors U] [HasSubLinearLogic U]

  @[reducible] def constFun (A : U) {B : U} (b : B) : A ⟶ B := ((defConstFun₂ A B).app b).F
  @[reducible] def constFun₂ (A B : U) : B ⟶ (A ⟶ B) := (defConstFun₂ A B).F

  instance constFun.isFunApp {A B : U} {b : B} : IsFunApp B (constFun A b) := ⟨constFun₂ A B, b⟩

end HasSubLinearLogic

class HasAffineLogic (U : Universe) [HasFunctors U] extends
  HasLinearLogic U, HasSubLinearLogic U


class HasNonLinearLogic (U : Universe) [HasFunctors U] where
(defDupFun₂ (A B : U) : (A ⟶ A ⟶ B) ⟶ A ⟶{λ F a => F a a} B)

namespace HasNonLinearLogic

  variable {U : Universe} [HasFunctors U] [HasNonLinearLogic U]

  @[reducible] def dupFun {A B : U} (F : A ⟶ A ⟶ B) : A ⟶ B := ((defDupFun₂ A B).app F).F
  @[reducible] def dupFun₂ (A B : U) : (A ⟶ A ⟶ B) ⟶ (A ⟶ B) := (defDupFun₂ A B).F

  instance dupFun.isFunApp {A B : U} {F : A ⟶ A ⟶ B} : IsFunApp (A ⟶ A ⟶ B) (dupFun F) :=
  ⟨dupFun₂ A B, F⟩

end HasNonLinearLogic

class HasFullLogic (U : Universe) [HasFunctors U] extends
  HasAffineLogic U, HasNonLinearLogic U