import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedFunctors

import UniverseAbstractions.MathlibFragments.Init.CoreExt



namespace UniverseAbstractions.Layer1

set_option autoImplicit false
set_option linter.unusedVariables false

open HasPiType HasFunctors HasIdFun HasExternalLinearLogic HasExternalSubLinearLogic
     HasExternalNonLinearLogic

universe u v w vv



def Prerelation (α : Sort u) (V : Universe.{v, vv}) := α → α → V

namespace Prerelation

  section

    variable {α : Sort u} {V : Universe}

    class IsFull (R : Prerelation α V) where
      inst (a b : α) : R a b

    class HasRefl (R : Prerelation α V) where
      refl (a : α) : R a a

    variable [HasLinearLogic V]

    class HasSymm (R : Prerelation α V) where
      symmFun (a b : α) : R a b ⥤ R b a

    @[reducible] def HasSymm.symm {R : Prerelation α V} [h : HasSymm R] {a b : α} (e : R a b) :
        R b a :=
      (h.symmFun a b) e

    postfix:max "⁻¹" => Prerelation.HasSymm.symm

    class HasTrans (R : Prerelation α V) where
      revTransFun₂ (a b c : α) : R b c ⥤ R a b ⥤ R a c

    namespace HasTrans

      @[reducible] def revTrans {R : Prerelation α V} [h : HasTrans R] {a b c : α}
                                (g : R b c) (f : R a b) :
          R a c :=
        (h.revTransFun₂ a b c) g f

      @[reducible] def revTransFun {R : Prerelation α V} [h : HasTrans R] (a : α) {b c : α}
                                   (g : R b c) :
          R a b ⥤ R a c :=
        (h.revTransFun₂ a b c) g

      @[reducible] def trans {R : Prerelation α V} [h : HasTrans R] {a b c : α}
                             (f : R a b) (g : R b c) :
          R a c :=
        revTrans g f

      def transFun {R : Prerelation α V} [h : HasTrans R] {a b : α} (f : R a b) (c : α) :
          R b c ⥤ R a c :=
        swapFun (h.revTransFun₂ a b c) f

      def transFun₂ {R : Prerelation α V} [h : HasTrans R] (a b c : α) : R a b ⥤ R b c ⥤ R a c :=
        swapFun₂ (h.revTransFun₂ a b c)

      infixr:90 " • " => Prerelation.HasTrans.revTrans

      instance revTrans.isFunApp {R : Prerelation α V} [h : HasTrans R] {a b c : α}
                                 {g : R b c} {f : R a b} :
          IsFunApp (g • f) :=
        ⟨revTransFun a g, f⟩

      instance revTransFun.isFunApp {R : Prerelation α V} [h : HasTrans R] {a b c : α} {g : R b c} :
          IsFunApp (revTransFun a g) :=
        ⟨revTransFun₂ a b c, g⟩

      instance revTrans.isFunApp₂' {R : Prerelation α V} [h : HasTrans R] {a b c : α}
                                   {g : R b c} {f : R a b} :
          IsFunApp₂' (g • f) :=
        ⟨⟨transFun f c, g⟩⟩

      instance transFun.isFunApp {R : Prerelation α V} [h : HasTrans R] {a b c : α} {f : R a b} :
          IsFunApp (transFun f c) :=
        ⟨transFun₂ a b c, f⟩

    end HasTrans

    class IsPreorder (R : Prerelation α V) extends HasRefl R, HasTrans R
    class IsEquivalence (R : Prerelation α V) extends IsPreorder R, HasSymm R

    section

      variable (R : Prerelation α V)

      -- (Intentionally non-`@[reducible]`, as it would cause instance loops.)
      def opposite : Prerelation α V := λ a b => R b a

      namespace opposite

        instance isFull [h : IsFull R] : IsFull (opposite R) := ⟨λ a b => h.inst b a⟩

        instance hasRefl  [h : HasRefl  R] : HasRefl  (opposite R) := ⟨h.refl⟩
        instance hasSymm  [h : HasSymm  R] : HasSymm  (opposite R) := ⟨λ a b => h.symmFun b a⟩
        instance hasTrans [h : HasTrans R] : HasTrans (opposite R) := ⟨λ a b c => h.transFun₂ c b a⟩

        instance isPreorder    [IsPreorder    R] : IsPreorder    (opposite R) := ⟨⟩
        instance isEquivalence [IsEquivalence R] : IsEquivalence (opposite R) := ⟨⟩

      end opposite

      -- TODO: I think "lift" is not the correct word for this.
      @[reducible] def lift {ω : Sort w} (l : ω → α) : Prerelation ω V := λ a b => R (l a) (l b)

      namespace lift

        variable {ω : Sort w} (l : ω → α)

        instance isFull [h : IsFull R] : IsFull (lift R l) := ⟨λ a b => h.inst (l a) (l b)⟩

        instance hasRefl  [h : HasRefl  R] : HasRefl  (lift R l) := ⟨λ a     => h.refl         (l a)⟩
        instance hasSymm  [h : HasSymm  R] : HasSymm  (lift R l) := ⟨λ a b   => h.symmFun      (l a) (l b)⟩
        instance hasTrans [h : HasTrans R] : HasTrans (lift R l) := ⟨λ a b c => h.revTransFun₂ (l a) (l b) (l c)⟩

        instance isPreorder    [IsPreorder    R] : IsPreorder    (lift R l) := ⟨⟩
        instance isEquivalence [IsEquivalence R] : IsEquivalence (lift R l) := ⟨⟩

      end lift

    end

  end

  section

    def unitRelation (α : Sort u) {V : Universe.{v}} (B : V) : Prerelation α V := λ _ _ => B

    def emptyRelation (V : Universe.{v}) : Prerelation PEmpty.{u} V := λ e _ => PEmpty.elim e

    instance emptyRelation.isFull (V : Universe.{v}) : IsFull (emptyRelation V) where
      inst e _ := PEmpty.elim e

    instance emptyRelation.isEquivalence (V : Universe.{v}) [HasLinearLogic V] :
        IsEquivalence (emptyRelation V) where
      refl         e     := PEmpty.elim e
      symmFun      e _   := PEmpty.elim e
      revTransFun₂ e _ _ := PEmpty.elim e

  end

  section

    variable {α : Sort u} {V : Universe} [HasLinearLogic V]

    @[reducible] def implication (R S : Prerelation α V) : Prerelation α V :=
      λ a b => R a b ⥤ S a b

    -- Using the class `IsFull` here instead of just defining `HasImplication` as a universally
    -- quantified type seems a little over the top, but it solves the problem that we want the
    -- quantifier to have explicit binders but also want a `CoeFun` where the same binders are
    -- implicit.
    class HasImplication (R S : Prerelation α V) extends IsFull (implication R S)

    namespace HasImplication

      instance coeFun (R S : Prerelation α V) :
          CoeFun (HasImplication R S) (λ _ => ∀ {a b}, R a b → S a b) :=
        ⟨λ F {a b} => apply (F.inst a b)⟩

      def opposite (R S : Prerelation α V) [h : HasImplication R S] :
          HasImplication (opposite R) (opposite S) where
        inst a b := h.inst b a

      def lift (R S : Prerelation α V) [h : HasImplication R S] {ω : Sort w} (l : ω → α) :
          HasImplication (lift R l) (lift S l) where
        inst a b := h.inst (l a) (l b)

      def idImpl (R : Prerelation α V) : HasImplication R R where
        inst a b := idFun (R a b)

      def constImpl [HasSubLinearLogic V] (R : Prerelation α V) {C : V} (c : C) :
          HasImplication R (unitRelation α C) where
        inst a b := constFun (R a b) c

      def compImpl (R S T : Prerelation α V) [hRS : HasImplication R S] [hST : HasImplication S T] :
          HasImplication R T where
        inst a b := hST.inst a b ⊙ hRS.inst a b

      def symmImpl (R : Prerelation α V) [HasSymm R] :
          HasImplication R (Prerelation.opposite R) where
        inst := HasSymm.symmFun

    end HasImplication

    @[reducible] def implication₂ (R S T : Prerelation α V) : Prerelation α V :=
      implication R (implication S T)

    class HasImplication₂ (R S T : Prerelation α V) extends HasImplication R (implication S T)

    namespace HasImplication₂

      def swapImpl (R S T : Prerelation α V) [h : HasImplication₂ R S T] :
          HasImplication₂ S R T where
        inst a b := swapFun₂ (h.inst a b)

      def dupImpl [HasNonLinearLogic V] (R T : Prerelation α V) [h : HasImplication₂ R R T] :
          HasImplication R T where
        inst a b := dupFun (h.inst a b)

      def substImpl [HasNonLinearLogic V] (R S T : Prerelation α V) [hRS : HasImplication R S]
                    [hRST : HasImplication₂ R S T] :
          HasImplication R T where
        inst a b := revSubstFun (hRST.inst a b) (hRS.inst a b)

    end HasImplication₂

  end

end Prerelation

open Prerelation



def DependentPrerelation {U : Universe.{u}} {V : Universe.{v}} (R : Prerelation U V)
                         (W : Universe.{w}) :=
  ∀ {A B}, R A B → (A → B → W)

namespace DependentPrerelation

  variable {U V W : Universe} {R : Prerelation U V}

  class HasDependentRefl (S : DependentPrerelation R W) [h : HasRefl R] where
    refl {A : U} (a : A) : S (h.refl A) a a

  def ReflRel (S : DependentPrerelation R W) [h : HasRefl R] (A : U) : Prerelation A W :=
    S (h.refl A)

  instance (S : DependentPrerelation R W) [HasRefl R] [h : HasDependentRefl S] (A : U) :
      HasRefl (ReflRel S A) :=
    ⟨h.refl⟩

  variable [HasLinearLogic V] [HasLinearLogic W]

  class HasDependentSymm (S : DependentPrerelation R W) [h : HasSymm R] where
    symmFun {A B : U} (F : R A B) (a : A) (b : B) : S F a b ⥤ S F⁻¹ b a

  def HasDependentSymm.symm {S : DependentPrerelation R W} [HasSymm R] [h : HasDependentSymm S]
                            {A B : U} {F : R A B} {a : A} {b : B} (e : S F a b) :
      S F⁻¹ b a :=
    (h.symmFun F a b) e

  postfix:max "[⁻¹]" => DependentPrerelation.HasDependentSymm.symm

  class HasDependentTrans (S : DependentPrerelation R W) [h : HasTrans R] where
    transFun₂ {A B C : U} (F : R A B) (G : R B C) (a : A) (b : B) (c : C) :
      S F a b ⥤ S G b c ⥤ S (G • F) a c

  def HasDependentTrans.trans {S : DependentPrerelation R W} [HasTrans R] [h : HasDependentTrans S]
                              {A B C : U} {F : R A B} {G : R B C} {a : A} {b : B} {c : C}
                              (f : S F a b) (g : S G b c) :
      S (G • F) a c :=
    (h.transFun₂ F G a b c) f g

  notation:90 g:91 " [•] " f:90 => DependentPrerelation.HasDependentTrans.trans f g

  class IsDependentPreorder (S : DependentPrerelation R W) [h : IsPreorder R] extends
    HasDependentRefl S, HasDependentTrans S

  class IsDependentEquivalence (S : DependentPrerelation R W) [h : IsEquivalence R] extends
    IsDependentPreorder S, HasDependentSymm S

end DependentPrerelation
