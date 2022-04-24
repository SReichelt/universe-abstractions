import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Axioms.Singletons
import UniverseAbstractions.Universes.Layer1.Axioms.Products
import UniverseAbstractions.Universes.Layer1.Axioms.Coproducts
import UniverseAbstractions.Universes.Layer1.Axioms.Equivalences
import UniverseAbstractions.Universes.Layer1.Meta.Tactics.Functoriality

import UniverseAbstractions.MathlibFragments.Init.CoreExt



namespace UniverseAbstractions.Layer1

set_option autoBoundImplicitLocal false

open HasFunctors HasLinearLogic

universe u v w vv



def Prerelation (α : Sort u) (V : Universe.{v, vv}) := α → α → V

namespace Prerelation

  section

    variable {α : Sort u} {V : Universe} [HasFunctors V] [HasLinearLogic V]

    class HasRefl (R : Prerelation α V) where
    (refl (a : α) : R a a)

    class HasSymm (R : Prerelation α V) where
    (symmFun (a b : α) : R a b ⟶ R b a)

    def HasSymm.symm {R : Prerelation α V} [h : HasSymm R] {a b : α} (e : R a b) : R b a :=
    (h.symmFun a b) e

    postfix:max "⁻¹" => Prerelation.HasSymm.symm

    class HasTrans (R : Prerelation α V) where
    (transFun₂ (a b c : α) : R a b ⟶ R b c ⟶ R a c)

    def HasTrans.trans {R : Prerelation α V} [h : HasTrans R] {a b c : α} (f : R a b) (g : R b c) :
      R a c :=
    (h.transFun₂ a b c) f g

    notation:90 g:91 " • " f:90 => Prerelation.HasTrans.trans f g

    class IsPreorder (R : Prerelation α V) extends HasRefl R, HasTrans R
    class IsEquivalence (R : Prerelation α V) extends IsPreorder R, HasSymm R

    section

      variable (R : Prerelation α V)

      -- (Intentionally non-`@[reducible]`, as it would cause instance loops.)
      def opposite : Prerelation α V := λ a b => R b a

      namespace opposite

        instance hasRefl  [h : HasRefl  R] : HasRefl  (opposite R) := ⟨h.refl⟩
        instance hasSymm  [h : HasSymm  R] : HasSymm  (opposite R) := ⟨λ a b => h.symmFun b a⟩
        instance hasTrans [h : HasTrans R] : HasTrans (opposite R) := ⟨λ a b c => Λ f g => (h.transFun₂ c b a) g f⟩

        instance isPreorder    [IsPreorder    R] : IsPreorder    (opposite R) := ⟨⟩
        instance isEquivalence [IsEquivalence R] : IsEquivalence (opposite R) := ⟨⟩

      end opposite

      -- TODO: I think "lift" is not the correct word for this.
      @[reducible] def lift {ω : Sort w} (l : ω → α) : Prerelation ω V := λ a b => R (l a) (l b)

      namespace lift

        variable {ω : Sort w} (l : ω → α)

        instance hasRefl  [h : HasRefl  R] : HasRefl  (lift R l) := ⟨λ a     => h.refl      (l a)⟩
        instance hasSymm  [h : HasSymm  R] : HasSymm  (lift R l) := ⟨λ a b   => h.symmFun   (l a) (l b)⟩
        instance hasTrans [h : HasTrans R] : HasTrans (lift R l) := ⟨λ a b c => h.transFun₂ (l a) (l b) (l c)⟩

        instance isPreorder    [IsPreorder    R] : IsPreorder    (lift R l) := ⟨⟩
        instance isEquivalence [IsEquivalence R] : IsEquivalence (lift R l) := ⟨⟩

      end lift

    end

    section

      open HasProducts

      variable [HasProducts V] (R S : Prerelation α V)

      def product : Prerelation α V := λ a b => R a b ⊓ S a b

      namespace product

        instance hasRefl  [hR : HasRefl  R] [hS : HasRefl  S] : HasRefl  (product R S) :=
        ⟨λ a => intro (hR.refl a) (hS.refl a)⟩
        instance hasSymm  [hR : HasSymm  R] [hS : HasSymm  S] : HasSymm  (product R S) :=
        ⟨λ a b => elimFun (Λ el er => intro el⁻¹ er⁻¹)⟩
        instance hasTrans [hR : HasTrans R] [hS : HasTrans S] : HasTrans (product R S) :=
        ⟨λ a b c => elimFun (Λ fl fr => elimFun (Λ gl gr => intro (gl • fl) (gr • fr)))⟩

        instance isPreorder    [IsPreorder    R] [IsPreorder    S] : IsPreorder    (product R S) := ⟨⟩
        instance isEquivalence [IsEquivalence R] [IsEquivalence S] : IsEquivalence (product R S) := ⟨⟩

      end product

    end

    section

      open HasCoproducts

      variable [HasCoproducts V] (R S : Prerelation α V)

      def coproduct : Prerelation α V := λ a b => R a b ⊔ S a b

      namespace coproduct

        instance hasLeftRefl [hR : HasRefl R] : HasRefl (coproduct R S) :=
        ⟨λ a => leftIntro (hR.refl a) (S a a)⟩
        instance hasRightRefl [hS : HasRefl S] : HasRefl (coproduct R S) :=
        ⟨λ a => rightIntro (R a a) (hS.refl a)⟩
        instance hasSymm [hR : HasSymm R] [hS : HasSymm S] : HasSymm (coproduct R S) :=
        ⟨λ a b => elimFun (Λ el => leftIntro el⁻¹ (S b a)) (Λ er => rightIntro (R b a) er⁻¹)⟩

      end coproduct

    end

  end

  section

    open HasTop

    def unitRelation (α : Sort u) {V : Universe.{v}} (B : V) : Prerelation α V := λ _ _ => B

    def topRelation (α : Sort u) (V : Universe.{v}) [HasFunctors V] [HasTop V] : Prerelation α V :=
    unitRelation α (Top V)

    instance topRelation.isEquivalence (α : Sort u) {V : Universe.{v}}
                                      [HasFunctors V] [HasLinearLogic V] [HasTop V] :
      IsEquivalence (topRelation α V) :=
    { refl      := λ _     => top V,
      symmFun   := λ _ _   => HasTop.elimFun (top V),
      transFun₂ := λ _ _ _ => HasTop.elimFun (idFun (Top V)) }

    def emptyRelation (V : Universe.{v}) : Prerelation PEmpty.{u} V := λ e _ => PEmpty.elim e

    instance emptyRelation.isEquivalence (V : Universe.{v}) [HasFunctors V] :
      IsEquivalence (emptyRelation V) :=
    { refl      := λ e     => PEmpty.elim e,
      symmFun   := λ e _   => PEmpty.elim e,
      transFun₂ := λ e _ _ => PEmpty.elim e }

  end

end Prerelation

open Prerelation



namespace HasFunctors

  variable (U : Universe) [hFun : HasFunctors U]

  def funRel : Prerelation U U := hFun.Fun

  instance funRel.isPreorder [HasLinearLogic U] : IsPreorder (funRel U) :=
  { refl      := λ A     => idFun A,
    transFun₂ := λ A B C => compFun₃ A B C }

end HasFunctors


namespace HasEquivalences

  variable (U : Universe) [HasFunctors U]

  def equivRel [hEquiv : HasEquivalences U] : Prerelation U U := hEquiv.Equiv

  instance equivRel.isPreorder [HasLinearLogic U] [HasEquivOpFun U] : IsEquivalence (equivRel U) :=
  { refl      := λ A     => HasEquivOp.refl         A,
    symmFun   := λ A B   => HasEquivOpFun.symmFun   A B,
    transFun₂ := λ A B C => HasEquivOpFun.transFun₂ A B C }

end HasEquivalences



class HasEquivalenceRelation (α : Sort u) (V : outParam Universe.{v, vv})
                             [outParam (HasFunctors V)] :
  Sort (max 1 u v vv) where
(R : Prerelation α V)
[h : Prerelation.IsEquivalence R]

namespace HasEquivalenceRelation

  variable {α : Sort u} {V : Universe} [HasFunctors V] [h : HasEquivalenceRelation α V]

  instance isEquivalence : IsEquivalence h.R := h.h

end HasEquivalenceRelation



def DependentPrerelation {U : Universe.{u}} {V : Universe.{v}} (R : Prerelation U V)
                         (W : Universe.{w}) :=
∀ {A B}, R A B → (A → B → W)

namespace DependentPrerelation

  variable {U V W : Universe} [HasFunctors V] [HasFunctors W] {R : Prerelation U V}

  class HasDependentRefl (S : DependentPrerelation R W) [h : HasRefl R] where
  (refl {A : U} (a : A) : S (h.refl A) a a)

  def ReflRel (S : DependentPrerelation R W) [h : HasRefl R] (A : U) : Prerelation A W :=
  S (h.refl A)

  instance (S : DependentPrerelation R W) [HasRefl R] [h : HasDependentRefl S] (A : U) :
    HasRefl (ReflRel S A) :=
  ⟨h.refl⟩

  class HasDependentSymm (S : DependentPrerelation R W) [h : HasSymm R] where
  (symmFun {A B : U} (F : R A B) (a : A) (b : B) : S F a b ⟶ S F⁻¹ b a)

  def HasDependentSymm.symm {S : DependentPrerelation R W} [HasSymm R] [h : HasDependentSymm S]
                            {A B : U} {F : R A B} {a : A} {b : B} (e : S F a b) :
    S F⁻¹ b a :=
  (h.symmFun F a b) e

  postfix:max "[⁻¹]" => DependentPrerelation.HasDependentSymm.symm

  class HasDependentTrans (S : DependentPrerelation R W) [h : HasTrans R] where
  (transFun₂ {A B C : U} (F : R A B) (G : R B C) (a : A) (b : B) (c : C) :
     S F a b ⟶ S G b c ⟶ S (G • F) a c)

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
