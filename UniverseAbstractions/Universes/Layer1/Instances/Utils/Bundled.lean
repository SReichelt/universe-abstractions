import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Products



namespace UniverseAbstractions.Layer1

set_option autoImplicit false

universe u uu u' v w

open HasSigmaType



structure Bundled {U : Universe.{u, uu}} (Φ : U → Sort v) : Sort (max 1 uu v) where
  T : U
  [h : Φ T]

namespace Bundled

  variable {U : Universe.{u, uu}} [HasUnivFunctors U U]

  instance hasInstances (Φ : U → Sort v) : HasInstances (Bundled Φ) := ⟨λ A => A.T⟩

  def univ (Φ : U → Sort v) : Universe.{u, max 1 uu v} := ⟨Bundled Φ⟩

  class HasInstCondition (Φ : U → Sort v) (A : U) where
    IsInst  : A → Sort w
    [hSigma : HasTypeWithIntro U (PSigma IsInst)]
    [h      : Φ (Sigma U IsInst)]

  namespace HasInstCondition

    variable (Φ : U → Sort v) (A : U) [hCond : HasInstCondition Φ A]

    instance : HasTypeWithIntro U (PSigma hCond.IsInst) := hCond.hSigma

  end HasInstCondition

  def type (Φ : U → Sort v) (A : U) [hCond : HasInstCondition Φ A] : univ Φ where
    T := Sigma U hCond.IsInst
    h := hCond.h

  instance hasType (Φ : U → Sort v) (α : Sort u') [HasType U α] [HasInstCondition Φ [α | U]] :
      HasType (univ Φ) α where
    T     := type Φ [α | U]
    hElim := ⟨λ a => (fst a : [α | U])⟩

  def defInst {Φ : U → Sort v} {α : Sort u'} [HasType U α] [hCond : HasInstCondition Φ [α | U]]
              {a : α} {a' : [α | U]_{a}} (isInst : hCond.IsInst (Φ := Φ) a') :
      [α | univ Φ]_{a} :=
    intro U a' isInst

  def defInst' {Φ : U → Sort v} {α : Sort u'} [HasTypeWithIntro U α]
               [hCond : HasInstCondition Φ [α | U]] {a : α} (isInst : hCond.IsInst (Φ := Φ) a) :
      [α | univ Φ]_{a} :=
    defInst isInst

end Bundled
