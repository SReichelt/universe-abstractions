import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences



set_option autoBoundImplicitLocal false
--set_option pp.universes true



-- TODO: Extract general `IsFunctorial` class.
-- Include identity type constructor.



class HasTypeFun {U V UtV : Universe} [HasFunctors {U} {V} UtV] [HasIdentity {V}]
                 (T : U → V) where
(defTypeFun : ⌊U⌋ ⟶{λ A => T A} ⌊V⌋)

namespace HasTypeFun

  open HasCongrArg HasTypeIdentity

  variable {U V UtV : Universe} [HasFunctors {U} {V} UtV] (T : U → V)

  @[reducible] def typeFun [HasIdentity {V}] [h : HasTypeFun T] : ⌊U⌋ ⟶ ⌊V⌋ :=
  h.defTypeFun

  variable [HasIdentity {U}] [HasTypeIdentity V] [h : HasTypeFun T] [HasCongrArg {U} {V}]

  def castInstTo  {A₁ A₂ : U} (E : ⸤A₁⸥ ≃ ⸤A₂⸥) (b : T A₁) : T A₂ :=
  castTo  (defCongrArg h.defTypeFun E) b
  def castInstInv {A₁ A₂ : U} (E : ⸤A₁⸥ ≃ ⸤A₂⸥) (b : T A₂) : T A₁ :=
  castInv (defCongrArg h.defTypeFun E) b

end HasTypeFun



class HasRightTypeFun {U V W VtW : Universe} [HasFunctors {V} {W} VtW] [HasIdentity {W}]
                      (T : U → V → W) where
(defTypeFun (A : U) : ⌊V⌋ ⟶{λ B => T A B} ⌊W⌋)

namespace HasRightTypeFun

  open HasCongrArg HasTypeIdentity

  variable {U V W VtW : Universe} [HasFunctors {V} {W} VtW] (T : U → V → W)

  @[reducible] def typeFun [HasIdentity {W}] [h : HasRightTypeFun T] (A : U) : ⌊V⌋ ⟶ ⌊W⌋ :=
  h.defTypeFun A

  variable [HasIdentity {V}] [HasTypeIdentity W] [h : HasRightTypeFun T] [HasCongrArg {V} {W}]

  def castInstTo  {A : U} {B₁ B₂ : V} (E : ⸤B₁⸥ ≃ ⸤B₂⸥) (c : T A B₁) : T A B₂ :=
  castTo  (defCongrArg (h.defTypeFun A) E) c
  def castInstInv {A : U} {B₁ B₂ : V} (E : ⸤B₁⸥ ≃ ⸤B₂⸥) (c : T A B₂) : T A B₁ :=
  castInv (defCongrArg (h.defTypeFun A) E) c

end HasRightTypeFun

class HasLeftTypeFun {U V W UtW : Universe} [HasFunctors {U} {W} UtW] [HasIdentity {W}]
                     (T : U → V → W) where
(defRevTypeFun (B : V) : ⌊U⌋ ⟶{λ A => T A B} ⌊W⌋)

namespace HasLeftTypeFun

  open HasCongrArg HasTypeIdentity

  variable {U V W UtW : Universe} [HasFunctors {U} {W} UtW] (T : U → V → W)

  @[reducible] def revTypeFun [HasIdentity {W}] [h : HasLeftTypeFun T] (B : V) : ⌊U⌋ ⟶ ⌊W⌋ :=
  h.defRevTypeFun B

  variable [HasIdentity {U}] [HasTypeIdentity W] [h : HasLeftTypeFun T] [HasCongrArg {U} {W}]

  def castInstTo  {A₁ A₂ : U} {B : V} (E : ⸤A₁⸥ ≃ ⸤A₂⸥) (c : T A₁ B) : T A₂ B :=
  castTo  (defCongrArg (h.defRevTypeFun B) E) c
  def castInstInv {A₁ A₂ : U} {B : V} (E : ⸤A₁⸥ ≃ ⸤A₂⸥) (c : T A₂ B) : T A₁ B :=
  castInv (defCongrArg (h.defRevTypeFun B) E) c

end HasLeftTypeFun

class HasTypeBiFun {U V W VtW UtVtW : Universe} [HasFunctors {V} {W} VtW]
                   [HasFunctors {U} VtW UtVtW] [HasIdentity {W}] [HasIdentity VtW]
                   (T : U → V → W) extends
  HasRightTypeFun T where
(defTypeFunFun : ⌊U⌋ ⟶{λ A => defTypeFun A} (⌊V⌋ ⟶ ⌊W⌋))

namespace HasTypeBiFun

  open HasCongrFun HasSwapFun HasSwapFunFun

  variable {U V W VtW UtVtW : Universe} [HasFunctors {V} {W} VtW] [HasFunctors {U} VtW UtVtW]
           [HasIdentity {W}] [HasIdentity VtW] (T : U → V → W) [h : HasTypeBiFun T]

  @[reducible] def typeFunFun : ⌊U⌋ ⟶ ⌊V⌋ ⟶ ⌊W⌋ := h.defTypeFunFun

  variable {UtW : Universe} [HasFunctors {U} {W} UtW] [HasCongrFun {V} {W}]

  def defRevTypeFun [HasSwapFun {U} {V} {W}] (B : V) :
    ⌊U⌋ ⟶{λ A => T A B} ⌊W⌋ :=
  swapFun (typeFunFun T) B
  ◄ byDef₂

  instance [HasSwapFun {U} {V} {W}] : HasLeftTypeFun T := ⟨defRevTypeFun T⟩

  def defRevTypeFunFun {VUtW : Universe} [HasFunctors {V} UtW VUtW] [HasIdentity UtW]
                       [HasSwapFunFun {U} {V} {W}] :
    ⌊V⌋ ⟶{λ B => defRevTypeFun T B} (⌊U⌋ ⟶ ⌊W⌋) :=
  defSwapFunFun (typeFunFun T)

  @[reducible] def revTypeFunFun {VUtW : Universe} [HasFunctors {V} UtW VUtW] [HasIdentity UtW]
                                 [HasSwapFunFun {U} {V} {W}] :
    ⌊V⌋ ⟶ ⌊U⌋ ⟶ ⌊W⌋ :=
  defRevTypeFunFun T

end HasTypeBiFun
