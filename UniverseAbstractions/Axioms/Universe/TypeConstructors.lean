import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences



set_option autoBoundImplicitLocal false
--set_option pp.universes true



-- TODO: Add identity type constructor.



class HasTypeFun {U V UtV : Universe} [HasFunctors {U} {V} UtV] [HasIdentity {V}]
                 (T : U → V) extends
  IsFunctorial (A := ⌊U⌋) (B := ⌊V⌋) T

namespace HasTypeFun

  open HasCongrArg HasTypeIdentity

  variable {U V UtV : Universe} [HasFunctors {U} {V} UtV] (T : U → V)

  @[reducible] def typeFun [HasIdentity {V}] [h : HasTypeFun T] : ⌊U⌋ ⟶ ⌊V⌋ :=
  h.defFun

  variable [HasIdentity {U}] [HasTypeIdentity V] [h : HasTypeFun T] [HasCongrArg {U} {V}]

  def castInstTo  {A₁ A₂ : U} (E : ⸤A₁⸥ ≃ ⸤A₂⸥) (b : T A₁) : T A₂ :=
  castTo  (defCongrArg h.defFun E) b
  def castInstInv {A₁ A₂ : U} (E : ⸤A₁⸥ ≃ ⸤A₂⸥) (b : T A₂) : T A₁ :=
  castInv (defCongrArg h.defFun E) b

end HasTypeFun



class HasRightTypeFun {U V W VtW : Universe} [h : HasFunctors {V} {W} VtW] [HasIdentity {W}]
                      (T : U → V → W) extends
  IsRightFunctorial (A := ⌊U⌋) (B := ⌊V⌋) (C := ⌊W⌋) T

namespace HasRightTypeFun

  open HasCongrArg HasTypeIdentity

  variable {U V W VtW : Universe} [HasFunctors {V} {W} VtW] (T : U → V → W)

  @[reducible] def typeFun [HasIdentity {W}] [h : HasRightTypeFun T] (A : U) : ⌊V⌋ ⟶ ⌊W⌋ :=
  h.defRightFun A

  variable [HasIdentity {V}] [HasTypeIdentity W] [h : HasRightTypeFun T] [HasCongrArg {V} {W}]

  def castInstTo  {A : U} {B₁ B₂ : V} (E : ⸤B₁⸥ ≃ ⸤B₂⸥) (c : T A B₁) : T A B₂ :=
  castTo  (defCongrArg (h.defRightFun A) E) c
  def castInstInv {A : U} {B₁ B₂ : V} (E : ⸤B₁⸥ ≃ ⸤B₂⸥) (c : T A B₂) : T A B₁ :=
  castInv (defCongrArg (h.defRightFun A) E) c

end HasRightTypeFun

class HasLeftTypeFun {U V W UtW : Universe} [HasFunctors {U} {W} UtW] [HasIdentity {W}]
                     (T : U → V → W) extends
  IsLeftFunctorial (A := ⌊U⌋) (B := ⌊V⌋) (C := ⌊W⌋) T

namespace HasLeftTypeFun

  open HasCongrArg HasTypeIdentity

  variable {U V W UtW : Universe} [HasFunctors {U} {W} UtW] (T : U → V → W)

  @[reducible] def revTypeFun [HasIdentity {W}] [h : HasLeftTypeFun T] (B : V) : ⌊U⌋ ⟶ ⌊W⌋ :=
  h.defLeftFun B

  variable [HasIdentity {U}] [HasTypeIdentity W] [h : HasLeftTypeFun T] [HasCongrArg {U} {W}]

  def castInstTo  {A₁ A₂ : U} {B : V} (E : ⸤A₁⸥ ≃ ⸤A₂⸥) (c : T A₁ B) : T A₂ B :=
  castTo  (defCongrArg (h.defLeftFun B) E) c
  def castInstInv {A₁ A₂ : U} {B : V} (E : ⸤A₁⸥ ≃ ⸤A₂⸥) (c : T A₂ B) : T A₁ B :=
  castInv (defCongrArg (h.defLeftFun B) E) c

end HasLeftTypeFun

class HasTypeBiFun {U V W VtW UtVtW : Universe} [HasFunctors {V} {W} VtW]
                   [HasFunctors {U} VtW UtVtW] [HasIdentity {W}] [HasIdentity VtW]
                   (T : U → V → W) extends
  IsBiFunctorial (A := ⌊U⌋) (B := ⌊V⌋) (C := ⌊W⌋) T

namespace HasTypeBiFun

  open HasCongrFun HasSwapFunFun

  variable {U V W VtW UtVtW : Universe} [HasFunctors {V} {W} VtW] [HasFunctors {U} VtW UtVtW]
           [HasIdentity {W}] [HasIdentity VtW] (T : U → V → W) [h : HasTypeBiFun T]

  instance hasRightTypeFun : HasRightTypeFun T := ⟨⟩

  @[reducible] def typeFunFun : ⌊U⌋ ⟶ ⌊V⌋ ⟶ ⌊W⌋ := IsBiFunctorial.rightFunFun T

  variable {UtW : Universe} [HasFunctors {U} {W} UtW] [HasCongrFun {V} {W}]

  instance hasLeftTypeFun [HasSwapFun {U} {V} {W}] : HasLeftTypeFun T := ⟨⟩

  def defRevTypeFunFun {VUtW : Universe} [HasFunctors {V} UtW VUtW] [HasIdentity UtW]
                       [HasSwapFunFun {U} {V} {W}] :
    ⌊V⌋ ⟶{λ B => (hasLeftTypeFun T).defLeftFun B} (⌊U⌋ ⟶ ⌊W⌋) :=
  defSwapFunFun (typeFunFun T)

  @[reducible] def revTypeFunFun {VUtW : Universe} [HasFunctors {V} UtW VUtW] [HasIdentity UtW]
                                 [HasSwapFunFun {U} {V} {W}] :
    ⌊V⌋ ⟶ ⌊U⌋ ⟶ ⌊W⌋ :=
  defRevTypeFunFun T

end HasTypeBiFun



-- TODO: move
--namespace HasTypeIdentity
--
--  variable (U V : Universe) [HasTypeIdentity U] [HasTypeIdentity V]
--
--  instance hasTypeFunctors : HasFunctors {U} {V} sort :=
--  { Fun   := sorry,
--    apply := sorry }
--
--end HasTypeIdentity
--
--namespace HasFunctors
--
--  variable (U V : Universe) {UV VtUV : Universe} [h : HasFunctors U V UV]
--           [HasTypeIdentity V] [HasTypeIdentity UV]
--
--  instance hasRightTypeFun : HasRightTypeFun h.Fun := sorry
--
--  instance hasRightTypeCongrArg : HasCongrArg {V} {UV} := sorry
--
--end HasFunctors
