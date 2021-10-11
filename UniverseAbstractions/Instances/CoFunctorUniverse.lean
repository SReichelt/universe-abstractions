import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.FunctorExtensionality
import UniverseAbstractions.Lemmas.DerivedFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w wv iu iv



def coFunctorUniverse {U : Universe.{u}} (A : U) (V : Universe.{v}) {VU : Universe.{v}} [HasFunctors V U VU] :
  Universe.{v} :=
{ A    := ⌈V⌉,
  inst := ⟨λ B => ⌈B ⟶ A⌉⟩ }

namespace coFunctorUniverse

  open HasCongrArg HasLinearFunOp HasSubLinearFunOp HasAffineFunOp HasNonLinearFunOp HasFullFunOp
       HasLinearFunExt HasAffineFunExt HasFullFunExt

  notation:20 V:21 " {⟶ " A:0 "}" => coFunctorUniverse A V

  def type {U : Universe.{u}} {V VU : Universe.{v}} [HasFunctors V U VU] (B : V) (A : U) : V {⟶ A} := B
  infixr:20 " ⟶! " => coFunctorUniverse.type

  def inst {U : Universe.{u}} {V VU : Universe.{v}} [HasFunctors V U VU] {B : V} {A : U} (F : B ⟶ A) : B ⟶! A := F

  instance hasIdentity' {U : Universe.{u}} (A : U) (V : Universe.{v}) {VU : Universe.{v}} [HasFunctors V U VU]
                        (IVU : Universe.{iv}) [h : HasIdentity'.{v, iv} VU IVU] :
    HasIdentity'.{v, iv} (V {⟶ A}) IVU :=
  ⟨λ (B : V) => h.Eq (B ⟶ A)⟩

  def idInst {U : Universe.{u}} (A : U) {UU : Universe.{u}} [HasFunctors U U UU] [HasIdentity.{u, iu} U]
             [HasIdFun U] :
    A ⟶! A :=
  HasIdFun.idFun A

  section Linear

    instance hasIndependentFunctors {U : Universe.{u}} (A : U) (V : Universe.{v}) (W : Universe.{w})
                                    {VU : Universe.{v}} {WU : Universe.{w}} {WV : Universe.{wv}}
                                    [HasFunctors V U VU] [HasFunctors W U WU] [h : HasFunctors W V WV]
                                    [HasIdentity.{u, iu} U] [HasCompFun W V U] :
      HasFunctors (V {⟶ A}) (W {⟶ A}) WV :=
    { Fun   := λ B C => h.Fun C B,
      apply := λ G F => F ⊙ G }

    def independentFunctor {U : Universe.{u}} (A : U) {V : Universe.{v}} {W : Universe.{w}}
                           {VU : Universe.{v}} {WU : Universe.{w}} {WV : Universe.{wv}}
                           [HasFunctors V U VU] [HasFunctors W U WU] [h : HasFunctors W V WV]
                           [HasIdentity.{u, iu} U] [HasCompFun W V U] {B : V} {C : W} (G : C ⟶ B) :
      (B ⟶! A) ⟶ (C ⟶! A) :=
    G

    variable {U : Universe.{u}} (A : U) [HasIdentity.{u, iu} U] [h : HasEmbeddedFunctors U]
             [HasLinearFunOp U]

    instance hasIndependentCongrArg : HasCongrArg (U {⟶ A}) (U {⟶ A}) :=
    ⟨λ {B C : U} (F : C ⟶ B) {G₁ G₂ : B ⟶ A} h => defCongrArg (defCompFunFun F A) h⟩

    variable [HasLinearFunExt U]

    instance hasIdFun : HasIdFun (U {⟶ A}) :=
    ⟨λ (B : U) => ⟨idFun B, λ (F : B ⟶ A) => rightId F⟩⟩

    instance hasIndependentCompFun : HasCompFun (U {⟶ A}) (U {⟶ A}) (U {⟶ A}) :=
    ⟨λ {B C D : U} (G : C ⟶ B) (H : D ⟶ C) => ⟨compFun H G, λ (F : B ⟶ A) => (compAssoc (U := U) H G F)⁻¹⟩⟩

  end Linear

end coFunctorUniverse
