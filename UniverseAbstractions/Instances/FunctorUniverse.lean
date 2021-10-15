import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.FunctorExtensionality
import UniverseAbstractions.Lemmas.DerivedFunctors
import UniverseAbstractions.Lemmas.DerivedFunctorExtensionality
import UniverseAbstractions.Instances.Utils.Direct



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w vw iu iv iw



def functorUniverse {U : Universe.{u}} (A : U) (V : Universe.{v}) {UV : Universe.{v}} [HasFunctors U V UV] :
  Universe.{v} :=
{ A    := ⌈V⌉,
  inst := ⟨λ B => ⌈A ⟶ B⌉⟩ }

namespace functorUniverse

  open MetaRelation HasFunctors HasCongrArg HasCongrFun HasEmbeddedFunctors
       HasLinearFunOp HasSubLinearFunOp HasAffineFunOp HasNonLinearFunOp HasFullFunOp
       HasLinearFunExt HasAffineFunExt HasFullFunExt

  notation:20 "{" A:0 " ⟶} " V:21 => functorUniverse A V

  def type {U : Universe.{u}} {V UV : Universe.{v}} [HasFunctors U V UV] (A : U) (B : V) : {A ⟶} V := B
  infixr:20 " !⟶ " => functorUniverse.type

  def inst {U : Universe.{u}} {V UV : Universe.{v}} [HasFunctors U V UV] {A : U} {B : V} (F : A ⟶ B) : A !⟶ B := F

  instance hasIdentity' {U : Universe.{u}} (A : U) (V : Universe.{v}) {UV : Universe.{v}} [HasFunctors U V UV]
                        (IUV : Universe.{iv}) [h : HasIdentity'.{v, iv} UV IUV] :
    HasIdentity'.{v, iv} ({A ⟶} V) IUV :=
  ⟨λ (B : V) => h.Eq (A ⟶ B)⟩

  def idInst {U : Universe.{u}} (A : U) {UU : Universe.{u}} [HasFunctors U U UU] [HasIdentity.{u, iu} U]
             [HasIdFun U] :
    A !⟶ A :=
  HasIdFun.idFun A

  def embed {U : Universe.{u}} (A : U) {V : Universe.{v}} {UV : Universe.{v}} [HasFunctors U V UV]
            [HasIdentity.{v, iv} V] [HasConstFun U V] {B : V} (b : B) :
    A !⟶ B :=
  HasConstFun.constFun A b

  -- Linear logic in `U` gives us:
  -- * "independent" functors that map values from `{A ⟶} V` to `{A ⟶} W` but do not depend on
  --   an instance of `A` themselves,
  -- * "dependent" functors in `{A ⟶} U` that map from `U` to `{A ⟶} U`.

  section Linear

    instance hasIndependentFunctors {U : Universe.{u}} (A : U) (V : Universe.{v}) (W : Universe.{w})
                                    {UV : Universe.{v}} {UW : Universe.{w}} {VW : Universe.{vw}}
                                    [HasFunctors U V UV] [HasFunctors U W UW] [h : HasFunctors V W VW]
                                    [HasIdentity.{w, iw} W] [HasCompFun U V W] :
      HasFunctors ({A ⟶} V) ({A ⟶} W) VW :=
    { Fun   := h.Fun,
      apply := λ G F => G ⊙ F }

    def independentFunctor {U : Universe.{u}} (A : U) {V : Universe.{v}} {W : Universe.{w}}
                           {UV : Universe.{v}} {UW : Universe.{w}} {VW : Universe.{vw}}
                           [HasFunctors U V UV] [HasFunctors U W UW] [h : HasFunctors V W VW]
                           [HasIdentity.{w, iw} W] [HasCompFun U V W] {B : V} {C : W} (G : B ⟶ C) :
      (A !⟶ B) ⟶ (A !⟶ C) :=
    G

    variable {U : Universe.{u}} (A : U) [HasIdentity.{u, iu} U] [h : HasEmbeddedFunctors U]
             [HasLinearFunOp U] [HasLinearFunExt U]

    instance hasIndependentCongrArg : HasCongrArg ({A ⟶} U) ({A ⟶} U) :=
    ⟨λ {B C : U} (G : B ⟶ C) {F₁ F₂ : A ⟶ B} h => defCongrArg (defRevCompFunFun A G) h⟩

    instance hasDependentFunctors : HasFunctors U ({A ⟶} U) ({A ⟶} U) :=
    { Fun   := h.Fun,
      apply := swapFun }

    def dependentFunctor {B C : U} (F : A !⟶ (B ⟶ C)) : B ⟶ (A !⟶ C) := F

    instance hasDependentCongrArg : HasCongrArg U ({A ⟶} U) :=
    ⟨λ {B C : U} (G : A ⟶ B ⟶ C) {b₁ b₂ : B} h => defCongrArg (defSwapFunFun G) h⟩

    variable [HasLinearFunExt U]

    def defInstFun (B : U) : (A ⟶ B) ⟶[λ F => inst F] (A !⟶ B) :=
    HasFunctors.toDefFun' (dependentFunctor A (appFunFun A B)) (λ F => swapApp F)

    @[reducible] def instFun (B : U) : (A ⟶ B) ⟶ (A !⟶ B) := defInstFun A B

    def independentIdFun (B : U) : B ⟶ B := idFun B
    def independentIdFun.eff (B : U) (F : A ⟶ B) :
      independentIdFun B • F ≃ F :=
    leftId F

    instance hasIdFun : HasIdFun ({A ⟶} U) :=
    ⟨λ (B : U) => ⟨independentIdFun B, independentIdFun.eff A B⟩⟩

    def independentCompFun {B C D : U} (G : B ⟶ C) (H : C ⟶ D) : B ⟶ D := H • G
    def independentCompFun.eff {B C D : U} (G : B ⟶ C) (H : C ⟶ D) (F : A ⟶ B) :
      independentCompFun G H • F ≃ H • (G • F) :=
    compAssoc F G H

    instance hasIndependentCompFun : HasCompFun ({A ⟶} U) ({A ⟶} U) ({A ⟶} U) :=
    ⟨λ G H => ⟨independentCompFun G H, independentCompFun.eff A G H⟩⟩

    def independentDependentCompFun {B C D : U} (G : B ⟶ C) (H : A ⟶ C ⟶ D) : A ⟶ B ⟶ D := compFunFun G D • H
    def independentDependentCompFun.eff {B C D : U} (G : B ⟶ C) (H : A ⟶ C ⟶ D) (b : B) :
      swapFun (independentDependentCompFun A G H) b ≃ swapFun H (G b) :=
    defCongrArg (defCompFunFun H D) (swapCompFun G b D) • swapComp H (compFunFun G D) b

    instance hasIndependentDependentCompFun : HasCompFun U U ({A ⟶} U) :=
    ⟨λ G H => ⟨independentDependentCompFun A G H, independentDependentCompFun.eff A G H⟩⟩

    def dependentIndependentCompFun {B C D : U} (G : A ⟶ B ⟶ C) (H : C ⟶ D) : A ⟶ B ⟶ D := revCompFunFun B H • G
    def dependentIndependentCompFun.eff {B C D : U} (G : A ⟶ B ⟶ C) (H : C ⟶ D) (b : B) :
      swapFun (dependentIndependentCompFun A G H) b ≃ H • swapFun G b :=
    compAssoc G (appFun b C) H •
    defCongrArg (defCompFunFun G D) (swapRevCompFun H b) •
    swapComp G (revCompFunFun B H) b

    instance hasDependentIndependentCompFun : HasCompFun U ({A ⟶} U) ({A ⟶} U) :=
    ⟨λ G H => ⟨dependentIndependentCompFun A G H, dependentIndependentCompFun.eff A G H⟩⟩

    section Affine

      variable [HasSubLinearFunOp U]

      instance : HasAffineFunOp U := ⟨⟩

      variable [HasAffineFunExt U]

      def defEmbedFun (B : U) : B ⟶[λ b => embed A b] (A !⟶ B) :=
      HasFunctors.toDefFun' (dependentFunctor A (constFun A (idFun B)))
                            (λ b => defCongrArg (defConstFunFun A B) byDef • swapConst A (idFun B) b)

      @[reducible] def embedFun (B : U) : B ⟶ (A !⟶ B) := defEmbedFun A B

      def dependentConstFun (B : U) {C : U} (F : A ⟶ C) : A ⟶ B ⟶ C := constFunFun B C • F
      def dependentConstFun.eff (B : U) {C : U} (F : A ⟶ C) (b : B) :
        swapFun (dependentConstFun A B F) b ≃ F :=
      leftId F • defCongrArg (defCompFunFun F C) (swapConstFun b C) • swapComp F (constFunFun B C) b

      instance hasDependentConstFun : HasConstFun U ({A ⟶} U) :=
      ⟨λ B {C} F => ⟨dependentConstFun A B F, dependentConstFun.eff A B F⟩⟩

    end Affine

  end Linear

  variable {U : Universe.{u}} (A : U) [HasIdentity.{u, iu} U] [h : HasStandardFunctors U]

  def embed.congrArg {B : U} {b₁ b₂ : B} (e : b₁ ≃ b₂) : embed A b₁ ≃ embed A b₂ :=
  defCongrArg (defConstFunFun A B) e

  instance hasFunctors : HasFunctors ({A ⟶} U) ({A ⟶} U) ({A ⟶} U) :=
  { Fun   := h.Fun,
    apply := revSubstFun }

  def toFunctor {B C : U} (F : A !⟶ (B ⟶ C)) : (A !⟶ B) ⟶ (A !⟶ C) := F

  def embedFunctor {B C : U} (G : B ⟶ C) : (A !⟶ B) ⟶ (A !⟶ C) := toFunctor A (embed A G)
  def embedFunctor.eff {B C : U} (G : B ⟶ C) (b : B) :
    (embedFunctor A G) (embed A b) ≃ embed A (G b) :=
  substConst A b G

  def embedIdInst {B : U} (F : A ⟶ B) : (embedFunctor A F) (idInst A) ≃ inst F :=
  rightId F • substConstFun (idFun A) F

  instance hasCongrArg : HasCongrArg ({A ⟶} U) ({A ⟶} U) :=
  ⟨λ {B C : U} (G : A ⟶ B ⟶ C) {F₁ F₂ : A ⟶ B} h => defCongrArg (defRevSubstFunFun G) h⟩

  instance hasEmbeddedFunctors : HasEmbeddedFunctors ({A ⟶} U) := ⟨⟩

  def baseIdFun (B : U) : A ⟶ B ⟶ B := embedFunctor A (idFun B)
  def baseIdFun.eff (B : U) (F : A ⟶ B) :
    substFun F (baseIdFun A B) ≃ F :=
  leftId F • substConstFun F (idFun B)

  def baseAppFun {B : U} (F : A ⟶ B) (C : U) : A ⟶ (B ⟶ C) ⟶ C := appFunFun B C • F
  def baseAppFun.eff {B : U} (F : A ⟶ B) (C : U) (G : A ⟶ B ⟶ C) :
    substFun G (baseAppFun A F C) ≃ substFun F G :=
  substApp F G

  def baseAppFunFun (B C : U) : A ⟶ B ⟶ (B ⟶ C) ⟶ C := embedFunctor A (appFunFun B C)
  def baseAppFunFun.eff (B C : U) (F : A ⟶ B) :
    substFun F (baseAppFunFun A B C) ≃ baseAppFun A F C :=
  substConstFun F (appFunFun B C)

  def baseCompFun {B C D : U} (G : A ⟶ B ⟶ C) (H : A ⟶ C ⟶ D) : A ⟶ B ⟶ D := substFun G (revCompFunFunFun B C D • H)
  def baseCompFun.eff {B C D : U} (G : A ⟶ B ⟶ C) (H : A ⟶ C ⟶ D) (F : A ⟶ B) :
    substFun F (baseCompFun A G H) ≃ substFun (substFun F G) H :=
  substAssoc F G H

  def baseCompFunFun {B C : U} (G : A ⟶ B ⟶ C) (D : U) : A ⟶ (C ⟶ D) ⟶ (B ⟶ D) := compFunFunFun B C D • G
  def baseCompFunFun.eff {B C : U} (G : A ⟶ B ⟶ C) (D : U) (H : A ⟶ C ⟶ D) :
    substFun H (baseCompFunFun A G D) ≃ baseCompFun A G H :=
  defCongrArg (defDupFunFun A (B ⟶ D))
              (compAssoc H (swapFunFun (compFunFunFun B C D)) (compFunFun G (B ⟶ D))) •
  dupSwap ((compFunFun G (B ⟶ D) • swapFunFun (compFunFunFun B C D)) • H) •
  defCongrArg (defDupFunFun A (B ⟶ D))
              (defCongrArg (defRevCompFunFun A (compFunFun H (B ⟶ D)))
                           (reverseSwap (swapCompExt G (compFunFunFun B C D))) •
               swapCompExt H (compFunFun G (B ⟶ D) • swapFunFun (compFunFunFun B C D)))⁻¹

  def baseCompFunFunFun (B C D : U) : A ⟶ (B ⟶ C) ⟶ (C ⟶ D) ⟶ (B ⟶ D) := embedFunctor A (compFunFunFun B C D)
  def baseCompFunFunFun.eff (B C D : U) (G : A ⟶ B ⟶ C) :
    substFun G (baseCompFunFunFun A B C D) ≃ baseCompFunFun A G D :=
  substConstFun G (compFunFunFun B C D)

  instance hasLinearFunOp : HasLinearFunOp ({A ⟶} U) :=
  { defIdFun         := λ B     => ⟨baseIdFun         A B,     baseIdFun.eff         A B⟩,
    defAppFun        := λ F C   => ⟨baseAppFun        A F C,   baseAppFun.eff        A F C⟩,
    defAppFunFun     := λ B C   => ⟨baseAppFunFun     A B C,   baseAppFunFun.eff     A B C⟩,
    defCompFun       := λ G H   => ⟨baseCompFun       A G H,   baseCompFun.eff       A G H⟩,
    defCompFunFun    := λ G D   => ⟨baseCompFunFun    A G D,   baseCompFunFun.eff    A G D⟩,
    defCompFunFunFun := λ B C D => ⟨baseCompFunFunFun A B C D, baseCompFunFunFun.eff A B C D⟩ }

  def baseConstFun (B : U) {C : U} (F : A ⟶ C) : A ⟶ B ⟶ C := constFunFun B C • F
  def baseConstFun.eff (B : U) {C : U} (F : A ⟶ C) (G : A ⟶ B) :
    substFun G (baseConstFun A B F) ≃ F :=
  dupConst F •
  dupSwap (constFun A F) •
  defCongrArg (defDupFunFun A C) ((swapConstExt A F)⁻¹ •
                                  defCongrArg (defCompFunFun F (A ⟶ C)) (leftConstExt G C) •
                                  (compAssoc F (constFunFun B C) (compFunFun G C))⁻¹)

  def baseConstFunFun (B C : U) : A ⟶ C ⟶ B ⟶ C := embedFunctor A (constFunFun B C)
  def baseConstFunFun.eff (B C : U) (F : A ⟶ C) :
    substFun F (baseConstFunFun A B C) ≃ baseConstFun A B F :=
  substConstFun F (constFunFun B C)

  instance hasAffineFunOp : HasAffineFunOp ({A ⟶} U) :=
  { defConstFun    := λ B {_} F => ⟨baseConstFun    A B F, baseConstFun.eff    A B F⟩,
    defConstFunFun := λ B C     => ⟨baseConstFunFun A B C, baseConstFunFun.eff A B C⟩ }

  def baseDupFun {B C : U} (G : A ⟶ B ⟶ B ⟶ C) : A ⟶ B ⟶ C := dupFunFun B C • G
  def baseDupFun.eff {B C : U} (G : A ⟶ B ⟶ B ⟶ C) (F : A ⟶ B) :
    substFun F (baseDupFun A G) ≃ substFun F (substFun F G) :=
  substDup F G

  def baseDupFunFun (B C : U) : A ⟶ (B ⟶ B ⟶ C) ⟶ (B ⟶ C) := embedFunctor A (dupFunFun B C)
  def baseDupFunFun.eff (B C : U) (G : A ⟶ B ⟶ B ⟶ C) :
    substFun G (baseDupFunFun A B C) ≃ baseDupFun A G :=
  substConstFun G (dupFunFun B C)

  instance hasFullFunOp : HasFullFunOp ({A ⟶} U) :=
  { defDupFun    := λ G   => ⟨baseDupFun    A G,   baseDupFun.eff    A G⟩,
    defDupFunFun := λ B C => ⟨baseDupFunFun A B C, baseDupFunFun.eff A B C⟩ }

  class HasSimpEmbed {B : U} (b : B) where
  (simpEmbed   : A !⟶ B)
  (simpEmbedEq : simpEmbed ≃ embed A b)

  namespace HasSimpEmbed

    instance (priority := low) refl {B : U} (b : B) : HasSimpEmbed A b :=
    { simpEmbed   := embed A b,
      simpEmbedEq := HasRefl.refl (embed A b) }

    instance funApp {B C : U} (G : B ⟶ C) (b : B) [hG : HasSimpEmbed A G] [hb : HasSimpEmbed A b] :
      HasSimpEmbed A (G b) :=
    { simpEmbed   := (toFunctor A hG.simpEmbed) hb.simpEmbed,
      simpEmbedEq := embedFunctor.eff A G b •
                     congrArg (embedFunctor A G) hb.simpEmbedEq •
                     HasCongrFun.congrFun (U := {A ⟶} U) (V := {A ⟶} U) hG.simpEmbedEq hb.simpEmbed }

    def byFunApp {B C : U} {F : A !⟶ C} [hF : IsFunApp (A !⟶ B) F] {c : C} [hc : IsFunApp B c]
                 [hcF : HasSimpEmbed A hc.F] [hca : HasSimpEmbed A hc.a]
                 (eF : hF.F ≃ toFunctor A hcF.simpEmbed) (ec : hF.a ≃ hca.simpEmbed) :
      F ≃ embed A c :=
    embed.congrArg A hc.e •
    (funApp A hc.F hc.a).simpEmbedEq •
    congrArg (toFunctor A hcF.simpEmbed) ec •
    congrFun eF hF.a •
    hF.e⁻¹

    instance embedAppFun {B C : U} {b : B} [hb : HasSimpEmbed A b] :
      HasSimpEmbed A (appFun b C) :=
    ⟨appFun (U := {A ⟶} U) hb.simpEmbed C,
     byFunApp A (HasRefl.refl _) hb.simpEmbedEq⟩

    instance embedCompFunFun {B C D : U} {G : B ⟶ C} [hG : HasSimpEmbed A G] :
      HasSimpEmbed A (compFunFun G D) :=
    ⟨compFunFun (U := {A ⟶} U) (toFunctor A hG.simpEmbed) D,
     byFunApp A (HasRefl.refl _) hG.simpEmbedEq⟩

    instance embedCompFun {B C D : U} {G : B ⟶ C} {H : C ⟶ D}
                          [hG : HasSimpEmbed A G] [hH : HasSimpEmbed A H] :
      HasSimpEmbed A (compFun G H) :=
    ⟨compFun (U := {A ⟶} U) (toFunctor A hG.simpEmbed) (toFunctor A hH.simpEmbed),
     byFunApp A (embedCompFunFun A).simpEmbedEq hH.simpEmbedEq⟩

    instance embedTrans {B C D : U} {G : B ⟶ C} {H : C ⟶ D}
                        [hG : HasSimpEmbed A G] [hH : HasSimpEmbed A H] :
      HasSimpEmbed A (H • G) :=
    embedCompFun A

    instance embedConstFun {B C : U} {c : C} [hc : HasSimpEmbed A c] :
      HasSimpEmbed A (constFun B c) :=
    ⟨constFun (U := {A ⟶} U) B hc.simpEmbed,
     byFunApp A (HasRefl.refl _) hc.simpEmbedEq⟩

    instance embedDupFun {B C : U} {G : B ⟶ B ⟶ C} [hG : HasSimpEmbed A G] :
      HasSimpEmbed A (dupFun G) :=
    ⟨dupFun (U := {A ⟶} U) (toFunctor A hG.simpEmbed),
     byFunApp A (HasRefl.refl _) hG.simpEmbedEq⟩

    instance embedSwapFun {B C D : U} {G : B ⟶ C ⟶ D} {c : C}
                          [hG : HasSimpEmbed A G] [hc : HasSimpEmbed A c] :
      HasSimpEmbed A (swapFun G c) :=
    embedTrans A

    instance embedSwapFunFun {B C D : U} {G : B ⟶ C ⟶ D} [hG : HasSimpEmbed A G] :
      HasSimpEmbed A (swapFunFun G) :=
    embedTrans A

    instance embedSwapFunFunFun {B C D : U} :
      HasSimpEmbed A (swapFunFunFun B C D) :=
    embedTrans A

    instance embedRevCompFunFun {B C D : U} {G : C ⟶ D} [hG : HasSimpEmbed A G] :
      HasSimpEmbed A (revCompFunFun B G) :=
    embedSwapFun A

    instance embedRevCompFunFunFun {B C D : U} :
      HasSimpEmbed A (revCompFunFunFun B C D) :=
    embedSwapFunFun A

    instance embedSubstFun {B C D : U} {G : B ⟶ C} {H : B ⟶ C ⟶ D}
                           [hG : HasSimpEmbed A G] [hH : HasSimpEmbed A H] :
      HasSimpEmbed A (substFun G H) :=
    embedDupFun A

    instance embedSubstFunFun {B C D : U} {G : B ⟶ C} [hG : HasSimpEmbed A G] :
      HasSimpEmbed A (substFunFun G D) :=
    embedTrans A

    instance embedSubstFunFunFun {B C D : U} :
      HasSimpEmbed A (substFunFunFun B C D) :=
    embedTrans A

    def bySimp {B : U} {b₁ b₂ : B} [hb₁ : HasSimpEmbed A b₁] [hb₂ : HasSimpEmbed A b₂]
               (e : b₁ ≃ b₂) :
      hb₁.simpEmbed ≃ hb₂.simpEmbed :=
    hb₂.simpEmbedEq⁻¹ • embed.congrArg A e • hb₁.simpEmbedEq

  end HasSimpEmbed

  instance hasDirectLinearFunExt : HasDirectLinearFunExt ({A ⟶} U) :=
  { rightId        := λ B C     : U => HasSimpEmbed.bySimp A (rightIdExt B C),
    leftId         := λ B C     : U => HasSimpEmbed.bySimp A (leftIdExt B C),
    swapApp        := λ B C     : U => HasSimpEmbed.bySimp A (swapAppExt B C),
    swapCompFun    := λ B C D   : U => HasSimpEmbed.bySimp A (swapCompFunExtExt B C D),
    swapRevCompFun := λ B C D   : U => HasSimpEmbed.bySimp A (swapRevCompFunExtExt B C D),
    compAssoc      := λ B C D E : U => HasSimpEmbed.bySimp A (compAssocExtExtExt B C D E) }

  instance hasDirectSubLinearFunExt : HasDirectSubLinearFunExt ({A ⟶} U) :=
  { rightConst := λ B C D : U => HasSimpEmbed.bySimp A (rightConstExtExt B C D),
    leftConst  := λ B C D : U => HasSimpEmbed.bySimp A (leftConstExtExt B C D) }

  instance hasDirectNonLinearFunExt : HasDirectNonLinearFunExt ({A ⟶} U) :=
  { dupSwap  := λ B C   : U => HasSimpEmbed.bySimp A (dupSwapExt B C),
    dupConst := λ B C   : U => HasSimpEmbed.bySimp A (dupConstExt B C),
    dupDup   := λ B C   : U => HasSimpEmbed.bySimp A (dupDupExt B C),
    rightDup := λ B C D : U => HasSimpEmbed.bySimp A (rightDupExtExt B C D),
    substDup := λ B C D : U => HasSimpEmbed.bySimp A (substDupExtExt B C D) }

  instance hasStandardFunctors : HasStandardFunctors ({A ⟶} U) := ⟨⟩

end functorUniverse



inductive OptionalFunctorType {U : Universe.{u}} (A : U) (V : Universe.{v}) {UV : Universe.{v}} [HasFunctors U V UV] where
| const (B : V)
| fn (AB : {A ⟶} V)
| idFn
| empty

instance {U : Universe.{u}} (A : U) (V : Universe.{v}) {UV : Universe.{v}} [HasFunctors U V UV] :
  HasInstances.{v, v + 1} (OptionalFunctorType A V) :=
⟨λ β => match β with
        | OptionalFunctorType.const B => ⌈B⌉
        | OptionalFunctorType.fn AB   => ⌈AB⌉
        | OptionalFunctorType.idFn    => PUnit.{v}
        | OptionalFunctorType.empty   => PEmpty.{v}⟩

def optionalFunctorUniverse {U : Universe.{u}} (A : U) (V : Universe.{v}) {UV : Universe.{v}} [HasFunctors U V UV] :
  Universe.{v} :=
⟨OptionalFunctorType A V⟩

namespace optionalFunctorUniverse

  open OptionalFunctorType MetaRelation HasCongrArg HasLinearFunOp

  notation:20 "{" A:0 " ⟶}? " V:21 => optionalFunctorUniverse A V

  variable {U : Universe.{u}} (A : U) [HasIdentity.{u, iu} U] [h : HasEmbeddedFunctors U] [HasLinearFunOp U]

  instance hasIdentity' {U : Universe.{u}} (A : U) (V : Universe.{v}) {UV : Universe.{v}} [HasFunctors U V UV]
                        (IV : Universe.{iv}) [hConst : HasIdentity'.{v, iv} V IV]
                        [hFn : HasIdentity'.{v, iv} ({A ⟶} V) IV] :
    HasIdentity'.{v, iv} ({A ⟶}? V) IV :=
  ⟨λ β => match β with
          | const B => hConst.Eq B
          | fn AB   => hFn.Eq AB
          | idFn    => { R := unitRelation PUnit.{v} sorry, -- TODO: Require `IV` to have a unit type
                         h := sorry }
          | empty   => { R := unitRelation PEmpty.{v} sorry, -- TODO: Require `IV` to have a unit type
                         h := sorry }⟩

  -- TODO: This is noncomputable only due a technicality regarding `PEmpty.elim` that can hopefully be solved.
  noncomputable instance hasFunctors : HasFunctors ({A ⟶}? U) ({A ⟶}? U) ({A ⟶}? U) :=
  { Fun   := λ β γ => match β, γ with
                      | const B, const C => const (B ⟶ C)
                      | const B, fn AC   => fn (B ⟶ AC)
                      | fn AB,   fn AC   => const (AB ⟶ AC)
                      | idFn,    δ       => δ
                      | _,       _       => empty,
    apply := λ {β γ} => match β, γ with
                        | const B, const C => λ (G : B ⟶ C)   (b : B)  => G b
                        | const B, fn AC   => λ (G : B ⟶ AC)  (b : B)  => G b
                        | fn AB,   fn AC   => λ (G : AB ⟶ AC) (F : AB) => G F
                        | idFn,    _       => λ G _ => G
                        | const _, idFn    => PEmpty.elim
                        | fn _,    const _ => PEmpty.elim
                        | fn _,    idFn    => PEmpty.elim
                        | const _, empty   => PEmpty.elim
                        | fn _,    empty   => PEmpty.elim
                        | empty,   _       => PEmpty.elim }

  noncomputable instance hasCongrArg : HasCongrArg ({A ⟶}? U) ({A ⟶}? U) :=
  ⟨λ {β γ} => match β, γ with
              | const B, const C => λ (G : B ⟶ C)   {_ _} h => congrArg G h
              | const B, fn AC   => λ (G : B ⟶ AC)  {_ _} h => congrArg G h
              | fn AB,   fn AC   => λ (G : AB ⟶ AC) {_ _} h => congrArg G h
              | idFn,    _       => λ G {_ _} _ => HasRefl.refl G
              | const _, idFn    => λ G => PEmpty.elim G
              | fn _,    const _ => λ G => PEmpty.elim G
              | fn _,    idFn    => λ G => PEmpty.elim G
              | const _, empty   => λ G => PEmpty.elim G
              | fn _,    empty   => λ G => PEmpty.elim G
              | empty,   _       => λ G => PEmpty.elim G⟩

  noncomputable instance hasEmbeddedFunctors : HasEmbeddedFunctors ({A ⟶}? U) := ⟨⟩

end optionalFunctorUniverse
