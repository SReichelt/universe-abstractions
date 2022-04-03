/-
A universe of bundled sets, defined in such a way that the type of instances of a bundled set is
the corresponding subtype.
This is mostly a toy universe, probably with few practical applications. What makes it interesting
is that all operations really happen on the base type, e.g. the set of functors between two bundled
sets is defined as a subset of the type of functions between the base types. In this sense, all
operations are automatically extended to the entire base type, even though this is invisible from
within the universe.
-/



import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.FunctorExtensionality
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences
import UniverseAbstractions.Instances.Utils.Trivial

import UniverseAbstractions.MathlibFragments.Init.Set
import UniverseAbstractions.MathlibFragments.Data.Equiv.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w w'



structure BundledSet where
{α : Type u}
(s : Set α)

namespace BundledSet

  open MetaRelation HasFunctors HasCongrArg HasLinearFunOp

  instance : HasInstances.{u + 1, u + 2} BundledSet.{u} := ⟨λ A => Subtype A.s⟩
  def univ : Universe.{u + 1, u + 2} := ⟨BundledSet.{u}⟩

  -- Instance equivalences

  -- For convenience, we compare the values instead of the subtype instances.
  instance hasEquivalenceRelation (A : univ.{u}) : HasEquivalenceRelation A prop :=
  ⟨MetaRelation.lift (nativeRelation (@Eq A.α)) Subtype.val⟩

  instance hasInstanceEquivalences : HasInstanceEquivalences univ.{u} prop :=
  ⟨hasEquivalenceRelation⟩

  -- Functors

  def IsFun {A B : univ} (f : A.α → B.α) := ∀ {a}, a ∈ A.s → f a ∈ B.s
  def funSet (A B : univ) : Set (A.α → B.α) := {f | IsFun f}
  def FunSet (A B : univ) := Subtype (funSet A B)
  def bundledFunSet (A B : univ) : BundledSet := ⟨funSet A B⟩

  def apply {A B : univ} (F : FunSet A B) (a : A) : B :=
  ⟨F.val a.val, F.property a.property⟩

  instance hasFunctors : HasFunctors univ.{u} univ.{v} univ.{max u v} :=
  { Fun   := bundledFunSet,
    apply := apply }

  def asFun {A B : univ} (F : FunSet A B) : A ⟶ B := F

  def defFun {A B : univ} (F : FunSet A B) {f : A → B}
             -- Work around Lean defeq problems.
             (h : ∀ a : A, F.val a.val = (f a).val := by intro; rfl) :
    A ⟶{f} B :=
  toDefFun' (asFun F) h

  instance hasCongrArg : HasCongrArg univ.{u} univ.{v} :=
  ⟨λ {_ _} F {_ _} h => _root_.congrArg F.val h⟩

  instance hasCongrFun : HasCongrFun univ.{u} univ.{v} :=
  ⟨λ h a => _root_.congrFun h a.val⟩

  instance hasInternalFunctors : HasInternalFunctors univ.{u} := ⟨⟩

  instance hasIdFun : HasIdFun univ.{u} := ⟨λ A => defFun ⟨id, id⟩⟩

  instance hasConstFun : HasConstFun univ.{u} univ.{v} :=
  ⟨λ A {B} b => defFun ⟨Function.const A.α b.val, λ _ => b.property⟩⟩

  instance hasRevAppFun : HasRevAppFun univ.{u} :=
  ⟨λ {A} a B => defFun (A := A ⟶ B) ⟨λ f => f a.val, λ h => h a.property⟩⟩

  instance hasCompFun : HasCompFun univ.{u} univ.{v} univ.{w} :=
  ⟨λ F G => defFun ⟨G.val ∘ F.val, G.property ∘ F.property⟩⟩

  instance hasCompFunFun : HasCompFunFun univ.{u} univ.{v} :=
  ⟨λ {A B} F C => defFun (A := B ⟶ C) (B := A ⟶ C)
                         ⟨λ g => g ∘ F.val, λ h => h ∘ F.property⟩⟩

  instance hasRevCompFunFun : HasRevCompFunFun univ.{u} univ.{v} :=
  ⟨λ A {B C} G => defFun (A := A ⟶ B) (B := A ⟶ C)
                         ⟨λ f => G.val ∘ f, λ h => G.property ∘ h⟩⟩

  instance hasSwapFun : HasSwapFun univ.{u} univ.{v} univ.{w} :=
  ⟨λ F b => defFun ⟨λ a => F.val a b.val, λ h => F.property h b.property⟩⟩

  instance hasSwapFunFun : HasSwapFunFun univ.{u} univ.{v} univ.{w} :=
  ⟨λ {A B C} F => defFun (A := B) (B := A ⟶ C)
                         ⟨λ b a => F.val a b, λ {b} hb {a} ha => F.property ha hb⟩⟩

  instance hasDupFun : HasDupFun univ.{u} univ.{v} :=
  ⟨λ F => defFun ⟨λ a => F.val a a, λ h => F.property h h⟩⟩

  instance hasSubstFun : HasSubstFun univ.{u} univ.{v} univ.{w} :=
  ⟨λ F G => defFun ⟨λ a => G.val a (F.val a), λ h => G.property h (F.property h)⟩⟩

  instance hasBiCompFun : HasBiCompFun univ.{u} univ.{v} univ.{w} univ.{w'} :=
  ⟨λ F G H => defFun ⟨λ a => H.val (F.val a) (G.val a),
                      λ h => H.property (F.property h) (G.property h)⟩⟩

  instance hasRevBiCompFunFun : HasRevBiCompFunFun univ.{u} univ.{v} univ.{w'} :=
  ⟨λ {A B C D} H F => defFun (A := A ⟶ C) (B := A ⟶ D)
                             ⟨λ g a => H.val (F.val a) (g a),
                              λ {g} hg {a} ha => H.property (F.property ha) (hg ha)⟩⟩

  instance hasRevBiCompFunFunFun : HasRevBiCompFunFunFun univ.{u} univ.{w'} :=
  ⟨λ A {B C D} H => defFun (A := A ⟶ B) (B := (A ⟶ C) ⟶ (A ⟶ D))
                           ⟨λ f g a => H.val (f a) (g a),
                            λ {f} hf {g} hg {a} ha => H.property (hf ha) (hg ha)⟩⟩

  instance hasLinearFunOp : HasLinearFunOp univ.{u} :=
  { defIdFun     := λ A     => defFun ⟨id, id⟩,
    defRevAppFun := λ A B   => ⟨λ a => defFun (A := A ⟶ B) ⟨λ f => f a.val, λ h => h a.property⟩,
                                defFun (A := A) (B := (A ⟶ B) ⟶ B)
                                       ⟨λ a f => f a, λ {a} ha {f} hf => hf ha⟩⟩,
    defCompFun   := λ A B C => ⟨λ F => ⟨λ G => defFun ⟨G.val ∘ F.val, G.property ∘ F.property⟩,
                                        defFun (A := B ⟶ C) (B := A ⟶ C)
                                               ⟨λ g => g ∘ F.val, λ h => h ∘ F.property⟩⟩,
                                defFun (A := A ⟶ B) (B := (B ⟶ C) ⟶ (A ⟶ C))
                                       ⟨λ f g => g ∘ f, λ {f} hf {g} hg => hg ∘ hf⟩⟩ }

  instance hasAffineFunOp : HasAffineFunOp univ.{u} :=
  { defConstFun := λ A B => ⟨λ b => defFun ⟨Function.const A.α b.val, λ _ => b.property⟩,
                             defFun (A := B) (B := A ⟶ B)
                                    ⟨λ b _ => b, λ {b} hb {_} _ => hb⟩⟩ }

  instance hasFullFunOp : HasFullFunOp univ.{u} :=
  { defDupFun := λ A B => ⟨λ F => defFun ⟨λ a => F.val a a, λ h => F.property h h⟩,
                           defFun (A := A ⟶ A ⟶ B) (B := A ⟶ B)
                                  ⟨λ f a => f a a, λ {f} hf {a} ha => hf ha ha⟩⟩ }

  -- Functor extensionality does not hold trivially because two functors to be equivalent if their
  -- corresponding functions are equal, and those have domains that are larger than the designated
  -- set. However, since the functors we defined above just map everything in the usual way, the
  -- extensionality axioms hold by `rfl`.

  instance hasLinearFunExt : HasLinearFunOp.HasLinearFunExt univ.{u} :=
  { rightId              := λ _         => rfl,
    rightIdExt           := λ _ _       => rfl,
    leftId               := λ _         => rfl,
    leftIdExt            := λ _ _       => rfl,
    swapRevApp           := λ _         => rfl,
    swapRevAppExt        := λ _ _       => rfl,
    swapCompFun          := λ _ _ _     => rfl,
    swapCompFunExt       := λ _ _       => rfl,
    swapCompFunExtExt    := λ _ _ _     => rfl,
    swapRevCompFun       := λ _ _       => rfl,
    swapRevCompFunExt    := λ _ {_ _} _ => rfl,
    swapRevCompFunExtExt := λ _ _ _     => rfl,
    compAssoc            := λ _ _ _     => rfl,
    compAssocExt         := λ _ _ _     => rfl,
    compAssocExtExt      := λ _ _ _     => rfl,
    compAssocExtExtExt   := λ _ _ _ _   => rfl }

  instance hasAffineFunExt : HasAffineFunOp.HasAffineFunExt univ.{u} :=
  { rightConst       := λ _ {_ _} _ _ => rfl,
    rightConstExt    := λ _ {_} _ _   => rfl,
    rightConstExtExt := λ _ _ _       => rfl,
    leftConst        := λ _ _         => rfl,
    leftConstExt     := λ _ _         => rfl,
    leftConstExtExt  := λ _ _ _       => rfl }

  instance hasFullFunExt : HasFullFunOp.HasFullFunExt univ.{u} :=
  { dupSwap        := λ _     => rfl,
    dupSwapExt     := λ _ _   => rfl,
    dupConst       := λ _     => rfl,
    dupConstExt    := λ _ _   => rfl,
    rightDup       := λ _ _   => rfl,
    rightDupExt    := λ _ _   => rfl,
    rightDupExtExt := λ _ _ _ => rfl,
    substDup       := λ _ _   => rfl,
    substDupExt    := λ _ _   => rfl,
    substDupExtExt := λ _ _ _ => rfl }

  instance hasStandardFunctors : HasStandardFunctors univ.{u} := ⟨⟩

  -- Singletons

  def unitSet : BundledSet.{u} :=
  { α := PUnit,
    s := Set.univ }

  instance hasTopInstance : HasTop univ.{u} :=
  { T := unitSet,
    t := ⟨PUnit.unit, trivial⟩ }

  instance hasTopEq : HasTop.HasTopEq univ.{u} := ⟨λ _ => rfl⟩

  instance hasInternalTop : HasInternalTop univ.{u} :=
  { defElimFun := λ a => defFun ⟨λ _ => a.val, λ _ => a.property⟩ }

  instance hasTopExt : HasInternalTop.HasTopExt univ.{u} :=
  { elimFunEq := λ h => funext (λ _ => h) }

  def emptySet : BundledSet.{u} :=
  { α := PEmpty,
    s := ∅ }

  instance hasBotInstance : HasBot univ.{u} :=
  { B    := emptySet,
    elim := λ e => PEmpty.elim e.val }

  instance hasInternalBot : HasInternalBot univ.{u} :=
  { defElimFun := λ A => defFun (A := HasBot.Bot univ)
                                ⟨PEmpty.elim, λ {e} _ => PEmpty.elim e⟩
                                (h := λ e => PEmpty.elim e.val) }

  -- Products

  def prodSet (A : univ.{u}) (B : univ.{v}) : BundledSet.{max u v} :=
  { α := PProd A.α B.α,
    s := {p | p.fst ∈ A.s ∧ p.snd ∈ B.s} }

  instance hasProducts : HasProducts univ.{u} univ.{v} univ.{max u v} :=
  { Prod  := prodSet,
    intro := λ a b => ⟨⟨a.val, b.val⟩, ⟨a.property, b.property⟩⟩,
    fst   := λ P   => ⟨P.val.fst, P.property.left⟩,
    snd   := λ P   => ⟨P.val.snd, P.property.right⟩ }

  instance hasProductEq : HasProducts.HasProductEq univ.{u} univ.{v} :=
  { introEq := λ _   => rfl,
    fstEq   := λ _ _ => rfl,
    sndEq   := λ _ _ => rfl }

  instance hasInternalProducts : HasInternalProducts univ.{u} :=
  { defIntroFun    := λ A B   => ⟨λ a => defFun (B := A ⊓ B)
                                                ⟨λ b => ⟨a.val, b⟩, λ h => And.intro a.property h⟩,
                                  defFun (B := B ⟶ A ⊓ B)
                                         ⟨λ a b => ⟨a, b⟩, λ {a} ha {b} hb => ⟨ha, hb⟩⟩⟩,
    defElimFun     := λ A B C => ⟨λ F => defFun (A := A ⊓ B)
                                                ⟨λ p => F.val p.fst p.snd, λ h => F.property h.left h.right⟩,
                                  defFun (A := A ⟶ B ⟶ C) (B := A ⊓ B ⟶ C)
                                         ⟨λ f p => f p.fst p.snd, λ {f} hf {p} hp => hf hp.left hp.right⟩⟩ }

  instance hasProductExt : HasInternalProducts.HasProductExt univ.{u} :=
  { introEqExt      := λ _ _   => rfl,
    elimEqExt       := λ _ _   => rfl,
    elimEqExtExt    := λ _     => rfl,
    elimEqExtExtExt := λ _ _ _ => rfl }

  -- Equivalences

  def equivSet (A : univ.{u}) (B : univ.{v}) : BundledSet.{max u v} :=
  { α := A.α ≃ B.α,
    s := {e | IsFun e.toFun ∧ IsFun e.invFun} }

  instance hasEquivalences : HasEquivalences univ.{u} univ.{v} univ.{max u v} :=
  { Equiv := equivSet,
    desc  := λ E => { toFun  := ⟨E.val.toFun,  E.property.left⟩,
                      invFun := ⟨E.val.invFun, E.property.right⟩,
                      left   := ⟨λ a => E.val.leftInv  a.val⟩,
                      right  := ⟨λ b => E.val.rightInv b.val⟩ } }

  def defEquiv {A : univ.{u}} {B : univ.{v}} {e : A ⮂ B}
               (leftInv  : ∀ a : A.α, e.invFun.val (e.toFun.val a) = a)
               (rightInv : ∀ b : B.α, e.toFun.val (e.invFun.val b) = b) :
    A ⟷{e} B :=
  { E        := ⟨⟨e.toFun.val, e.invFun.val, leftInv, rightInv⟩,
                 ⟨e.toFun.property, e.invFun.property⟩⟩,
    toFunEq  := rfl,
    invFunEq := rfl }

  instance hasInternalEquivalences : HasInternalEquivalences univ.{u} :=
  { defToFunFun := λ A B => defFun (A := A ⟷ B) (B := A ⟶ B) ⟨Equiv.toFun, And.left⟩,
    isExt       := λ E => { leftExt  := ⟨funext E.val.leftInv⟩,
                            rightExt := ⟨funext E.val.rightInv⟩ },
    toFunInj    := Equiv.inj }

  instance hasEquivOp : HasEquivOp univ.{u} :=
  { defRefl  := λ A   => defEquiv (λ _ => rfl) (λ _ => rfl),
    defSymm  := λ E   => defEquiv E.val.rightInv E.val.leftInv,
    defTrans := λ E F => defEquiv (Equiv.trans_leftInv  E.val F.val)
                                  (Equiv.trans_rightInv E.val F.val) }

  instance hasTypeIdentity : HasTypeIdentity univ.{u} := ⟨⟩

end BundledSet
