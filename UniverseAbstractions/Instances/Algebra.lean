import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Singletons
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences
import UniverseAbstractions.Instances.Utils.Bundled
import UniverseAbstractions.Instances.Utils.Trivial

import UniverseAbstractions.MathlibFragments.Init.CoreExt



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v



-- TODO: Use a universe as the base, to make everything stackable, and to hopefully enable extension to vector spaces etc.

class CommSemigroup (α : Type u) : Type u where
(op                   : α → α → α)
(op_assoc (a b c : α) : op (op a b) c = op a (op b c))
(op_comm  (a b   : α) : op a b = op b a)

namespace CommSemigroup

  open MetaRelation Bundled

  @[reducible] def typeClass : SimpleTypeClass.{u + 1, u + 1} := CommSemigroup.{u}
  @[reducible] def univ : Universe.{u + 1, u + 2} := Bundled.univ typeClass.{u}

  instance inst (A : univ.{u}) : CommSemigroup.{u} A := A.inst

  -- Instance equivalences

  instance hasEquivalenceRelation (A : univ.{u}) : HasEquivalenceRelation A prop :=
  ⟨nativeRelation (@Eq A)⟩

  instance hasInstanceEquivalences : HasInstanceEquivalences univ.{u} prop :=
  ⟨hasEquivalenceRelation⟩

  -- Functors

  class IsHom {A B : univ} (f : A → B) : Prop where
  (h_op (a b : A) : f (op a b) = op (f a) (f b))

  instance hasFunctoriality : HasFunctoriality univ.{u} univ.{v} := ⟨IsHom⟩

  @[simp] theorem simp_op_arg' {A B : univ} (F : HasFunctoriality.Fun A B) (a₁ a₂ : A) :
    F.f ((inst A).op a₁ a₂) = (inst B).op (F.f a₁) (F.f a₂) :=
  F.isFun.h_op a₁ a₂

  theorem funExt' {A B : univ} {F G : HasFunctoriality.Fun A B} (h : ∀ a, F.f a = G.f a) : F = G :=
  have h₁ : F.f = G.f := funext h;
  by induction F; induction G; subst h₁; simp

  instance functorSemigroup (A B : univ) : CommSemigroup (HasFunctoriality.Fun A B) :=
  { op       := λ F G   => { f     := λ a => (inst B).op (F.f a) (G.f a),
                             isFun := ⟨λ a₁ a₂ => by simp;
                                                     rw [op_assoc, op_assoc];
                                                     apply congrArg;
                                                     rw [←op_assoc, ←op_assoc];
                                                     apply congrFun;
                                                     apply congrArg;
                                                     rw [op_comm]⟩ },
    op_assoc := λ F G H => funExt' λ a => (inst B).op_assoc (F.f a) (G.f a) (H.f a),
    op_comm  := λ F G   => funExt' λ a => (inst B).op_comm (F.f a) (G.f a) }

  instance hasFunctorialityInstances :
    HasFunctorialityInstances univ.{u} univ.{v} typeClass.{max u v} :=
  ⟨functorSemigroup⟩

  def defFun {A B : univ} {f : A → B} (isHom : IsHom f) : A ⟶{f} B :=
  Bundled.HasFunctorialityInstances.defFun isHom

  instance hasCongrArg : HasCongrArg univ.{u} univ.{v} :=
  ⟨λ F => congrArg F.f⟩

  instance hasInternalFunctors : HasInternalFunctors univ.{u} := ⟨⟩

  @[simp] theorem simp_op_arg {A B : univ} (F : A ⟶ B) (a₁ a₂ : A) : F (op a₁ a₂) = op (F a₁) (F a₂) :=
  simp_op_arg' F a₁ a₂

  @[simp] theorem simp_op_fun {A B : univ} (F G : A ⟶ B) (a : A) : (op F G) a = op (F a) (G a) :=
  rfl

  theorem funExt {A B : univ} {F G : A ⟶ B} (h : ∀ a, F a = G a) : F = G :=
  funExt' h

  -- TODO: Can we make everything `by simp` again?
  instance hasLinearFunOp : HasLinearFunOp univ.{u} :=
  { defIdFun         := λ A     => defFun ⟨λ a₁ a₂ => rfl⟩,
    defRevAppFun     := λ a B   => defFun ⟨λ F₁ F₂ => rfl⟩,
    defRevAppFunFun  := λ A B   => defFun ⟨λ a₁ a₂ => funExt λ F => simp_op_arg F a₁ a₂⟩,
    defCompFun       := λ F G   => defFun ⟨λ a₁ a₂ => by simp⟩,
    defCompFunFun    := λ F C   => defFun ⟨λ G₁ G₂ => funExt λ a => rfl⟩,
    defCompFunFunFun := λ A B C => defFun ⟨λ F₁ F₂ => funExt λ G => funExt λ a => simp_op_arg G (F₁ a) (F₂ a)⟩ }

  instance hasTrivialExtensionality : HasTrivialExtensionality univ.{u} univ.{v} := ⟨funExt⟩

  instance hasLinearFunctors : HasLinearFunctors univ.{u} := ⟨⟩

  -- Singletons

  instance unitSemigroup : CommSemigroup PUnit :=
  { op       := λ _ _   => PUnit.unit,
    op_assoc := λ _ _ _ => rfl,
    op_comm  := λ _ _   => rfl }

  instance hasTopInstance : HasTopInstance typeClass.{u} := ⟨unitSemigroup⟩

  instance hasTopEq : HasTop.HasTopEq univ.{u} := ⟨λ _ => rfl⟩

  instance emptySemigroup : CommSemigroup PEmpty :=
  { op       := λ a _   => PEmpty.elim a,
    op_assoc := λ a _ _ => PEmpty.elim a,
    op_comm  := λ a _   => PEmpty.elim a }

  instance hasBotInstance : HasBotInstance typeClass.{u} := ⟨emptySemigroup⟩

  instance hasInternalBot : HasInternalBot univ.{u} :=
  { defElimFun := λ A => defFun ⟨λ a _ => PEmpty.elim a⟩ }

  -- Products

  instance prodSemigroup (A : univ.{u}) (B : univ.{v}) : CommSemigroup (PProd A B) :=
  { op       := λ a b   => ⟨op a.fst b.fst, op a.snd b.snd⟩,
    op_assoc := λ a b c => PProd.ext' ⟨op_assoc a.fst b.fst c.fst, op_assoc a.snd b.snd c.snd⟩,
    op_comm  := λ a b   => PProd.ext' ⟨op_comm a.fst b.fst, op_comm a.snd b.snd⟩ }

  instance hasProductInstances : HasProductInstances univ.{u} univ.{v} typeClass.{max u v} :=
  ⟨prodSemigroup⟩

  instance hasProductEq : HasProducts.HasProductEq univ.{u} univ.{v} :=
  { introEq := λ _   => PProd.ext' ⟨rfl, rfl⟩,
    fstEq   := λ _ _ => rfl,
    sndEq   := λ _ _ => rfl }

end CommSemigroup
