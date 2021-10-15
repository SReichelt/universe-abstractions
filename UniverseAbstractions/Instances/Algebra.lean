import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Singletons
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences
import UniverseAbstractions.Instances.Utils.Bundled



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v



-- TODO: Use a universe as the base, to make everything stackable.

class CommSemigroup (α : Type u) where
(op                   : α → α → α)
(op_assoc (a b c : α) : op (op a b) c = op a (op b c))
(op_comm  (a b   : α) : op a b = op b a)

namespace CommSemigroup

  open Bundled

  @[reducible] def univ : Universe := Bundled.univ CommSemigroup

  instance inst (A : univ) : CommSemigroup ⌈A⌉ := Bundled.inst A

  instance hasIdentity' : HasIdentity' univ prop := sorry

  class IsHom {A B : univ} (f : A → B) : Prop where
  (h_op (a b : A) : f (op a b) = op (f a) (f b))

  instance hasFunctoriality : HasFunctoriality CommSemigroup.{u} CommSemigroup.{v} prop := ⟨IsHom⟩

  @[simp] theorem simp_op_arg' {A B : univ} (F : A ⟶' B) (a₁ a₂ : A) :
    F.f ((inst A).op a₁ a₂) = (inst B).op (F.f a₁) (F.f a₂) :=
  F.isFun.h_op a₁ a₂

  theorem funExt' {A B : univ} {F G : A ⟶' B} (h : ∀ a, F.f a = G.f a) : F = G :=
  have h₁ : F.f = G.f := funext h;
  by induction F; induction G; subst h₁; simp

  instance hasFunctorInstances : HasFunctorInstances CommSemigroup :=
  ⟨λ A B => { op       := λ F G   => ⟨λ a => (inst B).op (F.f a) (G.f a),
                                      ⟨λ a₁ a₂ => by simp;
                                                     rw [op_assoc, op_assoc];
                                                     apply congrArg;
                                                     rw [←op_assoc, ←op_assoc];
                                                     apply congrFun;
                                                     apply congrArg;
                                                     rw [op_comm]⟩⟩,
              op_assoc := λ F G H => funExt' λ a => (inst B).op_assoc (F.f a) (G.f a) (H.f a),
              op_comm  := λ F G   => funExt' λ a => (inst B).op_comm (F.f a) (G.f a) }⟩

  instance hasFunctors : HasFunctors univ univ univ := Bundled.hasFunctors CommSemigroup

  instance hasCongrArg : HasCongrArg univ univ := sorry

  instance hasInternalFunctors : HasInternalFunctors univ := ⟨⟩

  @[simp] theorem simp_op_arg {A B : univ} (F : A ⟶ B) (a₁ a₂ : A) : F (op a₁ a₂) = op (F a₁) (F a₂) :=
  simp_op_arg' F a₁ a₂

  @[simp] theorem simp_op_fun {A B : univ} (F G : A ⟶ B) (a : A) : (op F G) a = op (F a) (G a) :=
  rfl

  theorem funExt {A B : univ} {F G : A ⟶ B} (h : ∀ a, F a = G a) : F = G :=
  funExt' h

  instance hasLinearFunOp : HasLinearFunOp univ :=
  { defIdFun         := λ A     => defFun ⟨λ a₁ a₂ => rfl⟩,
    defAppFun        := λ a B   => defFun ⟨λ F₁ F₂ => rfl⟩,
    defAppFunFun     := λ A B   => defFun ⟨λ a₁ a₂ => funExt λ F => by simp⟩,
    defCompFun       := λ F G   => defFun ⟨λ a₁ a₂ => by simp⟩,
    defCompFunFun    := λ F C   => defFun ⟨λ G₁ G₂ => funExt λ a => by simp⟩,
    defCompFunFunFun := λ A B C => defFun ⟨λ F₁ F₂ => funExt λ G => funExt λ a => by simp⟩ }

end CommSemigroup
