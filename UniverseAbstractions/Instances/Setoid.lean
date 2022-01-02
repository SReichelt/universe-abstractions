import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.FunctorExtensionality
import UniverseAbstractions.Instances.Utils.Bundled
import UniverseAbstractions.Instances.Utils.Trivial



set_option autoBoundImplicitLocal false
-- TODO: This is only necessary due to importing `Trivial`; can it be fixed?
set_option synthInstance.maxHeartbeats 10000

universe u v w w'



namespace Setoid

  open Bundled MetaRelation HasFunctors HasCongrArg HasLinearFunOp

  def typeClass : SimpleTypeClass.{max 1 u, max 1 u} := Setoid.{max 1 u}
  @[reducible] def univ : Universe.{max 1 u, (max 1 u) + 1} := Bundled.univ typeClass.{u}

  instance inst (A : univ.{u}) : Setoid.{max 1 u} A := Bundled.inst A

  -- Instance equivalences

  instance hasEquivalenceRelation (A : univ.{u}) : HasEquivalenceRelation A prop :=
  ⟨nativeRelation (inst A).r⟩

  instance hasInstanceEquivalences : HasInstanceEquivalences univ.{u} prop :=
  ⟨hasEquivalenceRelation⟩

  -- Functors

  def IsFun {A B : univ} (f : A → B) : Prop :=
  ∀ {a₁ a₂ : A}, a₁ ≈ a₂ → f a₁ ≈ f a₂

  def IsFun₂ {A B C : univ} (f : A → B → C) : Prop :=
  ∀ {a₁ a₂ : A} {b₁ b₂ : B}, a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ ≈ f a₂ b₂

  instance hasFunctoriality : HasFunctoriality univ.{u} univ.{v} prop := ⟨IsFun⟩

  def FunEquiv {α : Sort u} {φ : α → univ} (f₁ f₂ : ∀ a, φ a) : Prop :=
  ∀ a, f₁ a ≈ f₂ a

  instance funSetoid (A : univ.{u}) (B : univ.{v}) : Setoid.{max 1 u v} (A ⟶' B) :=
  { r     := λ F₁ F₂ => FunEquiv F₁.f F₂.f,
    iseqv := { refl  := λ F   a => (inst B).refl  (F.f a),
               symm  := λ h   a => (inst B).symm  (h a),
               trans := λ h i a => (inst B).trans (h a) (i a) } }

  instance hasFunctorialityInstances :
    HasFunctorialityInstances univ.{u} univ.{v} typeClass.{max u v} :=
  ⟨funSetoid⟩

  def isFun₂ {A B C : univ} (F : A ⟶ B ⟶ C) : IsFun₂ (λ a b => F a b) :=
  λ {a₁ a₂ b₁ b₂} h₁ h₂ => Setoid.trans ((F.isFun h₁) b₁) ((F a₂).isFun h₂)

  def defFun {A B : univ} {f : A → B} (isFun : IsFun f) : A ⟶{f} B :=
  Bundled.HasFunctorialityInstances.defFun isFun

  def defFun₂ {A B C : univ} {f : A → B → C} (isFun : IsFun₂ f) :
    A ⟶{λ a => (defFun (isFun (Setoid.refl a)))} (B ⟶ C) :=
  defFun (λ h b => (isFun h) (Setoid.refl b))

  instance hasCongrArg : HasCongrArg univ.{u} univ.{v} := ⟨BundledFunctor.isFun⟩
  instance hasCongrFun : HasCongrFun univ.{u} univ.{v} := ⟨id⟩

  instance hasInternalFunctors : HasInternalFunctors univ.{u} := ⟨⟩

  instance hasIdFun : HasIdFun univ.{u} := ⟨λ A => defFun id⟩

  instance hasConstFun : HasConstFun univ.{u} univ.{v} :=
  ⟨λ A {B} b => defFun (λ a => Setoid.refl b)⟩

  instance hasRevAppFun : HasRevAppFun univ.{u} := ⟨λ a B => defFun (λ h => h a)⟩

  instance hasCompFun : HasCompFun univ.{u} univ.{v} univ.{w} :=
  ⟨λ F G => defFun (G.isFun ∘ F.isFun)⟩

  instance hasCompFunFun : HasCompFunFun univ.{u} univ.{v} :=
                                     -- Work around Lean defeq problem.
  ⟨λ F C => defFun (λ {G₁ G₂} h a => have h₁ : (G₁ ⊙ F).f a = G₁ (F a) := rfl;
                                     have h₂ : (G₂ ⊙ F).f a = G₂ (F a) := rfl;
                                     h₁ ▸ h₂ ▸ h (F a))⟩

  instance hasRevCompFunFun : HasRevCompFunFun univ.{u} univ.{v} :=
                                           -- Work around Lean defeq problem.
  ⟨λ A {B C} G => defFun (λ {F₁ F₂} h a => have h₁ : (G ⊙ F₁).f a = G (F₁ a) := rfl;
                                           have h₂ : (G ⊙ F₂).f a = G (F₂ a) := rfl;
                                           h₁ ▸ h₂ ▸ G.isFun (h a))⟩

  instance hasSwapFun : HasSwapFun univ.{u} univ.{v} univ.{w} :=
  ⟨λ F b => defFun (λ h => (F.isFun h) b)⟩

  instance hasSwapFunFun : HasSwapFunFun univ.{u} univ.{v} univ.{w} :=
                                   -- Work around Lean defeq problem.
  ⟨λ F => defFun (λ {b₁ b₂} h a => have h₁ : (HasSwapFun.swapFun F b₁).f a = F a b₁ := rfl; 
                                   have h₂ : (HasSwapFun.swapFun F b₂).f a = F a b₂ := rfl; 
                                   h₁ ▸ h₂ ▸ (F a).isFun h)⟩

  instance hasDupFun : HasDupFun univ.{u} univ.{v} :=
  ⟨λ F => defFun (λ h => isFun₂ F h h)⟩

  instance hasSubstFun : HasSubstFun univ.{u} univ.{v} univ.{w} :=
  ⟨λ F G => defFun (λ h => isFun₂ G h (F.isFun h))⟩

  instance hasBiCompFun : HasBiCompFun univ.{u} univ.{v} univ.{w} univ.{w'} :=
  ⟨λ F G H => defFun (λ h => isFun₂ H (F.isFun h) (G.isFun h))⟩

  instance hasRevBiCompFunFun : HasRevBiCompFunFun univ.{u} univ.{v} univ.{w'} :=
                                     -- Work around Lean defeq problem.
  ⟨λ H F => defFun (λ {G₁ G₂} h a => have h₁ : (HasBiCompFun.biCompFun F G₁ H).f a = H (F a) (G₁ a) := rfl;
                                     have h₂ : (HasBiCompFun.biCompFun F G₂ H).f a = H (F a) (G₂ a) := rfl;
                                     h₁ ▸ h₂ ▸ (H (F a)).isFun (h a))⟩

  instance hasRevBiCompFunFunFun : HasRevBiCompFunFunFun univ.{u} univ.{w'} :=
                                               -- Work around Lean defeq problem.
  ⟨λ A {B C D} H => defFun (λ {F₁ F₂} h G a => have h₁ : ((HasRevBiCompFunFun.revBiCompFunFun H F₁).f G).f a = H (F₁ a) (G a) := rfl;
                                               have h₂ : ((HasRevBiCompFunFun.revBiCompFunFun H F₂).f G).f a = H (F₂ a) (G a) := rfl;
                                               h₁ ▸ h₂ ▸ (H.isFun (h a)) (G a))⟩

  instance hasLinearFunOp : HasLinearFunOp univ.{u} :=
  { defRevAppFunFun  := λ A B   => defFun (λ h F => F.isFun h),
    defCompFunFunFun := λ A B C => defFun (λ h G a => G.isFun (h a)) }

  instance hasAffineFunOp : HasAffineFunOp univ.{u} :=
  { defConstFunFun := λ A B => defFun (λ h a => h) }

  instance hasFullFunOp : HasFullFunOp univ.{u} :=
  { defDupFunFun := λ A B => defFun (λ h a => h a a) }

  instance hasTrivialExtensionality : HasTrivialExtensionality univ.{u} univ.{v} := ⟨id⟩

  instance hasStandardFunctors : HasStandardFunctors univ.{u} := ⟨⟩

  -- Singletons

  instance unitSetoid : Setoid.{u} PUnit.{u} :=
  { r     := λ _ _ => True,
    iseqv := { refl  := λ _   => trivial,
               symm  := λ _   => trivial,
               trans := λ _ _ => trivial } }

  instance hasTopInstance : HasTopInstance typeClass.{u} := ⟨unitSetoid⟩

  instance hasTopEq : HasTop.HasTopEq univ.{u} := ⟨λ _ => trivial⟩

  instance hasInternalTop : HasInternalTop univ.{u} :=
  { defElimFun := λ a => defFun (λ _ => Setoid.refl a) }

  instance emptySetoid : Setoid.{u} PEmpty.{u} :=
  { r     := λ _ _ => False,
    iseqv := { refl  := PEmpty.elim,
               symm  := id,
               trans := Function.const False } }

  instance hasBotInstance : HasBotInstance typeClass.{u} := ⟨emptySetoid⟩

  instance hasInternalBot : HasInternalBot univ.{u} :=
  { defElimFun := λ A => defFun False.elim }

  -- Products

  instance prodSetoid (A : univ.{u}) (B : univ.{v}) : Setoid.{max 1 u v} (PProd A B) :=
  { r     := λ p₁ p₂ => p₁.fst ≈ p₂.fst ∧ p₁.snd ≈ p₂.snd,
    iseqv := { refl  := λ p   => ⟨Setoid.refl  p.fst,         Setoid.refl  p.snd⟩,
               symm  := λ h   => ⟨Setoid.symm  h.left,        Setoid.symm  h.right⟩,
               trans := λ h i => ⟨Setoid.trans h.left i.left, Setoid.trans h.right i.right⟩ } }

  instance hasProductInstances : HasProductInstances univ.{u} univ.{v} typeClass.{max u v} :=
  ⟨prodSetoid⟩

  instance hasInternalProducts : HasInternalProducts univ.{u} :=
  { defIntroFun    := λ a B   => defFun (λ h   => ⟨Setoid.refl a, h⟩),
    defIntroFunFun := λ A B   => defFun (λ h b => ⟨h, Setoid.refl b⟩),
    defElimFun     := λ F     => defFun (λ h   => isFun₂ F h.left h.right),
    defElimFunFun  := λ A B C => defFun (λ h p => h p.fst p.snd) }

  -- Equivalences

  instance equivSetoid (A : univ.{u}) (B : univ.{v}) : Setoid.{max 1 u v} (A ⮂ B) :=
  { r     := λ e₁ e₂ => e₁.toFun ≈ e₂.toFun,
    iseqv := { refl  := λ e   => Setoid.refl  e.toFun,
               symm  := λ h   => Setoid.symm  h,
               trans := λ h i => Setoid.trans h i } }

  instance hasEquivalenceInstances :
    HasEquivalenceInstances univ.{u} univ.{v} typeClass.{max u v} :=
  { Equiv     := EquivDesc,
    desc      := id,
    equivInst := equivSetoid }

  instance hasInternalEquivalences : HasInternalEquivalences univ.{u} :=
  { defToFunFun := λ A B => defFun id,
    isExt       := HasTrivialExtensionality.equivDescExt univ }

  instance hasTrivialEquivalenceCondition : HasTrivialEquivalenceCondition univ.{u} :=
  ⟨λ e => { E        := e,
            toFunEq  := Setoid.refl e.toFun,
            invFunEq := Setoid.refl e.invFun }⟩

end Setoid
