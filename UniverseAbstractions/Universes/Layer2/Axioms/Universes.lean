import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.StandardEquivalences
import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations



namespace UniverseAbstractions.Layer2

set_option autoBoundImplicitLocal false

open Layer1.Prerelation

universe u uu v vv



structure Universe extends Layer1.Universe.{u, uu} where
(V : Layer1.Universe.{v, vv})
[hV : Layer1.IsStandardUniverse V]
[hasEq (A : I) : Layer1.HasEquivalenceRelation A V]

namespace Universe

  instance : Coe Universe Layer1.Universe := ⟨Universe.toUniverse⟩

  instance hasInstances : Layer1.HasInstances.{uu, (max u uu v vv) + 1} Universe.{u, uu, v, vv} :=
  ⟨λ U => U.I⟩

  section

    variable (U : Universe.{u, uu})

    instance instInst : Layer1.HasInstances.{u, uu} U.I := Layer1.Universe.instInst U
    instance : Layer1.HasInstances U := instInst U

    instance : Layer1.IsStandardUniverse U.V := U.hV

  end

  variable {U : Universe}

  instance (A : U) : Layer1.HasEquivalenceRelation A U.V := U.hasEq A

  @[reducible] def InstEq (A : U) : Layer1.Prerelation A U.V := (U.hasEq A).R

  namespace InstEq

    instance (A : U.toUniverse) : IsEquivalence (α := ⌈A⌉) (InstEq A) := (U.hasEq A).h

    notation:25 a:26 " ≃⟨" A:0 "⟩ " b:26 => (Universe.InstEq A) a b
    infix:25 " ≃ " => Universe.InstEq _

    variable {A : U}

    @[reducible] def refl (a : A) : a ≃ a := HasRefl.refl a
    @[reducible] def symm {a b : A} (e : a ≃ b) : b ≃ a := e⁻¹
    @[reducible] def trans {a b c : A} (f : a ≃ b) (g : b ≃ c) : a ≃ c := g • f
    @[reducible] def trans_symm {a a' b b' : A} (e : a ≃ b) (ea : a ≃ a') (eb : b ≃ b') : a' ≃ b' :=
    eb • e • ea⁻¹

  end InstEq

  -- TODO remove duplication

  structure DefPi {A : U} (φ : A → U.V) where
  (p              : U.V)
  (appFun (a : A) : p ⟶ φ a)

  namespace DefPi

    variable {A B : U} {φ : A → U.V} (p : DefPi φ)

    structure DefLambda (h : ∀ a, φ a) where
    (i : p.p)

  end DefPi

  structure DefPi₂ {A B : U} (φ : A → B → U.V) where
  (app (a : A) : DefPi (φ a))
  (toDefPi     : DefPi (λ a => (app a).p))

  @[reducible] def DefPi₂.p {A B : U} {φ : A → B → U.V} (p : DefPi₂ φ) := p.toDefPi.p

  namespace DefPi₂

    variable {A B : U} {φ : A → B → U.V} (p : DefPi₂ φ)

    def appFun (a : A) (b : B) : p.p ⟶ φ a b := (p.app a).appFun b ⊙ p.toDefPi.appFun a

    structure DefLambda (h : ∀ a b, φ a b) where
    (app (a : A) : DefPi.DefLambda (p.app a) (h a))
    (toDefPi     : DefPi.DefLambda p.toDefPi (λ a => (app a).i))

    @[reducible] def DefLambda.i {h : ∀ a b, φ a b} (i : DefLambda p h) : p.p := i.toDefPi.i

  end DefPi₂

  structure DefPi₃ {A B C : U} (φ : A → B → C → U.V) where
  (app (a : A) : DefPi₂ (φ a))
  (toDefPi     : DefPi (λ a => (app a).p))

  @[reducible] def DefPi₃.p {A B C : U} {φ : A → B → C → U.V} (p : DefPi₃ φ) := p.toDefPi.p

  namespace DefPi₃

    variable {A B C : U} {φ : A → B → C → U.V} (p : DefPi₃ φ)

    def appFun (a : A) (b : B) (c : C) : p.p ⟶ φ a b c := (p.app a).appFun b c ⊙ p.toDefPi.appFun a

    structure DefLambda (h : ∀ a b c, φ a b c) where
    (app (a : A) : DefPi₂.DefLambda (p.app a) (h a))
    (toDefPi     : DefPi.DefLambda p.toDefPi (λ a => (app a).i))

    @[reducible] def DefLambda.i {h : ∀ a b c, φ a b c} (i : DefLambda p h) : p.p := i.toDefPi.i

  end DefPi₃

  structure DefPi₄ {A B C D : U} (φ : A → B → C → D → U.V) where
  (app (a : A) : DefPi₃ (φ a))
  (toDefPi     : DefPi (λ a => (app a).p))

  @[reducible] def DefPi₄.p {A B C D : U} {φ : A → B → C → D → U.V} (p : DefPi₄ φ) := p.toDefPi.p

  namespace DefPi₄

    variable {A B C D : U} {φ : A → B → C → D → U.V} (p : DefPi₄ φ)

    def appFun (a : A) (b : B) (c : C) (d : D ): p.p ⟶ φ a b c d :=
    (p.app a).appFun b c d ⊙ p.toDefPi.appFun a

    structure DefLambda (h : ∀ a b c d, φ a b c d) where
    (app (a : A) : DefPi₃.DefLambda (p.app a) (h a))
    (toDefPi     : DefPi.DefLambda p.toDefPi (λ a => (app a).i))

    @[reducible] def DefLambda.i {h : ∀ a b c d, φ a b c d} (i : DefLambda p h) : p.p := i.toDefPi.i

  end DefPi₄

end Universe
