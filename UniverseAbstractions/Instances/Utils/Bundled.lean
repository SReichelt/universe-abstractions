import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Singletons
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w uv cu cv cuv iuw



class HasFunctoriality (U : Universe.{u}) (V : Universe.{v}) where
(IsFun {A : U} {B : V} : (A → B) → Sort w)

namespace HasFunctoriality

  structure Fun {U : Universe.{u}} {V : Universe.{v}} [h : HasFunctoriality.{u, v, w} U V]
                (A : U) (B : V) : Sort (max 1 u v w) where
  (f     : A → B)
  (isFun : h.IsFun f)

  infixr:20 " ⟶' " => HasFunctoriality.Fun

end HasFunctoriality



namespace Bundled

  open MetaRelation

  def SimpleTypeClass := Bundled.TypeClass.{u, u + 1, cu} sort.{u}

  class HasFunctorInstances (U : Universe.{u}) (V : Universe.{v})
                            (φ : outParam SimpleTypeClass.{uv, cuv}) where
  (Fun                     : U → V → Sort uv)
  (apply   {A : U} {B : V} : Fun A B → (A → B))
  (funInst (A : U) (B : V) : φ (Fun A B))

  instance hasFunctors (U : Universe.{u}) (V : Universe.{v}) {φ : SimpleTypeClass.{uv, cuv}}
                       [h : HasFunctorInstances U V φ] :
    HasFunctors U V (univ φ) :=
  { Fun   := λ A B => type (h.funInst A B),
    apply := h.apply }

  class HasFunctorialityInstances (U : Universe.{u}) (V : Universe.{v})
                                  [h : HasFunctoriality.{u, v, w} U V]
                                  (φ : outParam SimpleTypeClass.{max 1 u v w, cuv}) where
  (funInst (A : U) (B : V) : φ (A ⟶' B))

  namespace HasFunctorialityInstances

    instance hasFunctorInstances (U : Universe.{u}) (V : Universe.{v})
                                 [HasFunctoriality.{u, v, w} U V]
                                 (φ : outParam SimpleTypeClass.{max 1 u v w, cuv})
                                 [h : HasFunctorialityInstances U V φ] :
      HasFunctorInstances U V φ :=
    { Fun     := HasFunctoriality.Fun,
      apply   := HasFunctoriality.Fun.f,
      funInst := h.funInst }

    def defFun {U : Universe.{u}} {V : Universe.{v}} [h : HasFunctoriality.{u, v, w} U V]
               {φ : SimpleTypeClass.{max 1 u v w, cuv}} [HasFunctorialityInstances U V φ]
               [HasIdentity V] {A : U} {B : V} {f : A → B} (isFun : h.IsFun f) :
      A ⟶{f} B :=
    { F   := { f     := f,
               isFun := isFun },
      eff := λ a => HasRefl.refl (f a) }

  end HasFunctorialityInstances

  class HasTopInstance (φ : SimpleTypeClass.{u, cu}) where
  (topInst : φ PUnit)

  instance hasTop (φ : SimpleTypeClass.{u, cu}) [h : HasTopInstance φ] :
    HasTop (univ φ) :=
  { T := type h.topInst,
    t := PUnit.unit }

  class HasBotInstance (φ : SimpleTypeClass.{u, cu}) where
  (botInst : φ PEmpty)

  instance hasBot (φ : SimpleTypeClass.{u, cu}) [h : HasBotInstance φ] :
    HasBot (univ φ) :=
  { B    := type h.botInst,
    elim := PEmpty.elim }

  class HasProductInstances (U : Universe.{u}) (V : Universe.{v})
                            (φ : outParam SimpleTypeClass.{max 1 u v, cuv}) where
  (prodInst (A : U) (B : V) : φ (PProd A B))

  instance hasProducts (U : Universe.{u}) (V : Universe.{v})
                       {φ : SimpleTypeClass.{max 1 u v, cuv}}
                       [h : HasProductInstances U V φ] :
    HasProducts U V (univ φ) :=
  { Prod  := λ A B => type (h.prodInst A B),
    intro := PProd.mk,
    fst   := PProd.fst,
    snd   := PProd.snd }

  class HasEquivalenceInstances (U : Universe.{u}) (V : Universe.{v})
                                {UV VU : Universe} [HasIdentity U] [HasIdentity V]
                                [HasFunctors U V UV] [HasFunctors V U VU]
                                (φ : outParam SimpleTypeClass.{uv, cuv}) where
  (Equiv                     : U → V → Sort uv)
  (desc      {A : U} {B : V} : Equiv A B → (A ⮂ B))
  (equivInst (A : U) (B : V) : φ (Equiv A B))

  instance hasEquivalences (U : Universe.{u}) (V : Universe.{v})
                           {UV VU : Universe} [HasIdentity U] [HasIdentity V]
                           [HasFunctors U V UV] [HasFunctors V U VU]
                           {φ : SimpleTypeClass.{uv, cuv}}
                           [h : HasEquivalenceInstances U V φ] :
    HasEquivalences U V (univ φ) :=
  { Equiv := λ A B => type (h.equivInst A B),
    desc  := h.desc }

end Bundled
