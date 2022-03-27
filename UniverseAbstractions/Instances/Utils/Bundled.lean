import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Singletons
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences
import UniverseAbstractions.Axioms.Universe.DependentTypes.DependentFunctors
import UniverseAbstractions.Axioms.Universe.DependentTypes.DependentProducts



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w uv upv cu cv cuv iuw



class HasFunctoriality (U : Universe.{u}) (V : Universe.{v}) where
(IsFun {A : U} {B : V} : (A → B) → Sort w)

namespace HasFunctoriality

  structure Fun {U : Universe.{u}} {V : Universe.{v}} [h : HasFunctoriality.{u, v, w} U V]
                (A : U) (B : V) : Sort (max 1 u v w) where
  (f     : A → B)
  (isFun : h.IsFun f)

end HasFunctoriality

class HasDependentFunctoriality (U : Universe.{u}) (V : Universe.{v}) {UpV : Universe.{upv}}
                                [HasFunctors U {V} UpV] where
(IsFun {A : U} {φ : A ⟶ ⌊V⌋} : HasFunctors.Pi φ → Sort w)

namespace HasDependentFunctoriality

  structure Pi {U : Universe.{u}} {V : Universe.{v}} {UpV : Universe.{upv}}
               [HasFunctors U {V} UpV] [h : HasDependentFunctoriality.{u, v, w} U V]
               {A : U} (φ : A ⟶ ⌊V⌋) : Sort (max 1 u v w) where
  (f     : HasFunctors.Pi φ)
  (isFun : h.IsFun f)

end HasDependentFunctoriality



namespace Bundled

  open MetaRelation

  def SimpleTypeClass := sort.{u} → Sort cu

  class HasFunctorInstances (U : Universe.{u}) (V : Universe.{v})
                            (Φ : outParam SimpleTypeClass.{uv, cuv}) where
  (Fun                     : U → V → Sort uv)
  (apply   {A : U} {B : V} : Fun A B → (A → B))
  (funInst (A : U) (B : V) : Φ (Fun A B))

  instance hasFunctors (U : Universe.{u}) (V : Universe.{v}) {Φ : SimpleTypeClass.{uv, cuv}}
                       [h : HasFunctorInstances U V Φ] :
    HasFunctors U V (univ Φ) :=
  { Fun   := λ A B => type (h.funInst A B),
    apply := h.apply }

  class HasFunctorialityInstances (U : Universe.{u}) (V : Universe.{v})
                                  [h : HasFunctoriality.{u, v, w} U V]
                                  (Φ : outParam SimpleTypeClass.{max 1 u v w, cuv}) where
  (funInst (A : U) (B : V) : Φ (HasFunctoriality.Fun A B))

  namespace HasFunctorialityInstances

    instance hasFunctorInstances (U : Universe.{u}) (V : Universe.{v})
                                 [h : HasFunctoriality.{u, v, w} U V]
                                 (Φ : outParam SimpleTypeClass.{max 1 u v w, cuv})
                                 [h : HasFunctorialityInstances U V Φ] :
      HasFunctorInstances U V Φ :=
    { Fun     := HasFunctoriality.Fun,
      apply   := HasFunctoriality.Fun.f,
      funInst := h.funInst }

    def toDefFun {U : Universe.{u}} {V : Universe.{v}} [h : HasFunctoriality.{u, v, w} U V]
                 {Φ : SimpleTypeClass.{max 1 u v w, cuv}} [HasFunctorialityInstances U V Φ]
                 [HasIdentity V] {A : U} {B : V} (F : A ⟶ B) :
      A ⟶{F.f} B :=
    HasFunctors.toDefFun F

    def defFun {U : Universe.{u}} {V : Universe.{v}} [h : HasFunctoriality.{u, v, w} U V]
               {Φ : SimpleTypeClass.{max 1 u v w, cuv}} [HasFunctorialityInstances U V Φ]
               [HasIdentity V] {A : U} {B : V} {f : A → B} (isFun : h.IsFun f) :
      A ⟶{f} B :=
    toDefFun ⟨f, isFun⟩

  end HasFunctorialityInstances

  class HasTopInstance (Φ : SimpleTypeClass.{u, cu}) where
  (topInst : Φ PUnit)

  instance hasTop (Φ : SimpleTypeClass.{u, cu}) [h : HasTopInstance Φ] :
    HasTop (univ Φ) :=
  { T := type h.topInst,
    t := PUnit.unit }

  class HasBotInstance (Φ : SimpleTypeClass.{u, cu}) where
  (botInst : Φ PEmpty)

  instance hasBot (Φ : SimpleTypeClass.{u, cu}) [h : HasBotInstance Φ] :
    HasBot (univ Φ) :=
  { B    := type h.botInst,
    elim := PEmpty.elim }

  class HasProductInstances (U : Universe.{u}) (V : Universe.{v})
                            (Φ : outParam SimpleTypeClass.{max 1 u v, cuv}) where
  (prodInst (A : U) (B : V) : Φ (PProd A B))

  instance hasProducts (U : Universe.{u}) (V : Universe.{v})
                       {Φ : SimpleTypeClass.{max 1 u v, cuv}}
                       [h : HasProductInstances U V Φ] :
    HasProducts U V (univ Φ) :=
  { Prod  := λ A B => type (h.prodInst A B),
    intro := PProd.mk,
    fst   := PProd.fst,
    snd   := PProd.snd }

  class HasEquivalenceInstances (U : Universe.{u}) (V : Universe.{v})
                                {UV VU : Universe} [HasIdentity U] [HasIdentity V]
                                [HasFunctors U V UV] [HasFunctors V U VU]
                                (Φ : outParam SimpleTypeClass.{uv, cuv}) where
  (Equiv                     : U → V → Sort uv)
  (desc      {A : U} {B : V} : Equiv A B → (A ⮂ B))
  (equivInst (A : U) (B : V) : Φ (Equiv A B))

  instance hasEquivalences (U : Universe.{u}) (V : Universe.{v})
                           {UV VU : Universe} [HasIdentity U] [HasIdentity V]
                           [HasFunctors U V UV] [HasFunctors V U VU]
                           {Φ : SimpleTypeClass.{uv, cuv}}
                           [h : HasEquivalenceInstances U V Φ] :
    HasEquivalences U V (univ Φ) :=
  { Equiv := λ A B => type (h.equivInst A B),
    desc  := h.desc }

  class HasDependentFunctorInstances (U : Universe.{u}) (V : Universe.{v}) {UpV : Universe.{upv}}
                                     [HasFunctors U {V} UpV]
                                     (Φ : outParam SimpleTypeClass.{uv, cuv}) where
  (Pi     {A : U}               : (A ⟶ ⌊V⌋) → Sort uv)
  (apply  {A : U} {φ : A ⟶ ⌊V⌋} : Pi φ → HasFunctors.Pi φ)
  (piInst {A : U} (φ : A ⟶ ⌊V⌋) : Φ (Pi φ))

  instance hasDependentFunctors (U : Universe.{u}) (V : Universe.{v}) {UpV : Universe.{upv}}
                                [HasFunctors U {V} UpV] {Φ : SimpleTypeClass.{uv, cuv}}
                                [h : HasDependentFunctorInstances U V Φ] :
    HasDependentFunctors U V (univ Φ) :=
  { Pi    := λ φ => type (h.piInst φ),
    apply := h.apply }

  class HasDependentFunctorialityInstances (U : Universe.{u}) (V : Universe.{v})
                                           {UpV : Universe.{upv}} [HasFunctors U {V} UpV]
                                           [h : HasDependentFunctoriality.{u, v, w} U V]
                                           (Φ : outParam SimpleTypeClass.{max 1 u v w, cuv}) where
  (piInst {A : U} (φ : A ⟶ ⌊V⌋) : Φ (HasDependentFunctoriality.Pi φ))

  namespace HasDependentFunctorialityInstances

    instance hasDependentFunctorInstances (U : Universe.{u}) (V : Universe.{v})
                                          {UpV : Universe.{upv}} [HasFunctors U {V} UpV]
                                          [h : HasDependentFunctoriality.{u, v, w} U V]
                                          (Φ : outParam SimpleTypeClass.{max 1 u v w, cuv})
                                          [h : HasDependentFunctorialityInstances U V Φ] :
      HasDependentFunctorInstances U V Φ :=
    { Pi     := HasDependentFunctoriality.Pi,
      apply  := HasDependentFunctoriality.Pi.f,
      piInst := h.piInst }

    def toDefPi {U : Universe.{u}} {V : Universe.{v}} {UpV : Universe.{upv}}
                [HasFunctors U {V} UpV] [h : HasDependentFunctoriality.{u, v, w} U V]
                {Φ : SimpleTypeClass.{max 1 u v w, cuv}}
                [HasDependentFunctorialityInstances U V Φ] [HasTypeIdentity V]
                {A : U} {φ : A ⟶ ⌊V⌋} (F : Π φ) :
      Π{F.f} (HasFunctors.toDefFun φ) :=
    HasDependentFunctors.toDefPi F

    def defPi {U : Universe.{u}} {V : Universe.{v}} {UpV : Universe.{upv}} [HasFunctors U {V} UpV]
              [h : HasDependentFunctoriality.{u, v, w} U V]
              {Φ : SimpleTypeClass.{max 1 u v w, cuv}} [HasDependentFunctorialityInstances U V Φ]
              [HasTypeIdentity V] {A : U} {φ : A ⟶ ⌊V⌋} {f : HasFunctors.Pi φ} (isFun : h.IsFun f) :
      Π{f} (HasFunctors.toDefFun φ) :=
    toDefPi ⟨f, isFun⟩

  end HasDependentFunctorialityInstances

  class HasDependentProductInstances (U : Universe.{u}) (V : Universe.{v}) {UpV : Universe.{upv}}
                                     [HasFunctors U {V} UpV]
                                     (Φ : outParam SimpleTypeClass.{max 1 u v, cuv}) where
  (sigmaInst {A : U} (φ : A ⟶ ⌊V⌋) : Φ (PSigma (λ a => φ a)))

  instance hasDependentProducts (U : Universe.{u}) (V : Universe.{v}) {UpV : Universe.{upv}}
                                [HasFunctors U {V} UpV] {Φ : SimpleTypeClass.{max 1 u v, cuv}}
                                [h : HasDependentProductInstances U V Φ] :
    HasDependentProducts U V (univ Φ) :=
  { Sigma := λ φ => type (h.sigmaInst φ),
    intro := PSigma.mk,
    fst   := PSigma.fst,
    snd   := PSigma.snd }

end Bundled
