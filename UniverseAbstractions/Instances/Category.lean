import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Singletons
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences
import UniverseAbstractions.Axioms.Categories
import UniverseAbstractions.Instances.Basic
import UniverseAbstractions.Instances.Utils.Bundled

import mathlib4_experiments.CoreExt



set_option autoBoundImplicitLocal false
set_option pp.universes true

universe u v u' v'



-- TODO: Generalize to higher categories

class Category (α : Type (max u v)) : Type (max u v) where
(M         : MetaRelation α sort.{v})
[hPreorder : MetaRelation.IsPreorder M]
[hCategory : MetaRelation.IsCategory M]

namespace Category

  open MetaRelation IsSemigroupoid IsCategory Bundled

  @[reducible] def typeClass : SimpleTypeClass.{(max u v) + 1, (max u v) + 1} := Category.{u, v}
  @[reducible] def univ : Universe := Bundled.univ.{u + 1, (max u v) + 1} typeClass.{u, v}

  instance inst (A : univ.{u, v}) : Category.{u, v} ⌈A⌉ := Bundled.inst A
  def Hom.rel (A : univ) : MetaRelation ⌈A⌉ sort := (inst A).M
  def Hom {A : univ} (a b : A) := ⌈(Hom.rel A) a b⌉
  instance isPreorder (A : univ) : IsPreorder (Hom.rel A) := (inst A).hPreorder
  instance isCategory (A : univ) : IsCategory (Hom.rel A) := (inst A).hCategory

  def idHom {A : univ} (a : A) : Hom a a := HasRefl.refl a

  class IsIso {A : univ} {a b : A} (f : Hom a b) (g : Hom b a) : Prop where
  (gfInv : g • f = idHom a)
  (fgInv : f • g = idHom b)

  namespace IsIso

    instance refl {A : univ} (a : A) : IsIso (idHom a) (idHom a) :=
    ⟨rightId (idHom a), rightId (idHom a)⟩

    instance symm {A : univ} {a b : A}
                  (f : Hom a b) (g : Hom b a) [isIso : IsIso f g] :
      IsIso g f :=
    ⟨isIso.fgInv, isIso.gfInv⟩

    instance trans {A : univ} {a b c : A}
                   (f  : Hom a b) (g  : Hom b a) [isIso : IsIso f  g]
                   (f' : Hom b c) (g' : Hom c b) [isIso : IsIso f' g'] :
      IsIso (f' • f) (g • g') :=
    ⟨sorry,
     sorry⟩

  end IsIso

  structure Iso {A : univ} (a b : A) where
  (f     : Hom a b)
  (g     : Hom b a)
  [isIso : IsIso f g]

  namespace Iso

    instance {A : univ} {a b : A} (e : Iso a b) : IsIso e.f e.g := e.isIso

    def rel (A : univ) : MetaRelation ⌈A⌉ sort := @Iso A

    instance isEquivalence (A : univ) : IsEquivalence (rel A) :=
    { refl  := λ a   => ⟨idHom a,   idHom a⟩,
      symm  := λ e   => ⟨e.g,       e.f⟩,
      trans := λ e f => ⟨f.f • e.f, e.g • f.g⟩ }

    def equivalence (A : univ) : EquivalenceRelation ⌈A⌉ sort := ⟨rel A⟩

  end Iso

  instance hasIdentity' : HasIdentity' univ sort := ⟨Iso.equivalence⟩

  class IsFun {A : univ.{u, v}} {B : univ.{u', v'}} (φ : A → B) : Type (max u v u' v') where
  (mapHom  {a b   : A}                             : Hom a b → Hom (φ a) (φ b))
  (h_refl  (a     : A)                             : mapHom (idHom a) = idHom (φ a))
  (h_trans {a b c : A} (f : Hom a b) (g : Hom b c) : mapHom (g • f) = mapHom g • mapHom f)

  instance hasFunctoriality : HasFunctoriality typeClass.{u, v} typeClass.{u', v'} type.{max u v u' v'} :=
  ⟨IsFun⟩

  instance funIsPreorder : IsPreorder (V := type.{max u v})
                                      (Bundled.Fun (φ := typeClass.{u, v}) (ψ := typeClass.{u, v})) :=
  sorry

  instance funIsCategory : IsCategory (V := type.{max u v})
                                      (Bundled.Fun (φ := typeClass.{u, v}) (ψ := typeClass.{u, v})) :=
  sorry

  instance hasFunctorInstances : HasFunctorInstances.{u + 1, (max u v) + 1, (max u v) + 1} typeClass.{u, v} :=
  ⟨λ A B => sorry⟩

  instance hasFunctors : HasFunctors univ univ univ :=
  Bundled.hasFunctors.{u + 1, (max u v) + 1, (max u v) + 1} typeClass.{u, v}

  instance hasCongrArg : HasCongrArg univ univ :=
  ⟨λ F => sorry⟩

  instance hasInternalFunctors : HasInternalFunctors univ := ⟨⟩

  instance hasLinearFunOp : HasLinearFunOp univ := sorry

end Category
