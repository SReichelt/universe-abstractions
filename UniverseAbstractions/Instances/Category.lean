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
--set_option pp.universes true

universe u v iv



class Category (V : Universe.{v}) [HasIdentity.{v, iv} V] [HasInternalFunctors V] [HasLinearFunOp V]
               (α : Type (max u v iv)) :
  Type (max u v iv) where
(M         : MetaRelation α V)
[hPreorder : MetaRelation.IsPreorder  M]
[hTransFun : MetaRelation.HasTransFun M]
[hCategory : MetaRelation.IsCategory  M]

namespace Category

  open MetaRelation IsSemigroupoid IsCategory Bundled

  @[reducible] def typeClass (V : Universe.{v}) [HasIdentity.{v, iv} V] [HasInternalFunctors V] [HasLinearFunOp V] :
    SimpleTypeClass.{(max u v iv) + 1, (max u v iv) + 1} := Category.{u, v, iv} V
  @[reducible] def univ (V : Universe.{v}) [HasIdentity.{v, iv} V] [HasInternalFunctors V] [HasLinearFunOp V] :
    Universe := Bundled.univ.{u + 1, (max u v iv) + 1} (typeClass.{u, v, iv} V)

  variable {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasInternalFunctors V] [HasLinearFunOp V]

  instance inst (A : univ.{u, v, iv} V) : Category.{u, v, iv} V ⌈A⌉ := Bundled.inst A

  def Hom.rel (A : univ V) : MetaRelation ⌈A⌉ V := (inst A).M
  @[reducible] def Hom {A : univ V} (a b : A) := ⌈(Hom.rel A) a b⌉

  instance isPreorder  (A : univ V) : IsPreorder  (Hom.rel A) := (inst A).hPreorder
  instance hasTransFun (A : univ V) : HasTransFun (Hom.rel A) := (inst A).hTransFun
  instance isCategory  (A : univ V) : IsCategory  (Hom.rel A) := (inst A).hCategory

  def idHom {A : univ V} (a : A) : Hom a a := HasRefl.refl a

  -- TODO: Integrate iso into `IsCategory`

  class IsIso {A : univ V} {a b : A} (f : Hom a b) (g : Hom b a) where
  (gfInv : g • f ≃ idHom a)
  (fgInv : f • g ≃ idHom b)

  namespace IsIso

    instance refl {A : univ V} (a : A) : IsIso (idHom a) (idHom a) :=
    ⟨rightId (idHom a), rightId (idHom a)⟩

    instance symm {A : univ V} {a b : A}
                  (f : Hom a b) (g : Hom b a) [isIso : IsIso f g] :
      IsIso g f :=
    ⟨isIso.fgInv, isIso.gfInv⟩

    instance trans {A : univ V} {a b c : A}
                   (f  : Hom a b) (g  : Hom b a) [isIso : IsIso f  g]
                   (f' : Hom b c) (g' : Hom c b) [isIso : IsIso f' g'] :
      IsIso (f' • f) (g • g') :=
    ⟨sorry,
     sorry⟩

  end IsIso

  structure Iso {A : univ V} (a b : A) where
  (f     : Hom a b)
  (g     : Hom b a)
  [isIso : IsIso f g]

  namespace Iso

    instance {A : univ V} {a b : A} (e : Iso a b) : IsIso e.f e.g := e.isIso

    def rel (A : univ V) : MetaRelation ⌈A⌉ sort := Iso (A := A)

    instance isEquivalence (A : univ V) : IsEquivalence (rel A) :=
    { refl  := λ a   => ⟨idHom a,   idHom a⟩,
      symm  := λ e   => ⟨e.g,       e.f⟩,
      trans := λ e f => ⟨f.f • e.f, e.g • f.g⟩ }

    def equivalence (A : univ V) : EquivalenceRelation ⌈A⌉ sort := ⟨rel A⟩

  end Iso

  instance hasIdentity' : HasIdentity' (univ V) sort := ⟨Iso.equivalence⟩

  class IsFun {A B : univ.{u, v, iv} V} (φ : A → B) : Type (max u v iv) where
  (mapHom  {a b   : A}                             : Hom a b → Hom (φ a) (φ b))
  (h_refl  (a     : A)                             : mapHom (idHom a) ≃ idHom (φ a))
  (h_trans {a b c : A} (f : Hom a b) (g : Hom b c) : mapHom (g • f) ≃ mapHom g • mapHom f)

  instance hasFunctoriality : HasFunctoriality (typeClass.{u, v, iv} V) (typeClass.{u, v, iv} V) type.{max u v iv} :=
  ⟨IsFun⟩

  instance funIsPreorder : IsPreorder (V := type.{max u v iv})
                                      (Bundled.Fun (φ := typeClass.{u, v, iv} V) (ψ := typeClass.{u, v, iv} V)) :=
  sorry

  instance funIsCategory : IsCategory (V := type.{max u v iv})
                                      (Bundled.Fun (φ := typeClass.{u, v, iv} V) (ψ := typeClass.{u, v, iv} V)) :=
  sorry

  instance hasFunctorInstances : HasFunctorInstances.{u + 1, (max u v iv) + 1, (max u v iv) + 1} (typeClass.{u, v, iv} V) :=
  ⟨λ A B => sorry⟩

  instance hasFunctors : HasFunctors (univ V) (univ V) (univ V) :=
  Bundled.hasFunctors.{u + 1, (max u v iv) + 1, (max u v iv) + 1} (typeClass.{u, v, iv} V)

  instance hasCongrArg : HasCongrArg (univ V) (univ V) :=
  ⟨λ F => sorry⟩

  instance hasInternalFunctors : HasInternalFunctors (univ V) := ⟨⟩

  instance hasLinearFunOp : HasLinearFunOp (univ V) := sorry

end Category
