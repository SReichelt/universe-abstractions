import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Singletons
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.Universe.Equivalences
import UniverseAbstractions.Axioms.CategoryTheory.Basic
import UniverseAbstractions.Instances.Basic
import UniverseAbstractions.Instances.Utils.Bundled

import mathlib4_experiments.CoreExt



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u u' v iv



class Category (V : Universe.{v}) [HasIdentity.{v, iv} V] [HasInternalFunctors V] [HasFullFunOp V]
               (α : Type (max u v iv)) :
  Type (max u v iv) where
(M                  : MetaRelation α V)
[hCategory          : MetaRelation.IsCategory M]
[I                  : MetaRelation α V]
[hGroupoid          : MetaRelation.IsGroupoid I]
(isoToHom (a b : α) : I a b ⟶ M a b)
-- TODO: isoToHom must be functor of categories

namespace Category

  open MetaRelation HasFunctors HasCongrArg HasLinearFunOp IsAssociative IsCategoricalPreorder Bundled

  @[reducible] def typeClass (V : Universe.{v}) [HasIdentity.{v, iv} V] [HasInternalFunctors V] [HasFullFunOp V] :
    SimpleTypeClass.{(max u v iv) + 1, (max u v iv) + 1} := Category.{u, v, iv} V
  @[reducible] def univ (V : Universe.{v}) [HasIdentity.{v, iv} V] [HasInternalFunctors V] [HasFullFunOp V] :
    Universe := Bundled.univ.{u + 1, (max u v iv) + 1} (typeClass.{u, v, iv} V)

  variable {V : Universe.{v}} [HasIdentity.{v, iv} V] [HasInternalFunctors V] [HasFullFunOp V]

  instance inst (A : univ.{u, v, iv} V) : Category.{u, v, iv} V ⌈A⌉ := Bundled.inst A

  instance isCategory (A : univ V) : IsCategory (inst A).M := (inst A).hCategory

  @[reducible] def Hom {A : univ V} (a b : A) := (inst A).M a b
  infixr:20 " ⇾ " => Category.Hom

  def idHom {A : univ V} (a : A) : a ⇾ a := HasRefl.refl a

  -- TODO: Integrate iso into `IsCategory` and functor

  class IsIso {A : univ V} {a b : A} (f : a ⇾ b) (g : b ⇾ a) where
  (gfInv : g • f ≃ idHom a)
  (fgInv : f • g ≃ idHom b)

  namespace IsIso

    instance refl {A : univ V} (a : A) : IsIso (idHom a) (idHom a) :=
    ⟨rightId (idHom a), rightId (idHom a)⟩

    instance symm {A : univ V} {a b : A}
                  (f : a ⇾ b) (g : b ⇾ a) [isIso : IsIso f g] :
      IsIso g f :=
    ⟨isIso.fgInv, isIso.gfInv⟩

    instance trans {A : univ V} {a b c : A}
                   (f  : a ⇾ b) (g  : b ⇾ a) [isIso : IsIso f  g]
                   (f' : b ⇾ c) (g' : c ⇾ b) [isIso : IsIso f' g'] :
      IsIso (f' • f) (g • g') :=
    ⟨sorry,
     sorry⟩

  end IsIso

  structure Iso {A : univ V} (a b : A) where
  (f     : a ⇾ b)
  (g     : b ⇾ a)
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

  instance hasInstanceEquivalences : HasInstanceEquivalences (univ V) sort := ⟨Iso.equivalence⟩

  class IsFun {A : univ.{u, v, iv} V} {B : univ.{u', v, iv} V} (φ : A → B) : Type (max u v iv) where
  (mapHom             {a b : A}                           : (a ⇾ b) ⟶ (φ a ⇾ φ b))
  (mapHom_refl        (a : A)                             : mapHom (idHom a) ≃ idHom (φ a))
  (mapHom_trans       {a b c : A} (f : a ⇾ b) (g : b ⇾ c) : mapHom (g • f) ≃ mapHom g • mapHom f)
  (mapHom_transExt    {a b : A} (f : a ⇾ b) (c : A)       :
     mapHom • HasTransFun.transFun (inst A).M f c
     ≃[λ g => (byDef • byDef)⁻¹ •
              mapHom_trans f g •
              (byArgDef • byDef)]
     HasTransFun.transFun (inst B).M (mapHom f) (φ c) • mapHom)
  (mapHom_transExtExt (a b c : A)                         :
     revCompFunFun (b ⇾ c) mapHom • HasTransFun.transFunFun (inst A).M a b c
     ≃[λ f => (byDef • byArgDef • byArgDef • byDef)⁻¹ •
              mapHom_transExt f c •
              (byDef • byArgDef • byDef)]
     compFunFun mapHom (φ a ⇾ φ c) • HasTransFun.transFunFun (inst B).M (φ a) (φ b) (φ c) • mapHom)

  instance hasFunctoriality : HasFunctoriality (typeClass.{u, v, iv} V) (typeClass.{u', v, iv} V) type.{max u v iv} :=
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
