import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u cu v cv w iuw



namespace Bundled

  open MetaRelation

  def SimpleTypeClass := Bundled.TypeClass.{u, cu} sort.{max u cu}

  class HasFunctoriality (φ : SimpleTypeClass.{u, cu}) (ψ : SimpleTypeClass.{v, cv}) (W : outParam Universe.{w}) where
  (IsFun {A : Bundled φ} {B : Bundled ψ} : (A → B) → W)

  structure Fun {φ : SimpleTypeClass.{u, cu}} {ψ : SimpleTypeClass.{v, cv}} {W : Universe.{w}} [h : HasFunctoriality φ ψ W]
                (A : Bundled φ) (B : Bundled ψ) : Sort (max 1 u cu v cv w) where
  (f     : A → B)
  (isFun : h.IsFun f)

  infixr:20 " ⟶' " => Bundled.Fun

  class HasFunctorInstances (φ : SimpleTypeClass.{max 1 u w, cu}) {W : Universe.{w}} [h : HasFunctoriality φ φ W] where
  (funInst (A B : Bundled φ) : φ (A ⟶' B))

  instance hasFunctors (φ : SimpleTypeClass.{max 1 u w, cu}) {W : Universe.{w}} [HasFunctoriality φ φ W]
                       [h : HasFunctorInstances.{u, cu, w} φ] :
    HasFunctors (univ.{max 1 u w, cu} φ) (univ.{max 1 u w, cu} φ) (univ.{max 1 u w, cu} φ) :=
  { Fun   := λ A B => { A    := A ⟶' B,
                        inst := h.funInst A B },
    apply := Fun.f }

  def defFun {φ : SimpleTypeClass.{max 1 u w, cu}} [hId : HasIdentity.{max 1 u cu w, iuw} (univ.{max 1 u w, cu} φ)]
             {W : Universe.{w}} [h : HasFunctoriality φ φ W] [HasFunctorInstances.{u, cu, w} φ]
             {A B : univ.{max 1 u w, cu} φ} {f : A → B} (isFun : h.IsFun f) :
    A ⟶[f] B :=
  { F   := { f     := f,
             isFun := isFun },
    eff := λ a => HasRefl.refl (f a) }

end Bundled
