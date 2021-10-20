import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors



set_option autoBoundImplicitLocal false
set_option pp.universes true

universe u v w iuw



-- TODO: Generalize to arbitrary `GeneralizedTypeClass`.
def SimpleTypeClass := GeneralizedTypeClass.{u + 1, u + 2, u + 1} type.{u}



namespace Bundled

  open MetaRelation

  class HasFunctoriality (φ : SimpleTypeClass.{u}) (ψ : SimpleTypeClass.{v}) (W : outParam Universe.{w}) :
    Type (max (u + 1) (v + 1) w) where
  (IsFun {A : Bundled φ} {B : Bundled ψ} : (A → B) → W)

  structure Fun {φ : SimpleTypeClass.{u}} {ψ : SimpleTypeClass.{v}} {W : Universe.{w}} [h : HasFunctoriality φ ψ W]
                (A : Bundled φ) (B : Bundled ψ) : Type (max u v w) where
  (f     : A → B)
  (isFun : h.IsFun f)

  infixr:20 " ⟶' " => Bundled.Fun

  class HasFunctorInstances (φ : SimpleTypeClass.{max u w}) {W : Universe.{w}} [h : HasFunctoriality φ φ W] :
    Type ((max u w) + 1) where
  (funInst (A B : Bundled φ) : φ (A ⟶' B))

  instance hasFunctors (φ : SimpleTypeClass.{max u w}) {W : Universe.{w}} [HasFunctoriality φ φ W]
                       [h : HasFunctorInstances.{u, w} φ] :
    HasFunctors (univ φ) (univ φ) (univ φ) :=
  { Fun   := λ A B => { A    := A ⟶' B,
                        inst := h.funInst A B },
    apply := Fun.f }

  def defFun {φ : SimpleTypeClass.{max u w}} [hId : HasIdentity.{(max u w) + 1, iuw} (univ φ)] {W : Universe.{w}}
             [h : HasFunctoriality φ φ W] [HasFunctorInstances.{u, w} φ]
             {A B : univ φ} {f : A → B} (isFun : h.IsFun f) :
    A ⟶[f] B :=
  { F   := { f     := f,
             isFun := isFun },
    eff := λ a => HasRefl.refl (f a) }

end Bundled
