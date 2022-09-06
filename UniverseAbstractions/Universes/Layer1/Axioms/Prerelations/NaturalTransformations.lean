import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations.AttachedRelations
import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations.Isomorphisms



namespace UniverseAbstractions.Layer1

set_option autoImplicit false
set_option linter.unusedVariables false

open Universe HasPiType HasFunctors HasPreorderRelation HasIsomorphisms

universe u v



namespace HasPreorderRelation

  variable {V : Universe} [HasLinearLogic V] {α : Sort u} {P : α → Sort v}
           [∀ a, HasPreorderRelation V (P a)]


  -- In layer 1, natural transformations are essentially just Π types of the correct shape; the
  -- actual concept of naturality requires equivalence of morphisms and thus at least layer 2.
  --
  -- We first introduce a base class that works for arbitrary dependent functions instead of just
  -- preorder functors.

  class HasNaturalTransformationsBase (f g : ∀ a, P a) extends
    HasExternalPiType (λ a => f a ⟶ g a)

  namespace HasNaturalTransformationsBase

    variable (f g : ∀ a, P a) [HasNaturalTransformationsBase f g]

    @[reducible] def Nat : V := Pi (λ a => f a ⟶ g a)

    @[reducible] def DefNat (h : ∀ a, f a ⟶ g a) := DefPi (λ a => f a ⟶ g a) h

  end HasNaturalTransformationsBase

  open HasNaturalTransformationsBase


  class HasIdNatBase (f : ∀ a, P a) [HasNaturalTransformationsBase f f] where
    defIdNat : DefNat f f (λ a => idHom (f a))

  namespace HasIdNatBase

    variable (f : ∀ a, P a) [HasNaturalTransformationsBase f f] [hIdNat : HasIdNatBase f]

    @[reducible] def idNat : Nat f f := hIdNat.defIdNat

    instance idHom.isPiApp {a : α} : IsPiApp (idHom (f a)) := ⟨idNat f, a, rfl⟩

  end HasIdNatBase


  class HasCompNatBase (f g h : ∀ a, P a) [HasNaturalTransformationsBase f g]
                       [HasNaturalTransformationsBase g h] [HasNaturalTransformationsBase f h] where
    defCompNat (η : Nat f g) (ε : Nat g h) : DefNat f h (λ a => ε a • η a)
    defCompNatFun₂ : Nat g h ⥤ Nat f g ⥤{λ ε η => defCompNat η ε} Nat f h

  namespace HasCompNatBase

    @[reducible] def compNat {f g h : ∀ a, P a} [HasNaturalTransformationsBase f g]
                             [HasNaturalTransformationsBase g h] [HasNaturalTransformationsBase f h]
                             [hCompNat : HasCompNatBase f g h] (η : Nat f g) (ε : Nat g h) :
        Nat f h :=
      hCompNat.defCompNat η ε

    instance compHom.isPiApp {f g h : ∀ a, P a} [HasNaturalTransformationsBase f g]
                             [HasNaturalTransformationsBase g h] [HasNaturalTransformationsBase f h]
                             [HasCompNatBase f g h] {η : Nat f g} {ε : Nat g h} {a : α} :
        IsPiApp (ε a • η a) :=
      ⟨compNat η ε, a, rfl⟩

    @[reducible] def compNatFun₂ (f g h : ∀ a, P a) [HasNaturalTransformationsBase f g]
                                 [HasNaturalTransformationsBase g h]
                                 [HasNaturalTransformationsBase f h]
                                 [hCompNat : HasCompNatBase f g h] :
        Nat g h ⥤ Nat f g ⥤ Nat f h :=
      hCompNat.defCompNatFun₂

    instance compNat.isFunApp₂ {f g h : ∀ a, P a} [HasNaturalTransformationsBase f g]
                               [HasNaturalTransformationsBase g h]
                               [HasNaturalTransformationsBase f h] [HasCompNatBase f g h]
                               {η : Nat f g} {ε : Nat g h} :
        IsFunApp₂ (compNat η ε) :=
      ⟨compNatFun₂ f g h, ε, η⟩

  end HasCompNatBase

end HasPreorderRelation


namespace HasEquivalenceRelationBase

  variable {V : Universe} [HasLinearLogic V] {α : Sort u} {P : α → Sort v}
           [∀ a, HasEquivalenceRelationBase V (P a)]

  namespace HasNaturalTransformationsBase

    variable (f g : ∀ a, P a) [h : HasNaturalTransformationsBase (P := λ a => asPreorder (P a)) f g]

    instance : HasPiType (λ a => f a ≃ g a) := h.toHasPiType
    instance : HasPiAppFun (λ a => f a ≃ g a) := h.toHasPiAppFun

    @[reducible] def Nat : V := Pi (λ a => f a ≃ g a)

    @[reducible] def DefNat (h : ∀ a, f a ≃ g a) := DefPi (λ a => f a ≃ g a) h

  end HasNaturalTransformationsBase

  open HasNaturalTransformationsBase


  class HasInvNatBase (f g : ∀ a, P a)
                      [HasNaturalTransformationsBase (P := λ a => asPreorder (P a)) f g]
                      [HasNaturalTransformationsBase (P := λ a => asPreorder (P a)) g f] where
    defInvNat (η : Nat f g) : DefNat g f (λ a => (η a)⁻¹)
    defInvNatFun : Nat f g ⥤{λ η => defInvNat η} Nat g f

  namespace HasInvNatBase

    @[reducible] def invNat {f g : ∀ a, P a}
                            [HasNaturalTransformationsBase (P := λ a => asPreorder (P a)) f g]
                            [HasNaturalTransformationsBase (P := λ a => asPreorder (P a)) g f]
                            [h : HasInvNatBase f g] (η : Nat f g) :
        Nat g f :=
      h.defInvNat η

    instance invIso.isPiApp {f g : ∀ a, P a}
                            [HasNaturalTransformationsBase (P := λ a => asPreorder (P a)) f g]
                            [HasNaturalTransformationsBase (P := λ a => asPreorder (P a)) g f]
                            [HasInvNatBase f g] {η : Nat f g} {a : α} :
        IsPiApp (η a)⁻¹ :=
      ⟨invNat η, a, rfl⟩

    @[reducible] def invNatFun (f g : ∀ a, P a)
                               [HasNaturalTransformationsBase (P := λ a => asPreorder (P a)) f g]
                               [HasNaturalTransformationsBase (P := λ a => asPreorder (P a)) g f]
                               [h : HasInvNatBase f g] :
        Nat f g ⥤ Nat g f :=
      h.defInvNatFun

    instance invNat.isFunApp {f g : ∀ a, P a}
                             [HasNaturalTransformationsBase (P := λ a => asPreorder (P a)) f g]
                             [HasNaturalTransformationsBase (P := λ a => asPreorder (P a)) g f]
                             [HasInvNatBase f g] {η : Nat f g} :
        IsFunApp (invNat η) :=
      ⟨invNatFun f g, η⟩

  end HasInvNatBase

end HasEquivalenceRelationBase



namespace HasPreorderRelation

  variable {V : Universe} [HasLinearLogic V] {α : Sort u} {β : Sort v} [HasPreorderRelation V α]
           [HasPreorderRelation V β]


  -- In layer 1, natural transformations are essentially just Π types of the correct shape; the
  -- actual concept of naturality requires equivalence of morphisms and thus at least layer 2.
  --
  -- We do not want to quantify over functors here because if we did, then the class could no longer
  -- be instantiated in universes with more constraints on functors than what our `PreorderFunctor`
  -- specifies. (This could be solved to some extent, but not fully, by demanding that the
  -- functoriality condition be a Π type with two variables.)
  --
  -- Without quantifying over functors, we cannot directly define functor preorders/categories.
  -- Instead, they are given by `Layer2.HasFunctors`/`Layer3.HasFunctors`.

  class HasNaturalTransformations (F G : PreorderFunctor α β) extends
    HasNaturalTransformationsBase F.φ G.φ

  namespace HasNaturalTransformations

    variable (F G : PreorderFunctor α β) [HasNaturalTransformations F G]

    @[reducible] def Nat : V := HasNaturalTransformationsBase.Nat F.φ G.φ

    @[reducible] def DefNat (h : ∀ a, F a ⟶ G a) := HasNaturalTransformationsBase.DefNat F.φ G.φ h

  end HasNaturalTransformations

  open HasNaturalTransformations


  class HasIdNat (F : PreorderFunctor α β) [HasNaturalTransformations F F] extends
    HasIdNatBase F.φ

  namespace HasIdNat

    variable (F : PreorderFunctor α β) [HasNaturalTransformations F F] [HasIdNat F]

    @[reducible] def idNat : Nat F F := HasIdNatBase.idNat F.φ

    instance idHom.isPiApp {a : α} : IsPiApp (idHom (F a)) := HasIdNatBase.idHom.isPiApp F.φ

  end HasIdNat


  class HasCompNat (F G H : PreorderFunctor α β) [HasNaturalTransformations F G]
                   [HasNaturalTransformations G H] [HasNaturalTransformations F H] extends
    HasCompNatBase F.φ G.φ H.φ

  namespace HasCompNat

    @[reducible] def compNat {F G H : PreorderFunctor α β} [HasNaturalTransformations F G]
                             [HasNaturalTransformations G H] [HasNaturalTransformations F H]
                             [HasCompNat F G H] (η : Nat F G) (ε : Nat G H) :
        Nat F H :=
      HasCompNatBase.compNat η ε

    instance compHom.isPiApp {F G H : PreorderFunctor α β} [HasNaturalTransformations F G]
                             [HasNaturalTransformations G H] [HasNaturalTransformations F H]
                             [HasCompNat F G H] {η : Nat F G} {ε : Nat G H} {a : α} :
        IsPiApp (ε a • η a) :=
      HasCompNatBase.compHom.isPiApp

    @[reducible] def compNatFun₂ (F G H : PreorderFunctor α β) [HasNaturalTransformations F G]
                                 [HasNaturalTransformations G H] [HasNaturalTransformations F H]
                                 [HasCompNat F G H] :
        Nat G H ⥤ Nat F G ⥤ Nat F H :=
      HasCompNatBase.compNatFun₂ F.φ G.φ H.φ

    instance compNat.isFunApp₂ {F G H : PreorderFunctor α β} [HasNaturalTransformations F G]
                               [HasNaturalTransformations G H] [HasNaturalTransformations F H]
                               [HasCompNat F G H] {η : Nat F G} {ε : Nat G H} :
        IsFunApp₂ (compNat η ε) :=
      HasCompNatBase.compNat.isFunApp₂

  end HasCompNat


  class IsNaturalIsomorphism [hαIso : HasIsomorphisms α] [hβIso : HasIsomorphisms β]
                             {F G : PreorderFunctor α β} [IsIsoFunctor F] [IsIsoFunctor G]
                             [HasNaturalTransformations F G] [HasNaturalTransformations G F]
                             [HasNaturalTransformations (IsIsoFunctor.toEquivalenceFunctor F)
                                                        (IsIsoFunctor.toEquivalenceFunctor G)]
                             (η : Nat F G) (ε : Nat G F) where
    defAppIso (a : α) : DefType.DefInst (hβIso.defIsoType (F a) (G a)) ⟨η a, ε a⟩
    defNatIso : DefNat (IsIsoFunctor.toEquivalenceFunctor F) (IsIsoFunctor.toEquivalenceFunctor G)
                       (λ a => (defAppIso a).inst)

end HasPreorderRelation


namespace HasEquivalenceRelationBase

  variable {V : Universe} [HasLinearLogic V] {α : Sort u} {β : Sort v}
           [HasEquivalenceRelationBase V α] [HasEquivalenceRelationBase V β]

  namespace HasNaturalTransformations

    variable (F G : EquivalenceFunctor α β) [h : HasNaturalTransformations F G]

    instance : HasNaturalTransformationsBase (P := λ a => asPreorder β) F.φ G.φ :=
      h.toHasNaturalTransformationsBase

    @[reducible] def Nat : V := Pi (λ a => F a ≃ G a)

    @[reducible] def DefNat (h : ∀ a, F a ≃ G a) := DefPi (λ a => F a ≃ G a) h

  end HasNaturalTransformations

  open HasNaturalTransformations


  class HasInvNat (F G : EquivalenceFunctor α β) [HasNaturalTransformations F G]
                  [HasNaturalTransformations G F] extends
    HasInvNatBase F.φ G.φ

  namespace HasInvNat

    @[reducible] def invNat {F G : EquivalenceFunctor α β} [HasNaturalTransformations F G]
                            [HasNaturalTransformations G F] [h : HasInvNat F G] (η : Nat F G) :
        Nat G F :=
      HasInvNatBase.invNat η

    instance invIso.isPiApp {F G : EquivalenceFunctor α β} [HasNaturalTransformations F G]
                            [HasNaturalTransformations G F] [h : HasInvNat F G] {η : Nat F G}
                            {a : α} :
        IsPiApp (η a)⁻¹ :=
      HasInvNatBase.invIso.isPiApp

    @[reducible] def invNatFun (F G : EquivalenceFunctor α β) [HasNaturalTransformations F G]
                               [HasNaturalTransformations G F] [h : HasInvNat F G] :
        Nat F G ⥤ Nat G F :=
      HasInvNatBase.invNatFun F.φ G.φ

    instance invNat.isFunApp {F G : EquivalenceFunctor α β} [HasNaturalTransformations F G]
                             [HasNaturalTransformations G F] [h : HasInvNat F G] {η : Nat F G} :
        IsFunApp (invNat η) :=
      HasInvNatBase.invNat.isFunApp

  end HasInvNat

end HasEquivalenceRelationBase
