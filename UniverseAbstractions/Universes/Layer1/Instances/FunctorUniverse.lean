import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Functors
import UniverseAbstractions.Universes.Layer1.Axioms.Singletons
import UniverseAbstractions.Universes.Layer1.Axioms.Products
import UniverseAbstractions.Universes.Layer1.Axioms.Coproducts
import UniverseAbstractions.Universes.Layer1.Axioms.Equivalences
import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations
import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations.Isomorphisms
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedFunctors
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedSingletonFunctors
import UniverseAbstractions.Universes.Layer1.Lemmas.DerivedProductFunctors
import UniverseAbstractions.Universes.Layer1.Meta.Tactics.Functoriality



namespace UniverseAbstractions.Layer1

set_option autoImplicit false

universe u v

open HasPiType HasFunctors HasLinearLogic HasExternalLinearLogic HasExternalSubLinearLogic
     HasExternalNonLinearLogic Prerelation HasPreorderRelation HasEquivalenceRelationBase



def functorUniverse (α : Sort u) (V : Universe) [HasUnivFunctors V V] [HasExternalFullLogic α V] :
    Universe where
  I := V
  h := ⟨λ B => α ⥤ B⟩

namespace functorUniverse

  notation:20 "{" α:0 " ⥤} " V:21 => functorUniverse α V

  variable (α : Sort u) {V : Universe} [HasLinearLogic V] [HasExternalFullLogic α V]

  def type (B : V) : {α ⥤} V := B
  infixr:20 " !⥤ " => functorUniverse.type

  def embedInst {B : V} (b : B) : α !⥤ B := constFun α (B := B) b

  instance hasFunType (B C : V) : HasType ({α ⥤} V) ((α !⥤ B) → (α !⥤ C)) where
    T     := (B ⥤ C : V)
    hElim := ⟨revSubstFun⟩

  instance hasFunctors (B : V) : HasFunctors (α !⥤ B) ({α ⥤} V) where
    hFun (C : V) := hasFunType α B C

  instance hasUnivFunctors : HasUnivFunctors ({α ⥤} V) ({α ⥤} V) where
    hFun (B : V) := hasFunctors α B

  def embedFunctor {B C : V} (F : B ⥤ C) : (α !⥤ B) ⥤ (α !⥤ C) := embedInst α F

  instance hasLinearLogic : HasLinearLogic ({α ⥤} V) where
    defIdFun       (B     : V) := embedFunctor α (idFun B)
    defRevAppFun₂  (B C   : V) := embedFunctor α (revAppFun₂ B C)
    defRevCompFun₃ (B C D : V) := embedFunctor α (revCompFun₃ B C D)

  instance hasSubLinearLogic [HasSubLinearLogic V] : HasSubLinearLogic ({α ⥤} V) where
    defConstFun₂ (B C : V) := embedFunctor α (constFun₂ B C)

  instance hasAffineLogic [HasSubLinearLogic V] : HasAffineLogic ({α ⥤} V) := ⟨⟩

  instance hasNonLinearLogic [HasNonLinearLogic V] : HasNonLinearLogic ({α ⥤} V) where
    defDupFun₂ (B C : V) := embedFunctor α (dupFun₂ B C)

  instance hasFullLogic [HasSubLinearLogic V] [HasNonLinearLogic V] : HasFullLogic ({α ⥤} V) := ⟨⟩

  def embeddedTopElimFun [HasTop V] {B : V} (F : α ⥤ B) : α ⥤ (⊤_V ⥤ B) :=
    Λ a => HasTop.elimFun (F a)

  instance hasTop [HasTop V] : HasTop ({α ⥤} V) where
    T            := ⊤_V
    hElim        := ⟨λ _ => PUnit.unit⟩
    hIntro       := ⟨λ _ => embedInst α ∗_V⟩
    defElimFun F := embeddedTopElimFun α F

  section

    variable [HasProducts V] [HasSubLinearLogic V]

    def embeddedFst {B C : V} (F : α ⥤ B ⊓ C) : α ⥤ B := Λ a => HasProducts.fst (F a)
    def embeddedSnd {B C : V} (F : α ⥤ B ⊓ C) : α ⥤ C := Λ a => HasProducts.snd (F a)

    def embeddedIntro {B C : V} (F : α ⥤ B) (G : α ⥤ C) : α ⥤ B ⊓ C :=
      Λ a => HasProducts.intro (F a) (G a)
    def embeddedIntroFun₂ (B C : V) : α ⥤ B ⥤ C ⥤ B ⊓ C :=
      embedInst α (HasProducts.introFun₂ B C)

    def embeddedElimFun {B C D : V} (F : α ⥤ B ⥤ C ⥤ D) : α ⥤ (B ⊓ C ⥤ D) :=
      Λ a => HasProducts.elimFun (F a)
    def embeddedElimFun₂ (B C D : V) : α ⥤ (B ⥤ C ⥤ D) ⥤ (B ⊓ C ⥤ D) :=
      embedInst α (HasProducts.elimFun₂ B C D)

    instance hasExternalProducts (B C : V) : HasExternalProducts ({α ⥤} V) (α !⥤ B) (α !⥤ C) where
      T                   := (B ⊓ C : V)
      hElim               := ⟨λ P => ⟨embeddedFst α P, embeddedSnd α P⟩⟩
      hIntro              := ⟨λ p => embeddedIntro α p.fst p.snd⟩
      defIntroFun₂        := embeddedIntroFun₂ α B C
      defElimFun₂ (D : V) := embeddedElimFun₂ α B C D

    instance hasProducts : HasProducts ({α ⥤} V) where
      hProd (B C : V) := hasExternalProducts α B C

  end

  section

    variable {β : Sort v} (R : Prerelation β V)

    def embedPrerelation : Prerelation β ({α ⥤} V) := R

    instance isFull [hR : IsFull R] : IsFull (embedPrerelation α R) :=
      ⟨λ B C => embedInst α (hR.inst B C)⟩

    instance hasRefl  [hR : HasRefl  R] : HasRefl  (embedPrerelation α R) :=
      ⟨λ B     => embedInst α (hR.refl         B)⟩
    instance hasSymm  [hR : HasSymm  R] : HasSymm  (embedPrerelation α R) :=
      ⟨λ B C   => embedInst α (hR.symmFun      B C)⟩
    instance hasTrans [hR : HasTrans R] : HasTrans (embedPrerelation α R) :=
      ⟨λ B C D => embedInst α (hR.revTransFun₂ B C D)⟩

    instance isPreorder    [IsPreorder    R] : IsPreorder    (embedPrerelation α R) := ⟨⟩
    instance isEquivalence [IsEquivalence R] : IsEquivalence (embedPrerelation α R) := ⟨⟩

  end

  section

    variable {β : Sort v} [h : HasPreorderRelation V β] [HasIsomorphisms β]

    def embeddedIsoToHom  {b c : β} (e : α ⥤ b ≃ c) : α ⥤ (b ⟶ c) :=
      Λ a => HasIsomorphisms.toHom  (e a)
    def embeddedIsoInvHom {b c : β} (e : α ⥤ b ≃ c) : α ⥤ (c ⟶ b) :=
      Λ a => HasIsomorphisms.invHom (e a)

    def embeddedIsoRefl (b : β) : α ⥤ b ≃ b := embedInst α (idIso b)

    def embeddedIsoSymm {b c : β} (F : α ⥤ b ≃ c) : α ⥤ c ≃ b := Λ a => (F a)⁻¹
    def embeddedIsoSymmFun (b c : β) : α ⥤ b ≃ c ⥤ c ≃ b := embedFunctor α (HasSymm.symmFun b c)

    def embeddedIsoTrans {b c d : β} (F : α ⥤ b ≃ c) (G : α ⥤ c ≃ d) : α ⥤ b ≃ d :=
      Λ a => G a • F a
    def embeddedIsoRevTransFun₂ (b c d : β) : α ⥤ c ≃ d ⥤ b ≃ c ⥤ b ≃ d :=
      embedFunctor α (HasTrans.revTransFun₂ b c d)

  end

  section

    variable [HasEquivalences V]

    instance hasIsoType (B C : V) : HasType ({α ⥤} V) (DefIso (α !⥤ B) (α !⥤ C)) where
      T     := (B ≃ C : V)
      hElim := ⟨λ E => ⟨embeddedIsoToHom α E, embeddedIsoInvHom α E⟩⟩

    instance hasEquivalences : HasEquivalences ({α ⥤} V) where
      hIsoType        (B C : V)   := hasIsoType α B C
      defToHomFun     (B C : V)   := embedFunctor α (HasEquivalences.toFun₂ B C)
      defRefl         (B : V)     := embeddedIsoRefl α B
      defSymm         F           := embeddedIsoSymm α F
      defSymmFun      (B C : V)   := embeddedIsoSymmFun α B C
      defTrans        F G         := embeddedIsoTrans α F G
      defRevTransFun₂ (B C D : V) := embeddedIsoRevTransFun₂ α B C D

    -- TODO standard equivalences

  end

end functorUniverse
