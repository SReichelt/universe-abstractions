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

universe u uu uv w

open HasPiType HasFunctors HasIdFun HasPiAppFunPi HasRevCompFunPiFun HasConstPi HasConstPiFun
     HasDupPiFun HasSubstPi Prerelation HasPreorderRelation HasEquivalenceRelationBase



def functorUniverse (α : Sort u) (U : Universe.{u, uu}) [HasUnivFunctors U U]
                    [HasExternalFullLogic α U] :
    Universe.{u, uu} where
  I := U
  h := ⟨λ B => α ⥤ B⟩

namespace functorUniverse

  notation:20 "{" α:0 " ⥤} " U:21 => functorUniverse α U

  variable (α : Sort u) {U : Universe.{u, uu}} [hLinFun : HasLinearLogic U]
           [HasExternalFullLogic α U]

  def type (B : U) : {α ⥤} U := B
  infixr:20 " !⥤ " => functorUniverse.type

  def embedInst {B : U} (b : B) : α !⥤ B := constFun α (B := B) b

  instance hasUnivFunctors : HasUnivFunctors ({α ⥤} U) ({α ⥤} U) where
    hFun (B C : U) := { defPiType := { A    := (hLinFun.hFun B C).defPiType.A
                                       elim := revSubstFun } }

  def embedFunctor {B C : U} (F : B ⥤ C) : (α !⥤ B) ⥤ (α !⥤ C) := embedInst α F

  def embeddedIdFun (B : U) [HasIdFun B] := embedFunctor α (idFun B)

  def embeddedRevAppFun₂ (B C : U) [HasPiAppFunPi (Function.const B C)] :=
    embedFunctor α (revAppFun₂ B C)

  def embeddedRevCompFun₃ (B C D : U) [HasRevCompFunPiFun B (Function.const C D)] :=
    embedFunctor α (revCompFun₃ B C D)

  def embeddedConstFun₂ (B C : U) [HasConstPiFun B C] := embedFunctor α (constFun₂ B C)

  def embeddedDupFun₂ (B C : U) [HasDupPiFun (Function.const B (Function.const B C))] :=
    embedFunctor α (dupFun₂ B C)

  instance hasLinearLogic : HasLinearLogic ({α ⥤} U) where
    defIdFun       (B     : U) :=
      DefFun.mk   (α := α !⥤ B)                                       (embeddedIdFun       α B)
    defRevAppFun₂  (B C   : U) :=
      DefFun₂.mk' (α := α !⥤ B) (β := α !⥤ B ⥤ C)                    (embeddedRevAppFun₂  α B C)
    defRevCompFun₃ (B C D : U) :=
      DefFun₃.mk' (α := α !⥤ C ⥤ D) (β := α !⥤ B ⥤ C) (γ := α !⥤ B) (embeddedRevCompFun₃ α B C D)

  instance hasSubLinearLogic [HasSubLinearLogic U] : HasSubLinearLogic ({α ⥤} U) where
    defConstFun₂ (B C : U) := DefFun₂.mk' (α := α !⥤ C) (β := α !⥤ B) (embeddedConstFun₂ α B C)

  instance hasAffineLogic [HasSubLinearLogic U] : HasAffineLogic ({α ⥤} U) := ⟨⟩

  instance hasNonLinearLogic [HasNonLinearLogic U] : HasNonLinearLogic ({α ⥤} U) where
    defDupFun₂ (B C : U) :=
      DefFun₂.mk' (α := α !⥤ B ⥤ B ⥤ C) (β := α !⥤ B) (embeddedDupFun₂ α B C)

  instance hasFullLogic [HasSubLinearLogic U] [HasNonLinearLogic U] : HasFullLogic ({α ⥤} U) := ⟨⟩

  def embeddedTopElimFun [HasTop U] {B : U} (F : α ⥤ B) : α ⥤ (⊤_U ⥤ B) :=
    Λ a => HasTop.elimFun (F a)

  instance hasTop [hTop : HasTop U] : HasTop ({α ⥤} U) where
    defTopType   := { A       := hTop.defTopType.A,
                      elim    := λ _ => PUnit.unit,
                      defInst := λ _ => ⟨embedInst α ∗_U⟩ }
    defElimFun F := ⟨embeddedTopElimFun α F⟩

  section

    variable [hProd : HasInnerProducts U] [HasSubLinearLogic U]

    def embeddedFst {B C : U} (F : α ⥤ B ⊓ C) : α ⥤ B := Λ a => HasProducts.fst (F a)
    def embeddedSnd {B C : U} (F : α ⥤ B ⊓ C) : α ⥤ C := Λ a => HasProducts.snd (F a)

    def embeddedIntro {B C : U} (F : α ⥤ B) (G : α ⥤ C) : α ⥤ B ⊓ C :=
      Λ a => HasProducts.intro (F a) (G a)
    def embeddedIntroFun₂ (B C : U) : α ⥤ B ⥤ C ⥤ B ⊓ C :=
      embedInst α (HasProducts.introFun₂ B C)

    def embeddedElimFun {B C D : U} (F : α ⥤ B ⥤ C ⥤ D) : α ⥤ (B ⊓ C ⥤ D) :=
      Λ a => HasProducts.elimFun (F a)
    def embeddedElimFun₂ (B C D : U) : α ⥤ (B ⥤ C ⥤ D) ⥤ (B ⊓ C ⥤ D) :=
      embedInst α (HasProducts.elimFun₂ B C D)

    instance hasProducts (B C : U) : HasProducts (α !⥤ B) (α !⥤ C) where
      defProdType         := { A       := (hProd.hProd B C).defProdType.A,
                               elim    := λ P => ⟨embeddedFst α P, embeddedSnd α P⟩,
                               defInst := λ p => ⟨embeddedIntro α p.fst p.snd⟩ }
      defIntroFun₂        := DefFun₂.mk' (embeddedIntroFun₂ α B C)
      defElimFun₂ (D : U) := DefFun₂.mk' (embeddedElimFun₂ α B C D)

    instance hasInnerProducts : HasInnerProducts ({α ⥤} U) where
      hProd (B C : U) := hasProducts α B C

  end

  section

    variable {β : Sort w} (R : Prerelation β U)

    def embedPrerelation : Prerelation β ({α ⥤} U) := R

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

    variable {β : Sort w} [h : HasPreorderRelation U β] [HasIsomorphisms β]

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

    variable [hEquiv : HasEquivalences U]

    instance hasEquivalences : HasEquivalences ({α ⥤} U) where
      defIsoType      (B C : U)   := { A    := (hEquiv.defIsoType B C).A,
                                       elim := λ E => ⟨embeddedIsoToHom α E, embeddedIsoInvHom α E⟩ }
      defToHomFun     (B C : U)   := ⟨embedFunctor α (hEquiv.defToHomFun B C)⟩
      defRefl         (B : U)     := ⟨embeddedIsoRefl α B⟩
      defSymm         F           := ⟨embeddedIsoSymm α F⟩
      defSymmFun      (B C : U)   := ⟨embeddedIsoSymmFun α B C⟩
      defTrans        F G         := ⟨embeddedIsoTrans α F G⟩
      defRevTransFun₂ (B C D : U) := DefFun₂.mk' (embeddedIsoRevTransFun₂ α B C D)

    -- TODO standard equivalences

  end

end functorUniverse
