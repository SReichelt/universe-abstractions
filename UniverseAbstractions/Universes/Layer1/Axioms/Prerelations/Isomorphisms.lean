import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations.AttachedRelations



namespace UniverseAbstractions.Layer1

set_option autoImplicit false
set_option linter.unusedVariables false

open HasFunctors Prerelation HasPreorderRelation HasEquivalenceRelationBase

universe u u' u''



namespace HasPreorderRelation

  variable {V : Universe} [HasLinearLogic V]

  structure DefIso {α : Sort u} [HasPreorderRelation V α] (a b : α) where
    toHom  : a ⟶ b
    invHom : b ⟶ a

  namespace DefIso

    variable {α : Sort u} [HasPreorderRelation V α]

    def refl (a : α) : DefIso a a := ⟨idHom a, idHom a⟩

    def symm {a b : α} (e : DefIso a b) : DefIso b a := ⟨e.invHom, e.toHom⟩

    def trans {a b c : α} (e : DefIso a b) (f : DefIso b c) : DefIso a c :=
      ⟨f.toHom • e.toHom, e.invHom • f.invHom⟩

  end DefIso

  class HasIsomorphismsBase (α : Sort u) [hα : HasPreorderRelation V α] where
    [hIsoType (a b : α) : HasType V (DefIso a b)]
    defToHomFun (a b : α) : [(hIsoType a b).A ⥤ (a ⟶ b)]_{λ e => ((hIsoType a b).hElim.elim e).toHom}

  namespace HasIsomorphismsBase

    section

      variable {α : Sort u} [HasPreorderRelation V α] [h : HasIsomorphismsBase α]

      instance (a b : α) : HasType V (DefIso a b) := h.hIsoType a b

    end

  end HasIsomorphismsBase

  class HasIsomorphisms (α : Sort u) [hα : HasPreorderRelation V α] extends
      HasIsomorphismsBase α where
    defRefl (a : α) : [DefIso a a | V]_{DefIso.refl a}
    defSymm {a b : α} (e : [DefIso a b | V]) : [DefIso b a | V]_{DefIso.symm (e : DefIso a b)}
    defSymmFun (a b : α) : [[DefIso a b | V] ⥤ [DefIso b a | V]]_{defSymm}
    defTrans {a b c : α} (e : [DefIso a b | V]) (f : [DefIso b c | V]) :
      [DefIso a c | V]_{DefIso.trans (e : DefIso a b) (f : DefIso b c)}
    defRevTransFun₂ (a b c : α) :
      [[DefIso b c | V] ⥤ [DefIso a b | V] ⥤ [DefIso a c | V]]__{λ f e => defTrans e f}

  namespace HasIsomorphisms

    section

      variable (α : Sort u) [HasPreorderRelation V α] [h : HasIsomorphisms α]

      def isoRel : Prerelation α V := λ a b => [DefIso a b | V]

      instance isoRel.isEquivalence : IsEquivalence (isoRel α) where
        refl         := h.defRefl
        symmFun      := h.defSymmFun
        revTransFun₂ := h.defRevTransFun₂

      instance hasEquivalenceRelation : HasEquivalenceRelationBase V α := ⟨isoRel α⟩

    end

    section

      variable {α : Sort u} [HasPreorderRelation V α] [h : HasIsomorphisms α]

      instance (a b : α) : HasElim (a ≃ b) (DefIso a b) := (h.hIsoType a b).hElim

      @[reducible] def toHom  {a b : α} (e : a ≃ b) : a ⟶ b := (e : DefIso a b).toHom
      @[reducible] def invHom {a b : α} (e : a ≃ b) : b ⟶ a := (e : DefIso a b).invHom

      @[reducible] def toHomFun (a b : α) : a ≃ b ⥤ (a ⟶ b) := h.defToHomFun a b
      def invHomFun (a b : α) : a ≃ b ⥤ (b ⟶ a) := toHomFun b a ⊙ HasSymm.symmFun a b

      instance toHom.isFunApp  {a b : α} {e : a ≃ b} : IsFunApp (toHom  e) := ⟨toHomFun  a b, e⟩
      instance invHom.isFunApp {a b : α} {e : a ≃ b} : IsFunApp (invHom e) := ⟨invHomFun a b, e⟩

    end

    section

      variable (α : Sort u) [HasPreorderRelation V α] [h : HasIsomorphisms α]

      def toHomFunctor : PreorderFunctor (asPreorder α) α where
        φ  := id
        hφ := { inst := toHomFun (h := h) }

      def invHomFunctor : PreorderFunctor (asPreorder α) (opposite α) where
        φ  := id
        hφ := { inst := invHomFun (h := h) }

      instance opposite.hasIsomorphisms : HasIsomorphisms (opposite α) where
        hIsoType (a b : α)          := { A     := b ≃ a,
                                         hElim := ⟨λ e => ⟨(toHom e : b ⟶ a), (invHom e : a ⟶ b)⟩⟩ }
        defToHomFun (a b : α)       := h.defToHomFun b a
        defRefl (a : α)             := idIso a
        defSymm {a b : α} e         := (e⁻¹ : a ≃ b)
        defSymmFun (a b : α)        := (HasSymm.symmFun b a : b ≃ a ⥤ a ≃ b)
        defTrans {a b c : α} e f    := (e • f : c ≃ a)
        defRevTransFun₂ (a b c : α) := (HasTrans.transFun₂ c b a : c ≃ b ⥤ b ≃ a ⥤ c ≃ a)

    end

    class IsIsoFunctor {α : Sort u} {β : Sort u'} [hα : HasPreorderRelation V α]
                       [hαIso : HasIsomorphisms α] [hβ : HasPreorderRelation V β]
                       [hβIso : HasIsomorphisms β] (F : PreorderFunctor α β) where
      defIso {a b : α} (e : a ≃ b) : [F a ≃ F b]_{⟨F.hφ (toHom e), F.hφ (invHom e)⟩}
      defIsoFun (a b : α) : [a ≃ b ⥤ F a ≃ F b]_{defIso}

    namespace IsIsoFunctor

      variable {α : Sort u} {β : Sort u'} [hα : HasPreorderRelation V α] [hαIso : HasIsomorphisms α]
               [hβ : HasPreorderRelation V β] [hβIso : HasIsomorphisms β] (F : PreorderFunctor α β)
               [hFIso : IsIsoFunctor F]

      @[reducible] def iso {a b : α} (e : a ≃ b) : F a ≃ F b := hFIso.defIso e
      @[reducible] def isoFun (a b : α) : a ≃ b ⥤ F a ≃ F b := hFIso.defIsoFun a b

      instance iso.isFunApp {a b : α} {e : a ≃ b} : IsFunApp (iso F e) := ⟨isoFun F a b, e⟩

      @[reducible] def iso.opposite {a b : opposite α} (e : b ≃ a) : F a ≃ F b := iso F e

      def toEquivalenceFunctor : EquivalenceFunctor α β where
        φ  := F.φ
        hφ := { inst := isoFun F (hα := hα) }

    end IsIsoFunctor

    class IsIsoFunctor₂ {α : Sort u} {β : Sort u'} {γ : Sort u''} [hα : HasPreorderRelation V α]
                        [hαIso : HasIsomorphisms α] [hβ : HasPreorderRelation V β]
                        [hβIso : HasIsomorphisms β] [hγ : HasPreorderRelation V γ]
                        [hγIso : HasIsomorphisms γ] (F : PreorderFunctor₂ α β γ) where
      [app  (a : α) : IsIsoFunctor (F.app  a)]
      [app₂ (b : β) : IsIsoFunctor (F.app₂ b)]

    namespace IsIsoFunctor₂

      variable {α : Sort u} {β : Sort u'} {γ : Sort u''} [hα : HasPreorderRelation V α]
               [hαIso : HasIsomorphisms α] [hβ : HasPreorderRelation V β]
               [hβIso : HasIsomorphisms β] [hγ : HasPreorderRelation V γ]
               [hγIso : HasIsomorphisms γ] (F : PreorderFunctor₂ α β γ) [hFIso : IsIsoFunctor₂ F]

      instance (a : α) : IsIsoFunctor (F.app  a) := hFIso.app  a
      instance (b : β) : IsIsoFunctor (F.app₂ b) := hFIso.app₂ b

      def toEquivalenceFunctor₂ : EquivalenceFunctor₂ α β γ where
        φ  := F.φ
        hφ := { app  := λ a => (IsIsoFunctor.toEquivalenceFunctor (F.app  a)).hφ,
                app₂ := λ b => (IsIsoFunctor.toEquivalenceFunctor (F.app₂ b) (hα := hα)).hφ }

    end IsIsoFunctor₂

  end HasIsomorphisms

end HasPreorderRelation


namespace HasEquivalenceRelationBase

  variable {V : Universe} [HasLinearLogic V]

  def defIsoInst {α : Sort u} [hα : HasEquivalenceRelationBase V α] {a b : α} (e : a ≃ b) :
      DefIso (α := asPreorder α) a b where
    toHom  := (e   : a ≃ b)
    invHom := (e⁻¹ : b ≃ a)

  instance hasIsomorphisms (α : Sort u) [hα : HasEquivalenceRelationBase V α] :
      HasIsomorphisms (asPreorder α) where
    hIsoType (a b : α)          := { A     := a ≃ b,
                                     hElim := ⟨defIsoInst⟩ }
    defToHomFun (a b : α)       := HasIdFun.defIdFun
    defRefl (a : α)             := idIso a
    defSymm {a b : α} e         := (e⁻¹ : b ≃ a)
    defSymmFun (a b : α)        := (HasSymm.symmFun a b : a ≃ b ⥤ b ≃ a)
    defTrans {a b c : α} e f    := (f • e : a ≃ c)
    defRevTransFun₂ (a b c : α) := (HasTrans.revTransFun₂ a b c : b ≃ c ⥤ a ≃ b ⥤ a ≃ c)

end HasEquivalenceRelationBase
