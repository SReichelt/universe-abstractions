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
    defIsoType (a b : α) : DefType V (DefIso a b)
    defToHomFun (a b : α) : defIsoType a b ⥤{λ e => ((defIsoType a b).elim e).toHom} (a ⟶ b)

  namespace HasIsomorphismsBase

    section

      variable {α : Sort u} [HasPreorderRelation V α] [h : HasIsomorphismsBase α]

      @[reducible] def DefIsoInst (a b : α) (toHom : a ⟶ b) (invHom : b ⟶ a) :=
        DefType.DefInst (h.defIsoType a b) ⟨toHom, invHom⟩

      namespace DefIsoInst

        notation:20 a:21 " ≃{" toHom:0 "," invHom:0 "} " b:21 =>
          HasPreorderRelation.HasIsomorphismsBase.DefIsoInst a b toHom invHom

        @[reducible] def cast {a b : α} {toHom₁ toHom₂ : a ⟶ b} {invHom₁ invHom₂ : b ⟶ a}
                              (e : a ≃{toHom₁,invHom₁} b) :
            a ≃{toHom₂,invHom₂} b :=
          DefType.DefInst.cast e

      end DefIsoInst

    end

  end HasIsomorphismsBase

  class HasIsomorphisms (α : Sort u) [hα : HasPreorderRelation V α] extends
      HasIsomorphismsBase α where
    defRefl (a : α) : DefType.DefInst (defIsoType a a) (DefIso.refl a)
    defSymm {a b : α} (e : (defIsoType a b).A) :
      DefType.DefInst (defIsoType b a) (DefIso.symm ((defIsoType a b).elim e))
    defSymmFun (a b : α) : defIsoType a b ⥤{λ e => (defSymm e).inst} defIsoType b a
    defTrans {a b c : α} (e : (defIsoType a b).A) (f : (defIsoType b c).A) :
      DefType.DefInst (defIsoType a c)
                      (DefIso.trans ((defIsoType a b).elim e) ((defIsoType b c).elim f))
    defRevTransFun₂ (a b c : α) :
      defIsoType b c ⥤ defIsoType a b ⥤{λ f e => (defTrans e f).inst} (defIsoType a c).A

  namespace HasIsomorphisms

    section

      variable (α : Sort u) [HasPreorderRelation V α] [h : HasIsomorphisms α]

      def isoRel : Prerelation α V := λ a b => h.defIsoType a b

      instance isoRel.isEquivalence : IsEquivalence (isoRel α) where
        refl         a     := (h.defRefl a).inst
        symmFun      a b   := (h.defSymmFun a b).inst
        revTransFun₂ a b c := (h.defRevTransFun₂ a b c).inst

      instance hasEquivalenceRelation : HasEquivalenceRelationBase V α := ⟨isoRel α⟩

    end

    section

      variable {α : Sort u} [HasPreorderRelation V α] [h : HasIsomorphisms α]

      @[reducible] def defIsoInst {a b : α} (e : a ≃ b) : DefIso a b := (h.defIsoType a b).elim e

      @[reducible] def toHom  {a b : α} (e : a ≃ b) : a ⟶ b := (defIsoInst e).toHom
      @[reducible] def invHom {a b : α} (e : a ≃ b) : b ⟶ a := (defIsoInst e).invHom

      @[reducible] def toHomFun (a b : α) : a ≃ b ⥤ (a ⟶ b) := (h.defToHomFun a b).inst
      def invHomFun (a b : α) : a ≃ b ⥤ (b ⟶ a) := toHomFun b a ⊙ HasSymm.symmFun a b

      instance toHom.isFunApp  {a b : α} {e : a ≃ b} : IsFunApp (toHom  e) := ⟨toHomFun  a b, e⟩
      instance invHom.isFunApp {a b : α} {e : a ≃ b} : IsFunApp (invHom e) := ⟨invHomFun a b, e⟩

      instance coeIso {a b : α} (e : DefIso a b) :
          Coe (DefType.DefInst (h.defIsoType a b) e) (a ≃ b) :=
        DefType.DefInst.coeType (h.defIsoType a b) e

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
        defIsoType (a b : α)        := { A    := b ≃ a,
                                         elim := λ e => ⟨(toHom e : b ⟶ a), (invHom e : a ⟶ b)⟩ }
        defToHomFun (a b : α)       := h.defToHomFun b a
        defRefl (a : α)             := ⟨idIso a⟩
        defSymm {a b : α} e         := ⟨(e⁻¹ : a ≃ b)⟩
        defSymmFun (a b : α)        := ⟨(HasSymm.symmFun b a : b ≃ a ⥤ a ≃ b)⟩
        defTrans {a b c : α} e f    := ⟨(e • f : c ≃ a)⟩
        defRevTransFun₂ (a b c : α) := ⟨λ f => ⟨(HasTrans.transFun f a : b ≃ a ⥤ c ≃ a)⟩,
                                        ⟨(HasTrans.transFun₂ c b a : c ≃ b ⥤ b ≃ a ⥤ c ≃ a)⟩⟩

    end

    class IsIsoFunctor {α : Sort u} {β : Sort u'} [hα : HasPreorderRelation V α]
                       [hαIso : HasIsomorphisms α] [hβ : HasPreorderRelation V β]
                       [hβIso : HasIsomorphisms β] (F : PreorderFunctor α β) where
      defIso {a b : α} (e : a ≃ b) : F a ≃{F.hφ (toHom e), F.hφ (invHom e)} F b
      defIsoFun (a b : α) : a ≃ b ⥤{λ e => (defIso e).inst} F a ≃ F b

    namespace IsIsoFunctor

      variable {α : Sort u} {β : Sort u'} [hα : HasPreorderRelation V α] [hαIso : HasIsomorphisms α]
               [hβ : HasPreorderRelation V β] [hβIso : HasIsomorphisms β] (F : PreorderFunctor α β)
               [hFIso : IsIsoFunctor F]

      @[reducible] def iso {a b : α} (e : a ≃ b) : F a ≃ F b := (hFIso.defIso e).inst
      @[reducible] def isoFun (a b : α) : a ≃ b ⥤ F a ≃ F b := (hFIso.defIsoFun a b).inst

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
    defIsoType (a b : α)        := { A    := a ≃ b,
                                     elim := defIsoInst }
    defToHomFun (a b : α)       := HasIdFun.defIdFun
    defRefl (a : α)             := ⟨idIso a⟩
    defSymm {a b : α} e         := ⟨(e⁻¹ : b ≃ a)⟩
    defSymmFun (a b : α)        := ⟨(HasSymm.symmFun a b : a ≃ b ⥤ b ≃ a)⟩
    defTrans {a b c : α} e f    := ⟨(f • e : a ≃ c)⟩
    defRevTransFun₂ (a b c : α) := ⟨λ f => ⟨(HasTrans.revTransFun a f : a ≃ b ⥤ a ≃ c)⟩,
                                    ⟨(HasTrans.revTransFun₂ a b c : b ≃ c ⥤ a ≃ b ⥤ a ≃ c)⟩⟩

end HasEquivalenceRelationBase
