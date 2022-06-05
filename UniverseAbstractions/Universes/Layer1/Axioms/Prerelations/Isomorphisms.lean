import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations.AttachedRelations



namespace UniverseAbstractions.Layer1

set_option autoBoundImplicitLocal false

open Universe HasFunctors Prerelation HasPreorderRelation HasEquivalenceRelationBase

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

  class HasIsomorphisms (α : Sort u) [hα : HasPreorderRelation V α] where
    defIso (a b : α) : DefType V (DefIso a b)
    defToHomFun (a b : α) : defIso a b ⥤{λ e => ((defIso a b).elim e).toHom} (a ⟶ b)
    defRefl (a : α) : DefType.DefInst (defIso a a) (DefIso.refl a)
    defSymm {a b : α} (e : (defIso a b).A) :
      DefType.DefInst (defIso b a) (DefIso.symm ((defIso a b).elim e))
    defSymmFun (a b : α) : defIso a b ⥤{λ e => (defSymm e).inst} defIso b a
    defTrans {a b c : α} (e : (defIso a b).A) (f : (defIso b c).A) :
      DefType.DefInst (defIso a c) (DefIso.trans ((defIso a b).elim e) ((defIso b c).elim f))
    defRevTransFun₂ (a b c : α) :
      defIso b c ⥤ defIso a b ⥤{λ f e => (defTrans e f).inst} (defIso a c).A

  namespace HasIsomorphisms

    section

      variable (α : Sort u) [HasPreorderRelation V α] [h : HasIsomorphisms α]

      def isoRel : Prerelation α V := λ a b => h.defIso a b

      instance isoRel.isEquivalence : IsEquivalence (isoRel α) where
        refl         a     := (h.defRefl a).inst
        symmFun      a b   := (h.defSymmFun a b).inst
        revTransFun₂ a b c := (h.defRevTransFun₂ a b c).inst

      instance hasEquivalenceRelation : HasEquivalenceRelationBase V α := ⟨isoRel α⟩

    end

    section

      variable {α : Sort u} [HasPreorderRelation V α] [h : HasIsomorphisms α]

      @[reducible] def defIsoInst {a b : α} (e : a ≃ b) : DefIso a b := (h.defIso a b).elim e

      @[reducible] def toHom  {a b : α} (e : a ≃ b) : a ⟶ b := (defIsoInst e).toHom
      @[reducible] def invHom {a b : α} (e : a ≃ b) : b ⟶ a := (defIsoInst e).invHom

      @[reducible] def toHomFun (a b : α) : a ≃ b ⟶ (a ⟶ b) := (h.defToHomFun a b).inst
      def invHomFun (a b : α) : a ≃ b ⟶ (b ⟶ a) := toHomFun b a • HasSymm.symmFun a b

      instance toHom.isFunApp {a b : α} {e : a ≃ b} : IsFunApp (a ≃ b) (toHom e) :=
        ⟨toHomFun a b, e⟩

      instance invHom.isFunApp {a b : α} {e : a ≃ b} : IsFunApp (a ≃ b) (invHom e) :=
        ⟨invHomFun a b, e⟩

      instance coeIso {a b : α} (e : DefIso a b) : Coe (DefType.DefInst (h.defIso a b) e) (a ≃ b) :=
        DefType.DefInst.coeType (h.defIso a b) e

      @[reducible] def DefIsoInst (a b : α) (toHom : a ⟶ b) (invHom : b ⟶ a) :=
        DefType.DefInst (h.defIso a b) ⟨toHom, invHom⟩

      namespace DefIsoInst

        notation:20 a:21 " ≃{" toHom:0 "," invHom:0 "} " b:21 =>
          HasPreorderRelation.HasIsomorphisms.DefIsoInst a b toHom invHom

        @[reducible] def cast {a b : α} {toHom₁ toHom₂ : a ⟶ b} {invHom₁ invHom₂ : b ⟶ a}
                              (e : a ≃{toHom₁,invHom₁} b) :
            a ≃{toHom₂,invHom₂} b :=
          DefType.DefInst.cast e

      end DefIsoInst

    end

    section

      variable (α : Sort u) [HasPreorderRelation V α] [h : HasIsomorphisms α]

      def toHomFunctor : PreorderFunctor (α := asPreorder α) (@id α) := ⟨toHomFun (h := h)⟩

      def invHomFunctor : PreorderFunctor (α := asPreorder α) (β := opposite α) (@id α) :=
        ⟨invHomFun (h := h)⟩

      instance opposite.hasIsomorphisms : HasIsomorphisms (opposite α) where
        defIso (a b : α)            := { A    := b ≃ a,
                                         elim := λ e => ⟨(toHom e : b ⟶ a), (invHom e : a ⟶ b)⟩ }
        defToHomFun (a b : α)       := h.defToHomFun b a
        defRefl (a : α)             := ⟨idIso a⟩
        defSymm {a b : α} e         := ⟨(e⁻¹ : a ≃ b)⟩
        defSymmFun (a b : α)        := ⟨(HasSymm.symmFun b a : b ≃ a ⟶ a ≃ b)⟩
        defTrans {a b c : α} e f    := ⟨(e • f : c ≃ a)⟩
        defRevTransFun₂ (a b c : α) := ⟨λ f => ⟨(HasTrans.transFun f a : b ≃ a ⟶ c ≃ a)⟩,
                                        ⟨(HasTrans.transFun₂ c b a : c ≃ b ⟶ b ≃ a ⟶ c ≃ a)⟩⟩

    end

    class IsIsoFunctor {α : Sort u} {β : Sort u'} [hα : HasPreorderRelation V α]
                       [hαIso : HasIsomorphisms α] [hβ : HasPreorderRelation V β]
                       [hβIso : HasIsomorphisms β] {φ : α → β} (F : PreorderFunctor φ) where
      defIso {a b : α} (e : a ≃ b) : φ a ≃{F (toHom e), F (invHom e)} φ b
      defIsoFun (a b : α) : a ≃ b ⥤{λ e => (defIso e).inst} φ a ≃ φ b

    namespace IsIsoFunctor

      variable {α : Sort u} {β : Sort u'} [hα : HasPreorderRelation V α] [hαIso : HasIsomorphisms α]
               [hβ : HasPreorderRelation V β] [hβIso : HasIsomorphisms β] {φ : α → β}
               (F : PreorderFunctor φ) [hFIso : IsIsoFunctor F]

      @[reducible] def iso {a b : α} (e : a ≃ b) : φ a ≃ φ b := (hFIso.defIso e).inst
      @[reducible] def isoFun (a b : α) : a ≃ b ⟶ φ a ≃ φ b := (hFIso.defIsoFun a b).inst

      instance iso.isFunApp {a b : α} {e : a ≃ b} : IsFunApp (a ≃ b) (iso F e) :=
        ⟨isoFun F a b, e⟩

      @[reducible] def iso.opposite {a b : opposite α} (e : b ≃ a) : φ a ≃ φ b := iso F e

      def toEquivalenceFunctor : EquivalenceFunctor φ := ⟨isoFun F (hα := hα)⟩

    end IsIsoFunctor

    class IsIsoFunctor₂ {α : Sort u} {β : Sort u'} {γ : Sort u''} [hα : HasPreorderRelation V α]
                        [hαIso : HasIsomorphisms α] [hβ : HasPreorderRelation V β]
                        [hβIso : HasIsomorphisms β] [hγ : HasPreorderRelation V γ]
                        [hγIso : HasIsomorphisms γ] {φ : α → β → γ} (F : PreorderFunctor₂ φ) where
      [app  (a : α) : IsIsoFunctor (F.app  a)]
      [app₂ (b : β) : IsIsoFunctor (F.app₂ b)]

    namespace IsIsoFunctor₂

      variable {α : Sort u} {β : Sort u'} {γ : Sort u''} [hα : HasPreorderRelation V α]
               [hαIso : HasIsomorphisms α] [hβ : HasPreorderRelation V β]
               [hβIso : HasIsomorphisms β] [hγ : HasPreorderRelation V γ]
               [hγIso : HasIsomorphisms γ] {φ : α → β → γ} (F : PreorderFunctor₂ φ)
               [hFIso : IsIsoFunctor₂ F]

      instance (a : α) : IsIsoFunctor (F.app  a) := hFIso.app  a
      instance (b : β) : IsIsoFunctor (F.app₂ b) := hFIso.app₂ b

      def toEquivalenceFunctor₂ : EquivalenceFunctor₂ φ where
        app  a := IsIsoFunctor.toEquivalenceFunctor (F.app  a)
        app₂ b := IsIsoFunctor.toEquivalenceFunctor (F.app₂ b)

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
    defIso (a b : α)            := { A    := a ≃ b,
                                     elim := defIsoInst }
    defToHomFun (a b : α)       := HasIdFun.defIdFun
    defRefl (a : α)             := ⟨idIso a⟩
    defSymm {a b : α} e         := ⟨(e⁻¹ : b ≃ a)⟩
    defSymmFun (a b : α)        := ⟨(HasSymm.symmFun a b : a ≃ b ⟶ b ≃ a)⟩
    defTrans {a b c : α} e f    := ⟨(f • e : a ≃ c)⟩
    defRevTransFun₂ (a b c : α) := ⟨λ f => ⟨(HasTrans.revTransFun a f : a ≃ b ⟶ a ≃ c)⟩,
                                    ⟨(HasTrans.revTransFun₂ a b c : b ≃ c ⟶ a ≃ b ⟶ a ≃ c)⟩⟩

end HasEquivalenceRelationBase
