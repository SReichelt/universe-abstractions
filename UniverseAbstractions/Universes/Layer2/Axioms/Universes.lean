import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations
import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations.AttachedEquivalences
import UniverseAbstractions.Universes.Layer1.Axioms.StandardEquivalences



namespace UniverseAbstractions

set_option autoImplicit false

open Layer1.Prerelation Layer1.HasEquivalences Layer1.HasEquivalenceRelationBase

universe u uu v u' u'' v' w



class HasPropositions (Prp : outParam Universe.{v, u}) [outParam (Layer1.HasLinearLogic Prp)]
                      [outParam (Layer1.HasEquivalences Prp)] (U : Universe.{u, uu}) where
  [hEq (A : U) : Layer1.HasEquivalenceRelation Prp A]

namespace HasPropositions

  variable {Prp U : Universe} [Layer1.HasLinearLogic Prp] [Layer1.HasEquivalences Prp]
           [h : HasPropositions Prp U]

  instance (A : U) : Layer1.HasEquivalenceRelation Prp A := h.hEq A

end HasPropositions



namespace Layer2

  variable {Prp : Universe.{v, u}} [Layer1.HasLinearLogic Prp] [Layer1.HasEquivalences Prp]

  class HasDefEq (α : Sort u') where
    DefEq : α → α → Sort v'
    refl  (a     : α) : DefEq a a
    symm  {a b   : α} : DefEq a b → DefEq b a
    trans {a b c : α} : DefEq a b → DefEq b c → DefEq a c

  namespace HasDefEq

    variable {α : Sort u'} [h : HasDefEq α]

    def lift {ω : Sort w} (l : ω → α) : HasDefEq ω where
      DefEq a b := h.DefEq (l a) (l b)
      refl a    := h.refl (l a)
      symm      := h.symm
      trans     := h.trans

  end HasDefEq

  structure DefType (U : Universe.{u, uu}) [HasPropositions Prp U] (α : Sort u') [hEq : HasDefEq α]
                    extends
      Layer1.DefType U α where
    elimCongrArg {a b : A} : a ≃ b → hEq.DefEq (elim a) (elim b)

  namespace DefType

    instance (U : Universe.{u, uu}) [HasPropositions Prp U] (α : Sort u') [HasDefEq α] :
        Coe (DefType U α) U :=
      ⟨λ A => A.A⟩

    variable {U : Universe.{u, uu}} [HasPropositions Prp U] {α : Sort u'}

    section

      variable [hEq : HasDefEq α]

      @[reducible] def ElimEq {A : DefType U α} (a b : A.A) := hEq.DefEq (A.elim a) (A.elim b)

      def defEqType {A : DefType U α} (a b : A.A) : Layer1.DefType Prp (ElimEq a b) where
        A    := a ≃ b
        elim := A.elimCongrArg

      @[reducible] def DefEquiv {A : DefType U α} (a b : A.A) (eElim : ElimEq a b) :=
        Layer1.DefType.DefInst (defEqType a b) eElim
      notation:25 a:26 " ≃{" eElim:0 "} " b:26 => DefType.DefEquiv a b eElim

      @[reducible] def DefEquiv.e {A : DefType U α} {a b : A.A} {eElim : ElimEq a b}
                                  (e : a ≃{eElim} b) :
          a ≃ b :=
        e.inst

      class HasDefInstEq {A : Layer1.DefType U α} {a : α} (defInst : Layer1.DefType.DefInst A a)
                         where
        e : hEq.DefEq (A.elim defInst.inst) a

      namespace HasDefInstEq

        def triv {A : DefType U α} (inst : A.A) : HasDefInstEq (a := A.elim inst) ⟨inst⟩ :=
          ⟨hEq.refl (A.elim inst)⟩

        def cast {A : DefType U α} {a b : α} (eab : hEq.DefEq a b)
                {defInst : Layer1.DefType.DefInst A.toDefType a}
                (e : HasDefInstEq defInst) :
            HasDefInstEq (Layer1.DefType.DefInst.cast (b := b) defInst) :=
          ⟨hEq.trans e.e eab⟩

      end HasDefInstEq

      structure DefInst (A : DefType U α) (a : α) extends
        Layer1.DefType.DefInst A.toDefType a, HasDefInstEq toDefInst

      namespace DefInst

        instance coeType (A : DefType U α) (a : α) : Coe (DefInst A a) A := ⟨λ i => i.inst⟩

        instance {A : DefType U α} {a : α} (i : DefInst A a) : HasDefInstEq i.toDefInst :=
          i.toHasDefInstEq

        def fromInst {A : DefType U α} (inst : A.A) : DefInst A (A.elim inst) :=
          ⟨⟨inst⟩, HasDefInstEq.triv inst⟩

        def cast {A : DefType U α} {a b : α} (eab : hEq.DefEq a b) (i : DefInst A a) : DefInst A b :=
          ⟨Layer1.DefType.DefInst.cast i.toDefInst, HasDefInstEq.cast eab i.toHasDefInstEq⟩

        @[reducible] def DefInstEquiv {A : DefType U α} {a : α} (i j : DefInst A a) :=
          i.inst ≃{hEq.trans i.e (hEq.symm j.e)} j.inst

      end DefInst

    end

    def map {β : Sort u''} [HasDefEq β] (f : α → β) (A : DefType U α (hEq := HasDefEq.lift f)) :
        DefType U β :=
      let _ := HasDefEq.lift f
      { toDefType    := Layer1.DefType.map A.toDefType f
        elimCongrArg := A.elimCongrArg }

  end DefType

  structure DefTypeWithIntro (U : Universe.{u, uu}) [HasPropositions Prp U] (α : Sort u')
                             [hEq : HasDefEq α] extends
      DefType U α where
    defInst (a : α) : DefType.DefInst toDefType_1 a

  namespace DefTypeWithIntro
    
    instance (U : Universe.{u, uu}) [HasPropositions Prp U] (α : Sort u') [HasDefEq α] :
        Coe (DefTypeWithIntro U α) U :=
      ⟨λ A => A.A⟩

    variable {U : Universe.{u, uu}} [HasPropositions Prp U] {α : Sort u'} [HasDefEq α]

    @[reducible] def inst (A : DefTypeWithIntro U α) (a : α) : A.A := (A.defInst a).inst

  end DefTypeWithIntro

end Layer2
