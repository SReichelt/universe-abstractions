import UniverseAbstractions.Universes.Layer1.Axioms.Universes
import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations
import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations.AttachedEquivalences
import UniverseAbstractions.Universes.Layer1.Axioms.StandardEquivalences



namespace UniverseAbstractions.Layer2

set_option autoImplicit false

open Layer1.Prerelation Layer1.HasEquivalences Layer1.HasEquivalenceRelationBase

universe u uu v u' v'



class HasPropositions (V : outParam Layer1.Universe.{v, u}) [outParam (Layer1.HasLinearLogic V)]
                      [outParam (Layer1.HasEquivalences V)] (U : Layer1.Universe.{u, uu}) where
  [hEq (A : U) : Layer1.HasEquivalenceRelation V A]

namespace HasPropositions

  variable {V U : Layer1.Universe} [Layer1.HasLinearLogic V] [Layer1.HasEquivalences V]
           [h : HasPropositions V U]

  instance (A : U) : Layer1.HasEquivalenceRelation V A := h.hEq A

end HasPropositions


structure Universe extends Layer1.Universe.{u, uu} where
  V : Layer1.Universe.{v, u}
  [hV : Layer1.IsPositiveUniverse V]
  [hProp : HasPropositions V toUniverse]

namespace Universe

  instance : Coe Universe Layer1.Universe := ⟨Universe.toUniverse⟩

  instance hasInstances : Layer1.HasInstances.{uu, (max u uu v) + 1} Universe.{u, uu, v} :=
    ⟨λ U => U.I⟩

  section

    variable (U : Universe.{u, uu})

    instance instInst : Layer1.HasInstances.{u, uu} U.I := Layer1.Universe.instInst U
    instance : Layer1.HasInstances U := instInst U

    instance : Layer1.IsPositiveUniverse U.V := U.hV
    instance : HasPropositions U.V U := U.hProp

  end

  @[reducible] def fromLayer1 (U : Layer1.Universe) {V : Layer1.Universe}
                              [Layer1.IsPositiveUniverse V] [HasPropositions V U] :
      Universe :=
    ⟨U, V⟩

  section

    variable {U : Universe}

    instance (A : U) : Layer1.HasEquivalenceRelation U.V A := U.hProp.hEq A

  end

  class HasDefEq (α : Sort u') where
    DefEq : α → α → Sort v'
    refl  (a     : α) : DefEq a a
    symm  {a b   : α} : DefEq a b → DefEq b a
    trans {a b c : α} : DefEq a b → DefEq b c → DefEq a c

  structure DefType (U : Universe.{u, uu, v}) (α : Sort u') [hEq : HasDefEq α] extends
      Layer1.Universe.DefType U α where
    elimCongrArg {a b : A} : a ≃ b → hEq.DefEq (elim a) (elim b)

  namespace DefType

    instance (U : Universe.{u, uu, v}) (α : Sort u') [HasDefEq α] : Coe (DefType U α) U :=
      ⟨λ A => A.A⟩

    variable {U : Universe.{u, uu, v}} {α : Sort u'} [hEq : HasDefEq α]

    @[reducible] def ElimEq {A : DefType U α} (a b : A.A) := hEq.DefEq (A.elim a) (A.elim b)

    def defEqType {A : DefType U α} (a b : A.A) :
        Layer1.Universe.DefType U.V (ElimEq a b) where
      A    := a ≃ b
      elim := A.elimCongrArg

    @[reducible] def DefEquiv {A : DefType U α} (a b : A.A) (eElim : ElimEq a b) :=
      Layer1.Universe.DefType.DefInst (defEqType a b) eElim
    notation:25 a:26 " ≃{" eElim:0 "} " b:26 => Universe.DefType.DefEquiv a b eElim

    @[reducible] def DefEquiv.e {A : DefType U α} {a b : A.A} {eElim : ElimEq a b}
                                (e : a ≃{eElim} b) :
        a ≃ b :=
      e.inst

    class HasDefInstEq {A : Layer1.Universe.DefType U α} {a : α}
                       (defInst : Layer1.Universe.DefType.DefInst A a) where
      e : hEq.DefEq (A.elim defInst.inst) a

    namespace HasDefInstEq

      def triv {A : DefType U α} (inst : A.A) : HasDefInstEq (a := A.elim inst) ⟨inst⟩ :=
        ⟨hEq.refl (A.elim inst)⟩

      def cast {A : DefType U α} {a b : α} (eab : hEq.DefEq a b)
               {defInst : Layer1.Universe.DefType.DefInst A.toDefType a}
               (e : HasDefInstEq defInst) :
          HasDefInstEq (Layer1.Universe.DefType.DefInst.cast (b := b) defInst) :=
        ⟨hEq.trans e.e eab⟩

    end HasDefInstEq

    structure DefInst (A : DefType U α) (a : α) extends
      Layer1.Universe.DefType.DefInst A.toDefType a, HasDefInstEq toDefInst

    namespace DefInst

      instance coeType (A : DefType U α) (a : α) : Coe (DefInst A a) A := ⟨λ i => i.inst⟩

      instance {A : DefType U α} {a : α} (i : DefInst A a) : HasDefInstEq i.toDefInst :=
        i.toHasDefInstEq

      def fromInst {A : DefType U α} (inst : A.A) : DefInst A (A.elim inst) :=
        ⟨⟨inst⟩, HasDefInstEq.triv inst⟩

      def cast {A : DefType U α} {a b : α} (eab : hEq.DefEq a b) (i : DefInst A a) : DefInst A b :=
        ⟨Layer1.Universe.DefType.DefInst.cast i.toDefInst, HasDefInstEq.cast eab i.toHasDefInstEq⟩

      @[reducible] def DefInstEquiv {A : DefType U α} {a : α} (i j : DefInst A a) :=
        i.inst ≃{hEq.trans i.e (hEq.symm j.e)} j.inst

    end DefInst

  end DefType

  structure DefTypeWithIntro (U : Universe.{u, uu, v}) (α : Sort u') [hEq : HasDefEq α] extends
      DefType U α where
    defInst (a : α) : DefType.DefInst toDefType_1 a

  namespace DefTypeWithIntro
    
    instance (U : Universe.{u, uu, v}) (α : Sort u') [HasDefEq α] : Coe (DefTypeWithIntro U α) U :=
      ⟨λ A => A.A⟩

    variable {U : Universe.{u, uu, v}} {α : Sort u'} [HasDefEq α]

    @[reducible] def inst (A : DefTypeWithIntro U α) (a : α) : A.A := (A.defInst a).inst

  end DefTypeWithIntro

end Universe
