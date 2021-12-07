import UniverseAbstractions.Axioms.Universes



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w



def MetaProperty (α : Sort u) (V : Universe.{v}) := α → V

namespace MetaProperty

  variable {α : Sort u} {V : Universe} (P : MetaProperty α V)

  class HasInst where
  (inst (a : α) : P a)

  -- TODO: I think "lift" is not the correct word for this.
  @[reducible] def lift {ω : Sort w} (l : ω → α) : MetaProperty ω V := λ a => P (l a)

  namespace lift

    variable {ω : Sort w} (l : ω → α)

    instance hasInst [h : HasInst P] : HasInst (lift P l) := ⟨λ a => h.inst (l a)⟩

  end lift

end MetaProperty

def MetaProperty.nativeProperty {α : Sort u} (p : α → Prop) : MetaProperty α prop := p

def MetaProperty.unitProperty (α : Sort u) {V : Universe.{v}} (B : V) :
  MetaProperty α V :=
λ _ => B

def MetaProperty.unitSatisfied (α : Sort u) {V : Universe.{v}} {B : V} (b : B) :
  HasInst (MetaProperty.unitProperty α B) :=
{ inst  := λ _ => b }



def DependentMetaProperty {U : Universe.{u}} {V : Universe.{v}} (P : MetaProperty ⌈U⌉ V)
                          (W : Universe.{w}) :=
∀ {A}, P A → (A → W)

namespace DependentMetaProperty

  open MetaProperty

  variable {U V W : Universe} {P : MetaProperty ⌈U⌉ V} (Q : DependentMetaProperty P W)

  class HasDependentInst [h : HasInst P] where
  (inst {A : U} (a : A) : Q (h.inst A) a)

  def instProp [h : HasInst P] (A : U) : MetaProperty ⌈A⌉ W := Q (h.inst A)
  instance [HasInst P] [h : HasDependentInst Q] (A : U) : HasInst (instProp Q A) := ⟨h.inst⟩

end DependentMetaProperty
