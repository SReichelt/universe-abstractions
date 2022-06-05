import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations
import UniverseAbstractions.Universes.Layer1.Instances.Utils.DerivedUniverses
import UniverseAbstractions.Universes.Layer1.Meta.ExprUniverse



namespace UniverseAbstractions.Layer1.Meta

set_option autoBoundImplicitLocal false

open Lean Lean.Meta Prerelation



@[reducible] def optionalExprUniverse {β : Type} (inst : β → _Sort) : Universe.{1, 1} :=
functionUniverse (optionUniverse (exprUniverse inst))



-- We can optimize equivalence relations of expressions by using a distinct value (`none`) for
-- `refl` that we can treat specially in all operations.
-- In particular, we can use `none` for all terms that are defeq.

def optionalRelation {α β : Type} {inst : β → _Sort} (R : Prerelation α (exprUniverse inst)) :
    Prerelation α (optionalExprUniverse inst) :=
  λ a b => BinaryTree.leaf (R a b)

namespace optionalRelation

  variable {α β : Type} {inst : β → _Sort} [HasFunctors (exprUniverse inst)]
           (R : Prerelation α (exprUniverse inst))

  instance hasRefl : HasRefl (optionalRelation R) := ⟨λ _ => none⟩

  instance hasSymm [HasSymm R] : HasSymm (optionalRelation R) :=
    ⟨λ a b f => match f with
                | some f' => some f'⁻¹
                | none    => none⟩

  instance hasTrans [HasTrans R] : HasTrans (optionalRelation R) :=
    ⟨λ a b c f g => match f, g with
                    | some f', some g' => some (g' • f')
                    | some f', none    => some f'
                    | none,    some g' => some g'
                    | none,    none    => none⟩

  instance isPreorder [HasTrans R] : IsPreorder (optionalRelation R) := ⟨⟩
  instance isEquivalence [HasSymm R] [HasTrans R] : IsEquivalence (optionalRelation R) := ⟨⟩

  def materialize [HasRefl R] {a b : α} : (optionalRelation R) a b → R a b
    | some e => e
    | none   => HasRefl.refl (R := R) a

end optionalRelation
