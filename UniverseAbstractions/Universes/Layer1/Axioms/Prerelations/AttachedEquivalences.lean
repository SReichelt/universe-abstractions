import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations.AttachedRelations
import UniverseAbstractions.Universes.Layer1.Axioms.Equivalences



namespace UniverseAbstractions.Layer1

set_option autoBoundImplicitLocal false

universe u



class HasEquivalenceRelation (V : outParam Universe) [outParam (HasLinearLogic V)]
                             [outParam (HasEquivalences V)] (α : Sort u) extends
  HasEquivalenceRelationBase V α, HasEquivRelEquivalences α
