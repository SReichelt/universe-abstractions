import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations.AttachedRelations
import UniverseAbstractions.Universes.Layer1.Axioms.Equivalences



namespace UniverseAbstractions.Layer1

set_option autoImplicit false

universe u

open HasEquivalenceRelationBase



class HasEquivalenceRelation (V : outParam Universe) [outParam (HasLinearLogic V)]
                             [outParam (HasEquivalences V)] (α : Sort u) extends
  HasEquivalenceRelationBase V α, HasEquivRelEquivalences α
