import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Properties



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w w'



-- TODO require const pi to functor

class HasUniversality (U : Universe.{u}) [HasGeneralizedProperties.{u, v, w} U] (V : Universe.{v}) :
  Type (max u v w) where
(IsUniv {α : U} {P : HasGeneralizedProperties.Property V α} : HasGeneralizedProperties.Pi P → Sort w)

namespace HasUniversality

  structure Pi {U : Universe.{u}} [HasGeneralizedProperties.{u, v, w} U] {V : Universe.{v}}
               [h : HasUniversality.{u, v, w} U V] {α : U} (P : HasGeneralizedProperties.Property V α) :
    Sort (max 1 u v w) where
  (f      : HasGeneralizedProperties.Pi P)
  (isUniv : h.IsUniv f)

  variable {U : Universe.{u}} [HasGeneralizedProperties.{u, v, w} U] {V : Universe.{v}}
           [h : HasUniversality.{u, v, w} U V] {α : U} (P : HasGeneralizedProperties.Property V α)

  instance coeFun : CoeFun (Pi P) (λ _ => HasGeneralizedProperties.Pi P) := ⟨Pi.f⟩

end HasUniversality



class HasPiTypes (U : Universe.{u}) [HasGeneralizedProperties.{u, v, w'} U] (V : Universe.{v})
                 (W : outParam Universe.{w})
  extends HasUniversality.{u, v, w'} U V : Type (max u v w w') where
[embed {α : U} (P : HasGeneralizedProperties.Property V α) : HasEmbeddedType.{w, max 1 u v w'} W (HasUniversality.Pi P)]

namespace HasPiTypes

  variable {U : Universe} [HasGeneralizedProperties U] {V W : Universe} [h : HasPiTypes U V W]

  instance hasEmbeddedType {α : U} (P : HasGeneralizedProperties.Property V α) :
    HasEmbeddedType W (HasUniversality.Pi P) :=
  h.embed P

  def Pi {α : U} (P : HasGeneralizedProperties.Property V α) : W :=
  HasEmbeddedType.EmbeddedType W (HasUniversality.Pi P)

  variable {α : U} {P : HasGeneralizedProperties.Property V α}

  def toExternal   (F : Pi P)                 : HasUniversality.Pi P := HasEmbeddedType.toExternal   W F
  def fromExternal (F : HasUniversality.Pi P) : Pi P                 := HasEmbeddedType.fromExternal W F

  def funCoe (F : Pi P) : HasGeneralizedProperties.Pi P := (toExternal F).f
  instance coeFun : CoeFun ⌈Pi P⌉ (λ _ => HasGeneralizedProperties.Pi P) := ⟨funCoe⟩

  @[simp] theorem fromToExternal (F : Pi P)                 : fromExternal (toExternal F) = F := HasEmbeddedType.fromToExternal W F
  @[simp] theorem toFromExternal (F : HasUniversality.Pi P) : toExternal (fromExternal F) = F := HasEmbeddedType.toFromExternal W F

  @[simp] theorem toExternal.eff   (F : Pi P)                 (a : α) : (toExternal   F) a = F a := rfl
  @[simp] theorem fromExternal.eff (F : HasUniversality.Pi P) (a : α) : (fromExternal F) a = F a :=
  congrFun (congrArg HasUniversality.Pi.f (toFromExternal F)) a

end HasPiTypes



class HasEmbeddedPiTypes (U : Universe.{u}) [HasGeneralizedProperties.{u, v, w} U] (V : Universe.{v})
  extends HasPiTypes.{u, v, v, w} U V V
