import UniverseAbstractions.CategoryTheory.Basic
import UniverseAbstractions.CategoryTheory.Functors
import UniverseAbstractions.CategoryTheory.NaturalTransformations
import UniverseAbstractions.Axioms.Universe.Singletons



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v vv iv ivv



namespace CategoryTheory

  open Universe MetaRelation MetaFunctor HasTransFun HasSymmFun IsCategoricalPreorder
       HasCatProp HasCatProp.Category HasFunProp HasFunProp.Functor HasIsoRel HasIsoOp HasIsoNat
       HasFunctors

  namespace BundledRelation

    def unitRel (V : Universe.{v, vv}) [IsHomUniverse.{v, vv, iv, ivv} V] [HasTop V] :
      BundledRelation sort.{u} V :=
    { A   := PUnit,
      Hom := unitRelation PUnit (HasTop.Top V) }

    instance unitEquiv (V : Universe.{v, vv}) [IsHomUniverse.{v, vv, iv, ivv} V] [HasTop V] :
      IsEquivalence (unitRel.{u} V).Hom :=
    unitEquivalence PUnit (HasTop.top V)

    def unitGrpoidDesc (V : Universe.{v, vv}) [IsHomUniverse.{v, vv, iv, ivv} V]
                       [hTop : HasInternalTop V] [hTopEq : HasTop.HasTopEq V] :
      GrpoidDesc (unitRel.{u} V) :=
    { homIsEquivalence         := unitEquiv V,
      homHasSymmFun            := ⟨λ _ _   => hTop.defElimFun (HasTop.top V)⟩,
      homHasTransFun           := ⟨λ _ _ _ => ⟨λ _ => hTop.defElimFun (HasTop.top V),
                                               hTop.defElimFun (HasInternalTop.elimFun (HasTop.top V))⟩⟩,
      homIsGroupoidEquivalence := { assoc    := λ _ _ _ => HasInstanceEquivalences.refl (HasTop.top V),
                                    rightId  := λ _     => (hTopEq.topEq _)⁻¹,
                                    leftId   := λ _     => (hTopEq.topEq _)⁻¹,
                                    leftInv  := λ _     => HasInstanceEquivalences.refl (HasTop.top V),
                                    rightInv := λ _     => HasInstanceEquivalences.refl (HasTop.top V) } }

    def emptyRel (V : Universe.{v, vv}) [IsHomUniverse.{v, vv, iv, ivv} V] :
      BundledRelation sort.{u} V :=
    { A   := PEmpty,
      Hom := emptyRelation V }

    def emptyGrpoidDesc (V : Universe.{v, vv}) [IsHomUniverse.{v, vv, iv, ivv} V] :
      GrpoidDesc (emptyRel.{u} V) :=
    { homIsEquivalence         := emptyRelation.isEquivalence         V,
      homHasSymmFun            := emptyRelation.hasSymmFun            V,
      homHasTransFun           := emptyRelation.hasTransFun           V,
      homIsGroupoidEquivalence := emptyRelation.isGroupoidEquivalence V }

  end BundledRelation



  class HasUnitCat (V : Universe.{v, vv}) [IsHomUniverse.{v, vv, iv, ivv} V]
                   [HasInternalTop V] [HasTop.HasTopEq V] [HasCatProp sort.{u} V] where
  (defUnitCat : DefCat (GrpoidDesc.toCatDesc (BundledRelation.unitGrpoidDesc.{u} V)))

  namespace HasUnitCat

    variable (V : Universe.{v, vv}) [IsHomUniverse V] [HasInternalTop V] [HasTop.HasTopEq V]

    section

      variable [HasCatProp sort.{u} V] [h : HasUnitCat V]

      def unitCat : Category sort.{u} V := DefCat.toCategory h.defUnitCat
      def unitObj : unitCat.{u} V := PUnit.unit

      instance hasTop : HasTop (univ sort.{u} V) :=
      { T := unitCat V,
        t := unitObj V }

      def idHomDef : idHom (unitObj V) ≃' HasTop.top V := DefCat.catReflEq (unitObj V)

      def byHomDef {f : unitObj V ⇾ unitObj V} : f ≃ idHom (unitObj V) :=
      (idHomDef V)⁻¹ • HasTop.HasTopEq.topEq f

      def elimFunDesc {A : Category sort.{u} V} (a : A) :
        FunDesc (A := unitCat.{u} V) (B := A) (Function.const PUnit a) :=
      { F  := PreFunctor.unitRelation.preFunctor PUnit (Hom A) a,
        -- TODO: Wrong type class instance picked up?
        hF := sorry } --PreFunctor.unitRelation.isPreorderFunctor PUnit (Hom A) a }

    end

    section

      variable [IsCatUniverse sort.{u} V] [h : HasUnitCat V]

      instance hasTopEq : HasTop.HasTopEq (univ sort.{u} V) :=
      { topEq := λ _ => idIso (unitObj V) }

    end

  end HasUnitCat

  class HasUnitCatFun (V : Universe.{v, vv}) [IsHomUniverse.{v, vv, iv, ivv} V]
                      [HasInternalTop V] [HasTop.HasTopEq V] [IsSortNatUniverse.{u} V] extends
    HasUnitCat V where
  (defElimFun {A : Category sort.{max 1 u v} V} (a : A) : DefFun (HasUnitCat.elimFunDesc V a))

  namespace HasUnitCatFun

    variable (V : Universe.{v, vv}) [IsHomUniverse V] [IsSortNatUniverse.{u} V]
             [HasInternalTop V] [HasTop.HasTopEq V] [h : HasUnitCatFun V]

    def unitCat : IsSortNatUniverse.univ.{u} V := HasUnitCat.unitCat V
    def unitObj : unitCat.{u} V                := HasUnitCat.unitObj V

    def elimFun {A : IsSortNatUniverse.univ.{u} V} (a : A) : unitCat V ⟶ A :=
    DefFun.toFunctor (h.defElimFun a)

    instance hasInternalTop : HasInternalTop (IsSortNatUniverse.univ.{u} V) :=
    { defElimFun := λ a => toDefFun (elimFun V a) }

    def elimFunNatIsoDesc {A : IsSortNatUniverse.univ.{u} V} {a : A} {F : unitCat V ⟶ A}
                          (e : F (unitObj V) ⇿ a) :
      NatIsoDesc F (elimFun V a) :=
    { η        := λ _ => e,
      isToNat  := { nat := λ f => let h₁ : f ≃' idHom (unitObj V) := HasUnitCat.byHomDef V;
                                  (cancelLeftId (toHom e) (mapHomReflEq (elimFun V a) h₁))⁻¹ •
                                  cancelRightId (mapHomReflEq F h₁) (toHom e) },
      isInvNat := { nat := λ f => let h₁ : f ≃' idHom (unitObj V) := HasUnitCat.byHomDef V;
                                  (cancelLeftId (invHom e) (mapHomReflEq F h₁))⁻¹ •
                                  cancelRightId (mapHomReflEq (elimFun V a) h₁) (invHom e) } }

  end HasUnitCatFun

  class HasUnitCatFunNatIso (V : Universe.{v, vv}) [IsHomUniverse.{v, vv, iv, ivv} V]
                            [HasInternalTop V] [HasTop.HasTopEq V] [IsSortNatUniverse.{u} V]
                            extends
    HasUnitCatFun V where
  (defElimFunNatIso {A : Category sort.{max 1 u v} V} {a : A}
                    {F : HasUnitCatFun.unitCat.{u} V ⮕ A}
                    (e : F (HasUnitCatFun.unitObj.{u} V) ⇿ a) :
     DefNatIso (HasUnitCatFun.elimFunNatIsoDesc V e))

  namespace HasUnitCatFunNatIso

    variable (V : Universe.{v, vv}) [IsHomUniverse V] [IsSortNatUniverse.{u} V]
             [HasInternalTop V] [HasTop.HasTopEq V] [h : HasUnitCatFunNatIso V]

    instance hasTopExt : HasInternalTop.HasTopExt (IsSortNatUniverse.univ.{u} V) :=
    { elimFunEq := λ e => (h.defElimFunNatIso e).η }

  end HasUnitCatFunNatIso



  class HasEmptyCat (V : Universe.{v, vv}) [IsHomUniverse.{v, vv, iv, ivv} V]
                    [HasCatProp sort.{u} V] where
  (defEmptyCat : DefCat (GrpoidDesc.toCatDesc (BundledRelation.emptyGrpoidDesc.{u} V)))

  namespace HasEmptyCat

    variable (V : Universe.{v, vv}) [IsHomUniverse V] [HasCatProp sort.{u} V] [h : HasEmptyCat V]

    def emptyCat : Category sort.{u} V := DefCat.toCategory h.defEmptyCat

    instance hasBot : HasBot (univ sort.{u} V) :=
    { B    := emptyCat V,
      elim := λ b _ => PEmpty.elim b }

    def elimFunDesc (A : Category sort.{u} V) : FunDesc (A := emptyCat.{u} V) (B := A) PEmpty.elim :=
    { F  := PreFunctor.emptyRelation.preFunctor (Hom A),
      -- TODO: Wrong type class instance picked up?
      hF := sorry } --PreFunctor.emptyRelation.isPreorderFunctor (Hom A) }

  end HasEmptyCat

  class HasEmptyCatFun (V : Universe.{v, vv}) [IsHomUniverse.{v, vv, iv, ivv} V]
                       [IsSortNatUniverse.{u} V] extends
    HasEmptyCat V where
  (defElimFun (A : Category sort.{max 1 u v} V) : DefFun (HasEmptyCat.elimFunDesc V A))

  namespace HasEmptyCatFun

    variable (V : Universe.{v, vv}) [IsHomUniverse V] [IsSortNatUniverse.{u} V]
             [h : HasEmptyCatFun V]

    def emptyCat : IsSortNatUniverse.univ.{u} V := HasEmptyCat.emptyCat V

    def elimFun (A : IsSortNatUniverse.univ.{u} V) : emptyCat V ⟶ A :=
    DefFun.toFunctor (h.defElimFun A)

    instance hasInternalBot : HasInternalBot (IsSortNatUniverse.univ.{u} V) :=
    { defElimFun := λ A => toDefFun (elimFun V A) }

  end HasEmptyCatFun



  class IsSingletonUniverse (V : Universe.{v, vv}) [IsHomUniverse.{v, vv, iv, ivv} V]
                            [HasInternalTop V] [HasTop.HasTopEq V] [IsSortNatUniverse.{u} V] where
  [hasUnitCat  : HasUnitCatFunNatIso V]
  [hasEmptyCat : HasEmptyCatFun V]

end CategoryTheory
