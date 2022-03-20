import UniverseAbstractions.CategoryTheory.Basic
import UniverseAbstractions.CategoryTheory.Functors
import UniverseAbstractions.CategoryTheory.NaturalTransformations
import UniverseAbstractions.CategoryTheory.MultiFunctors



set_option autoBoundImplicitLocal false
set_option maxHeartbeats 100000
--set_option pp.universes true

universe u w ww iw iww



namespace CategoryTheory

  open MetaRelation HasTransFun IsAssociative IsCategoricalPreorder
       HasCatProp HasCatProp.Category HasFunProp HasFunProp.Functor HasNatRel HasNatOp HasNatOpEquiv HasNaturality
       HasIsoRel HasIsoOp HasIsomorphisms HasIsoPreFun HasIsoNat HasIsoNaturality
       HasFunctors HasCongrArg

  namespace IsSortNatUniverse

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W] [IsSortNatUniverse.{u} W]

    section

      variable {A B C : univ.{u} W}

      structure NatNatIsoDesc (F G : A ⟶ B ⟶ C) (η : ∀ a, F a ⇿ G a) where
      (toDesc  : NatNatDesc F G (λ a => toHom  (η a)))
      (invDesc : NatNatDesc G F (λ a => invHom (η a)))

      namespace NatNatIsoDesc

        def strict {φ : A → B → C} {F' G' : ∀ a, HasFunProp.Fun (φ a)}
                   {hEq : ∀ a, NatDesc.StrictNaturality (F' a) (G' a)}
                   {η : ∀ a, StrictDefNatIso (hEq a)}
                   {F : HasFunProp.Fun (B := B ⟶ C) (λ a => ⟨F' a⟩)}
                   {G : HasFunProp.Fun (B := B ⟶ C) (λ a => ⟨G' a⟩)}
                   (hNatEq : NatNatDesc.StrictNaturality₂ F G) :
          NatNatIsoDesc ⟨F⟩ ⟨G⟩ (λ a => (η a).η) :=
        { toDesc  := { natEq := λ {a₁ a₂} f b => (cancelRightId (byStrictNatIsoToHomDef (η := η a₁))
                                                                (nat (mapHom ⟨G⟩ f) b))⁻¹ •
                                                 hNatEq f b •
                                                 cancelLeftId (nat (mapHom ⟨F⟩ f) b)
                                                              (byStrictNatIsoToHomDef (η := η a₂)) },
          invDesc := { natEq := λ {a₁ a₂} f b => (cancelRightId (byStrictNatIsoInvHomDef (η := η a₁))
                                                                (nat (mapHom ⟨F⟩ f) b))⁻¹ •
                                                 (hNatEq f b)⁻¹ •
                                                 cancelLeftId (nat (mapHom ⟨G⟩ f) b)
                                                              (byStrictNatIsoInvHomDef (η := η a₂)) } }

      end NatNatIsoDesc

      section

        variable {F G : A ⟶ B ⟶ C} {η : ∀ a, F a ⇿ G a}

        structure DefNatNatIsoBase (desc : NatNatIsoDesc F G η) where
        (toDefNatNat  : DefNatNatBase desc.toDesc)
        (invDefNatNat : DefNatNatBase desc.invDesc)

        namespace DefNatNatIsoBase

          def trivial {desc : NatNatIsoDesc F G η} [HasTrivialNatEquiv B C] :
            DefNatNatIsoBase desc :=
          { toDefNatNat  := DefNatNatBase.trivial,
            invDefNatNat := DefNatNatBase.trivial }

          variable {desc : NatNatIsoDesc F G η} (ε : DefNatNatIsoBase desc)

          def natIsoDesc : NatIsoDesc F G :=
          { η        := η,
            isToNat  := { nat := ε.toDefNatNat.natEquiv },
            isInvNat := { nat := ε.invDefNatNat.natEquiv } }

        end DefNatNatIsoBase

        structure DefNatNatIso (desc : NatNatIsoDesc F G η) extends
          DefNatNatIsoBase desc, DefNatIso (DefNatNatIsoBase.natIsoDesc toDefNatNatIsoBase)

        namespace DefNatNatIso

          variable {desc : NatNatIsoDesc F G η}

          def trivial (ε : DefNatNatIsoBase desc) [HasTrivialIsoNaturalityCondition A (B ⟶ C)] :
            DefNatNatIso desc :=
          { toDefNatNatIsoBase := ε,
            toDefNatIso        := HasTrivialIsoNaturalityCondition.defNatIso }

        end DefNatNatIso

        section

          variable {desc : NatNatIsoDesc F G η} {ε : DefNatNatIso desc} {a : A}

          def byNatNatIsoDef : natIso ε.η a ≃' η a := byNatIsoDef

          def byNatNatIsoToHomDef  : nat (toHom  ε.η) a ≃' toHom  (η a) := byNatIsoToHomDef
          def byNatNatIsoInvHomDef : nat (invHom ε.η) a ≃' invHom (η a) := byNatIsoInvHomDef

        end

      end

      section

        variable {φ : A → B → C} {F' G' : ∀ a, HasFunProp.Fun (φ a)}
                 {hEq : ∀ a, NatDesc.StrictNaturality (F' a) (G' a)}

        def StrictDefNatNatIso (η : ∀ a, StrictDefNatIso (hEq a))
                               {F : HasFunProp.Fun (B := B ⟶ C) (λ a => ⟨F' a⟩)}
                               {G : HasFunProp.Fun (B := B ⟶ C) (λ a => ⟨G' a⟩)}
                               (hNatEq : NatNatDesc.StrictNaturality₂ F G) :=
        DefNatNatIso (NatNatIsoDesc.strict (η := η) hNatEq)

        variable {η : ∀ a, StrictDefNatIso (hEq a)}
                 {F : HasFunProp.Fun (B := B ⟶ C) (λ a => ⟨F' a⟩)}
                 {G : HasFunProp.Fun (B := B ⟶ C) (λ a => ⟨G' a⟩)}
                 {hNatEq : NatNatDesc.StrictNaturality₂ F G}
                 {ε : StrictDefNatNatIso η hNatEq} {a : A} {b : B}

        def byStrictNatNatIsoDef : natIso (natIso ε.η a) b ≃ idIso (φ a b) :=
        byStrictNatIsoDef • natIsoCongrArg (byNatNatIsoDef (ε := ε)) b

        def byStrictNatNatIsoToHomDef  : nat (nat (toHom  ε.η) a) b ≃ idHom (φ a b) :=
        byStrictNatIsoToHomDef  • natCongrArg (byNatNatIsoToHomDef  (ε := ε)) b

        def byStrictNatNatIsoInvHomDef : nat (nat (invHom ε.η) a) b ≃ idHom (φ a b) :=
        byStrictNatIsoInvHomDef • natCongrArg (byNatNatIsoInvHomDef (ε := ε)) b

      end

    end

    section

      variable {A B C D : univ.{u} W}

      structure NatNatNatIsoDesc (F G : A ⟶ B ⟶ C ⟶ D) (η : ∀ a, F a ⇿ G a) where
      (toDesc  : NatNatNatDesc F G (λ a => toHom  (η a)))
      (invDesc : NatNatNatDesc G F (λ a => invHom (η a)))

      namespace NatNatNatIsoDesc

        def strict {φ : A → B → C → D} {F'' G'' : ∀ a b, HasFunProp.Fun (φ a b)}
                   {hEq : ∀ a b, NatDesc.StrictNaturality (F'' a b) (G'' a b)}
                   {η' : ∀ a b, StrictDefNatIso (hEq a b)}
                   {F' : ∀ a, HasFunProp.Fun (B := C ⟶ D) (λ b => ⟨F'' a b⟩)}
                   {G' : ∀ a, HasFunProp.Fun (B := C ⟶ D) (λ b => ⟨G'' a b⟩)}
                   {hNatEq : ∀ a, NatNatDesc.StrictNaturality₂ (F' a) (G' a)}
                   {η : ∀ a, StrictDefNatNatIso (η' a) (hNatEq a)}
                   {F : HasFunProp.Fun (B := B ⟶ C ⟶ D) (λ a => ⟨F' a⟩)}
                   {G : HasFunProp.Fun (B := B ⟶ C ⟶ D) (λ a => ⟨G' a⟩)}
                   (hNatNatEq : NatNatNatDesc.StrictNaturality₃ F G) :
          NatNatNatIsoDesc ⟨F⟩ ⟨G⟩ (λ a => (η a).η) :=
        { toDesc  := { natNatEq := λ {a₁ a₂} f b c => (cancelRightId (byStrictNatNatIsoToHomDef (ε := η a₁))
                                                                     (nat (nat (mapHom ⟨G⟩ f) b) c))⁻¹ •
                                                      hNatNatEq f b c •
                                                      cancelLeftId (nat (nat (mapHom ⟨F⟩ f) b) c)
                                                                   (byStrictNatNatIsoToHomDef (ε := η a₂)) },
          invDesc := { natNatEq := λ {a₁ a₂} f b c => (cancelRightId (byStrictNatNatIsoInvHomDef (ε := η a₁))
                                                                     (nat (nat (mapHom ⟨F⟩ f) b) c))⁻¹ •
                                                      (hNatNatEq f b c)⁻¹ •
                                                      cancelLeftId (nat (nat (mapHom ⟨G⟩ f) b) c)
                                                                   (byStrictNatNatIsoInvHomDef (ε := η a₂)) } }

      end NatNatNatIsoDesc

      section

        variable {F G : A ⟶ B ⟶ C ⟶ D} {η : ∀ a, F a ⇿ G a}

        structure DefNatNatNatIsoBase (desc : NatNatNatIsoDesc F G η) where
        (toDefNatNatNat  : DefNatNatNatBase desc.toDesc)
        (invDefNatNatNat : DefNatNatNatBase desc.invDesc)

        namespace DefNatNatNatIsoBase

          def trivial {desc : NatNatNatIsoDesc F G η} [HasTrivialNatEquiv C D] :
            DefNatNatNatIsoBase desc :=
          { toDefNatNatNat  := DefNatNatNatBase.trivial,
            invDefNatNatNat := DefNatNatNatBase.trivial }

          variable {desc : NatNatNatIsoDesc F G η} (ε : DefNatNatNatIsoBase desc)

          def natNatIsoDesc : NatNatIsoDesc F G η :=
          { toDesc  := DefNatNatNatBase.natNatDesc ε.toDefNatNatNat,
            invDesc := DefNatNatNatBase.natNatDesc ε.invDefNatNatNat }

        end DefNatNatNatIsoBase

        structure DefNatNatNatIso (desc : NatNatNatIsoDesc F G η) extends
          DefNatNatNatIsoBase desc,
          DefNatNatIso (DefNatNatNatIsoBase.natNatIsoDesc toDefNatNatNatIsoBase)

        namespace DefNatNatNatIso

          variable {desc : NatNatNatIsoDesc F G η}

          def trivial (ε : DefNatNatNatIsoBase desc)
                      (θ : DefNatNatIsoBase (DefNatNatNatIsoBase.natNatIsoDesc ε))
                      [HasTrivialIsoNaturalityCondition A (B ⟶ C ⟶ D)] :
            DefNatNatNatIso desc :=
          { toDefNatNatNatIsoBase := ε,
            toDefNatNatIso        := DefNatNatIso.trivial θ }

        end DefNatNatNatIso

        section

          variable {desc : NatNatNatIsoDesc F G η} {ε : DefNatNatNatIso desc} {a : A}

          def byNatNatNatIsoDef : natIso ε.η a ≃' η a := byNatIsoDef

          def byNatNatNatIsoToHomDef  : nat (toHom  ε.η) a ≃' toHom  (η a) := byNatIsoToHomDef
          def byNatNatNatIsoInvHomDef : nat (invHom ε.η) a ≃' invHom (η a) := byNatIsoInvHomDef

        end

      end

      section

        variable {φ : A → B → C → D} {F'' G'' : ∀ a b, HasFunProp.Fun (φ a b)}
                 {hEq : ∀ a b, NatDesc.StrictNaturality (F'' a b) (G'' a b)}
                 {η' : ∀ a b, StrictDefNatIso (hEq a b)}
                 {F' : ∀ a, HasFunProp.Fun (B := C ⟶ D) (λ b => ⟨F'' a b⟩)}
                 {G' : ∀ a, HasFunProp.Fun (B := C ⟶ D) (λ b => ⟨G'' a b⟩)}
                 {hNatEq : ∀ a, NatNatDesc.StrictNaturality₂ (F' a) (G' a)}

        def StrictDefNatNatNatIso (η : ∀ a, StrictDefNatNatIso (η' a) (hNatEq a))
                                  {F : HasFunProp.Fun (B := B ⟶ C ⟶ D) (λ a => ⟨F' a⟩)}
                                  {G : HasFunProp.Fun (B := B ⟶ C ⟶ D) (λ a => ⟨G' a⟩)}
                                  (hNatNatEq : NatNatNatDesc.StrictNaturality₃ F G) :=
        DefNatNatNatIso (NatNatNatIsoDesc.strict (η := η) hNatNatEq)

        variable {η : ∀ a, StrictDefNatNatIso (η' a) (hNatEq a)}
                 {F : HasFunProp.Fun (B := B ⟶ C ⟶ D) (λ a => ⟨F' a⟩)}
                 {G : HasFunProp.Fun (B := B ⟶ C ⟶ D) (λ a => ⟨G' a⟩)}
                 {hNatNatEq : NatNatNatDesc.StrictNaturality₃ F G}
                 {ε : StrictDefNatNatNatIso η hNatNatEq} {a : A} {b : B} {c : C}

        def byStrictNatNatNatIsoDef : natIso (natIso (natIso ε.η a) b) c ≃ idIso (φ a b c) :=
        byStrictNatNatIsoDef • natIsoCongrArg (natIsoCongrArg (byNatNatNatIsoDef (ε := ε)) b) c

        def byStrictNatNatNatIsoToHomDef  : nat (nat (nat (toHom  ε.η) a) b) c ≃ idHom (φ a b c) :=
        byStrictNatNatIsoToHomDef  • natCongrArg (natCongrArg (byNatNatNatIsoToHomDef  (ε := ε)) b) c

        def byStrictNatNatNatIsoInvHomDef : nat (nat (nat (invHom ε.η) a) b) c ≃ idHom (φ a b c) :=
        byStrictNatNatIsoInvHomDef • natCongrArg (natCongrArg (byNatNatNatIsoInvHomDef (ε := ε)) b) c

      end

    end

    section

      variable {A B C D E : univ.{u} W}

      structure NatNatNatNatIsoDesc (F G : A ⟶ B ⟶ C ⟶ D ⟶ E) (η : ∀ a, F a ⇿ G a) where
      (toDesc  : NatNatNatNatDesc F G (λ a => toHom  (η a)))
      (invDesc : NatNatNatNatDesc G F (λ a => invHom (η a)))

      namespace NatNatNatNatIsoDesc

        def strict {φ : A → B → C → D → E} {F''' G''' : ∀ a b c, HasFunProp.Fun (φ a b c)}
                   {hEq : ∀ a b c, NatDesc.StrictNaturality (F''' a b c) (G''' a b c)}
                   {η'' : ∀ a b c, StrictDefNatIso (hEq a b c)}
                   {F'' : ∀ a b, HasFunProp.Fun (B := D ⟶ E) (λ c => ⟨F''' a b c⟩)}
                   {G'' : ∀ a b, HasFunProp.Fun (B := D ⟶ E) (λ c => ⟨G''' a b c⟩)}
                   {hNatEq : ∀ a b, NatNatDesc.StrictNaturality₂ (F'' a b) (G'' a b)}
                   {η' : ∀ a b, StrictDefNatNatIso (η'' a b) (hNatEq a b)}
                   {F' : ∀ a, HasFunProp.Fun (B := C ⟶ D ⟶ E) (λ b => ⟨F'' a b⟩)}
                   {G' : ∀ a, HasFunProp.Fun (B := C ⟶ D ⟶ E) (λ b => ⟨G'' a b⟩)}
                   {hNatNatEq : ∀ a, NatNatNatDesc.StrictNaturality₃ (F' a) (G' a)}
                   {η : ∀ a, StrictDefNatNatNatIso (η' a) (hNatNatEq a)}
                   {F : HasFunProp.Fun (B := B ⟶ C ⟶ D ⟶ E) (λ a => ⟨F' a⟩)}
                   {G : HasFunProp.Fun (B := B ⟶ C ⟶ D ⟶ E) (λ a => ⟨G' a⟩)}
                   (hNatNatNatEq : NatNatNatNatDesc.StrictNaturality₄ F G) :
          NatNatNatNatIsoDesc ⟨F⟩ ⟨G⟩ (λ a => (η a).η) :=
        { toDesc  := { natNatNatEq := λ {a₁ a₂} f b c d => (cancelRightId (byStrictNatNatNatIsoToHomDef (ε := η a₁))
                                                                          (nat (nat (nat (mapHom ⟨G⟩ f) b) c) d))⁻¹ •
                                                           hNatNatNatEq f b c d •
                                                           cancelLeftId (nat (nat (nat (mapHom ⟨F⟩ f) b) c) d)
                                                                        (byStrictNatNatNatIsoToHomDef (ε := η a₂)) },
          invDesc := { natNatNatEq := λ {a₁ a₂} f b c d => (cancelRightId (byStrictNatNatNatIsoInvHomDef (ε := η a₁))
                                                                          (nat (nat (nat (mapHom ⟨F⟩ f) b) c) d))⁻¹ •
                                                           (hNatNatNatEq f b c d)⁻¹ •
                                                           cancelLeftId (nat (nat (nat (mapHom ⟨G⟩ f) b) c) d)
                                                                        (byStrictNatNatNatIsoInvHomDef (ε := η a₂)) } }

      end NatNatNatNatIsoDesc

      section

        variable {F G : A ⟶ B ⟶ C ⟶ D ⟶ E} {η : ∀ a, F a ⇿ G a}

        structure DefNatNatNatNatIsoBase (desc : NatNatNatNatIsoDesc F G η) where
        (toDefNatNatNatNat  : DefNatNatNatNatBase desc.toDesc)
        (invDefNatNatNatNat : DefNatNatNatNatBase desc.invDesc)

        namespace DefNatNatNatNatIsoBase

          def trivial {desc : NatNatNatNatIsoDesc F G η} [HasTrivialNatEquiv D E] :
            DefNatNatNatNatIsoBase desc :=
          { toDefNatNatNatNat  := DefNatNatNatNatBase.trivial,
            invDefNatNatNatNat := DefNatNatNatNatBase.trivial }

          variable {desc : NatNatNatNatIsoDesc F G η} (ε : DefNatNatNatNatIsoBase desc)

          def natNatNatIsoDesc : NatNatNatIsoDesc F G η :=
          { toDesc  := DefNatNatNatNatBase.natNatNatDesc ε.toDefNatNatNatNat,
            invDesc := DefNatNatNatNatBase.natNatNatDesc ε.invDefNatNatNatNat }

        end DefNatNatNatNatIsoBase

        structure DefNatNatNatNatIso (desc : NatNatNatNatIsoDesc F G η) extends
          DefNatNatNatNatIsoBase desc,
          DefNatNatNatIso (DefNatNatNatNatIsoBase.natNatNatIsoDesc toDefNatNatNatNatIsoBase)

        namespace DefNatNatNatNatIso

          variable {desc : NatNatNatNatIsoDesc F G η}

          def trivial (ε : DefNatNatNatNatIsoBase desc)
                      (θ : DefNatNatNatIsoBase (DefNatNatNatNatIsoBase.natNatNatIsoDesc ε))
                      (ν : DefNatNatIsoBase (DefNatNatNatIsoBase.natNatIsoDesc θ))
                      [HasTrivialIsoNaturalityCondition A (B ⟶ C ⟶ D ⟶ E)] :
            DefNatNatNatNatIso desc :=
          { toDefNatNatNatNatIsoBase := ε,
            toDefNatNatNatIso        := DefNatNatNatIso.trivial θ ν }

        end DefNatNatNatNatIso

        section

          variable {desc : NatNatNatNatIsoDesc F G η} {ε : DefNatNatNatNatIso desc} {a : A}

          def byNatNatNatNatIsoDef : natIso ε.η a ≃' η a := byNatIsoDef

          def byNatNatNatNatIsoToHomDef  : nat (toHom  ε.η) a ≃' toHom  (η a) := byNatIsoToHomDef
          def byNatNatNatNatIsoInvHomDef : nat (invHom ε.η) a ≃' invHom (η a) := byNatIsoInvHomDef

        end

      end

      section

        variable {φ : A → B → C → D → E} {F''' G''' : ∀ a b c, HasFunProp.Fun (φ a b c)}
                 {hEq : ∀ a b c, NatDesc.StrictNaturality (F''' a b c) (G''' a b c)}
                 {η'' : ∀ a b c, StrictDefNatIso (hEq a b c)}
                 {F'' : ∀ a b, HasFunProp.Fun (B := D ⟶ E) (λ c => ⟨F''' a b c⟩)}
                 {G'' : ∀ a b, HasFunProp.Fun (B := D ⟶ E) (λ c => ⟨G''' a b c⟩)}
                 {hNatEq : ∀ a b, NatNatDesc.StrictNaturality₂ (F'' a b) (G'' a b)}
                 {η' : ∀ a b, StrictDefNatNatIso (η'' a b) (hNatEq a b)}
                 {F' : ∀ a, HasFunProp.Fun (B := C ⟶ D ⟶ E) (λ b => ⟨F'' a b⟩)}
                 {G' : ∀ a, HasFunProp.Fun (B := C ⟶ D ⟶ E) (λ b => ⟨G'' a b⟩)}
                 {hNatNatEq : ∀ a, NatNatNatDesc.StrictNaturality₃ (F' a) (G' a)}

        def StrictDefNatNatNatNatIso (η : ∀ a, StrictDefNatNatNatIso (η' a) (hNatNatEq a))
                                     {F : HasFunProp.Fun (B := B ⟶ C ⟶ D ⟶ E) (λ a => ⟨F' a⟩)}
                                     {G : HasFunProp.Fun (B := B ⟶ C ⟶ D ⟶ E) (λ a => ⟨G' a⟩)}
                                     (hNatNatNatEq : NatNatNatNatDesc.StrictNaturality₄ F G) :=
        DefNatNatNatNatIso (NatNatNatNatIsoDesc.strict (η := η) hNatNatNatEq)

-- Currently unused, and really slow to check.
--
--        variable {η : ∀ a, StrictDefNatNatNatIso (η' a) (hNatNatEq a)}
--                 {F : HasFunProp.Fun (B := B ⟶ C ⟶ D ⟶ E) (λ a => ⟨F' a⟩)}
--                 {G : HasFunProp.Fun (B := B ⟶ C ⟶ D ⟶ E) (λ a => ⟨G' a⟩)}
--                 {hNatNatNatEq : NatNatNatNatDesc.StrictNaturality₄ F G}
--                 {ε : StrictDefNatNatNatNatIso η hNatNatNatEq}
--                 {a : A} {b : B} {c : C} {d : D}
--
--        def byStrictNatNatNatNatIsoDef :
--          natIso (natIso (natIso (natIso ε.η a) b) c) d ≃ idIso (φ a b c d) :=
--        byStrictNatNatNatIsoDef •
--        natIsoCongrArg (natIsoCongrArg (natIsoCongrArg (byNatNatNatNatIsoDef (ε := ε)) b) c) d
--
--        def byStrictNatNatNatNatIsoToHomDef  :
--          nat (nat (nat (nat (toHom  ε.η) a) b) c) d ≃ idHom (φ a b c d) :=
--        byStrictNatNatNatIsoToHomDef  •
--        natCongrArg (natCongrArg (natCongrArg (byNatNatNatNatIsoToHomDef  (ε := ε)) b) c) d
--
--        def byStrictNatNatNatNatIsoInvHomDef :
--          nat (nat (nat (nat (invHom ε.η) a) b) c) d ≃ idHom (φ a b c d) :=
--        byStrictNatNatNatIsoInvHomDef •
--        natCongrArg (natCongrArg (natCongrArg (byNatNatNatNatIsoInvHomDef (ε := ε)) b) c) d

      end

    end

  end IsSortNatUniverse

end CategoryTheory
