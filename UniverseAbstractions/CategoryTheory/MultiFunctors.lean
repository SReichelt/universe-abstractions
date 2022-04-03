import UniverseAbstractions.CategoryTheory.Basic
import UniverseAbstractions.CategoryTheory.Functors
import UniverseAbstractions.CategoryTheory.NaturalTransformations



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u uu u' uu' u'' uu'' u''' uu''' u'''' uu'''' v vv w ww iw iww



namespace CategoryTheory

  open MetaRelation MetaFunctor HasTransFun HasSymmFun
       IsAssociative IsCategoricalPreorder
       HasCatProp HasCatProp.Category HasFunProp HasFunProp.Functor HasNatRel
       HasFunctors HasCongrArg HasCongrFun

  namespace HasNaturality

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]

    section

      variable {U : Universe.{u, uu}} {U' : Universe.{u', uu'}} {U'' : Universe.{u'', uu''}}
               [HasCatProp U W] [HasCatProp U' W] [HasCatProp U'' W]
               {A : Category U W} {B : Category U' W} {C : Category U'' W}
               [hFunBC : HasFunProp B C]

      structure FunFunDesc (F : A → (B ⮕ C)) where
      (natDesc {a₁ a₂ : A} : (a₁ ⇾ a₂) → NatDesc (F a₁) (F a₂))
      (defNatDescFun (a₁ a₂ : A) (b : B) : (a₁ ⇾ a₂) ⟶{λ f => (natDesc f).η b} (F a₁ b ⇾ F a₂ b))
      (natDescReflEq (a : A) (b : B) : (natDesc (idHom a)).η b ≃ idHom ((F a) b))
      (natDescTransEq {a₁ a₂ a₃ : A} (f : a₁ ⇾ a₂) (g : a₂ ⇾ a₃) (b : B) :
         (natDesc (g • f)).η b ≃ (natDesc g).η b • (natDesc f).η b)

      variable [HasCatProp sort.{max 1 u' u'' w} W] [hNatBC : HasNaturality B C] {F : A → (B ⮕' C)}

      structure DefFunFunBase (desc : FunFunDesc F) where
      (defNat {a₁ a₂ : A} (f : a₁ ⇾ a₂) : DefNat (desc.natDesc f))
      (defNatFun (a₁ a₂ : A) : (a₁ ⇾ a₂) ⟶{λ f => (defNat f).η} (F a₁ ⇾ F a₂))
      (natReflEq (a : A) :
         DefNatEquiv (defNat (idHom a)) (HasNatOp.defRefl (F a))
                     (desc.natDescReflEq a))
      (natTransEq {a₁ a₂ a₃ : A} (f : a₁ ⇾ a₂) (g : a₂ ⇾ a₃) :
         DefNatEquiv (defNat (g • f)) (HasNatOp.defTrans (defNat f).η (defNat g).η)
                     (λ b => (congrArgTrans (byNatDef (η := defNat f)) (byNatDef (η := defNat g)))⁻¹ •
                             desc.natDescTransEq f g b))

      namespace DefFunFunBase

        variable {desc : FunFunDesc F} (G : DefFunFunBase desc)

        @[reducible] def natFun (a₁ a₂ : A) : (a₁ ⇾ a₂) ⟶ (F a₁ ⇾ F a₂) :=
        G.defNatFun a₁ a₂

        def natPreFun : PreFunctor (Hom A) (Hom (B ⮕' C)) F := ⟨natFun G⟩

        instance : IsPreorderFunctor (natPreFun G) :=
        { reflEq  := λ a   => (DefCat.catReflEq (F a))⁻¹ • G.natReflEq a • byDef,
          transEq := λ f g => (DefCat.catTransEq (A := hNatBC.defFunCat) (G.defNat f).η (G.defNat g).η •
                               congrArgTrans byDef byDef)⁻¹ •
                              G.natTransEq f g •
                              byDef }

        def funDesc : FunDesc F := ⟨natPreFun G⟩

      end DefFunFunBase

      structure DefFunFun [hFunABC : HasFunProp A (B ⮕' C)] (desc : FunFunDesc F) extends
        DefFunFunBase desc, DefFun (DefFunFunBase.funDesc toDefFunFunBase)

      namespace DefFunFun

        variable [HasFunProp A (B ⮕' C)] {desc : FunFunDesc F}

        def trivial (G : DefFunFunBase desc) [HasTrivialFunctorialityCondition A (B ⮕' C)] :
          DefFunFun desc :=
        { toDefFunFunBase := G,
          toDefFun        := HasTrivialFunctorialityCondition.defFun }

        def toFunctor (G : DefFunFun desc) : A ⮕ B ⮕' C := DefFun.toFunctor G.toDefFun

        def byFunFunDefNat {G : DefFunFun desc} {a₁ a₂ : A} {f : a₁ ⇾ a₂} :
          mapHom (toFunctor G) f ≃' (G.defNat f).η :=
        DefFun.byMapHomDef

        def byFunFunDef {G : DefFunFun desc} {a₁ a₂ : A} {f : a₁ ⇾ a₂} {b : B} :
          nat (mapHom (toFunctor G) f) b ≃' (desc.natDesc f).η b :=
        byNatDef • nat.congrArg (byFunFunDefNat (G := G)) b

      end DefFunFun

    end

    section

      variable {U : Universe.{u, uu}} {U' : Universe.{u', uu'}} {U'' : Universe.{u'', uu''}}
               [HasCatProp U W] [HasCatProp U' W] [HasCatProp U'' W]
               [HasCatProp sort.{max 1 u' u'' w} W]
               {A : Category U W} {B : Category U' W} {C : Category U'' W} [hFunBC : HasFunProp B C]
               [hNatBC : HasNaturality B C] [hFunABC : HasFunProp A (B ⮕' C)]

      structure NatNatDesc (F G : A ⮕ B ⮕' C) (η : ∀ a, F a ⇾ G a) where
      (natEq {a₁ a₂ : A} (f : a₁ ⇾ a₂) (b : B) :
         nat (η a₂) b • nat (mapHom F f) b ≃ nat (mapHom G f) b • nat (η a₁) b)

      namespace NatNatDesc

        def StrictNaturality₂ {φ : A → B → C} {F' G' : ∀ a, hFunBC.Fun (φ a)}
                              (F : hFunABC.Fun (λ a => ⟨F' a⟩)) (G : hFunABC.Fun (λ a => ⟨G' a⟩)) :=
        ∀ {a₁ a₂ : A} (f : a₁ ⇾ a₂) (b : B),
          nat (mapHom ⟨F⟩ f) b ≃'{φ a₁ b ⇾ φ a₂ b} nat (mapHom ⟨G⟩ f) b

        def strict {φ : A → B → C} {F' G' : ∀ a, hFunBC.Fun (φ a)}
                   {hEq : ∀ a, NatDesc.StrictNaturality (F' a) (G' a)}
                   {η : ∀ a, StrictDefNat (hEq a)}
                   {F : hFunABC.Fun (λ a => ⟨F' a⟩)} {G : hFunABC.Fun (λ a => ⟨G' a⟩)}
                   (hNatEq : StrictNaturality₂ F G) :
          NatNatDesc ⟨F⟩ ⟨G⟩ (λ a => (η a).η) :=
        { natEq := λ {a₁ a₂} f b => (cancelRightId (byStrictNatDef (η := η a₁))
                                                   (nat (mapHom ⟨G⟩ f) b))⁻¹ •
                                    hNatEq f b •
                                    cancelLeftId (nat (mapHom ⟨F⟩ f) b)
                                                 (byStrictNatDef (η := η a₂)) }

      end NatNatDesc

      section

        variable {F G : A ⮕ B ⮕' C} {η : ∀ a, F a ⇾ G a}

        structure DefNatNatBase (desc : NatNatDesc F G η) where
        (natEquiv {a₁ a₂ : A} (f : a₁ ⇾ a₂) :
           NatEquiv (compHom (mapHom F f) (η a₂)) (compHom (η a₁) (mapHom G f))
                    (λ b => (nat.transEq' (η a₁) (mapHom G f) b)⁻¹ •
                            desc.natEq f b •
                            nat.transEq' (mapHom F f) (η a₂) b))

        namespace DefNatNatBase

          def trivial {desc : NatNatDesc F G η} [HasTrivialNatEquiv B C] : DefNatNatBase desc :=
          { natEquiv := λ _ => HasTrivialNatEquiv.natEquiv }

          variable {desc : NatNatDesc F G η} (ε : DefNatNatBase desc)

          def natDesc : NatDesc F G :=
          { η     := η,
            isNat := ⟨ε.natEquiv⟩ }

        end DefNatNatBase

        variable [HasCatProp sort.{max 1 u u' u'' w} W] [hNatABC : HasNaturality A (B ⮕' C)]

        structure DefNatNat (desc : NatNatDesc F G η) extends
          DefNatNatBase desc, DefNat (DefNatNatBase.natDesc toDefNatNatBase)

        namespace DefNatNat

          variable {desc : NatNatDesc F G η}

          def trivial (ε : DefNatNatBase desc) [HasTrivialNaturalityCondition A (B ⮕' C)] :
            DefNatNat desc :=
          { toDefNatNatBase := ε,
            toDefNat        := HasTrivialNaturalityCondition.defNat }

        end DefNatNat

        def byNatNatDef {desc : NatNatDesc F G η} {ε : DefNatNat desc} {a : A} :
          nat ε.η a ≃ η a :=
        byNatDef

      end

      section

        variable [HasCatProp sort.{max 1 u u' u'' w} W] [hNatABC : HasNaturality A (B ⮕' C)]
                 {φ : A → B → C} {F' G' : ∀ a, hFunBC.Fun (φ a)}
                 {hEq : ∀ a, NatDesc.StrictNaturality (F' a) (G' a)}

        def StrictDefNatNat (η : ∀ a, StrictDefNat (hEq a))
                            {F : hFunABC.Fun (λ a => ⟨F' a⟩)} {G : hFunABC.Fun (λ a => ⟨G' a⟩)}
                            (hNatEq : NatNatDesc.StrictNaturality₂ F G) :=
        DefNatNat (NatNatDesc.strict (η := η) hNatEq)

        def byStrictNatNatDef {η : ∀ a, StrictDefNat (hEq a)}
                              {F : hFunABC.Fun (λ a => ⟨F' a⟩)} {G : hFunABC.Fun (λ a => ⟨G' a⟩)}
                              {hNatEq : NatNatDesc.StrictNaturality₂ F G}
                              {ε : StrictDefNatNat η hNatEq} {a : A} {b : B} :
          nat (nat ε.η a) b ≃ idHom (φ a b) :=
        byStrictNatDef • nat.congrArg (byNatNatDef (ε := ε)) b

      end

    end

    section

      variable {U : Universe.{u, uu}} {U' : Universe.{u', uu'}} {U'' : Universe.{u'', uu''}}
               {U''' : Universe.{u''', uu'''}}
               [HasCatProp U W] [HasCatProp U' W] [HasCatProp U'' W] [HasCatProp U''' W]
               [HasCatProp sort.{max 1 u'' u''' w} W]
               {A : Category U W} {B : Category U' W} {C : Category U'' W} {D : Category U''' W}
               [hFunCD : HasFunProp C D] [hNatCD : HasNaturality C D]
               [hFunBCD : HasFunProp B (C ⮕' D)]

      structure FunFunFunDesc (F : A → (B ⮕ C ⮕' D)) where
      (revFunFunDesc (b : B) : FunFunDesc (λ a => (F a) b))
      (natNatDesc {a₁ a₂ : A} (f : a₁ ⇾ a₂) (G : ∀ b, DefFunFunBase (revFunFunDesc b)) :
         NatNatDesc (F a₁) (F a₂) (λ b => ((G b).defNat f).η))

      variable [HasCatProp sort.{max 1 u' u'' u''' w} W] [hNatBCD : HasNaturality B (C ⮕' D)]
               {F : A → (B ⮕' C ⮕' D)}

      structure DefFunFunFunBase (desc : FunFunFunDesc F) where
      (defRevFunFun (b : B) : DefFunFunBase (desc.revFunFunDesc b))
      (defNatNat {a₁ a₂ : A} (f : a₁ ⇾ a₂) : DefNatNatBase (desc.natNatDesc f defRevFunFun))

      namespace DefFunFunFunBase

        variable {desc : FunFunFunDesc F} (G : DefFunFunFunBase desc)

        def funFunDesc : FunFunDesc F :=
        { natDesc        := λ f       => DefNatNatBase.natDesc (G.defNatNat f),
          defNatDescFun  := λ a₁ a₂ b => (G.defRevFunFun b).defNatFun a₁ a₂,
          natDescReflEq  := λ a   b   => (DefCat.catReflEq ((F a) b))⁻¹ •
                                         (G.defRevFunFun b).natReflEq a,
          natDescTransEq := λ f g b   => (DefCat.catTransEq (A := hNatCD.defFunCat)
                                                            ((G.defRevFunFun b).defNat f).η
                                                            ((G.defRevFunFun b).defNat g).η)⁻¹ •
                                         (G.defRevFunFun b).natTransEq f g }

      end DefFunFunFunBase

      structure DefFunFunFun [hFunABCD : HasFunProp A (B ⮕' C ⮕' D)] (desc : FunFunFunDesc F) extends
        DefFunFunFunBase desc, DefFunFun (DefFunFunFunBase.funFunDesc toDefFunFunFunBase)

      namespace DefFunFunFun

        variable [hFunABCD : HasFunProp A (B ⮕' C ⮕' D)] {desc : FunFunFunDesc F}

        def trivial (G : DefFunFunFunBase desc) (H : DefFunFunBase (DefFunFunFunBase.funFunDesc G))
                    [HasTrivialFunctorialityCondition A (B ⮕' C ⮕' D)] :
          DefFunFunFun desc :=
        { toDefFunFunFunBase := G,
          toDefFunFun        := DefFunFun.trivial H }

        def toFunctor (G : DefFunFunFun desc) : A ⮕ B ⮕' C ⮕' D := DefFunFun.toFunctor G.toDefFunFun

        def byFunFunFunDefNat {G : DefFunFunFun desc} {a₁ a₂ : A} {f : a₁ ⇾ a₂} {b : B} :
          nat (mapHom (toFunctor G) f) b ≃' (G.funFunDesc.natDesc f).η b :=
        DefFunFun.byFunFunDef

        def byFunFunFunDef {G : DefFunFunFun desc} {a₁ a₂ : A} {f : a₁ ⇾ a₂} {b : B} {c : C} :
          nat (nat (mapHom (toFunctor G) f) b) c ≃' ((desc.revFunFunDesc b).natDesc f).η c :=
        byNatDef • nat.congrArg (byFunFunFunDefNat (G := G)) c

      end DefFunFunFun

    end

    section

      variable {U : Universe.{u, uu}} {U' : Universe.{u', uu'}} {U'' : Universe.{u'', uu''}}
               {U''' : Universe.{u''', uu'''}}
               [HasCatProp U W] [HasCatProp U' W] [HasCatProp U'' W] [HasCatProp U''' W]
               [HasCatProp sort.{max 1 u' u'' u''' w} W] [HasCatProp sort.{max 1 u'' u''' w} W]
               {A : Category U W} {B : Category U' W} {C : Category U'' W} {D : Category U''' W}
               [hFunCD : HasFunProp C D] [hNatCD : HasNaturality C D] [hFunBCD : HasFunProp B (C ⮕' D)]
               [hNatBCD : HasNaturality B (C ⮕' D)] [hFunABCD : HasFunProp A (B ⮕' C ⮕' D)]

      structure NatNatNatDesc (F G : A ⮕ B ⮕' C ⮕' D) (η : ∀ a, F a ⇾ G a) where
      (natNatEq {a₁ a₂ : A} (f : a₁ ⇾ a₂) (b : B) (c : C) :
         nat (nat (η a₂) b) c • nat (nat (mapHom F f) b) c ≃ nat (nat (mapHom G f) b) c • nat (nat (η a₁) b) c)

      namespace NatNatNatDesc

        def StrictNaturality₃ {φ : A → B → C → D} {F'' G'' : ∀ a b, hFunCD.Fun (φ a b)}
                              {F' : ∀ a, hFunBCD.Fun (λ b => ⟨F'' a b⟩)}
                              {G' : ∀ a, hFunBCD.Fun (λ b => ⟨G'' a b⟩)}
                              (F : hFunABCD.Fun (λ a => ⟨F' a⟩)) (G : hFunABCD.Fun (λ a => ⟨G' a⟩)) :=
        ∀ {a₁ a₂ : A} (f : a₁ ⇾ a₂) (b : B) (c : C),
          nat (nat (mapHom ⟨F⟩ f) b) c ≃'{φ a₁ b c ⇾ φ a₂ b c} nat (nat (mapHom ⟨G⟩ f) b) c

        def strict {φ : A → B → C → D} {F'' G'' : ∀ a b, hFunCD.Fun (φ a b)}
                   {hEq : ∀ a b, NatDesc.StrictNaturality (F'' a b) (G'' a b)}
                   {η' : ∀ a b, StrictDefNat (hEq a b)}
                   {F' : ∀ a, hFunBCD.Fun (λ b => ⟨F'' a b⟩)}
                   {G' : ∀ a, hFunBCD.Fun (λ b => ⟨G'' a b⟩)}
                   {hNatEq : ∀ a, NatNatDesc.StrictNaturality₂ (F' a) (G' a)}
                   {η : ∀ a, StrictDefNatNat (η' a) (hNatEq a)}
                   {F : hFunABCD.Fun (λ a => ⟨F' a⟩)} {G : hFunABCD.Fun (λ a => ⟨G' a⟩)}
                   (hNatNatEq : StrictNaturality₃ F G) :
          NatNatNatDesc ⟨F⟩ ⟨G⟩ (λ a => (η a).η) :=
        { natNatEq := λ {a₁ a₂} f b c => (cancelRightId (byStrictNatNatDef (ε := η a₁))
                                                        (nat (nat (mapHom ⟨G⟩ f) b) c))⁻¹ •
                                         hNatNatEq f b c •
                                         cancelLeftId (nat (nat (mapHom ⟨F⟩ f) b) c)
                                                      (byStrictNatNatDef (ε := η a₂)) }

      end NatNatNatDesc

      section

        variable {F G : A ⮕ B ⮕' C ⮕' D} {η : ∀ a, F a ⇾ G a}

        structure DefNatNatNatBase (desc : NatNatNatDesc F G η) where
        (natNatEquiv {a₁ a₂ : A} (f : a₁ ⇾ a₂) (b : B) :
           NatEquiv (compHom (nat (mapHom F f) b) (nat (η a₂) b)) (compHom (nat (η a₁) b) (nat (mapHom G f) b))
                    (λ c => (nat.transEq' (nat (η a₁) b) (nat (mapHom G f) b) c)⁻¹ •
                            desc.natNatEq f b c •
                            nat.transEq' (nat (mapHom F f) b) (nat (η a₂) b) c))

        namespace DefNatNatNatBase

          def trivial {desc : NatNatNatDesc F G η} [HasTrivialNatEquiv C D] : DefNatNatNatBase desc :=
          { natNatEquiv := λ _ _ => HasTrivialNatEquiv.natEquiv }

          variable {desc : NatNatNatDesc F G η} (ε : DefNatNatNatBase desc)

          def natNatDesc : NatNatDesc F G η :=
          { natEq := ε.natNatEquiv }

        end DefNatNatNatBase

        variable [HasCatProp sort.{max 1 u u' u'' u''' w} W] [hNatABCD : HasNaturality A (B ⮕' C ⮕' D)]

        structure DefNatNatNat (desc : NatNatNatDesc F G η) extends
          DefNatNatNatBase desc, DefNatNat (DefNatNatNatBase.natNatDesc toDefNatNatNatBase)

        namespace DefNatNatNat

          variable {desc : NatNatNatDesc F G η}

          def trivial (ε : DefNatNatNatBase desc) (θ : DefNatNatBase (DefNatNatNatBase.natNatDesc ε))
                      [HasTrivialNaturalityCondition A (B ⮕' C ⮕' D)] :
            DefNatNatNat desc :=
          { toDefNatNatNatBase := ε,
            toDefNatNat        := DefNatNat.trivial θ }

        end DefNatNatNat

        def byNatNatNatDef {desc : NatNatNatDesc F G η} {ε : DefNatNatNat desc} {a : A} :
          nat ε.η a ≃ η a :=
        byNatDef

      end

      section

        variable [HasCatProp sort.{max 1 u u' u'' u''' w} W] [HasNaturality A (B ⮕' C ⮕' D)]
                 {φ : A → B → C → D} {F'' G'' : ∀ a b, hFunCD.Fun (φ a b)}
                 {hEq : ∀ a b, NatDesc.StrictNaturality (F'' a b) (G'' a b)}
                 {η' : ∀ a b, StrictDefNat (hEq a b)}
                 {F' : ∀ a, hFunBCD.Fun (λ b => ⟨F'' a b⟩)}
                 {G' : ∀ a, hFunBCD.Fun (λ b => ⟨G'' a b⟩)}
                 {hNatEq : ∀ a, NatNatDesc.StrictNaturality₂ (F' a) (G' a)}

        def StrictDefNatNatNat (η : ∀ a, StrictDefNatNat (η' a) (hNatEq a))
                               {F : hFunABCD.Fun (λ a => ⟨F' a⟩)} {G : hFunABCD.Fun (λ a => ⟨G' a⟩)}
                               (hNatNatEq : NatNatNatDesc.StrictNaturality₃ F G) :=
        DefNatNatNat (NatNatNatDesc.strict (η := η) hNatNatEq)

        def byStrictNatNatNatDef {η : ∀ a, StrictDefNatNat (η' a) (hNatEq a)}
                                 {F : hFunABCD.Fun (λ a => ⟨F' a⟩)} {G : hFunABCD.Fun (λ a => ⟨G' a⟩)}
                                 {hNatNatEq : NatNatNatDesc.StrictNaturality₃ F G}
                                 {ε : StrictDefNatNatNat η hNatNatEq} {a : A} {b : B} {c : C} :
          nat (nat (nat ε.η a) b) c ≃ idHom (φ a b c) :=
        byStrictNatNatDef • nat.congrArg (nat.congrArg (byNatNatNatDef (ε := ε)) b) c

      end

    end

    section

      variable {U : Universe.{u, uu}} {U' : Universe.{u', uu'}} {U'' : Universe.{u'', uu''}}
               {U''' : Universe.{u''', uu'''}} {U'''' : Universe.{u'''', uu''''}}
               [HasCatProp U W] [HasCatProp U' W] [HasCatProp U'' W] [HasCatProp U''' W]
               [HasCatProp U'''' W] [HasCatProp sort.{max 1 u' u'' u''' u'''' w} W]
               [HasCatProp sort.{max 1 u'' u''' u'''' w} W] [HasCatProp sort.{max 1 u''' u'''' w} W]
               {A : Category U W} {B : Category U' W} {C : Category U'' W}
               {D : Category U''' W} {E : Category U'''' W}
               [hFunDE : HasFunProp D E] [hNatDE : HasNaturality D E]
               [hFunCDE : HasFunProp C (D ⮕' E)] [hNatCDE : HasNaturality C (D ⮕' E)]
               [hFunBCDE : HasFunProp B (C ⮕' D ⮕' E)] [hNatBCDE : HasNaturality B (C ⮕' D ⮕' E)]
               [hFunABCDE : HasFunProp A (B ⮕' C ⮕' D ⮕' E)]

      structure NatNatNatNatDesc (F G : A ⮕ B ⮕' C ⮕' D ⮕' E) (η : ∀ a, F a ⇾ G a) where
      (natNatNatEq {a₁ a₂ : A} (f : a₁ ⇾ a₂) (b : B) (c : C) (d : D) :
         nat (nat (nat (η a₂) b) c) d • nat (nat (nat (mapHom F f) b) c) d ≃
         nat (nat (nat (mapHom G f) b) c) d • nat (nat (nat (η a₁) b) c) d)

      namespace NatNatNatNatDesc

        def StrictNaturality₄ {φ : A → B → C → D → E} {F''' G''' : ∀ a b c, hFunDE.Fun (φ a b c)}
                              {F'' : ∀ a b, hFunCDE.Fun (λ c => ⟨F''' a b c⟩)}
                              {G'' : ∀ a b, hFunCDE.Fun (λ c => ⟨G''' a b c⟩)}
                              {F' : ∀ a, hFunBCDE.Fun (λ b => ⟨F'' a b⟩)}
                              {G' : ∀ a, hFunBCDE.Fun (λ b => ⟨G'' a b⟩)}
                              (F : hFunABCDE.Fun (λ a => ⟨F' a⟩))
                              (G : hFunABCDE.Fun (λ a => ⟨G' a⟩)) :=
        ∀ {a₁ a₂ : A} (f : a₁ ⇾ a₂) (b : B) (c : C) (d : D),
          nat (nat (nat (mapHom ⟨F⟩ f) b) c) d
          ≃'{φ a₁ b c d ⇾ φ a₂ b c d}
          nat (nat (nat (mapHom ⟨G⟩ f) b) c) d

        def strict {φ : A → B → C → D → E} {F''' G''' : ∀ a b c, hFunDE.Fun (φ a b c)}
                   {hEq : ∀ a b c, NatDesc.StrictNaturality (F''' a b c) (G''' a b c)}
                   {η'' : ∀ a b c, StrictDefNat (hEq a b c)}
                   {F'' : ∀ a b, hFunCDE.Fun (λ c => ⟨F''' a b c⟩)}
                   {G'' : ∀ a b, hFunCDE.Fun (λ c => ⟨G''' a b c⟩)}
                   {hNatEq : ∀ a b, NatNatDesc.StrictNaturality₂ (F'' a b) (G'' a b)}
                   {η' : ∀ a b, StrictDefNatNat (η'' a b) (hNatEq a b)}
                   {F' : ∀ a, hFunBCDE.Fun (λ b => ⟨F'' a b⟩)}
                   {G' : ∀ a, hFunBCDE.Fun (λ b => ⟨G'' a b⟩)}
                   {hNatNatEq : ∀ a, NatNatNatDesc.StrictNaturality₃ (F' a) (G' a)}
                   {η : ∀ a, StrictDefNatNatNat (η' a) (hNatNatEq a)}
                   {F : hFunABCDE.Fun (λ a => ⟨F' a⟩)} {G : hFunABCDE.Fun (λ a => ⟨G' a⟩)}
                   (hNatNatNatEq : StrictNaturality₄ F G) :
          NatNatNatNatDesc ⟨F⟩ ⟨G⟩ (λ a => (η a).η) :=
        { natNatNatEq := λ {a₁ a₂} f b c d => (cancelRightId (byStrictNatNatNatDef (ε := η a₁))
                                                             (nat (nat (nat (mapHom ⟨G⟩ f) b) c) d))⁻¹ •
                                              hNatNatNatEq f b c d •
                                              cancelLeftId (nat (nat (nat (mapHom ⟨F⟩ f) b) c) d)
                                                           (byStrictNatNatNatDef (ε := η a₂)) }

      end NatNatNatNatDesc

      section

        variable {F G : A ⮕ B ⮕' C ⮕' D ⮕' E} {η : ∀ a, F a ⇾ G a}

        structure DefNatNatNatNatBase (desc : NatNatNatNatDesc F G η) where
        (natNatNatEquiv {a₁ a₂ : A} (f : a₁ ⇾ a₂) (b : B) (c : C) :
           NatEquiv (compHom (nat (nat (mapHom F f) b) c) (nat (nat (η a₂) b) c))
                    (compHom (nat (nat (η a₁) b) c) (nat (nat (mapHom G f) b) c))
                    (λ d => (nat.transEq' (nat (nat (η a₁) b) c) (nat (nat (mapHom G f) b) c) d)⁻¹ •
                            desc.natNatNatEq f b c d •
                            nat.transEq' (nat (nat (mapHom F f) b) c) (nat (nat (η a₂) b) c) d))

        namespace DefNatNatNatNatBase

          def trivial {desc : NatNatNatNatDesc F G η} [HasTrivialNatEquiv D E] :
            DefNatNatNatNatBase desc :=
          { natNatNatEquiv := λ _ _ _ => HasTrivialNatEquiv.natEquiv }

          variable {desc : NatNatNatNatDesc F G η} (ε : DefNatNatNatNatBase desc)

          def natNatNatDesc : NatNatNatDesc F G η :=
          { natNatEq := ε.natNatNatEquiv }

        end DefNatNatNatNatBase

        variable [HasCatProp sort.{max 1 u u' u'' u''' u'''' w} W]
                 [hNatABCDE : HasNaturality A (B ⮕' C ⮕' D ⮕' E)]

        structure DefNatNatNatNat (desc : NatNatNatNatDesc F G η) extends
          DefNatNatNatNatBase desc,
          DefNatNatNat (DefNatNatNatNatBase.natNatNatDesc toDefNatNatNatNatBase)

        namespace DefNatNatNatNat

          variable {desc : NatNatNatNatDesc F G η}

          def trivial (ε : DefNatNatNatNatBase desc)
                      (θ : DefNatNatNatBase (DefNatNatNatNatBase.natNatNatDesc ε))
                      (ν : DefNatNatBase (DefNatNatNatBase.natNatDesc θ))
                      [HasTrivialNaturalityCondition A (B ⮕' C ⮕' D ⮕' E)] :
            DefNatNatNatNat desc :=
          { toDefNatNatNatNatBase := ε,
            toDefNatNatNat        := DefNatNatNat.trivial θ ν }

        end DefNatNatNatNat

        def byNatNatNatNatDef {desc : NatNatNatNatDesc F G η} {ε : DefNatNatNatNat desc} {a : A} :
          nat ε.η a ≃ η a :=
        byNatDef

      end

      section

        variable [HasCatProp sort.{max 1 u u' u'' u''' u'''' w} W] [HasNaturality A (B ⮕' C ⮕' D ⮕' E)]
                 {φ : A → B → C → D → E} {F''' G''' : ∀ a b c, hFunDE.Fun (φ a b c)}
                 {hEq : ∀ a b c, NatDesc.StrictNaturality (F''' a b c) (G''' a b c)}
                 {η'' : ∀ a b c, StrictDefNat (hEq a b c)}
                 {F'' : ∀ a b, hFunCDE.Fun (λ c => ⟨F''' a b c⟩)}
                 {G'' : ∀ a b, hFunCDE.Fun (λ c => ⟨G''' a b c⟩)}
                 {hNatEq : ∀ a b, NatNatDesc.StrictNaturality₂ (F'' a b) (G'' a b)}
                 {η' : ∀ a b, StrictDefNatNat (η'' a b) (hNatEq a b)}
                 {F' : ∀ a, hFunBCDE.Fun (λ b => ⟨F'' a b⟩)}
                 {G' : ∀ a, hFunBCDE.Fun (λ b => ⟨G'' a b⟩)}
                 {hNatNatEq : ∀ a, NatNatNatDesc.StrictNaturality₃ (F' a) (G' a)}

        def StrictDefNatNatNatNat (η : ∀ a, StrictDefNatNatNat (η' a) (hNatNatEq a))
                                  {F : hFunABCDE.Fun (λ a => ⟨F' a⟩)}
                                  {G : hFunABCDE.Fun (λ a => ⟨G' a⟩)}
                                  (hNatNatNatEq : NatNatNatNatDesc.StrictNaturality₄ F G) :=
        DefNatNatNatNat (NatNatNatNatDesc.strict (η := η) hNatNatNatEq)

        def byStrictNatNatNatNatDef {η : ∀ a, StrictDefNatNatNat (η' a) (hNatNatEq a)}
                                    {F : hFunABCDE.Fun (λ a => ⟨F' a⟩)}
                                    {G : hFunABCDE.Fun (λ a => ⟨G' a⟩)}
                                    {hNatNatNatEq : NatNatNatNatDesc.StrictNaturality₄ F G}
                                    {ε : StrictDefNatNatNatNat η hNatNatNatEq}
                                    {a : A} {b : B} {c : C} {d : D} :
          nat (nat (nat (nat ε.η a) b) c) d ≃ idHom (φ a b c d) :=
        byStrictNatNatNatDef •
        nat.congrArg (nat.congrArg (nat.congrArg (byNatNatNatNatDef (ε := ε)) b) c) d

      end

    end

  end HasNaturality

end CategoryTheory
