import UniverseAbstractions.CategoryTheory.Basic
import UniverseAbstractions.CategoryTheory.Functors
import UniverseAbstractions.CategoryTheory.NaturalTransformations
import UniverseAbstractions.CategoryTheory.MultiFunctors
import UniverseAbstractions.CategoryTheory.Functors.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u uu u' uu' u'' uu'' v vv w ww iw iww



namespace CategoryTheory

  open MetaRelation MetaFunctor MetaQuantification HasTransFun HasSymmFun
       IsAssociative IsCategoricalPreorder
       HasCatProp HasCatProp.Category HasFunProp HasFunProp.Functor HasNatRel
       HasFunctors HasCongrArg HasCongrFun HasLinearFunOp HasNonLinearFunOp

  namespace HasNaturality

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]

    section

      variable {U : Universe.{u, uu}} {V : Universe.{v, vv}} [HasCatProp U W] [HasCatProp V W]
               [HasCatProp sort.{max 1 u v w} W] {A : Category U W} (a : A) (B : Category V W)
               [HasFunProp A B] [h : HasNaturality A B]

      def revApp (F : A ⮕' B) : B := F a

      def revAppPreFun : PreFunctor (Hom (A ⮕' B)) (Hom B) (revApp a B) :=
      ⟨λ F₁ F₂ => natFun F₁ F₂ a⟩

      instance : IsPreorderFunctor (revAppPreFun a B) :=
      { reflEq  := λ F   => nat.reflEq' F a • byDef,
        transEq := λ η ε => (congrArgTrans byDef byDef)⁻¹ •
                            nat.transEq' η ε a •
                            byDef }

      def revAppFunDesc : FunDesc (revApp a B) := ⟨revAppPreFun a B⟩

    end

    class HasRevAppFun {U : Universe.{u, uu}} {V : Universe.{v, vv}} [HasCatProp U W]
                       [HasCatProp V W] [HasCatProp sort.{max 1 u v w} W]
                       (A : Category U W) (B : Category V W) [hFunAB : HasFunProp A B]
                       [hNatAB : HasNaturality A B] [hFunABB : HasFunProp (A ⮕' B) B] where
    (defRevAppFun (a : A) : HasFunProp.DefFun (revAppFunDesc a B))

    namespace HasRevAppFun

      variable {U : Universe.{u, uu}} {V : Universe.{v, vv}} [HasCatProp U W] [HasCatProp V W]
               [HasCatProp sort.{max 1 u v w} W] (A : Category U W) (B : Category V W)
               [HasFunProp A B] [hNatAB : HasNaturality A B] [HasFunProp (A ⮕' B) B]
               [h : HasRevAppFun A B]

      def revAppFun (a : A) : (A ⮕' B) ⮕ B := DefFun.toFunctor (h.defRevAppFun a)

      def mapRevNat {a₁ a₂ : A} (f : a₁ ⇾ a₂) :
        MetaQuantification (Hom B) (revApp a₁ B) (revApp a₂ B) :=
      λ F => mapHom F f

      instance mapRevNat.isNat {a₁ a₂ : A} (f : a₁ ⇾ a₂) :
        IsNatural (preFun (revAppFun A B a₁)) (preFun (revAppFun A B a₂)) (mapRevNat A B f) :=
      ⟨λ {F₁ F₂} η => (naturality η f •
                       congrArgTransLeft (mapHom F₁ f)
                                         (DefFun.byMapHomDef (φ := revApp a₂ B)))⁻¹ •
                      congrArgTransRight (DefFun.byMapHomDef (φ := revApp a₁ B))
                                         (mapHom F₂ f)⟩

      def revAppNatDesc {a₁ a₂ : A} (f : a₁ ⇾ a₂) :
        NatDesc (revAppFun A B a₁) (revAppFun A B a₂) :=
      { η     := mapRevNat       A B f,
        isNat := mapRevNat.isNat A B f }

      def revAppFunFunDesc : FunFunDesc (revAppFun A B) :=
      { natDesc        := revAppNatDesc A B,
        defNatDescFun  := λ a₁ a₂ F => toDefFun ((preFun F).baseFun a₁ a₂),
        natDescReflEq  := λ a   F   => mapHom.reflEq  F a,
        natDescTransEq := λ f g F   => mapHom.transEq F f g }

    end HasRevAppFun

    class HasRevAppFunFun {U : Universe.{u, uu}} {V : Universe.{v, vv}} [HasCatProp U W]
                          [HasCatProp V W] [HasCatProp sort.{max 1 u v w} W]
                          (A : Category U W) (B : Category V W) [hFunAB : HasFunProp A B]
                          [hNatAB : HasNaturality A B] [hFunABB : HasFunProp (A ⮕' B) B]
                          [hNatABB : HasNaturality (A ⮕' B) B]
                          [hFunAABB : HasFunProp A ((A ⮕' B) ⮕' B)] extends
      HasRevAppFun A B where
    (defRevAppFunFun : DefFunFun (HasRevAppFun.revAppFunFunDesc A B))

    namespace HasRevAppFunFun

      variable {U : Universe.{u, uu}} {V : Universe.{v, vv}} [HasCatProp U W] [HasCatProp V W]
               [HasCatProp sort.{max 1 u v w} W] (A : Category U W) (B : Category V W)
               [HasFunProp A B] [HasNaturality A B] [HasFunProp (A ⮕' B) B]
               [HasNaturality (A ⮕' B) B] [HasFunProp A ((A ⮕' B) ⮕' B)] [h : HasRevAppFunFun A B]

      def revAppFunFun : A ⮕ (A ⮕' B) ⮕' B := DefFunFun.toFunctor h.defRevAppFunFun

    end HasRevAppFunFun

    section

      variable {U : Universe.{u, uu}} {U' : Universe.{u', uu'}} {U'' : Universe.{u'', uu''}}
               [HasCatProp U W] [HasCatProp U' W] [HasCatProp U'' W]
               (A : Category U W) (B : Category U' W) (C : Category U'' W) [HasFunProp A B]
               [HasFunProp B C] [HasFunProp A C] [h : HasCompFun A B C]

      section

        variable [HasCatProp sort.{max 1 u' u'' w} W] [hNatBC : HasNaturality B C] (F : A ⮕ B)

        def mapCompNat {G₁ G₂ : B ⮕' C} (η : G₁ ⇾ G₂) :
          MetaQuantification (Hom C) (G₁.φ ∘ F.φ) (G₂.φ ∘ F.φ) :=
        λ a => nat η (F a)

        instance mapCompNat.isNat {G₁ G₂ : B ⮕' C} (η : G₁ ⇾ G₂) :
          IsNatural (preFun (G₁ ⭗ F)) (preFun (G₂ ⭗ F)) (mapCompNat A B C F η) :=
        ⟨λ {a₁ a₂} f => (congrArgTransLeft (mapCompNat A B C F η a₁)
                                           (DefFun.byMapHomDef (φ := G₂.φ ∘ F.φ)))⁻¹ •
                        naturality η (mapHom F f) •
                        congrArgTransRight (DefFun.byMapHomDef (φ := G₁.φ ∘ F.φ))
                                           (mapCompNat A B C F η a₂)⟩

        def compNatDesc {G₁ G₂ : B ⮕' C} (η : G₁ ⇾ G₂) :
          NatDesc (G₁ ⭗ F) (G₂ ⭗ F) :=
        { η     := mapCompNat       A B C F η,
          isNat := mapCompNat.isNat A B C F η }

        def compFunFunDesc : FunFunDesc (λ G : B ⮕' C => G ⭗ F) :=
        { natDesc        := compNatDesc A B C F,
          defNatDescFun  := λ G₁ G₂ a => hNatBC.defNatFun G₁ G₂ (F a),
          natDescReflEq  := λ G   a   => nat.reflEq'  G   (F a),
          natDescTransEq := λ η ε a   => nat.transEq' η ε (F a) }

      end

      section

        variable [HasCatProp sort.{max 1 u u' w} W] [hNatAB : HasNaturality A B] (G : B ⮕ C)

        def mapRevCompNat {F₁ F₂ : A ⮕' B} (η : F₁ ⇾ F₂) :
          MetaQuantification (Hom C) (G.φ ∘ F₁.φ) (G.φ ∘ F₂.φ) :=
        λ a => mapHom G (nat η a)

        instance mapRevCompNat.isNat {F₁ F₂ : A ⮕' B} (η : F₁ ⇾ F₂) :
          IsNatural (preFun (G ⭗ F₁)) (preFun (G ⭗ F₂)) (mapRevCompNat A B C G η) :=
        ⟨λ {a₁ a₂} f => (congrArgTransLeft (mapRevCompNat A B C G η a₁)
                                           (DefFun.byMapHomDef (φ := G.φ ∘ F₂.φ)))⁻¹ •
                        mapHom.transEq G (nat η a₁) (mapHom F₂ f) •
                        mapHom.congrArg G (naturality η f) •
                        (mapHom.transEq G (mapHom F₁ f) (nat η a₂))⁻¹ •
                        congrArgTransRight (DefFun.byMapHomDef (φ := G.φ ∘ F₁.φ))
                                           (mapRevCompNat A B C G η a₂)⟩

        def revCompNatDesc {F₁ F₂ : A ⮕' B} (η : F₁ ⇾ F₂) :
          NatDesc (G ⭗ F₁) (G ⭗ F₂) :=
        { η     := mapRevCompNat       A B C G η,
          isNat := mapRevCompNat.isNat A B C G η }

        def revCompFunFunDesc : FunFunDesc (λ F : A ⮕' B => G ⭗ F) :=
        { natDesc        := revCompNatDesc A B C G,
          defNatDescFun  := λ F₁ F₂ a => HasCompFun.defCompDefFun (hNatAB.defNatFun F₁ F₂ a)
                                                                  ((preFun G).baseFun (F₁ a) (F₂ a)),
          natDescReflEq  := λ F   a   => mapHom.reflEq G (F a) •
                                         mapHom.congrArg G (nat.reflEq' F a),
          natDescTransEq := λ η ε a   => mapHom.transEq G (nat η a) (nat ε a) •
                                         mapHom.congrArg G (nat.transEq' η ε a) }

      end

    end

    class HasCompFunFun {U : Universe.{u, uu}} {U' : Universe.{u', uu'}} {U'' : Universe.{u'', uu''}}
                        [HasCatProp U W] [HasCatProp U' W] [HasCatProp U'' W]
                        [HasCatProp sort.{max 1 u u'' w} W] [HasCatProp sort.{max 1 u' u'' w} W]
                        (A : Category U W) (B : Category U' W) (C : Category U'' W)
                        [hFunAB : HasFunProp A B] [hFunBC : HasFunProp B C]
                        [hFunAC : HasFunProp A C] [hNatBC : HasNaturality B C]
                        [hNatAC : HasNaturality A C] [hFunBCAC : HasFunProp (B ⮕' C) (A ⮕' C)]
                        [h : HasCompFun A B C] where
    (defCompFunFun (F : A ⮕ B) : DefFunFun (compFunFunDesc A B C F))

    namespace HasCompFunFun

      variable {U : Universe.{u, uu}} {U' : Universe.{u', uu'}} {U'' : Universe.{u'', uu''}}
               [HasCatProp U W] [HasCatProp U' W] [HasCatProp U'' W]
               [HasCatProp sort.{max 1 u u' w} W] [HasCatProp sort.{max 1 u u'' w} W]
               [HasCatProp sort.{max 1 u' u'' w} W]
               (A : Category U W) (B : Category U' W) (C : Category U'' W) [HasFunProp A B]
               [HasFunProp B C] [HasFunProp A C] [HasNaturality B C]
               [HasNaturality A C] [HasFunProp (B ⮕' C) (A ⮕' C)] [HasCompFun A B C]
               [h : HasCompFunFun A B C]

      def compFunFun (F : A ⮕ B) : (B ⮕' C) ⮕ (A ⮕' C) := DefFunFun.toFunctor (h.defCompFunFun F)

      def compFunFunFunDesc [HasNaturality A B] : FunFunFunDesc (λ F : A ⮕' B => compFunFun A B C F) :=
      { revFunFunDesc := revCompFunFunDesc A B C,
        natNatDesc    := λ {F₁ F₂} η H =>
                         { natEq := λ {G₁ G₂} ε a =>
                                    (naturality ε (nat η a) •
                                     congrArgTrans (byNatDef (η := (H G₁).defNat η)) DefFunFun.byFunFunDef)⁻¹ •
                                    congrArgTrans (DefFunFun.byFunFunDef (G := h.defCompFunFun F₁)) byNatDef } }

    end HasCompFunFun

    class HasCompFunFunFun {U : Universe.{u, uu}} {U' : Universe.{u', uu'}} {U'' : Universe.{u'', uu''}}
                           [HasCatProp U W] [HasCatProp U' W] [HasCatProp U'' W]
                           [HasCatProp sort.{max 1 u u' w} W] [HasCatProp sort.{max 1 u u'' w} W]
                           [HasCatProp sort.{max 1 u' u'' w} W] [HasCatProp sort.{max 1 u u' u'' w} W]
                           (A : Category U W) (B : Category U' W) (C : Category U'' W)
                           [hFunAB : HasFunProp A B] [hFunBC : HasFunProp B C]
                           [hFunAC : HasFunProp A C] [hNatAB : HasNaturality A B]
                           [hNatBC : HasNaturality B C] [hNatAC : HasNaturality A C]
                           [hFunBCAC : HasFunProp (B ⮕' C) (A ⮕' C)]
                           [hNatBCAC : HasNaturality (B ⮕' C) (A ⮕' C)]
                           [hFunABBCAC : HasFunProp (A ⮕' B) ((B ⮕' C) ⮕' (A ⮕' C))]
                           [h : HasCompFun A B C] extends
      HasCompFunFun A B C where
    (defCompFunFunFun : DefFunFunFun (HasCompFunFun.compFunFunFunDesc A B C))

    namespace HasCompFunFunFun

      variable {U : Universe.{u, uu}} {U' : Universe.{u', uu'}} {U'' : Universe.{u'', uu''}}
               [HasCatProp U W] [HasCatProp U' W] [HasCatProp U'' W]
               [HasCatProp sort.{max 1 u u' w} W] [HasCatProp sort.{max 1 u u'' w} W]
               [HasCatProp sort.{max 1 u' u'' w} W] [HasCatProp sort.{max 1 u u' u'' w} W]
               (A : Category U W) (B : Category U' W) (C : Category U'' W) [HasFunProp A B]
               [HasFunProp B C] [HasFunProp A C] [HasNaturality A B] [HasNaturality B C]
               [HasNaturality A C] [HasFunProp (B ⮕' C) (A ⮕' C)]
               [HasNaturality (B ⮕' C) (A ⮕' C)] [HasFunProp (A ⮕' B) ((B ⮕' C) ⮕' (A ⮕' C))]
               [HasCompFun A B C] [h : HasCompFunFunFun A B C]

      def compFunFunFun : (A ⮕' B) ⮕ (B ⮕' C) ⮕' (A ⮕' C) := DefFunFunFun.toFunctor h.defCompFunFunFun

    end HasCompFunFunFun

    section

      open HasFunProp.HasConstFun

      variable [HasSubLinearFunOp W] {U : Universe.{u, uu}} {V : Universe.{v, vv}} [HasCatProp U W]
               [HasCatProp V W] (A : Category U W) (B : Category V W) [HasFunProp A B]
               [h : HasConstFun A B]

      def mapConstNat {b₁ b₂ : B} (g : b₁ ⇾ b₂) :
        MetaQuantification (Hom B) (Function.const A b₁) (Function.const A b₂) :=
      λ _ => g

      instance mapConstNat.isNat {b₁ b₂ : B} (g : b₁ ⇾ b₂) :
        IsNatural (preFun (constFun A b₁)) (preFun (constFun A b₂)) (mapConstNat A B g) :=
      ⟨λ _ => (leftId g •
               congrArgTransLeft g (DefFun.byMapHomDef (φ := Function.const A b₂)))⁻¹ •
              (rightId g •
               congrArgTransRight (DefFun.byMapHomDef (φ := Function.const A b₁)) g)⟩

      def constNatDesc {b₁ b₂ : B} (g : b₁ ⇾ b₂) : NatDesc (constFun A b₁) (constFun A b₂) :=
      { η     := mapConstNat       A B g,
        isNat := mapConstNat.isNat A B g }

      def constFunFunDesc : FunFunDesc (λ b : B => constFun A b) :=
      { natDesc        := constNatDesc A B,
        defNatDescFun  := λ b₁ b₂ _ => HasIdFun.defIdFun (b₁ ⇾ b₂),
        natDescReflEq  := λ b   _   => HasInstanceEquivalences.refl (idHom b),
        natDescTransEq := λ f g _   => HasInstanceEquivalences.refl (g • f) }

    end

    class HasConstFunFun [HasSubLinearFunOp W] {U : Universe.{u, uu}} {V : Universe.{v, vv}}
                         [HasCatProp U W] [HasCatProp V W] [HasCatProp sort.{max 1 u v w} W]
                         (A : Category U W) (B : Category V W)
                         [hFunAB : HasFunProp A B] [hNatAB : HasNaturality A B]
                         [hFunBAB : HasFunProp B (A ⮕' B)] [h : HasConstFun A B] where
    (defConstFunFun : DefFunFun (constFunFunDesc A B))

    namespace HasConstFunFun

      variable [HasSubLinearFunOp W] {U : Universe.{u, uu}} {V : Universe.{v, vv}}
               [HasCatProp U W] [HasCatProp V W] [HasCatProp sort.{max 1 u v w} W]
               (A : Category U W) (B : Category V W) [HasFunProp A B] [HasNaturality A B]
               [HasFunProp B (A ⮕' B)] [HasConstFun A B] [h : HasConstFunFun A B]

      def constFunFun : B ⮕ (A ⮕' B) := DefFunFun.toFunctor h.defConstFunFun

    end HasConstFunFun

    section

      variable [HasNonLinearFunOp W] {U : Universe.{u, uu}} {V : Universe.{v, vv}}
               [HasCatProp U W] [HasCatProp V W] [HasCatProp sort.{max 1 u v w} W]
               {A : Category U W} {B : Category V W} [HasFunProp A B] [HasNaturality A B]
               [HasFunProp A (A ⮕' B)] (F : A ⮕ A ⮕' B)

      @[reducible] def dup (a : A) : B := (F a) a

      @[reducible] def mapDupHom {a₁ a₂ : A} (f : a₁ ⇾ a₂) : dup F a₁ ⇾ dup F a₂ :=
      mapHom (F a₂) f • nat (mapHom F f) a₁

      @[reducible] def mapDupHom' {a₁ a₂ : A} (f : a₁ ⇾ a₂) : dup F a₁ ⇾ dup F a₂ :=
      nat (mapHom F f) a₂ • mapHom (F a₁) f

      def mapDupHomEq {a₁ a₂ : A} (f : a₁ ⇾ a₂) : mapDupHom' F f ≃ mapDupHom F f :=
      naturality (mapHom F f) f

      def defMapDupHomArg (a₁ a₂ : A) :
        (a₁ ⇾ a₂)
        ⟶{λ f => transFun (Hom B) (nat (mapHom F f) a₁) (dup F a₂)}
        (((F a₂) a₁ ⇾ dup F a₂) ⟶ (dup F a₁ ⇾ dup F a₂)) :=
      transFunFun (Hom B) (dup F a₁) ((F a₂) a₁) (dup F a₂) •
      natFun (F a₁) (F a₂) a₁ •
      (preFun F).baseFun a₁ a₂
      ◄ byDefDef • byArgDef

      def defMapDupHomFun (a₁ a₂ : A) : (a₁ ⇾ a₂) ⟶{λ f => mapDupHom F f} (dup F a₁ ⇾ dup F a₂) :=
      substFun ((preFun (F a₂)).baseFun a₁ a₂) (defMapDupHomArg F a₁ a₂)
      ◄ byDef (F := (HasTransFun.defTransFun (dup F a₁) ((F a₂) a₁) (dup F a₂)).defFun _) • byFunDef

      @[reducible] def mapDupHomFun (a₁ a₂ : A) : (a₁ ⇾ a₂) ⟶ (dup F a₁ ⇾ dup F a₂) :=
      defMapDupHomFun F a₁ a₂

      def mapDupHomPreFun : PreFunctor (Hom A) (Hom B) (dup F) := ⟨mapDupHomFun F⟩

      instance mapDupHomPreFun.isPreorderFunctor : IsPreorderFunctor (mapDupHomPreFun F) :=
      { reflEq  := λ a => idId (dup F a) •
                          congrArgTrans (nat.reflEq' (F a) a •
                                         nat.congrArg (mapHom.reflEq F a) a)
                                        (mapHom.reflEq (F a) a) •
                          byDef (F := defMapDupHomFun F a a),
        transEq := λ {a₁ a₂ a₃} f g => (congrArgTrans (byDef (F := defMapDupHomFun F a₁ a₂))
                                                      (byDef (F := defMapDupHomFun F a₂ a₃)))⁻¹ •
                                       assoc (nat (mapHom F f) a₁) (mapHom (F a₂) f) (mapDupHom F g) •
                                       congrArgTransLeft (nat (mapHom F f) a₁)
                                                         ((assoc (mapHom (F a₂) f)
                                                                 (nat (mapHom F g) a₂)
                                                                 (mapHom (F a₃) g))⁻¹ •
                                                          congrArgTransRight (naturality (mapHom F g) f)⁻¹
                                                                             (mapHom (F a₃) g) •
                                                          assoc (nat (mapHom F g) a₁)
                                                                (mapHom (F a₃) f)
                                                                (mapHom (F a₃) g)) •
                                       (assoc (nat (mapHom F f) a₁) (nat (mapHom F g) a₁)
                                              (mapHom (F a₃) g • mapHom (F a₃) f))⁻¹ •
                                       congrArgTrans (nat.transEq' (mapHom F f) (mapHom F g) a₁ •
                                                      nat.congrArg (mapHom.transEq F f g) a₁)
                                                     (mapHom.transEq (F a₃) f g) •
                                       byDef (F := defMapDupHomFun F a₁ a₃) }

      def dupFunDesc : FunDesc (dup F) := ⟨mapDupHomPreFun F⟩

    end

    class HasDupFun [HasNonLinearFunOp W] {U : Universe.{u, uu}} {V : Universe.{v, vv}}
                    [HasCatProp U W] [HasCatProp V W] [HasCatProp sort.{max 1 u v w} W]
                    (A : Category U W) (B : Category V W)
                    [hFunAB : HasFunProp A B] [hNatAB : HasNaturality A B]
                    [hFunAAB : HasFunProp A (A ⮕' B)] where
    (defDupFun (F : A ⮕ A ⮕' B) : HasFunProp.DefFun (dupFunDesc F))

    namespace HasDupFun

      variable [HasNonLinearFunOp W] {U : Universe.{u, uu}} {V : Universe.{v, vv}}
               [HasCatProp U W] [HasCatProp V W] [HasCatProp sort.{max 1 u v w} W]
               (A : Category U W) (B : Category V W) [HasFunProp A B] [hNatAB : HasNaturality A B]
               [HasFunProp A (A ⮕' B)] [h : HasDupFun A B]

      def dupFun (F : A ⮕ A ⮕' B) : A ⮕ B := DefFun.toFunctor (h.defDupFun F)

      variable [hNatAAB : HasNaturality A (A ⮕' B)]

      def mapDupNat {F₁ F₂ : A ⮕' A ⮕' B} (η : F₁ ⇾ F₂) :
        MetaQuantification (Hom B) (dup F₁) (dup F₂) :=
      λ a => nat (nat η a) a

      instance mapDupNat.isNat {F₁ F₂ : A ⮕' A ⮕' B} (η : F₁ ⇾ F₂) :
        IsNatural (preFun (dupFun A B F₁)) (preFun (dupFun A B F₂)) (mapDupNat A B η) :=
      ⟨λ {a₁ a₂} f => congrArgTransLeft (mapDupNat A B η a₁) (DefFun.byMapHomDef (φ := dup F₂))⁻¹ •
                      (assoc (mapDupNat A B η a₁) (nat (mapHom F₂ f) a₁) (mapHom (F₂ a₂) f))⁻¹ •
                      congrArgTransRight (nat.transEq' (nat η a₁) (mapHom F₂ f) a₁ •
                                          nat.congrArg (naturality η f) a₁ •
                                          (nat.transEq' (mapHom F₁ f) (nat η a₂) a₁)⁻¹)
                                         (mapHom (F₂ a₂) f) •
                      assoc (nat (mapHom F₁ f) a₁) (nat (nat η a₂) a₁) (mapHom (F₂ a₂) f) •
                      congrArgTransLeft (nat (mapHom F₁ f) a₁)
                                        (naturality (nat η a₂) f) •
                      (assoc (nat (mapHom F₁ f) a₁) (mapHom (F₁ a₂) f) (mapDupNat A B η a₂))⁻¹ •
                      congrArgTransRight (DefFun.byMapHomDef (φ := dup F₁)) (mapDupNat A B η a₂)⟩

      def dupNatDesc {F₁ F₂ : A ⮕' A ⮕' B} (η : F₁ ⇾ F₂) :
        NatDesc (dupFun A B F₁) (dupFun A B F₂) :=
      { η     := mapDupNat       A B η,
        isNat := mapDupNat.isNat A B η }

      def dupFunFunDesc : FunFunDesc (λ F : A ⮕' A ⮕' B => dupFun A B F) :=
      { natDesc        := dupNatDesc A B,
        defNatDescFun  := λ F₁ F₂ a => HasCompFun.defCompDefDefFun (hNatAAB.defNatFun F₁ F₂ a) (hNatAB.defNatFun (F₁ a) (F₂ a) a),
        natDescReflEq  := λ F   a   => nat.reflEq' (F a) a •
                                       nat.congrArg (nat.reflEq' F a) a,
        natDescTransEq := λ η ε a   => nat.transEq' (nat η a) (nat ε a) a •
                                       nat.congrArg (nat.transEq' η ε a) a }

    end HasDupFun

    class HasDupFunFun [HasNonLinearFunOp W] {U : Universe.{u, uu}} {V : Universe.{v, vv}}
                       [HasCatProp U W] [HasCatProp V W] [HasCatProp sort.{max 1 u v w} W]
                       (A : Category U W) (B : Category V W)
                       [hFunAB : HasFunProp A B] [hNatAB : HasNaturality A B]
                       [hFunAAB : HasFunProp A (A ⮕' B)] [hNatAAB : HasNaturality A (A ⮕' B)]
                       [hFunAABAB : HasFunProp (A ⮕' A ⮕' B) (A ⮕' B)] extends
      HasDupFun A B where
    (defDupFunFun : DefFunFun (HasDupFun.dupFunFunDesc A B))

    namespace HasDupFunFun

      variable [HasNonLinearFunOp W] {U : Universe.{u, uu}} {V : Universe.{v, vv}}
               [HasCatProp U W] [HasCatProp V W] [HasCatProp sort.{max 1 u v w} W]
               (A : Category U W) (B : Category V W) [HasFunProp A B] [HasNaturality A B]
               [HasFunProp A (A ⮕' B)] [HasNaturality A (A ⮕' B)] [HasFunProp (A ⮕' A ⮕' B) (A ⮕' B)]
               [h : HasDupFunFun A B]

      def dupFunFun : (A ⮕' A ⮕' B) ⮕ (A ⮕' B) := DefFunFun.toFunctor h.defDupFunFun

    end HasDupFunFun

  end HasNaturality



  namespace IsSortNatUniverse

    open IsSortNatUniverse

    class HasLinearCatFun (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw, iww} W]
                          [IsSortNatUniverse.{u} W] extends
      IsFunUniverse.HasCatIdFun sort.{max 1 u w} W,
      IsFunUniverse.HasCatCompFun sort.{max 1 u w} sort.{max 1 u w} sort.{max 1 u w} W where
    [hasRevAppFunFun (A B : Category sort.{max 1 u w} W) : HasNaturality.HasRevAppFunFun A B]
    [hasCompFunFunFun (A B C : Category sort.{max 1 u w} W) : HasNaturality.HasCompFunFunFun A B C]

    namespace HasLinearCatFun

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]
               [IsSortNatUniverse.{u} W] [h : HasLinearCatFun.{u} W]

      instance (A B : univ.{u} W) : HasNaturality.HasRevAppFunFun A B :=
      h.hasRevAppFunFun A B

      instance (A B C : univ.{u} W) : HasNaturality.HasCompFunFunFun A B C :=
      h.hasCompFunFunFun A B C

      def idFun (A : univ.{u} W) : A ⟶ A := IsFunUniverse.HasCatIdFun.idFun A

      def revAppFun {A : univ.{u} W} (a : A) (B : univ.{u} W) :
        (A ⟶ B) ⟶ B :=
      HasNaturality.HasRevAppFun.revAppFun A B a

      def revAppFunFun (A B : univ.{u} W) : A ⟶ (A ⟶ B) ⟶ B :=
      HasNaturality.HasRevAppFunFun.revAppFunFun A B

      def compFun {A B C : univ.{u} W} (F : A ⟶ B) (G : B ⟶ C) : A ⟶ C :=
      IsFunUniverse.HasCatCompFun.compFun F G

      def compFunFun {A B : univ.{u} W} (F : A ⟶ B) (C : univ.{u} W) :
        (B ⟶ C) ⟶ (A ⟶ C) :=
      HasNaturality.HasCompFunFun.compFunFun A B C F

      def compFunFunFun (A B C : univ.{u} W) : (A ⟶ B) ⟶ (B ⟶ C) ⟶ (A ⟶ C) :=
      HasNaturality.HasCompFunFunFun.compFunFunFun A B C

      instance hasLinearFunOp : HasLinearFunOp (univ.{u} W) :=
      { defIdFun         := λ A     => toDefFun (idFun A),
        defRevAppFun     := λ A B   => ⟨λ a => toDefFun (revAppFun a B),
                                        toDefFun (revAppFunFun A B)⟩,
        defCompFun       := λ A B C => ⟨λ F => ⟨λ G => toDefFun (compFun F G),
                                                toDefFun (compFunFun F C)⟩,
                                        toDefFun (compFunFunFun A B C)⟩ }

    end HasLinearCatFun

    class HasAffineCatFun (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw, iww} W]
                          [HasSubLinearFunOp W] [IsSortNatUniverse.{u} W] extends
      HasLinearCatFun.{u} W,
      IsFunUniverse.HasCatConstFun sort.{max 1 u w} sort.{max 1 u w} W where
    [hasConstFunFun (A B : Category sort.{max 1 u w} W) : HasNaturality.HasConstFunFun A B]

    namespace HasAffineCatFun

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W] [HasSubLinearFunOp W]
               [IsSortNatUniverse.{u} W] [h : HasAffineCatFun.{u} W]

      instance (A B : univ.{u} W) : HasNaturality.HasConstFunFun A B := h.hasConstFunFun A B

      def constFun (A : univ.{u} W) {B : univ.{u} W} (b : B) : A ⟶ B :=
      IsFunUniverse.HasCatConstFun.constFun A b

      def constFunFun (A B : univ.{u} W) : B ⟶ (A ⟶ B) :=
      HasNaturality.HasConstFunFun.constFunFun A B

      instance hasAffineFunOp : HasAffineFunOp (univ.{u} W) :=
      { defConstFun := λ A B => ⟨λ b => toDefFun (constFun A b),
                                 toDefFun (constFunFun A B)⟩ }

    end HasAffineCatFun

    class HasFullCatFun (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw, iww} W]
                        [HasSubLinearFunOp W] [HasNonLinearFunOp W] [IsSortNatUniverse.{u} W]
                        extends
      HasAffineCatFun.{u} W where
    [hasDupFunFun (A B : Category sort.{max 1 u w} W) : HasNaturality.HasDupFunFun A B]

    namespace HasFullCatFun

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W] [HasSubLinearFunOp W]
               [HasNonLinearFunOp W] [IsSortNatUniverse.{u} W] [h : HasFullCatFun.{u} W]

      instance (A B : univ.{u} W) : HasNaturality.HasDupFunFun A B := h.hasDupFunFun A B

      def dupFun {A B : univ.{u} W} (F : A ⟶ A ⟶ B) : A ⟶ B :=
      HasNaturality.HasDupFun.dupFun A B F

      def dupFunFun (A B : univ.{u} W) : (A ⟶ A ⟶ B) ⟶ (A ⟶ B) :=
      HasNaturality.HasDupFunFun.dupFunFun A B

      instance hasFullFunOp : HasFullFunOp (univ.{u} W) :=
      { defDupFun := λ A B => ⟨λ F => toDefFun (dupFun F),
                               toDefFun (dupFunFun A B)⟩ }

    end HasFullCatFun

  end IsSortNatUniverse

end CategoryTheory
