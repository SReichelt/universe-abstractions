import UniverseAbstractions.CategoryTheory.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u uu v vv w ww iw iww



namespace CategoryTheory

  open Universe MetaRelation MetaFunctor HasTransFun HasSymmFun
       HasCatProp HasCatProp.Category HasIsomorphisms
       HasFunctors HasCongrArg

  structure FunDesc {U : Universe.{u, uu}} {V : Universe.{v, vv}} {W : Universe.{w, ww}}
                    [IsHomUniverse.{w, ww, iw, iww} W] [HasCatProp U W] [HasCatProp V W]
                    {A : Category U W} {B : Category V W} (φ : A → B) :
    Sort (max 1 u w iw) where
  (F  : PreFunctor (Hom A) (Hom B) φ)
  [hF : IsPreorderFunctor F]

  namespace FunDesc

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]

    section

      variable {U V : Universe} [HasCatProp U W] [HasCatProp V W]
               {A : Category U W} {B : Category V W} {φ : A → B} (F : FunDesc φ)

      instance : IsPreorderFunctor F.F := F.hF

    end

    section

      variable {U : Universe} [HasCatProp U W] (A : Category U W)

      @[reducible] def idPreFun : PreFunctor (Hom A) (Hom A) id :=
      PreFunctor.idFun.preFunctor (Hom A)

      instance : IsPreorderFunctor (idPreFun A) := inferInstance

      def idFun : FunDesc (@id A) := ⟨idPreFun A⟩

    end

    section

      variable [HasSubLinearFunOp W] {U V : Universe} [HasCatProp U W] [HasCatProp V W]
               (A : Category U W) {B : Category V W} (b : B)

      @[reducible] def constPreFun : PreFunctor (Hom A) (Hom B) (Function.const A b) :=
      PreFunctor.constFun.preFunctor (Hom A) (Hom B) b

      -- Work around Lean bug that makes definition in `Type.lean` fail.
      instance : IsPreorderFunctor (constPreFun A b) := inferInstance

      def constFun : FunDesc (Function.const A b) := ⟨constPreFun A b⟩

    end

    section

      variable {U U' U'' : Universe} [HasCatProp U W] [HasCatProp U' W] [HasCatProp U'' W]
               {A : Category U W} {B : Category U' W} {C : Category U'' W}
               {φ : A → B} {ψ : B → C} (F : FunDesc φ) (G : FunDesc ψ)

      @[reducible] def compPreFun : PreFunctor (Hom A) (Hom C) (ψ ∘ φ) :=
      PreFunctor.compFun.preFunctor F.F G.F

      -- Work around Lean bug that makes definition in `Type.lean` fail.
      instance : IsPreorderFunctor (compPreFun F G) := PreFunctor.compFun.isPreorderFunctor _ _

      def compFun : FunDesc (ψ ∘ φ) := ⟨compPreFun F G⟩

    end

  end FunDesc



  class HasFunProp {U : Universe.{u, uu}} {V : Universe.{v, vv}} {W : Universe.{w, ww}}
                   [IsHomUniverse.{w, ww, iw, iww} W] [HasCatProp U W] [HasCatProp V W]
                   (A : Category U W) (B : Category V W) where
  (Fun              : MetaProperty (A → B) W)
  (desc {φ : A → B} : Fun φ → FunDesc φ)

  namespace HasFunProp

    variable {U : Universe.{u, uu}} {V : Universe.{v, vv}} {W : Universe.{w, ww}}
             [IsHomUniverse.{w, ww, iw, iww} W] [HasCatProp U W] [HasCatProp V W]

    structure Functor (A : Category U W) (B : Category V W) [h : HasFunProp A B] :
      Sort (max 1 u v w) where
    {φ : A → B}
    (F : h.Fun φ)

    namespace Functor

      infixr:20 " ⮕ " => CategoryTheory.HasFunProp.Functor

      variable {A : Category U W} {B : Category V W} [h : HasFunProp A B]

      instance coeFun : CoeFun (A ⮕ B) (λ _ => A → B) := ⟨Functor.φ⟩

      variable (F : A ⮕ B)

      def desc : FunDesc F.φ := h.desc F.F
      @[reducible] def preFun : PreFunctor (Hom A) (Hom B) F.φ := (desc F).F
      @[reducible] def mapHom {a b : A} (f : a ⇾ b) : F a ⇾ F b := (preFun F) f

      def mapHom.reflEq (a : A) : mapHom F (idHom a) ≃ idHom (F a) :=
      IsReflFunctor.reflEq (F := preFun F) a

      def mapHom.transEq {a b c : A} (f : a ⇾ b) (g : b ⇾ c) :
        mapHom F (g • f) ≃ mapHom F g • mapHom F f :=
      IsTransFunctor.transEq (F := preFun F) f g

      def mapHom.congrArg {a b : A} {f₁ f₂ : a ⇾ b} (e : f₁ ≃ f₂) :
        mapHom F f₁ ≃ mapHom F f₂ :=
      HasCongrArg.congrArg ((preFun F).baseFun a b) e

      def mapHomReflEq {a : A} {f : a ⇾ a} (e : f ≃ idHom a) :
        mapHom F f ≃ idHom (F a) :=
      mapHom.reflEq F a • mapHom.congrArg F e

      def mapIsoDesc {a b : A} (e : IsoDesc a b) : IsoDesc (F a) (F b) :=
      { toHom  := mapHom F e.toHom,
        invHom := mapHom F e.invHom,
        isInv  := { leftInv  := mapHalfInv (preFun F) e.isInv.leftInv,
                    rightInv := mapHalfInv (preFun F) e.isInv.rightInv } }

    end Functor

    structure DefFun {A : Category U W} {B : Category V W} [h : HasFunProp A B] {φ : A → B}
                     (desc : FunDesc φ) where
    (F            : h.Fun φ)
    (eq (a b : A) : (h.desc F).F.baseFun a b ≃ desc.F.baseFun a b)

    namespace DefFun

      variable {A : Category U W} {B : Category V W} [h : HasFunProp A B] {φ : A → B}

      @[reducible] def toFunctor {desc : FunDesc φ} (F : DefFun desc) : A ⮕ B := ⟨F.F⟩

      def byMapHomDef {Φ : ∀ {a b}, (a ⇾ b) → (φ a ⇾ φ b)} {Φ' : ∀ a b, (a ⇾ b) ⟶{Φ} (φ a ⇾ φ b)}
                      {hF : IsPreorderFunctor ⟨λ a b => HasFunctors.fromDefFun (Φ' a b)⟩}
                      {F : DefFun ⟨⟨λ a b => HasFunctors.fromDefFun (Φ' a b)⟩⟩}
                      {a b : A} {f : a ⇾ b} :
        Functor.mapHom (toFunctor F) f ≃ Φ f :=
      byDef • HasCongrFun.congrFun (F.eq a b) f

    end DefFun

    class HasTrivialFunctorialityCondition (A : Category U W) (B : Category V W)
                                           [h : HasFunProp A B] where
    (functor {φ : A → B} (desc : FunDesc φ) : DefFun desc)

    namespace HasTrivialFunctorialityCondition

      variable {A : Category U W} {B : Category V W} [HasFunProp A B]
               [h : HasTrivialFunctorialityCondition A B]
      
      def defFun {φ : A → B} {desc : FunDesc φ} : DefFun desc := h.functor desc

    end HasTrivialFunctorialityCondition

  end HasFunProp



  class HasIsoPreFun {U : Universe.{u, uu}} {V : Universe.{v, vv}} {W : Universe.{w, ww}}
                     [IsHomUniverse.{w, ww, iw, iww} W] [IsCatUniverse U W] [IsCatUniverse V W]
                     {A : Category U W} {B : Category V W} [hFunProp : HasFunProp A B]
                     (F : A ⮕ B) where
  (defMapIso {a b : A} (e : a ⇿ b) :
     HasIsoRel.DefIso (HasFunProp.Functor.mapIsoDesc F (HasIsoRel.desc e)))
  (defMapIsoFun (a b : A) : (a ⇿ b) ⟶{λ e => (defMapIso e).e} (F a ⇿ F b))

  namespace HasIsoPreFun

    open HasFunProp HasFunProp.Functor HasIsoRel HasIsoOp HasIsomorphisms

    variable {U V W : Universe} [IsHomUniverse W] [IsCatUniverse U W] [IsCatUniverse V W]
             {A : Category U W} {B : Category V W} [HasFunProp A B] (F : A ⮕ B)
             [h : HasIsoPreFun F]

    def mapIso {a b : A} (e : a ⇿ b) : F a ⇿ F b := (h.defMapIso e).e

    @[reducible] def mapIsoFun (a b : A) : (a ⇿ b) ⟶ (F a ⇿ F b) := h.defMapIsoFun a b

    instance {a b : A} (e : a ⇿ b) : IsFunApp (a ⇿ b) (mapIso F e) :=
    { F := mapIsoFun F a b,
      a := e,
      e := byDef }

    def mapIsoCongrArg {a b : A} {e₁ e₂ : a ⇿ b} (e : e₁ ≃ e₂) : mapIso F e₁ ≃ mapIso F e₂ :=
    HasCongrArg.defCongrArg (h.defMapIsoFun a b) e

    def toHomComm  {a b : A} (e : a ⇿ b) : toHom  (mapIso F e) ≃ mapHom F (toHom  e) := byToDef
    def invHomComm {a b : A} (e : a ⇿ b) : invHom (mapIso F e) ≃ mapHom F (invHom e) := byInvDef

    def isoReflEq (a : A) : mapIso F (idIso a) ≃ idIso (F a) :=
    toHomInj ((toHom.reflEq (F a))⁻¹ •
             mapHom.reflEq F a •
             (mapHom.congrArg F (toHom.reflEq a) •
              toHomComm F (idIso a)))

    def isoSymmEq {a b : A} (e : a ⇿ b) : mapIso F e⁻¹ ≃ (mapIso F e)⁻¹ :=
    toHomInj ((invHomComm F e •
              toHom.symmEq (mapIso F e))⁻¹ •
             (mapHom.congrArg F (toHom.symmEq e) •
              toHomComm F e⁻¹))

    def isoTransEq {a b c : A} (e : a ⇿ b) (f : b ⇿ c) :
      mapIso F (f • e) ≃ mapIso F f • mapIso F e :=
    toHomInj ((congrArgTrans (toHomComm F e) (toHomComm F f) •
              toHom.transEq (mapIso F e) (mapIso F f))⁻¹ •
             mapHom.transEq F (toHom e) (toHom f) •
             (mapHom.congrArg F (toHom.transEq e f) •
              toHomComm F (f • e)))

    def isoPreFun : PreFunctor (Category.Iso A) (Category.Iso B) F.φ := ⟨mapIsoFun F⟩

    instance isoPreFun.isReflFunctor : IsReflFunctor (isoPreFun F) :=
    ⟨λ a => isoReflEq F a • byDef⟩

    instance isoPreFun.isSymmFunctor : IsSymmFunctor (isoPreFun F) :=
    ⟨λ e => (congrArgSymm byDef)⁻¹ • isoSymmEq F e • byDef⟩

    instance isoPreFun.isTransFunctor : IsTransFunctor (isoPreFun F) :=
    ⟨λ e f => (congrArgTrans byDef byDef)⁻¹ • isoTransEq F e f • byDef⟩

    instance isoPreFun.isPreorderFunctor    : IsPreorderFunctor    (isoPreFun F) := ⟨⟩
    instance isoPreFun.isEquivalenceFunctor : IsEquivalenceFunctor (isoPreFun F) := ⟨⟩

    @[reducible] def isoPreFun' : PreFunctor (Iso' A) (Iso' B) F.φ := isoPreFun F

    instance isoPreFun'.isReflFunctor : IsReflFunctor (isoPreFun' F) :=
    ⟨λ a => (DefCat.catReflEq (A := defIsoCat) (F a))⁻¹ •
            (isoPreFun.isReflFunctor F).reflEq a •
            congrArg (mapIsoFun F a a) (DefCat.catReflEq (A := defIsoCat) a)⟩

    instance isoPreFun'.isTransFunctor : IsTransFunctor (isoPreFun' F) :=
    ⟨λ {a b c} e f => (DefCat.catTransEq (A := defIsoCat) ((isoPreFun F) e) ((isoPreFun F) f))⁻¹ •
                      (isoPreFun.isTransFunctor F).transEq e f •
                      congrArg (mapIsoFun F a c) (DefCat.catTransEq (A := defIsoCat) e f)⟩

    instance isoPreFun'.isPreorderFunctor : IsPreorderFunctor (isoPreFun' F) := ⟨⟩

    def isoFunDesc : FunDesc (A := iso A) (B := iso B) F.φ := ⟨isoPreFun' F⟩

  end HasIsoPreFun

  class HasIsoFun {U : Universe.{u, uu}} {V : Universe.{v, vv}} {W : Universe.{w, ww}}
                  [IsHomUniverse.{w, ww, iw, iww} W] [IsCatUniverse U W] [IsCatUniverse V W]
                  {A : Category U W} {B : Category V W} [hFunProp : HasFunProp A B]
                  [hIsoFunProp : HasFunProp (iso A) (iso B)] (F : A ⮕ B) extends
    HasIsoPreFun F where
  (defIsoFun : HasFunProp.DefFun (HasIsoPreFun.isoFunDesc F))

  namespace HasIsoFun

    open HasFunProp HasFunProp.Functor HasIsoPreFun

    variable {U V W : Universe} [IsHomUniverse W] [IsCatUniverse U W] [IsCatUniverse V W]
             {A : Category U W} {B : Category V W} [HasFunProp A B]
             [HasFunProp (iso A) (iso B)] (F : A ⮕ B) [h : HasIsoFun F]

    @[reducible] def isoFunctor : iso A ⮕ iso B := DefFun.toFunctor h.defIsoFun

    def mapIso' {a b : A} (e : a ⇿ b) : F a ⇿ F b := mapHom (isoFunctor F) e

    def mapIsoEq {a b : A} (e : a ⇿ b) : mapIso' F e ≃ mapIso F e := DefFun.byMapHomDef

  end HasIsoFun



  class IsFunUniverse (U : Universe.{u, uu}) (V : Universe.{v, vv}) (W : Universe.{w, ww})
                      [IsHomUniverse.{w, ww, iw, iww} W]
                      [hU : IsCatUniverse U W] [hV : IsCatUniverse V W] where
  [hasFun (A : Category U W) (B : Category V W) : HasFunProp A B]
  [hasIsoFun {A : Category U W} {B : Category V W} (F : A ⮕ B) : HasIsoFun F]

  namespace IsFunUniverse

    open HasFunProp HasFunProp.Functor HasIsoRel HasIsomorphisms HasIsoPreFun

    section

      variable {U V W : Universe} [IsHomUniverse W] [IsCatUniverse U W] [IsCatUniverse V W]
               [h : IsFunUniverse U V W]

      instance (A : Category U W) (B : Category V W) : HasFunProp A B := h.hasFun A B

      variable {A : Category U W} {B : Category V W}

      instance (F : A ⮕ B) : HasIsoFun F := h.hasIsoFun F

      def mapHomToMapIso {φ : A → B} {F G : (h.hasFun A B).Fun φ} {a b : A} {e : a ⇿ b} :
        mapHom ⟨F⟩ (toHom e) ≃ mapHom ⟨G⟩ (toHom e) →
        mapIso ⟨F⟩ e         ≃ mapIso ⟨G⟩ e :=
      λ h₁ => toHomInj ((toHomComm ⟨G⟩ e)⁻¹ • h₁ • toHomComm ⟨F⟩ e)

    end

    section

      variable (U : Universe.{u, uu}) (V : Universe.{v, vv}) (W : Universe.{w, ww})
               [IsHomUniverse W] [IsCatUniverse U W] [IsCatUniverse V W] [h : IsFunUniverse U V W]

      def univ : Universe.{max 1 u v w, max 1 u uu v vv w ww} :=
      binaryOpUniverse (Category.univ U W) (Category.univ V W) (λ A B => A ⮕ B)

      instance (priority := low) hasFunctors :
        HasFunctors (Category.univ U W) (Category.univ V W) (univ U V W) :=
      { Fun   := binaryOpUniverse.type,
        apply := Functor.φ }

      instance (priority := low) hasCongrArg :
        HasCongrArg (Category.univ U W) (Category.univ V W) :=
      ⟨λ {_ _} F {_ _} e => mapIso F e⟩

    end

  end IsFunUniverse

  class IsSortFunUniverse (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw, iww} W]
                          [IsSortCatUniverse.{u} W] [IsSortCatUniverse.{v} W] extends
    IsFunUniverse sort.{u} sort.{v} W

end CategoryTheory
