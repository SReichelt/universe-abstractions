import UniverseAbstractions.CategoryTheory.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u u' u'' v w ww iw iww



namespace CategoryTheory

  open MetaRelation MetaFunctor HasCatProp HasCatProp.Category HasFunctors

  structure FunDesc {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]
                    [HasCatProp.{u} W] [HasCatProp.{v} W] {A : Category.{u} W} {B : Category.{v} W}
                    (φ : A → B) :
    Sort (max 1 u w iw) where
  (F  : PreFunctor (Hom A) (Hom B) φ)
  [hF : IsPreorderFunctor F]

  namespace FunDesc

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]

    section

      variable [HasCatProp.{u} W] [HasCatProp.{v} W] {A : Category.{u} W} {B : Category.{v} W}
               {φ : A → B} (F : FunDesc φ)

      instance : IsPreorderFunctor F.F := F.hF

    end

    section

      variable [HasCatProp.{u} W] (A : Category.{u} W)

      @[reducible] def idPreFun : PreFunctor (Hom A) (Hom A) id :=
      PreFunctor.idFun.preFunctor (Hom A)

      instance : IsPreorderFunctor (idPreFun A) := inferInstance

      def idFun : FunDesc (@id A) := ⟨idPreFun A⟩

    end

    section

      variable [HasSubLinearFunOp W] [HasCatProp.{u} W] [HasCatProp.{v} W]
               (A : Category.{u} W) {B : Category.{v} W} (b : B)

      @[reducible] def constPreFun : PreFunctor (Hom A) (Hom B) (Function.const A b) :=
      PreFunctor.constFun.preFunctor (Hom A) (Hom B) b

      -- Work around Lean bug that makes definition in `Type.lean` fail.
      instance : IsPreorderFunctor (constPreFun A b) := inferInstance

      def constFun : FunDesc (Function.const A b) := ⟨constPreFun A b⟩

    end

    section

      variable [HasCatProp.{u} W] [HasCatProp.{u'} W] [HasCatProp.{u''} W]
               {A : Category.{u} W} {B : Category.{u'} W} {C : Category.{u''} W}
               {φ : A → B} {ψ : B → C} (F : FunDesc φ) (G : FunDesc ψ)

      @[reducible] def compPreFun : PreFunctor (Hom A) (Hom C) (ψ ∘ φ) :=
      PreFunctor.compFun.preFunctor F.F G.F

      -- Work around Lean bug that makes definition in `Type.lean` fail.
      instance : IsPreorderFunctor (compPreFun F G) := PreFunctor.compFun.isPreorderFunctor _ _

      def compFun : FunDesc (ψ ∘ φ) := ⟨compPreFun F G⟩

    end

  end FunDesc

  class HasFunProp {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W] [HasCatProp.{u} W]
                   [HasCatProp.{v} W] (A : Category.{u} W) (B : Category.{v} W) where
  (Fun              : MetaProperty (A → B) W)
  (desc {φ : A → B} : Fun φ → FunDesc φ)

  namespace HasFunProp

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]

    structure Functor [HasCatProp.{u} W] [HasCatProp.{v} W] (A : Category.{u} W) (B : Category.{v} W)
                      [h : HasFunProp A B] :
      Sort (max 1 u v w) where
    {φ : A → B}
    (F : h.Fun φ)

    namespace Functor

      infixr:20 " ⮕ " => CategoryTheory.HasFunProp.Functor

      variable [HasCatProp.{u} W] [HasCatProp.{v} W] {A : Category.{u} W} {B : Category.{v} W}
               [h : HasFunProp A B]

      instance coeFun : CoeFun (A ⮕ B) (λ _ => A → B) := ⟨Functor.φ⟩

      variable (F : A ⮕ B)

      def desc : FunDesc F.φ := h.desc F.F
      @[reducible] def preFun : PreFunctor (Hom A) (Hom B) F.φ := (desc F).F
      @[reducible] def mapHom {a b : A} (f : a ⇾ b) : F a ⇾ F b := (preFun F) f

      def reflEq (a : A) : mapHom F (idHom a) ≃ idHom (F a) :=
      IsReflFunctor.reflEq (F := preFun F) a

      def transEq {a b c : A} (f : a ⇾ b) (g : b ⇾ c) :
        mapHom F (g • f) ≃ mapHom F g • mapHom F f :=
      IsTransFunctor.transEq (F := preFun F) f g

      def mapHomCongrArg {a b : A} {f₁ f₂ : a ⇾ b} (e : f₁ ≃ f₂) :
        mapHom F f₁ ≃ mapHom F f₂ :=
      HasCongrArg.congrArg ((preFun F).baseFun a b) e

    end Functor

    structure DefFun [HasCatProp.{u} W] [HasCatProp.{v} W] {A : Category.{u} W} {B : Category.{v} W}
                     [h : HasFunProp A B] {φ : A → B} (desc : FunDesc φ) where
    (F            : h.Fun φ)
    (eq (a b : A) : (h.desc F).F.baseFun a b ≃ desc.F.baseFun a b)

    namespace DefFun

      variable [HasCatProp.{u} W] [HasCatProp.{v} W] {A : Category.{u} W} {B : Category.{v} W}
               [h : HasFunProp A B] {φ : A → B}

      @[reducible] def toFunctor {desc : FunDesc φ} (F : DefFun desc) : A ⮕ B := ⟨F.F⟩

      def byMapHomDef {Φ : ∀ {a b}, (a ⇾ b) → (φ a ⇾ φ b)} {Φ' : ∀ a b, (a ⇾ b) ⟶{Φ} (φ a ⇾ φ b)}
                      {hF : IsPreorderFunctor ⟨λ a b => HasFunctors.fromDefFun (Φ' a b)⟩}
                      {F : DefFun ⟨⟨λ a b => HasFunctors.fromDefFun (Φ' a b)⟩⟩}
                      {a b : A} {f : a ⇾ b} :
        Functor.mapHom (toFunctor F) f ≃ Φ f :=
      byDef • HasCongrFun.congrFun (F.eq a b) f

    end DefFun

    class HasTrivialFunctorialityCondition [HasCatProp.{u} W] [HasCatProp.{v} W]
                                           (A : Category.{u} W) (B : Category.{v} W)
                                           [h : HasFunProp A B] where
    (functor {φ : A → B} (desc : FunDesc φ) : DefFun desc)

    namespace HasTrivialFunctorialityCondition

      variable [HasCatProp.{u} W] [HasCatProp.{v} W] {A : Category.{u} W} {B : Category.{v} W}
               [HasFunProp A B] [h : HasTrivialFunctorialityCondition A B]
      
      def defFun {φ : A → B} {desc : FunDesc φ} : DefFun desc := h.functor desc

    end HasTrivialFunctorialityCondition

    class HasIdFun [HasCatProp.{u} W] (A : Category.{u} W) [hFunAA : HasFunProp A A] where 
    (defIdFun : DefFun (FunDesc.idFun A))

    namespace HasIdFun

      instance trivial [HasCatProp.{u} W] (A : Category.{u} W) [HasFunProp A A]
                       [HasTrivialFunctorialityCondition A A] :
        HasIdFun A :=
      ⟨HasTrivialFunctorialityCondition.defFun⟩

      def idFun [HasCatProp.{u} W] (A : Category.{u} W) [HasFunProp A A] [h : HasIdFun A] : A ⮕ A :=
      DefFun.toFunctor h.defIdFun

    end HasIdFun

    class HasConstFun [HasSubLinearFunOp W] [HasCatProp.{u} W] [HasCatProp.{v} W]
                      (A : Category.{u} W) (B : Category.{v} W) [hFunAB : HasFunProp A B] where
    (defConstFun (b : B) : DefFun (FunDesc.constFun A b))

    namespace HasConstFun

      instance trivial [HasSubLinearFunOp W] [HasCatProp.{u} W] [HasCatProp.{v} W]
                       (A : Category.{u} W) (B : Category.{v} W) [HasFunProp A B]
                       [HasTrivialFunctorialityCondition A B] :
        HasConstFun A B :=
      ⟨λ _ => HasTrivialFunctorialityCondition.defFun⟩

      def constFun [HasSubLinearFunOp W] [HasCatProp.{u} W] [HasCatProp.{v} W] (A : Category.{u} W)
                   {B : Category.{v} W} [HasFunProp A B] [h : HasConstFun A B] (b : B) :
        A ⮕ B :=
      DefFun.toFunctor (h.defConstFun b)

    end HasConstFun

    class HasCompFun [HasCatProp.{u} W] [HasCatProp.{u'} W] [HasCatProp.{u''} W]
                     (A : Category.{u} W) (B : Category.{u'} W) (C : Category.{u''} W)
                     [hFunAB : HasFunProp A B] [hFunBC : HasFunProp B C] [hFunAC : HasFunProp A C]
                     where
    (defCompFun (F : A ⮕ B) (G : B ⮕ C) :
       DefFun (FunDesc.compFun (Functor.desc F) (Functor.desc G)))

    namespace HasCompFun

      instance trivial [HasCatProp.{u} W] [HasCatProp.{u'} W] [HasCatProp.{u''} W]
                       (A : Category.{u} W) (B : Category.{u'} W) (C : Category.{u''} W)
                       [HasFunProp A B] [HasFunProp B C] [HasFunProp A C]
                       [HasTrivialFunctorialityCondition A C] :
        HasCompFun A B C :=
      ⟨λ _ _ => HasTrivialFunctorialityCondition.defFun⟩

      def compFun [HasCatProp.{u} W] [HasCatProp.{u'} W] [HasCatProp.{u''} W]
                  {A : Category.{u} W} {B : Category.{u'} W} {C : Category.{u''} W}
                  [HasFunProp A B] [HasFunProp B C] [HasFunProp A C] [h : HasCompFun A B C]
                  (F : A ⮕ B) (G : B ⮕ C) :
        A ⮕ C :=
      DefFun.toFunctor (h.defCompFun F G)

      notation:90 G:91 " ⭗ " F:90 => CategoryTheory.HasFunProp.HasCompFun.compFun F G

    end HasCompFun

  end HasFunProp



  class IsFunUniverse (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw, iww} W]
                      [hCatUniv : IsCatUniverse.{u} W] where
  [hasFun (A B : Category W) : HasFunProp (W := W) A B]

  namespace IsFunUniverse

    open HasFunProp

    section

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]
               [IsCatUniverse.{u} W] [h : IsFunUniverse.{u} W]

      instance (A B : Category W) : HasFunProp A B := h.hasFun A B

    end

    class HasLinearFunctors (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw, iww} W]
                            [hCatUniv : IsCatUniverse.{u} W]
                            [hFunUniv : IsFunUniverse.{u} W] where
    [hasIdFun (A : Category W) : HasIdFun A]
    [hasCompFun (A B C : Category W) : HasCompFun A B C]

    namespace HasLinearFunctors

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]
               [IsCatUniverse.{u} W] [IsFunUniverse.{u} W] [h : HasLinearFunctors W]

      instance (A : Category W) : HasIdFun A := h.hasIdFun A
      instance (A B C : Category W) : HasCompFun A B C := h.hasCompFun A B C

      def idFun (A : Category W) : A ⮕ A := HasFunProp.HasIdFun.idFun A
      def compFun {A B C : Category W} (F : A ⮕ B) (G : B ⮕ C) : A ⮕ C := G ⭗ F

    end HasLinearFunctors

    class HasAffineFunctors (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw, iww} W]
                            [hCatUniv : IsCatUniverse.{u} W]
                            [hFunUniv : IsFunUniverse.{u} W] [HasSubLinearFunOp W] extends
      HasLinearFunctors W where
    [hasConstFun (A B : Category W) : HasConstFun A B]

    namespace HasAffineFunctors

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]
               [IsCatUniverse.{u} W] [IsFunUniverse.{u} W] [HasSubLinearFunOp W]
               [h : HasAffineFunctors W]

      instance (A B : Category W) : HasConstFun A B := h.hasConstFun A B

      def constFun (A : Category W) {B : Category W} (b : B) : A ⮕ B :=
      HasFunProp.HasConstFun.constFun A b

    end HasAffineFunctors

  end IsFunUniverse

end CategoryTheory
