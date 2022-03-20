import UniverseAbstractions.CategoryTheory.Basic
import UniverseAbstractions.CategoryTheory.Functors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u uu u' uu' u'' uu'' v vv w ww iw iww



namespace CategoryTheory

  open MetaRelation MetaFunctor HasTransFun HasSymmFun
       HasCatProp HasCatProp.Category
       HasFunctors HasCongrArg

  namespace HasFunProp

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]

    class HasIdFun {U : Universe.{u, uu}} [HasCatProp U W] (A : Category U W)
                   [hFunAA : HasFunProp A A] where 
    (defIdFun : DefFun (FunDesc.idFun A))

    namespace HasIdFun

      instance trivial {U : Universe} [HasCatProp U W] (A : Category U W) [HasFunProp A A]
                       [HasTrivialFunctorialityCondition A A] :
        HasIdFun A :=
      ⟨HasTrivialFunctorialityCondition.defFun⟩

      def idFun {U : Universe} [HasCatProp U W] (A : Category U W) [HasFunProp A A]
                [h : HasIdFun A] :
        A ⮕ A :=
      DefFun.toFunctor h.defIdFun

    end HasIdFun

    class HasConstFun [HasSubLinearFunOp W] {U : Universe.{u, uu}} {V : Universe.{v, vv}}
                      [HasCatProp U W] [HasCatProp V W] (A : Category U W) (B : Category V W)
                      [hFunAB : HasFunProp A B] where
    (defConstFun (b : B) : DefFun (FunDesc.constFun A b))

    namespace HasConstFun

      instance trivial [HasSubLinearFunOp W] {U V : Universe} [HasCatProp U W] [HasCatProp V W]
                       (A : Category U W) (B : Category V W) [HasFunProp A B]
                       [HasTrivialFunctorialityCondition A B] :
        HasConstFun A B :=
      ⟨λ _ => HasTrivialFunctorialityCondition.defFun⟩

      def constFun [HasSubLinearFunOp W] {U V : Universe} [HasCatProp U W] [HasCatProp V W]
                   (A : Category U W) {B : Category V W} [HasFunProp A B] [h : HasConstFun A B]
                   (b : B) :
        A ⮕ B :=
      DefFun.toFunctor (h.defConstFun b)

    end HasConstFun

    class HasCompFun {U : Universe.{u, uu}} {U' : Universe.{u', uu'}} {U'' : Universe.{u'', uu''}}
                     [HasCatProp U W] [HasCatProp U' W] [HasCatProp U'' W]
                     (A : Category U W) (B : Category U' W) (C : Category U'' W)
                     [hFunAB : HasFunProp A B] [hFunBC : HasFunProp B C] [hFunAC : HasFunProp A C]
                     where
    (defCompFun (F : A ⮕ B) (G : B ⮕ C) :
       DefFun (FunDesc.compFun (Functor.desc F) (Functor.desc G)))

    namespace HasCompFun

      instance trivial {U U' U'' : Universe} [HasCatProp U W] [HasCatProp U' W] [HasCatProp U'' W]
                       (A : Category U W) (B : Category U' W) (C : Category U'' W)
                       [HasFunProp A B] [HasFunProp B C] [HasFunProp A C]
                       [HasTrivialFunctorialityCondition A C] :
        HasCompFun A B C :=
      ⟨λ _ _ => HasTrivialFunctorialityCondition.defFun⟩

      def compFun {U U' U'' : Universe} [HasCatProp U W] [HasCatProp U' W] [HasCatProp U'' W]
                  {A : Category U W} {B : Category U' W} {C : Category U'' W}
                  [HasFunProp A B] [HasFunProp B C] [HasFunProp A C] [h : HasCompFun A B C]
                  (F : A ⮕ B) (G : B ⮕ C) :
        A ⮕ C :=
      DefFun.toFunctor (h.defCompFun F G)

      notation:90 G:91 " ⭗ " F:90 => CategoryTheory.HasFunProp.HasCompFun.compFun F G

    end HasCompFun

  end HasFunProp



  namespace IsFunUniverse

    open HasCatProp

    class HasCatIdFun (U : Universe.{u, uu}) (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw, iww} W]
                      [IsCatUniverse U W] [IsFunUniverse U U W] where
    [hasIdFun (A : Category U W) : HasFunProp.HasIdFun A]

    namespace HasCatIdFun

      variable {U W : Universe} [IsHomUniverse W] [IsCatUniverse U W] [IsFunUniverse U U W]
               [h : HasCatIdFun U W]

      instance (A : Category U W) : HasFunProp.HasIdFun A := h.hasIdFun A

      def idFun (A : Category.univ U W) : A ⟶ A := HasFunProp.HasIdFun.idFun A

      instance : HasIdFun (Category.univ U W) := ⟨λ A => toDefFun (idFun A)⟩

    end HasCatIdFun

    class HasCatConstFun (U : Universe.{u, uu}) (V : Universe.{v, vv}) (W : Universe.{w, ww})
                         [IsHomUniverse.{w, ww, iw, iww} W] [IsCatUniverse U W] [IsCatUniverse V W]
                         [IsFunUniverse U V W] [HasSubLinearFunOp W] where
    [hasConstFun (A : Category U W) (B : Category V W) : HasFunProp.HasConstFun A B]

    namespace HasCatConstFun

      variable {U V W : Universe} [IsHomUniverse W] [IsCatUniverse U W] [IsCatUniverse V W]
               [IsFunUniverse U V W] [HasSubLinearFunOp W] [h : HasCatConstFun U V W]

      instance (A : Category.univ U W) (B : Category.univ V W) : HasFunProp.HasConstFun A B :=
      h.hasConstFun A B

      def constFun (A : Category.univ U W) {B : Category.univ V W} (b : B) : A ⟶ B :=
      HasFunProp.HasConstFun.constFun A b

      instance : HasConstFun (Category.univ U W) (Category.univ V W) :=
      ⟨λ A {_} b => toDefFun (constFun A b)⟩

    end HasCatConstFun

    class HasCatCompFun (U : Universe.{u, uu}) (U' : Universe.{u', uu'}) (U'' : Universe.{u'', uu''})
                        (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw, iww} W]
                        [IsCatUniverse U W] [IsCatUniverse U' W] [IsCatUniverse U'' W]
                        [IsFunUniverse U U' W] [IsFunUniverse U' U'' W] [IsFunUniverse U U'' W] where
    [hasCompFun (A : Category U W) (B : Category U' W) (C : Category U'' W) :
      HasFunProp.HasCompFun A B C]

    namespace HasCatCompFun

      variable {U U' U'' W : Universe} [IsHomUniverse W] [IsCatUniverse U W] [IsCatUniverse U' W]
               [IsCatUniverse U'' W] [IsFunUniverse U U' W] [IsFunUniverse U' U'' W]
               [IsFunUniverse U U'' W] [h : HasCatCompFun U U' U'' W]

      instance (A : Category.univ U W) (B : Category.univ U' W) (C : Category.univ U'' W) :
        HasFunProp.HasCompFun A B C :=
      h.hasCompFun A B C

      def compFun {A : Category.univ U W} {B : Category.univ U' W} {C : Category.univ U'' W}
                  (F : A ⟶ B) (G : B ⟶ C) :
        A ⟶ C :=
      G ⭗ F

      instance : HasCompFun (Category.univ U W) (Category.univ U' W) (Category.univ U'' W) :=
      ⟨λ F G => toDefFun (compFun F G)⟩

    end HasCatCompFun

  end IsFunUniverse

end CategoryTheory
