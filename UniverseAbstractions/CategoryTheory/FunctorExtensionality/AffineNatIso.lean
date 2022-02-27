import UniverseAbstractions.CategoryTheory.Basic
import UniverseAbstractions.CategoryTheory.Functors
import UniverseAbstractions.CategoryTheory.NaturalTransformations
import UniverseAbstractions.CategoryTheory.Isomorphisms



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u w ww iw iww



namespace CategoryTheory

  open HasCatProp HasCatProp.Category HasFunProp HasFunProp.Functor HasNatRel HasNaturality
       HasIsoNat HasIsoNaturality
       HasLinearFunOp HasSubLinearFunOp

  namespace IsIsoUniverse

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W] [IsCatUniverse.{u} W]
             [IsFunUniverse.{u} W] [IsNatUniverse.{u} W] [h : IsIsoUniverse.{u} W]
             [HasSubLinearFunOp W] [IsFunUniverse.HasAffineFunctors W]
             [IsNatUniverse.HasAffineFunctors W]

    def rightConstNat (A : univ W) {B C : univ W} (b : B) (G : B ⟶ C) {a₁ a₂ : A} (f : a₁ ⇾ a₂) :
      mapHom (G • constFun A b) f
      ≃'{G b ⇾ G b}
      mapHom (constFun A (G b)) f :=
    reflEq G b • mapHomCongrArg G byConstFunDef • byCompFunDef ▹{idHom (G b)}◃ byConstFunDef

    def rightConstNatNat (A : univ W) {B : univ W} (b : B) (C : univ W) {G₁ G₂ : B ⟶ C} (ε : G₁ ⇾ G₂) (a : A) :
      nat (mapHom (compFunFun (constFun A b) C) ε) a
      ≃'{G₁ b ⇾ G₂ b}
      nat (mapHom (constFunFun A C • revAppFun b C) ε) a :=
    byCompFunFunDef
    ▹{nat ε b}◃
    byRevAppFunDef •
    byConstFunFunDef •
    natCongrArg (byCompFunDef (F := revAppFun b C) (G := constFunFun A C)) a

    def rightConstNatNatNat (A B C : univ W) {b₁ b₂ : B} (g : b₁ ⇾ b₂) (G : B ⟶ C) (a : A) :
      nat (nat (mapHom (compFunFunFun A B C • constFunFun A B) g) G) a
      ≃'{G b₁ ⇾ G b₂}
      nat (nat (mapHom (revCompFunFun (B ⟶ C) (constFunFun A C) • revAppFunFun B C) g) G) a :=
    mapHomCongrArg G byConstFunFunDef •
    byCompFunFunFunDef (η := mapHom (constFunFun A B) g) •
    natCongrArg (natCongrArg (byCompFunDef (F := constFunFun A B)
                                           (G := compFunFunFun A B C)
                                           (f := g)) G) a
    ▹{mapHom G g}◃
    byRevAppFunFunDef •
    byConstFunFunDef (g := nat (mapHom (revAppFunFun B C) g) G) •
    natCongrArg (byRevCompFunFunDef (G := constFunFun A C) (η := mapHom (revAppFunFun B C) g) •
                 natCongrArg (byCompFunDef (F := revAppFunFun B C)
                                           (G := revCompFunFun (B ⟶ C) (constFunFun A C))
                                           (f := g)) G) a

    class HasRightConstNat (A B C : univ W) where
    (defRightConstNat (b : B) (G : B ⟶ C) : StrictDefNatIso (φ := λ _ => G b) (rightConstNat A b G))
    (defRightConstNatNat (b : B) : StrictDefNatNatIso (defRightConstNat b) (rightConstNatNat A b C))
    (defRightConstNatNatNat : StrictDefNatNatNatIso defRightConstNatNat (rightConstNatNatNat A B C))

    def leftConstNat {A B C : univ W} (F : A ⟶ B) (c : C) {a₁ a₂ : A} (f : a₁ ⇾ a₂) :
      mapHom (constFun B c • F) f
      ≃'{c ⇾ c}
      mapHom (constFun A c) f :=
    byConstFunDef • byCompFunDef ▹{idHom c}◃ byConstFunDef

    def leftConstNatNat {A B : univ W} (F : A ⟶ B) (C : univ W) {c₁ c₂ : C} (h : c₁ ⇾ c₂) (a : A) :
      nat (mapHom (compFunFun F C • constFunFun B C) h) a
      ≃'{c₁ ⇾ c₂}
      nat (mapHom (constFunFun A C) h) a :=
    byConstFunFunDef •
    byCompFunFunDef (ε := mapHom (constFunFun B C) h) •
    natCongrArg (byCompFunDef (F := constFunFun B C) (G := compFunFun F C)) a
    ▹{h}◃
    byConstFunFunDef

    def leftConstNatNatNat (A B C : univ W) {F₁ F₂ : A ⟶ B} (η : F₁ ⇾ F₂) (c : C) (a : A) :
      nat (nat (mapHom (compFunFun (constFunFun B C) (A ⟶ C) • compFunFunFun A B C) η) c) a
      ≃'{c ⇾ c}
      nat (nat (mapHom (constFun (A ⟶ B) (constFunFun A C)) η) c) a :=
    byConstFunDef •
    byCompFunFunFunDef (G := constFun B c) •
    natCongrArg (byCompFunFunDef (F := constFunFun B C) (ε := mapHom (compFunFunFun A B C) η) •
                 natCongrArg (byCompFunDef (F := compFunFunFun A B C)
                                           (G := compFunFun (constFunFun B C) (A ⟶ C))) c) a
    ▹{idHom c}◃
    natReflEq' (constFun A c) a •
    natCongrArg (natReflEq' (constFunFun A C) c •
                 natCongrArg (byConstFunDef (b := constFunFun A C)) c) a

    class HasLeftConstNat (A B C : univ W) where
    (defLeftConstNat (F : A ⟶ B) (c : C) : StrictDefNatIso (φ := λ _ => c) (leftConstNat F c))
    (defLeftConstNatNat (F : A ⟶ B) : StrictDefNatNatIso (defLeftConstNat F) (leftConstNatNat F C))
    (defLeftConstNatNatNat : StrictDefNatNatNatIso defLeftConstNatNat (leftConstNatNatNat A B C))

  end IsIsoUniverse

end CategoryTheory
