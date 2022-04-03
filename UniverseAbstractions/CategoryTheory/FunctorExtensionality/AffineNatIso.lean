import UniverseAbstractions.CategoryTheory.Basic
import UniverseAbstractions.CategoryTheory.Functors
import UniverseAbstractions.CategoryTheory.NaturalTransformations
import UniverseAbstractions.CategoryTheory.MultiFunctors
import UniverseAbstractions.CategoryTheory.MultiFunctorIsomorphisms
import UniverseAbstractions.CategoryTheory.Functors.Nested
import UniverseAbstractions.CategoryTheory.Functors.FunDef



set_option autoBoundImplicitLocal false
set_option maxHeartbeats 100000
--set_option pp.universes true

universe u w ww iw iww



namespace CategoryTheory

  open HasCatProp HasCatProp.Category HasFunProp HasFunProp.Functor HasNatRel HasNaturality HasIsoNat
       HasLinearFunOp HasSubLinearFunOp

  namespace IsSortNatUniverse

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W] [HasSubLinearFunOp W]
             [IsSortNatUniverse.{u} W] [HasAffineCatFun.{u} W]

    def rightConstNat (A : univ.{u} W) {B C : univ.{u} W} (b : B) (G : B ⟶ C) {a₁ a₂ : A} (f : a₁ ⇾ a₂) :
      mapHom (G • constFun A b) f
      ≃'{G b ⇾ G b}
      mapHom (constFun A (G b)) f :=
    mapHom.reflEq G b • mapHom.congrArg G byConstFunDef • byCompFunDef ▹{idHom (G b)}◃ byConstFunDef

    def rightConstNatNat (A : univ.{u} W) {B : univ.{u} W} (b : B) (C : univ.{u} W) {G₁ G₂ : B ⟶ C} (ε : G₁ ⇾ G₂) (a : A) :
      nat (mapHom (compFunFun (constFun A b) C) ε) a
      ≃'{G₁ b ⇾ G₂ b}
      nat (mapHom (constFunFun A C • revAppFun b C) ε) a :=
    byCompFunFunDef
    ▹{nat ε b}◃
    byRevAppFunDef •
    byConstFunFunDef •
    nat.congrArg (byCompFunDef (F := revAppFun b C) (G := constFunFun A C)) a

    def rightConstNatNatNat (A B C : univ.{u} W) {b₁ b₂ : B} (g : b₁ ⇾ b₂) (G : B ⟶ C) (a : A) :
      nat (nat (mapHom (compFunFunFun A B C • constFunFun A B) g) G) a
      ≃'{G b₁ ⇾ G b₂}
      nat (nat (mapHom (revCompFunFun (B ⟶ C) (constFunFun A C) • revAppFunFun B C) g) G) a :=
    mapHom.congrArg G byConstFunFunDef •
    byCompFunFunFunDef (η := mapHom (constFunFun A B) g) •
    nat.congrArg (nat.congrArg (byCompFunDef (F := constFunFun A B)
                                             (G := compFunFunFun A B C)
                                             (f := g)) G) a
    ▹{mapHom G g}◃
    byRevAppFunFunDef •
    byConstFunFunDef (g := nat (mapHom (revAppFunFun B C) g) G) •
    nat.congrArg (byRevCompFunFunDef (G := constFunFun A C) (η := mapHom (revAppFunFun B C) g) •
                  nat.congrArg (byCompFunDef (F := revAppFunFun B C)
                                             (G := revCompFunFun (B ⟶ C) (constFunFun A C))
                                             (f := g)) G) a

    class HasRightConstNat (A B C : univ.{u} W) where
    (defRightConstNat (b : B) (G : B ⟶ C) : StrictDefNatIso (φ := λ _ => G b) (rightConstNat A b G))
    (defRightConstNatNat (b : B) : StrictDefNatNatIso (defRightConstNat b) (rightConstNatNat A b C))
    (defRightConstNatNatNat : StrictDefNatNatNatIso defRightConstNatNat (rightConstNatNatNat A B C))

    def leftConstNat {A B C : univ.{u} W} (F : A ⟶ B) (c : C) {a₁ a₂ : A} (f : a₁ ⇾ a₂) :
      mapHom (constFun B c • F) f
      ≃'{c ⇾ c}
      mapHom (constFun A c) f :=
    byConstFunDef • byCompFunDef ▹{idHom c}◃ byConstFunDef

    def leftConstNatNat {A B : univ.{u} W} (F : A ⟶ B) (C : univ.{u} W) {c₁ c₂ : C} (h : c₁ ⇾ c₂) (a : A) :
      nat (mapHom (compFunFun F C • constFunFun B C) h) a
      ≃'{c₁ ⇾ c₂}
      nat (mapHom (constFunFun A C) h) a :=
    byConstFunFunDef •
    byCompFunFunDef (ε := mapHom (constFunFun B C) h) •
    nat.congrArg (byCompFunDef (F := constFunFun B C) (G := compFunFun F C)) a
    ▹{h}◃
    byConstFunFunDef

    def leftConstNatNatNat (A B C : univ.{u} W) {F₁ F₂ : A ⟶ B} (η : F₁ ⇾ F₂) (c : C) (a : A) :
      nat (nat (mapHom (compFunFun (constFunFun B C) (A ⟶ C) • compFunFunFun A B C) η) c) a
      ≃'{c ⇾ c}
      nat (nat (mapHom (constFun (A ⟶ B) (constFunFun A C)) η) c) a :=
    byConstFunDef •
    byCompFunFunFunDef (G := constFun B c) •
    nat.congrArg (byCompFunFunDef (F := constFunFun B C) (ε := mapHom (compFunFunFun A B C) η) •
                  nat.congrArg (byCompFunDef (F := compFunFunFun A B C)
                                             (G := compFunFun (constFunFun B C) (A ⟶ C))) c) a
    ▹{idHom c}◃
    nat.reflEq' (constFun A c) a •
    nat.congrArg (nat.reflEq' (constFunFun A C) c •
                  nat.congrArg (byConstFunDef (b := constFunFun A C)) c) a

    class HasLeftConstNat (A B C : univ.{u} W) where
    (defLeftConstNat (F : A ⟶ B) (c : C) : StrictDefNatIso (φ := λ _ => c) (leftConstNat F c))
    (defLeftConstNatNat (F : A ⟶ B) : StrictDefNatNatIso (defLeftConstNat F) (leftConstNatNat F C))
    (defLeftConstNatNatNat : StrictDefNatNatNatIso defLeftConstNatNat (leftConstNatNatNat A B C))

  end IsSortNatUniverse

end CategoryTheory
