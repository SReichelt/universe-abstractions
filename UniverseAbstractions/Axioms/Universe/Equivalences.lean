import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.FunctorExtensionality
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.CategoryTheory.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v uv vu u_v



class HasEquivalences (U : Universe.{u}) (V : Universe.{v}) [HasIdentity U] [HasIdentity V]
                      {UV : Universe.{uv}} {VU : Universe.{vu}} [HasIdentity UV] [HasIdentity VU]
                      [HasFunctors U V UV] [HasFunctors V U VU]
                      (U_V : outParam Universe.{u_v}) where
(Equiv                                            : U → V → U_V)
(toFun    {A : U} {B : V} (E : Equiv A B)         : A ⟶ B)
(invFun   {A : U} {B : V} (E : Equiv A B)         : B ⟶ A)
(leftInv  {A : U} {B : V} (E : Equiv A B) (a : A) : invFun E (toFun E a) ≃ a)
(rightInv {A : U} {B : V} (E : Equiv A B) (b : B) : toFun E (invFun E b) ≃ b)

namespace HasEquivalences

  variable {U V UV VU U_V : Universe}
           [HasIdentity U] [HasIdentity V] [HasIdentity UV] [HasIdentity VU]
           [HasFunctors U V UV] [HasFunctors V U VU] [HasEquivalences U V (UV := UV) (VU := VU) U_V]

  -- Work around bug (?) that turns `UV` and `VU` into explicit parameters.
  @[reducible] def Equiv' (A : U) (B : V) : U_V := Equiv (UV := UV) (VU := VU) A B
  infix:20 " ⟷ " => HasEquivalences.Equiv'

end HasEquivalences



class HasInternalEquivalences (U : Universe.{u}) [HasIdentity U] [HasInternalFunctors U]
                              [HasLinearFunOp U] [HasInternalProducts U]
  extends HasEquivalences U U U where
(defElimFun  (A B : U)                 :
   (A ⟷ B)
   ⟶[λ E => HasProducts.intro (HasEquivalences.toFun E) (HasEquivalences.invFun E)]
   (A ⟶ B) ⊓ (B ⟶ A))
(leftInvExt  {A B : U} (E : Equiv A B) :
   invFun E • toFun E
   ≃[λ a => HasFunctors.byDef⁻¹ • leftInv E a • HasFunctors.byDef]
   HasLinearFunOp.idFun A)
(rightInvExt {A B : U} (E : Equiv A B) :
   toFun E • invFun E
   ≃[λ b => HasFunctors.byDef⁻¹ • rightInv E b • HasFunctors.byDef]
   HasLinearFunOp.idFun B)

namespace HasInternalEquivalences

  open MetaRelation HasFunctors HasCongrArg HasCongrFun HasLinearFunOp HasLinearFunExt HasEquivalences

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U]
           [HasLinearFunOp U] [HasLinearFunExt U]
           [HasInternalProducts U] [HasInternalEquivalences U]

  @[reducible] def elimFun (A B : U) : (A ⟷ B) ⟶ (A ⟶ B) ⊓ (B ⟶ A) := defElimFun A B

  structure HalfEquivDesc {A B : U} (toFun : A ⟶ B) (invFun : B ⟶ A) where
  (inv (a : A) : invFun (toFun a) ≃ a)
  (invExt      : invFun • toFun
                 ≃[λ a => byDef⁻¹ • inv a • byDef]
                 idFun A)

  namespace HalfEquivDesc

    def refl (A : U) : HalfEquivDesc (idFun A) (idFun A) :=
    { inv    := λ _ => byDef • byDef,
      invExt := rightId (idFun A) }

    def trans {A B C : U}
              {eToFun : A ⟶ B} {eInvFun : B ⟶ A} (e : HalfEquivDesc eToFun eInvFun)
              {fToFun : B ⟶ C} {fInvFun : C ⟶ B} (f : HalfEquivDesc fToFun fInvFun) :
      HalfEquivDesc (fToFun • eToFun) (eInvFun • fInvFun) :=
    { inv    := λ a => e.inv a • congrArg eInvFun (f.inv (eToFun a)) • byDef • byArgDef,
      invExt := e.invExt •
                defCongrArg (defRevCompFunFun A eInvFun)
                            (leftId eToFun •
                             defCongrArg (defCompFunFun eToFun B) f.invExt •
                             (compAssoc eToFun fToFun fInvFun)⁻¹) •
                compAssoc (fToFun • eToFun) fInvFun eInvFun }

  end HalfEquivDesc

  structure FullEquivDesc {A B : U} (toFun : A ⟶ B) (invFun : B ⟶ A) where
  (left  : HalfEquivDesc toFun invFun)
  (right : HalfEquivDesc invFun toFun)

  namespace FullEquivDesc

    def refl (A : U) : FullEquivDesc (idFun A) (idFun A) :=
    ⟨HalfEquivDesc.refl A, HalfEquivDesc.refl A⟩

    def symm {A B : U} {eToFun : A ⟶ B} {eInvFun : B ⟶ A} (e : FullEquivDesc eToFun eInvFun) :
      FullEquivDesc eInvFun eToFun :=
    ⟨e.right, e.left⟩

    def trans {A B C : U}
              {eToFun : A ⟶ B} {eInvFun : B ⟶ A} (e : FullEquivDesc eToFun eInvFun)
              {fToFun : B ⟶ C} {fInvFun : C ⟶ B} (f : FullEquivDesc fToFun fInvFun) :
      FullEquivDesc (fToFun • eToFun) (eInvFun • fInvFun) :=
    ⟨HalfEquivDesc.trans e.left f.left, HalfEquivDesc.trans f.right e.right⟩

  end FullEquivDesc

  structure EquivDesc (A B : U) where
  (toFun  : A ⟶ B)
  (invFun : B ⟶ A)
  (equiv  : FullEquivDesc toFun invFun)

  namespace EquivDesc

    def fromFullEquivDesc {A B : U} {toFun : A ⟶ B} {invFun : B ⟶ A}
                          (equiv : FullEquivDesc toFun invFun) :
      EquivDesc A B :=
    ⟨toFun, invFun, equiv⟩

    def refl (A : U) : EquivDesc A A :=
    fromFullEquivDesc (FullEquivDesc.refl A)

    def symm {A B : U} (e : EquivDesc A B) : EquivDesc B A :=
    fromFullEquivDesc (FullEquivDesc.symm e.equiv)

    def trans {A B C : U} (e : EquivDesc A B) (f : EquivDesc B C) : EquivDesc A C :=
    fromFullEquivDesc (FullEquivDesc.trans e.equiv f.equiv)

  end EquivDesc

  structure DefEquiv (A B : U) (desc : EquivDesc A B) where
  (E        : A ⟷ B)
  (toFunEq  : toFun  E ≃ desc.toFun)
  (invFunEq : invFun E ≃ desc.invFun)

  notation:20 A:21 " ⟷[" desc:0 "] " B:21 => HasInternalEquivalences.DefEquiv A B desc

  variable {A B : U}

  def toDesc  (E : A ⟷ B) : HalfEquivDesc (toFun E) (invFun E) := ⟨leftInv  E, leftInvExt  E⟩
  def invDesc (E : A ⟷ B) : HalfEquivDesc (invFun E) (toFun E) := ⟨rightInv E, rightInvExt E⟩

  def fullDesc (E : A ⟷ B) : FullEquivDesc (toFun E) (invFun E) := ⟨toDesc E, invDesc E⟩

  def desc (E : A ⟷ B) : EquivDesc A B := ⟨toFun E, invFun E, fullDesc E⟩

  def toDefEquiv (E : A ⟷ B) : A ⟷[desc E] B := ⟨E, HasRefl.refl (toFun E), HasRefl.refl (invFun E)⟩
  def fromDefEquiv {desc : EquivDesc A B} (E : A ⟷[desc] B) : A ⟷ B := E.E

  @[simp] theorem fromToDefEquiv (E : A ⟷ B) : fromDefEquiv (toDefEquiv E) = E := rfl

  instance {E : A ⟷ B} : CoeDep ⌈A ⟷ B⌉ E (A ⟷[desc E] B) := ⟨toDefEquiv E⟩
  instance {desc : EquivDesc A B} : Coe (A ⟷[desc] B) ⌈A ⟷ B⌉ := ⟨fromDefEquiv⟩

end HasInternalEquivalences



class HasEquivOp (U : Universe.{u}) [HasIdentity U] [HasInternalFunctors U]
                 [HasLinearFunOp U] [HasLinearFunOp.HasLinearFunExt U] [HasInternalProducts U]
                 [HasInternalEquivalences U] where
(defRefl  (A : U)                             :
   A ⟷[HasInternalEquivalences.EquivDesc.refl A] A)
(defSymm  {A B : U} (E : A ⟷ B)               :
   B ⟷[HasInternalEquivalences.EquivDesc.symm (HasInternalEquivalences.desc E)] A)
(defTrans {A B C : U} (E : A ⟷ B) (F : B ⟷ C) :
   A ⟷[HasInternalEquivalences.EquivDesc.trans (HasInternalEquivalences.desc E)
                                               (HasInternalEquivalences.desc F)] C)

namespace HasEquivOp

  open Universe MetaRelation HasEquivalences

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasLinearFunOp U]
           [HasLinearFunOp.HasLinearFunExt U] [HasInternalProducts U] [HasInternalEquivalences U]
           [HasEquivOp U]

  @[reducible] def refl (A : U) : A ⟷ A := defRefl A
  @[reducible] def symm {A B : U} (E : A ⟷ B) : B ⟷ A := defSymm E
  @[reducible] def trans {A B C : U} (E : A ⟷ B) (F : B ⟷ C) : A ⟷ C := defTrans E F

  instance isEquivalence : IsEquivalence (α := U) Equiv' :=
  { refl  := refl,
    symm  := symm
    trans := trans }

  def equivRelation : EquivalenceRelation U U := ⟨Equiv'⟩

  instance typeEquivalences : HasInstanceEquivalences (singletonUniverse U) U := ⟨λ _ => equivRelation⟩

end HasEquivOp

class HasEquivOpFun (U : Universe.{u}) [HasIdentity U] [HasInternalFunctors U]
                    [HasLinearFunOp U] [HasLinearFunOp.HasLinearFunExt U] [HasInternalProducts U]
                    [HasInternalEquivalences U] [HasEquivOp U] where
(defSymmFun     (A B : U)                           :
   (A ⟷ B) ⟶[λ E => HasEquivOp.symm E] (B ⟷ A))
(defTransFun    {A B : U} (E : A ⟷ B) (C : U)       :
   (B ⟷ C) ⟶[λ F => HasEquivOp.trans E F] (A ⟷ C))
(defTransFunFun (A B C : U)                         :
   (A ⟷ B) ⟶[λ E => defTransFun E C] ((B ⟷ C) ⟶ (A ⟷ C)))

namespace HasEquivOpFun

  open MetaRelation HasEquivalences 

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasLinearFunOp U]
           [HasLinearFunOp.HasLinearFunExt U] [HasInternalProducts U] [HasInternalEquivalences U]
           [HasEquivOp U] [HasEquivOpFun U]

  @[reducible] def symmFun (A B : U) : (A ⟷ B) ⟶ (B ⟷ A) := defSymmFun A B

  instance hasSymmFun : HasSymmFun (α := ⌈U⌉) Equiv' :=
  { defSymmFun := defSymmFun }

  @[reducible] def transFun {A B : U} (E : A ⟷ B) (C : U) : (B ⟷ C) ⟶ (A ⟷ C) := defTransFun E C
  @[reducible] def transFunFun (A B C : U) : (A ⟷ B) ⟶ (B ⟷ C) ⟶ (A ⟷ C) := defTransFunFun A B C

  instance hasTransFun : HasTransFun (α := ⌈U⌉) Equiv' :=
  { defTransFun    := defTransFun,
    defTransFunFun := defTransFunFun }

  -- TODO: groupoid

end HasEquivOpFun
