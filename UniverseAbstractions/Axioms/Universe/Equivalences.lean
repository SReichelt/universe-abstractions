import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.FunctorExtensionality
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.CategoryTheory.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v uv vu u_v iu



def HasEquivalences.Inv {U V UV VU : Universe} [HasIdentity U]
                        [HasFunctors U V UV] [HasFunctors V U VU]
                        {A : U} {B : V} (toFun : A ⟶ B) (invFun : B ⟶ A) :=
∀ a, invFun (toFun a) ≃ a

class HasEquivalences (U : Universe.{u}) (V : Universe.{v}) [HasIdentity U] [HasIdentity V]
                      {UV : Universe.{uv}} {VU : Universe.{vu}}
                      [HasFunctors U V UV] [HasFunctors V U VU]
                      (U_V : outParam Universe.{u_v}) where
(Equiv                                    : U → V → U_V)
(toFun    {A : U} {B : V}                 : Equiv A B → (A ⟶ B))
(invFun   {A : U} {B : V}                 : Equiv A B → (B ⟶ A))
(leftInv  {A : U} {B : V} (E : Equiv A B) : HasEquivalences.Inv (toFun E) (invFun E))
(rightInv {A : U} {B : V} (E : Equiv A B) : HasEquivalences.Inv (invFun E) (toFun E))

namespace HasEquivalences

  variable {U V UV VU U_V : Universe} [HasIdentity U] [HasIdentity V]
           [HasFunctors U V UV] [HasFunctors V U VU] [HasEquivalences U V U_V]

  -- Work around bug (?) that turns `UV` and `VU` into explicit parameters.
  @[reducible] def Equiv' (A : U) (B : V) : U_V := Equiv (UV := UV) (VU := VU) A B
  infix:20 " ⟷ " => HasEquivalences.Equiv'

  def to  {A : U} {B : V} (E : A ⟷ B) (a : A) : B := (toFun  E) a
  def inv {A : U} {B : V} (E : A ⟷ B) (b : B) : A := (invFun E) b

end HasEquivalences



  def HasInternalEquivalences.InvExt {U : Universe} [HasIdentity U] [HasInternalFunctors U]
                                     [HasLinearFunOp U]
                                     {A B : U} {toFun : A ⟶ B} {invFun : B ⟶ A}
                                     (inv : HasEquivalences.Inv toFun invFun) :=
  invFun • toFun ≃{▻ inv ◅} HasLinearFunOp.idFun A

class HasInternalEquivalences (U : Universe.{u}) [HasIdentity U] [HasInternalFunctors U]
                              [HasLinearFunOp U] [HasInternalProducts U]
  extends HasEquivalences U U U where
(defElimFun  (A B : U)                 :
   (A ⟷ B)
   ⟶{λ E => HasProducts.intro (HasEquivalences.toFun E) (HasEquivalences.invFun E)}
   (A ⟶ B) ⊓ (B ⟶ A))
(leftInvExt  {A B : U} (E : Equiv A B) : HasInternalEquivalences.InvExt (leftInv  E))
(rightInvExt {A B : U} (E : Equiv A B) : HasInternalEquivalences.InvExt (rightInv E))

namespace HasInternalEquivalences

  open MetaRelation HasFunctors HasCongrArg HasCongrFun HasLinearFunOp HasLinearFunExt HasEquivalences

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U]
           [HasLinearFunOp U] [HasLinearFunExt U]
           [HasInternalProducts U] [HasInternalEquivalences U]

  @[reducible] def elimFun (A B : U) : (A ⟷ B) ⟶ (A ⟶ B) ⊓ (B ⟶ A) := defElimFun A B

  structure HalfEquivDesc {A B : U} (toFun : A ⟶ B) (invFun : B ⟶ A) where
  (inv    : Inv toFun invFun)
  (invExt : InvExt inv)

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

    def fromHalfEquivDescs {A B : U} {toFun : A ⟶ B} {invFun : B ⟶ A}
                           (left : HalfEquivDesc toFun invFun)
                           (right : HalfEquivDesc invFun toFun) :
      EquivDesc A B :=
    fromFullEquivDesc ⟨left, right⟩

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

  notation:20 A:21 " ⟷{" desc:0 "} " B:21 => HasInternalEquivalences.DefEquiv A B desc
  notation:20 A:21 " ⟷{" left:0 "," right:0 "} " B:21 =>
  HasInternalEquivalences.DefEquiv A B (HasInternalEquivalences.EquivDesc.fromHalfEquivDescs left right)

  variable {A B : U}

  def toDesc  (E : A ⟷ B) : HalfEquivDesc (toFun E) (invFun E) := ⟨leftInv  E, leftInvExt  E⟩
  def invDesc (E : A ⟷ B) : HalfEquivDesc (invFun E) (toFun E) := ⟨rightInv E, rightInvExt E⟩

  def fullDesc     (E : A ⟷ B) : FullEquivDesc (toFun E) (invFun E) := ⟨toDesc E, invDesc E⟩
  def fullSymmDesc (E : A ⟷ B) : FullEquivDesc (invFun E) (toFun E) := ⟨invDesc E, toDesc E⟩

  def desc     (E : A ⟷ B) : EquivDesc A B := ⟨toFun E, invFun E, fullDesc     E⟩
  def symmDesc (E : A ⟷ B) : EquivDesc B A := ⟨invFun E, toFun E, fullSymmDesc E⟩

  def toDefEquiv (E : A ⟷ B) : A ⟷{desc E} B := ⟨E, HasRefl.refl (toFun E), HasRefl.refl (invFun E)⟩
  def fromDefEquiv {desc : EquivDesc A B} (E : A ⟷{desc} B) : A ⟷ B := E.E

  @[simp] theorem fromToDefEquiv (E : A ⟷ B) : fromDefEquiv (toDefEquiv E) = E := rfl

  instance {E : A ⟷ B} : CoeDep ⌈A ⟷ B⌉ E (A ⟷{desc E} B) := ⟨toDefEquiv E⟩
  instance {desc : EquivDesc A B} : Coe (A ⟷{desc} B) ⌈A ⟷ B⌉ := ⟨fromDefEquiv⟩

  def byToFunDef  {desc : EquivDesc A B} {E : A ⟷{desc} B} :
    toFun  (fromDefEquiv E) ≃ desc.toFun  :=
  E.toFunEq

  def byInvFunDef {desc : EquivDesc A B} {E : A ⟷{desc} B} :
    invFun (fromDefEquiv E) ≃ desc.invFun :=
  E.invFunEq

  def byToDef  {desc : EquivDesc A B} {E : A ⟷{desc} B} {a : A} :
    to  (fromDefEquiv E) a ≃ desc.toFun  a :=
  congrFun byToFunDef  a

  def byInvDef {desc : EquivDesc A B} {E : A ⟷{desc} B} {b : B} :
    inv (fromDefEquiv E) b ≃ desc.invFun b :=
  congrFun byInvFunDef b

end HasInternalEquivalences



class HasEquivOp (U : Universe.{u}) [HasIdentity U] [HasInternalFunctors U]
                 [HasLinearFunOp U] [HasLinearFunOp.HasLinearFunExt U] [HasInternalProducts U]
                 [HasInternalEquivalences U] where
(defRefl  (A : U)                             :
   A ⟷{HasInternalEquivalences.EquivDesc.refl A} A)
(defSymm  {A B : U} (E : A ⟷ B)               :
   B ⟷{HasInternalEquivalences.EquivDesc.symm (HasInternalEquivalences.desc E)} A)
(defTrans {A B C : U} (E : A ⟷ B) (F : B ⟷ C) :
   A ⟷{HasInternalEquivalences.EquivDesc.trans (HasInternalEquivalences.desc E)
                                               (HasInternalEquivalences.desc F)} C)

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

end HasEquivOp

class HasEquivOpFun (U : Universe.{u}) [HasIdentity U] [HasInternalFunctors U]
                    [HasLinearFunOp U] [HasLinearFunOp.HasLinearFunExt U] [HasInternalProducts U]
                    [HasInternalEquivalences U] [HasEquivOp U] where
(defSymmFun     (A B : U)                           :
   (A ⟷ B) ⟶{λ E => HasEquivOp.symm E} (B ⟷ A))
(defTransFun    {A B : U} (E : A ⟷ B) (C : U)       :
   (B ⟷ C) ⟶{λ F => HasEquivOp.trans E F} (A ⟷ C))
(defTransFunFun (A B C : U)                         :
   (A ⟷ B) ⟶{λ E => defTransFun E C} ((B ⟷ C) ⟶ (A ⟷ C)))

namespace HasEquivOpFun

  open MetaRelation HasFunctors HasEquivalences

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasLinearFunOp U]
           [HasLinearFunOp.HasLinearFunExt U] [HasInternalProducts U] [HasInternalEquivalences U]
           [HasEquivOp U] [HasEquivOpFun U]

  @[reducible] def symmFun (A B : U) : (A ⟷ B) ⟶ (B ⟷ A) := defSymmFun A B

  instance symm.isFunApp {A B : U} {E : A ⟷ B} : IsFunApp (A ⟷ B) (HasEquivOp.symm E) :=
  { F := symmFun A B,
    a := E,
    e := byDef }

  instance hasSymmFun : HasSymmFun (α := U) Equiv' :=
  { defSymmFun := defSymmFun }

  @[reducible] def transFun {A B : U} (E : A ⟷ B) (C : U) : (B ⟷ C) ⟶ (A ⟷ C) := defTransFun E C
  @[reducible] def transFunFun (A B C : U) : (A ⟷ B) ⟶ (B ⟷ C) ⟶ (A ⟷ C) := defTransFunFun A B C

  instance trans.isFunApp {A B C : U} {E : A ⟷ B} {F : B ⟷ C} : IsFunApp (B ⟷ C) (HasEquivOp.trans E F) :=
  { F := transFun E C,
    a := F,
    e := byDef }

  instance transFun.isFunApp {A B C : U} {E : A ⟷ B} : IsFunApp (A ⟷ B) (transFun E C) :=
  { F := transFunFun A B C,
    a := E,
    e := byDef }

  instance hasTransFun : HasTransFun (α := U) Equiv' :=
  { defTransFun    := defTransFun,
    defTransFunFun := defTransFunFun }

  -- TODO: groupoid

end HasEquivOpFun



def DependentEquivalence {U : Universe} [HasIdentity U] [HasInternalFunctors U]
                         [HasLinearFunOp U] [HasLinearFunOp.HasLinearFunExt U]
                         [HasInternalProducts U] [HasInternalEquivalences U]
                         {A B : U} (E : A ⟷ B) (a : A) (b : B) :=
HasEquivalences.to E a ≃ b
notation:25 a:26 " ≃[" E:0 "] " b:26 => DependentEquivalence E a b

namespace DependentEquivalence

  open MetaRelation DependentMetaRelation HasFunctors HasCongrArg HasLinearFunOp
       HasEquivalences HasInternalEquivalences

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U]
           [HasLinearFunOp U] [HasLinearFunExt U]
           [HasInternalProducts U] [HasInternalEquivalences U] [HasEquivOp U]

  def toInv {A B : U} {E : A ⟷ B} {a : A} {b : B} (e : a ≃[E] b) : a ≃ inv E b :=
  congrArg (invFun E) e • (leftInv E a)⁻¹

  def fromInv {A B : U} {E : A ⟷ B} {a : A} {b : B} (e : a ≃ inv E b) : a ≃[E] b :=
  rightInv E b • congrArg (toFun E) e

  def compDepInd {A B : U} {E : A ⟷ B} {a : A} {b₁ b₂ : B} (e : a ≃[E] b₁) (f : b₁ ≃ b₂) :
    a ≃[E] b₂ :=
  f • e

  def compIndDep {A B : U} {E : A ⟷ B} {a₁ a₂ : A} {b : B} (f : a₁ ≃ a₂) (e : a₂ ≃[E] b) :
    a₁ ≃[E] b :=
  e • congrArg (toFun E) f

  def refl {A : U} (a : A) :
    a ≃[HasRefl.refl A] a :=
  HasInstanceEquivalences.trans byToDef byDef

  def symm {A B : U} {E : A ⟷ B} {a : A} {b : B} (e : a ≃[E] b) :
    b ≃[E⁻¹] a :=
  leftInv E a • congrArg (invFun E) e⁻¹ • byToDef

  def trans {A B C : U} {E : A ⟷ B} {F : B ⟷ C} {a : A} {b : B} {c : C} (e : a ≃[E] b) (f : b ≃[F] c) :
    a ≃[F • E] c :=
  compIndDep e f • byDef • byToDef

  def fromEq {A : U} {a₁ a₂ : A} (e : a₁ ≃ a₂) : a₁ ≃[HasRefl.refl A] a₂ :=
  HasInstanceEquivalences.trans (refl a₁) e

  def toEq {A : U} {a₁ a₂ : A} (e : a₁ ≃[HasRefl.refl A] a₂) : a₁ ≃ a₂ :=
  HasInstanceEquivalences.trans (refl a₁)⁻¹ e

  instance isDependentEquivalence : IsDependentEquivalence (U := U) (R := Equiv') DependentEquivalence :=
  { refl  := refl,
    symm  := symm
    trans := trans }

  -- It would be nice to move these to `DependentMetaRelation`, but currently the dependent
  -- meta-relation isn't found automatically at all, so for now we define the notation
  -- specifically for `DependentEquivalence`.
  notation:90 g:91 " [•] " f:90 => DependentEquivalence.trans f g
  postfix:max "[⁻¹]" => DependentEquivalence.symm

end DependentEquivalence



-- A helper type class that summarizes everything we need for type equivalences to act as instance
-- equivalences in a universe of universes.

class HasTypeIdentity (U : Universe.{u}) where
[hasIdentity             : HasIdentity.{u, iu}            U]
[hasInternalFunctors     : HasInternalFunctors            U]
[hasLinearFunOp          : HasLinearFunOp                 U]
[hasLinearFunExt         : HasLinearFunOp.HasLinearFunExt U]
[hasInternalProducts     : HasInternalProducts            U]
[hasInternalEquivalences : HasInternalEquivalences        U]
[hasEquivOp              : HasEquivOp                     U]

namespace HasTypeIdentity

  open HasFunctors HasLinearFunOp HasEquivalences HasEquivOp

  variable {U : Universe} [HasTypeIdentity U]

  instance : HasIdentity             U := hasIdentity
  instance : HasInternalFunctors     U := hasInternalFunctors
  instance : HasLinearFunOp          U := hasLinearFunOp
  instance : HasLinearFunExt         U := hasLinearFunExt
  instance : HasInternalProducts     U := hasInternalProducts
  instance : HasInternalEquivalences U := hasInternalEquivalences
  instance : HasEquivOp              U := hasEquivOp

  instance typeEquivalences : HasInstanceEquivalences {U} U := ⟨λ _ => equivRelation⟩

  def castTo  {A B : ⌊U⌋} (E : A ≃ B) (a : A) : B := to  E a
  def castInv {A B : ⌊U⌋} (E : A ≃ B) (b : B) : A := inv E b

  def castToDef  {V VpU : Universe} [HasFunctors V {U} VpU] {B : V} {f : B → ⌊U⌋}
                 {φ : B ⟶{f} ⌊U⌋} {b : B} (a : ⌈⸥(fromDefFun φ) b⸤⌉) :
    f b :=
  castTo  byDef a

  def castInvDef {V VpU : Universe} [HasFunctors V {U} VpU] {B : V} {f : B → ⌊U⌋}
                 {φ : B ⟶{f} ⌊U⌋} {b : B} (a : f b) :
    ⌈⸥(fromDefFun φ) b⸤⌉ :=
  castInv byDef a

end HasTypeIdentity
