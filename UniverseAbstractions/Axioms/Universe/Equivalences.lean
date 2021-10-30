import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.FunctorExtensionality
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Axioms.CategoryTheory.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v uu vv uv vu u_v iu



structure HalfEquivDesc {U V UV VU : Universe} [HasIdentity U]
                        [HasFunctors U V UV] [HasFunctors V U VU]
                        {A : U} {B : V} (toFun : A ⟶ B) (invFun : B ⟶ A) where
(inv (a : A) : invFun (toFun a) ≃ a)

namespace HalfEquivDesc

  open HasFunctors HasCongrArg HasLinearFunOp HasLinearFunExt

  def refl {U UU : Universe} [HasIdentity U] [HasFunctors U U UU] [HasIdFun U] (A : U) :
    HalfEquivDesc (HasIdFun.idFun A) (HasIdFun.idFun A) :=
  ⟨λ _ => byDef • byDef⟩

  def trans {U V W UV VU VW WV UW WU : Universe}
            [HasIdentity U] [HasIdentity V] [HasIdentity W]
            [HasFunctors U V UV] [HasFunctors V U VU]
            [HasFunctors V W VW] [HasFunctors W V WV]
            [HasFunctors U W UW] [HasFunctors W U WU]
            [HasCompFun U V W] [HasCompFun W V U]
            [HasCongrArg V U] [HasCongrArg W U]
            {A : U} {B : V} {C : W}
            {eToFun : A ⟶ B} {eInvFun : B ⟶ A} (e : HalfEquivDesc eToFun eInvFun)
            {fToFun : B ⟶ C} {fInvFun : C ⟶ B} (f : HalfEquivDesc fToFun fInvFun) :
    HalfEquivDesc (fToFun ⊙ eToFun) (eInvFun ⊙ fInvFun) :=
  ⟨λ a => e.inv a • congrArg eInvFun (f.inv (eToFun a)) • byDef • byArgDef⟩

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U]
           [HasLinearFunOp U] [HasLinearFunExt U]

  class IsExtensional {A B : U} {toFun : A ⟶ B} {invFun : B ⟶ A}
                      (e : HalfEquivDesc toFun invFun) where
  (invExt : invFun ⊙ toFun ≃{▻ e.inv ◅} idFun A)

  namespace IsExtensional

    instance reflExt (A : U) : IsExtensional (refl A) :=
    ⟨rightId (idFun A)⟩

    instance transExt {A B C : U}
                      {eToFun : A ⟶ B} {eInvFun : B ⟶ A} (e : HalfEquivDesc eToFun eInvFun)
                      {fToFun : B ⟶ C} {fInvFun : C ⟶ B} (f : HalfEquivDesc fToFun fInvFun)
                      [he : IsExtensional e] [hf : IsExtensional f] :
      IsExtensional (trans e f) :=
    ⟨he.invExt •
     defCongrArg (defRevCompFunFun A eInvFun)
                 (leftId eToFun •
                  defCongrArg (defCompFunFun eToFun B) hf.invExt •
                  (compAssoc eToFun fToFun fInvFun)⁻¹) •
     compAssoc (fToFun • eToFun) fInvFun eInvFun⟩

  end IsExtensional

end HalfEquivDesc

structure EquivDesc {U V UV VU : Universe} [HasIdentity U] [HasIdentity V]
                    [HasFunctors U V UV] [HasFunctors V U VU] (A : U) (B : V) where
(toFun  : A ⟶ B)
(invFun : B ⟶ A)
(left   : HalfEquivDesc toFun invFun)
(right  : HalfEquivDesc invFun toFun)

namespace EquivDesc

  open HasLinearFunOp

  def fromHalfDescs {U V UV VU : Universe} [HasIdentity U] [HasIdentity V]
                    [HasFunctors U V UV] [HasFunctors V U VU] {A : U} {B : V}
                    {toFun : A ⟶ B} {invFun : B ⟶ A}
                    (left  : HalfEquivDesc toFun invFun)
                    (right : HalfEquivDesc invFun toFun) :
    EquivDesc A B :=
  ⟨toFun, invFun, left, right⟩

  def refl {U UU : Universe} [HasIdentity U] [HasFunctors U U UU] [HasIdFun U] (A : U) :
    EquivDesc A A :=
  ⟨HasIdFun.idFun A, HasIdFun.idFun A, HalfEquivDesc.refl A, HalfEquivDesc.refl A⟩

  def symm {U V UV VU : Universe} [HasIdentity U] [HasIdentity V]
           [HasFunctors U V UV] [HasFunctors V U VU] {A : U} {B : V}
           (e : EquivDesc A B) :
    EquivDesc B A :=
  ⟨e.invFun, e.toFun, e.right, e.left⟩

  def trans {U V W UV VU VW WV UW WU : Universe}
            [HasIdentity U] [HasIdentity V] [HasIdentity W]
            [HasFunctors U V UV] [HasFunctors V U VU]
            [HasFunctors V W VW] [HasFunctors W V WV]
            [HasFunctors U W UW] [HasFunctors W U WU]
            [HasCompFun U V W] [HasCompFun W V U]
            [HasCongrArg V U] [HasCongrArg W U] [HasCongrArg U W] [HasCongrArg V W]
            {A : U} {B : V} {C : W}
            (e : EquivDesc A B) (f : EquivDesc B C) :
    EquivDesc A C :=
  ⟨f.toFun ⊙ e.toFun, e.invFun ⊙ f.invFun,
   HalfEquivDesc.trans e.left f.left, HalfEquivDesc.trans f.right e.right⟩

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U]
           [HasLinearFunOp U] [HasLinearFunExt U]

  class IsExtensional {A B : U} (e : EquivDesc A B) where
  [leftExt  : HalfEquivDesc.IsExtensional e.left]
  [rightExt : HalfEquivDesc.IsExtensional e.right]

  namespace IsExtensional

    instance {A B : U} (e : EquivDesc A B) [he : IsExtensional e] :
      HalfEquivDesc.IsExtensional e.left :=
    he.leftExt

    instance {A B : U} (e : EquivDesc A B) [he : IsExtensional e] :
      HalfEquivDesc.IsExtensional e.right :=
    he.rightExt

    instance reflExt (A : U) : IsExtensional (refl A) :=
    { leftExt  := HalfEquivDesc.IsExtensional.reflExt A,
      rightExt := HalfEquivDesc.IsExtensional.reflExt A }

    instance symmExt {A B : U} (e : EquivDesc A B) [he : IsExtensional e] :
      IsExtensional (symm e) :=
    { leftExt  := he.rightExt,
      rightExt := he.leftExt }

    instance transExt {A B C : U} (e : EquivDesc A B) (f : EquivDesc B C)
                      [he : IsExtensional e] [hf : IsExtensional f] :
      IsExtensional (trans e f) :=
    { leftExt  := HalfEquivDesc.IsExtensional.transExt e.left  f.left,
      rightExt := HalfEquivDesc.IsExtensional.transExt f.right e.right }

  end IsExtensional

end EquivDesc



class HasEquivalences (U : Universe.{u}) (V : Universe.{v})
                      {UV : Universe.{uv}} {VU : Universe.{vu}}
                      [HasIdentity U] [HasIdentity V]
                      [HasFunctors U V UV] [HasFunctors V U VU]
                      (U_V : outParam Universe.{u_v}) where
(Equiv                : U → V → U_V)
(desc {A : U} {B : V} : Equiv A B → EquivDesc A B)

namespace HasEquivalences

  open MetaRelation HasCongrFun

  variable {U V UU VV UV VU U_V : Universe} [HasIdentity U] [HasIdentity V]
           [HasFunctors U V UV] [HasFunctors V U VU] [HasEquivalences U V U_V]

  -- Work around bug (?) that turns implicit into explicit universe parameters.
  @[reducible] def Equiv' (A : U) (B : V) : U_V := Equiv (UV := UV) (VU := VU) A B
  infix:20 " ⟷ " => HasEquivalences.Equiv'

  section

    variable {A : U} {B : V} (E : A ⟷ B)

    def toFun  : A ⟶ B := (desc E).toFun
    def invFun : B ⟶ A := (desc E).invFun

    def to  (a : A) : B := (toFun  E) a
    def inv (b : B) : A := (invFun E) b

    def leftInv  (a : A) : inv E (to E a) ≃ a := (desc E).left.inv  a
    def rightInv (b : B) : to E (inv E b) ≃ b := (desc E).right.inv b

    def symmDesc : EquivDesc B A := EquivDesc.symm (desc E)

  end

  structure DefEquiv (A : U) (B : V) (e : EquivDesc A B)
                     [HasIdentity UV] [HasIdentity VU] where
  (E        : A ⟷ B)
  (toFunEq  : toFun  E ≃ e.toFun)
  (invFunEq : invFun E ≃ e.invFun)

  notation:20 A:21 " ⟷{" desc:0 "} " B:21 => HasEquivalences.DefEquiv A B desc
  notation:20 A:21 " ⟷{" left:0 "," right:0 "} " B:21 =>
  HasEquivalences.DefEquiv A B (EquivDesc.fromHalfDescs left right)

  variable {A : U} {B : V} [HasIdentity UV] [HasIdentity VU]

  def toDefEquiv (E : A ⟷ B) : A ⟷{desc E} B := ⟨E, HasRefl.refl (toFun E), HasRefl.refl (invFun E)⟩
  def fromDefEquiv {e : EquivDesc A B} (E : A ⟷{e} B) : A ⟷ B := E.E

  @[simp] theorem fromToDefEquiv (E : A ⟷ B) : fromDefEquiv (toDefEquiv E) = E := rfl

  instance {E : A ⟷ B}         : CoeDep ⌈A ⟷ B⌉ E  (A ⟷{desc E} B) := ⟨toDefEquiv E⟩
  instance {e : EquivDesc A B} : Coe    (A ⟷{e} B) ⌈A ⟷ B⌉         := ⟨fromDefEquiv⟩

  def byToFunDef  {e : EquivDesc A B} {E : A ⟷{e} B} :
    toFun  (fromDefEquiv E) ≃ e.toFun  :=
  E.toFunEq

  def byInvFunDef {e : EquivDesc A B} {E : A ⟷{e} B} :
    invFun (fromDefEquiv E) ≃ e.invFun :=
  E.invFunEq

  def byToDef  [HasCongrFun U V] {e : EquivDesc A B} {E : A ⟷{e} B} {a : A} :
    to  (fromDefEquiv E) a ≃ e.toFun  a :=
  congrFun byToFunDef  a

  def byInvDef [HasCongrFun V U] {e : EquivDesc A B} {E : A ⟷{e} B} {b : B} :
    inv (fromDefEquiv E) b ≃ e.invFun b :=
  congrFun byInvFunDef b

end HasEquivalences



class HasInternalEquivalences (U : Universe.{u}) [HasIdentity U] [HasInternalFunctors U]
                              [HasLinearFunOp U] [HasInternalProducts U]
  extends HasEquivalences U U U where
(defElimFun (A B : U) :
   (A ⟷ B)
   ⟶{λ E => HasProducts.intro (HasEquivalences.toFun E) (HasEquivalences.invFun E)}
   (A ⟶ B) ⊓ (B ⟶ A))
[isExt {A B : U} (E : A ⟷ B) : EquivDesc.IsExtensional (desc E)]

namespace HasInternalEquivalences

  open HasLinearFunOp HasEquivalences

  variable {U : Universe} [HasIdentity U] [HasInternalFunctors U]
           [HasLinearFunOp U] [HasLinearFunExt U]
           [HasInternalProducts U] [HasInternalEquivalences U]

  @[reducible] def elimFun (A B : U) : (A ⟷ B) ⟶ (A ⟶ B) ⊓ (B ⟶ A) := defElimFun A B

  variable {A B : U} (E : A ⟷ B)

  instance descIsExt     : EquivDesc.IsExtensional (desc     E) := isExt E
  instance symmDescIsExt : EquivDesc.IsExtensional (symmDesc E) := EquivDesc.IsExtensional.symmExt (desc E)

  def leftInvExt  : invFun E • toFun E ≃{▻ leftInv  E ◅} idFun A := (isExt E).leftExt.invExt
  def rightInvExt : toFun E • invFun E ≃{▻ rightInv E ◅} idFun B := (isExt E).rightExt.invExt

end HasInternalEquivalences



class HasEquivOp (U : Universe.{u}) [HasIdentity U] [HasInternalFunctors U]
                 [HasLinearFunOp U] [HasLinearFunOp.HasLinearFunExt U] [HasInternalProducts U]
                 [HasInternalEquivalences U] where
(defRefl  (A : U)                             :
   A ⟷{EquivDesc.refl A} A)
(defSymm  {A B : U} (E : A ⟷ B)               :
   B ⟷{EquivDesc.symm (HasEquivalences.desc E)} A)
(defTrans {A B C : U} (E : A ⟷ B) (F : B ⟷ C) :
   A ⟷{EquivDesc.trans (HasEquivalences.desc E) (HasEquivalences.desc F)} C)

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
