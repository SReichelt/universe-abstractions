import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Singletons
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Lemmas.DerivedFunctors
import UniverseAbstractions.Lemmas.DerivedSingletonFunctors
import UniverseAbstractions.Lemmas.DerivedProductFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v w w' w''



class HasEquivalenceCondition (U : Universe.{u}) (UU : Universe.{v}) [HasFunctors U U UU] :
  Type (max u v w) where
(IsEquiv {A B : U} : (A ⟶ B) → (B ⟶ A) → Sort w)

namespace HasEquivalenceCondition

  variable {U : Universe.{u}} {UU : Universe.{v}} [HasFunctors U U UU]
           [h : HasEquivalenceCondition.{u, v, w} U UU]

  def DefEquiv (A B : U) (toFun : A ⟶ B) (invFun : B ⟶ A) := h.IsEquiv toFun invFun

  notation:20 A:21 " ⟷[" toFun:0 "," invFun:0 "] " B:21 => HasEquivalenceCondition.DefEquiv A B toFun invFun

  structure Equiv (A B : U) : Sort (max 1 u v w) where
  (toFun  : A ⟶ B)
  (invFun : B ⟶ A)
  (E      : A ⟷[toFun,invFun] B)

  infix:20 " ⟷' " => HasEquivalenceCondition.Equiv

  variable {A B : U}

  def toDefEquiv                                    (E : A ⟷' B)              : A ⟷[E.toFun,E.invFun] B := E.E
  def fromDefEquiv {toFun : A ⟶ B} {invFun : B ⟶ A} (E : A ⟷[toFun,invFun] B) : A ⟷'                  B := ⟨toFun, invFun, E⟩

  instance (E : A ⟷' B)                     : CoeDep (A ⟷' B)              E (A ⟷[E.toFun,E.invFun] B) := ⟨toDefEquiv E⟩
  instance {toFun : A ⟶ B} {invFun : B ⟶ A} : Coe    (A ⟷[toFun,invFun] B)   (A ⟷' B)                  := ⟨fromDefEquiv⟩

  @[simp] theorem fromToDefEquiv                                  (E : A ⟷' B)              : fromDefEquiv (toDefEquiv E) = E :=
  match E with | ⟨_, _, _⟩ => rfl
  @[simp] theorem toFromDefEquiv {toFun : A ⟶ B} {invFun : B ⟶ A} (E : A ⟷[toFun,invFun] B) : toDefEquiv (fromDefEquiv E) = E := rfl

end HasEquivalenceCondition



class HasEquivalences (U : Universe.{u}) (UU : Universe.{v}) [HasFunctors U U UU]
                      (U_U : outParam Universe.{w})
  extends HasEquivalenceCondition.{u, v, w'} U UU : Type (max u v w w') where
[embed (A B : U) : HasEmbeddedType.{w, max 1 u v w'} U_U (A ⟷' B)]

namespace HasEquivalences

  variable {U UU U_U : Universe} [HasFunctors U U UU] [h : HasEquivalences U UU U_U]

  instance hasEmbeddedType (A B : U) : HasEmbeddedType U_U (A ⟷' B) := h.embed A B

  def Equiv (A B : U) : U_U := HasEmbeddedType.EmbeddedType U_U (A ⟷' B)
  infix:20 " ⟷ " => HasEquivalences.Equiv

  variable {A B : U}

  def toExternal   (E : A ⟷  B) : A ⟷' B := HasEmbeddedType.toExternal   U_U E
  def fromExternal (E : A ⟷' B) : A ⟷  B := HasEmbeddedType.fromExternal U_U E

  @[simp] theorem fromToExternal (E : A ⟷  B) : fromExternal (toExternal E) = E := HasEmbeddedType.fromToExternal U_U E
  @[simp] theorem toFromExternal (E : A ⟷' B) : toExternal (fromExternal E) = E := HasEmbeddedType.toFromExternal U_U E

  def toFun  (E : A ⟷ B) : A ⟶ B := (toExternal E).toFun
  def invFun (E : A ⟷ B) : B ⟶ A := (toExternal E).invFun

  @[simp] theorem toFromExternal.to  (E : A ⟷' B) : (toExternal (fromExternal E)).toFun  = E.toFun  :=
  congrArg HasEquivalenceCondition.Equiv.toFun  (toFromExternal E)
  @[simp] theorem toFromExternal.inv (E : A ⟷' B) : (toExternal (fromExternal E)).invFun = E.invFun :=
  congrArg HasEquivalenceCondition.Equiv.invFun (toFromExternal E)

  def fromDefEquiv {to : A ⟶ B} {inv : B ⟶ A} (E : A ⟷[to,inv] B) : A ⟷ B :=
  fromExternal (HasEquivalenceCondition.fromDefEquiv E)

  instance {to : A ⟶ B} {inv : B ⟶ A} : Coe (A ⟷[to,inv] B) ⌈A ⟷ B⌉ := ⟨fromDefEquiv⟩

  @[simp] theorem fromDefEquiv.to.eff  {to : A ⟶ B} {inv : B ⟶ A} (E : A ⟷[to,inv] B) :
    toFun  (fromDefEquiv E) = to  :=
  by simp [fromDefEquiv, toFun,  HasEquivalenceCondition.fromDefEquiv]
  @[simp] theorem fromDefEquiv.inv.eff {to : A ⟶ B} {inv : B ⟶ A} (E : A ⟷[to,inv] B) :
    invFun (fromDefEquiv E) = inv :=
  by simp [fromDefEquiv, invFun, HasEquivalenceCondition.fromDefEquiv]

end HasEquivalences



class HasIdEquiv (U UU : Universe) [HasFunctors U U UU] [HasIdFun U] [HasEquivalenceCondition U UU] where
(defIdEquiv (A : U) : A ⟷[HasIdFun.idFun A, HasIdFun.idFun A] A)

namespace HasIdEquiv

  variable {U UU : Universe} [HasFunctors U U UU] [HasIdFun U]

  def idEquiv' [HasEquivalenceCondition U UU] [HasIdEquiv U UU] (A : U) : A ⟷' A := HasEquivalenceCondition.fromDefEquiv (defIdEquiv A)

  def idEquiv {U_U : Universe} [HasEquivalences U UU U_U] [HasIdEquiv U UU] (A : U) : A ⟷ A := HasEquivalences.fromExternal (idEquiv' A)

end HasIdEquiv

class HasInvEquiv' (U UU : Universe) [HasFunctors U U UU] [HasEquivalenceCondition U UU] where
(defInvEquiv {A B : U} (E : A ⟷' B) : B ⟷[E.invFun, E.toFun] A)

namespace HasInvEquiv'

  variable {U UU : Universe} [HasFunctors U U UU] [HasEquivalenceCondition U UU] [HasInvEquiv' U UU]

  def invEquiv' {A B : U} (E : A ⟷' B) : B ⟷' A := HasEquivalenceCondition.fromDefEquiv (defInvEquiv E)

end HasInvEquiv'

class HasInvEquiv (U UU U_U : Universe) [HasFunctors U U UU] [HasEquivalences U UU U_U] where
(defInvEquiv {A B : U} (E : A ⟷ B) : B ⟷[HasEquivalences.invFun E, HasEquivalences.toFun E] A)

namespace HasInvEquiv

  variable {U UU U_U : Universe} [HasFunctors U U UU] [HasEquivalences U UU U_U] [HasInvEquiv U UU U_U]

  def invEquiv {A B : U} (E : A ⟷ B) : B ⟷ A := HasEquivalences.fromDefEquiv (defInvEquiv E)

  instance hasInvEquiv' : HasInvEquiv' U UU :=
  ⟨λ E => HasEquivalences.toFromExternal E ▸ defInvEquiv (HasEquivalences.fromExternal E)⟩

end HasInvEquiv

class HasCompEquiv' (U UU : Universe) [HasFunctors U U UU] [HasCompFun U U U UU UU] [HasEquivalenceCondition U UU] where
(defCompEquiv {A B C : U} (E : A ⟷' B) (F : B ⟷' C) : A ⟷[HasCompFun.compFun E.toFun F.toFun,
                                                          HasCompFun.compFun F.invFun E.invFun] C)

namespace HasCompEquiv'

  variable {U UU : Universe} [HasFunctors U U UU] [HasCompFun U U U UU UU] [HasEquivalenceCondition U UU] [HasCompEquiv' U UU]

  def compEquiv' {A B C : U} (E : A ⟷' B) (F : B ⟷' C) : A ⟷' C := HasEquivalenceCondition.fromDefEquiv (defCompEquiv E F)

end HasCompEquiv'

class HasCompEquiv (U UU U_U : Universe) [HasFunctors U U UU] [HasCompFun U U U UU UU] [HasEquivalences U UU U_U] where
(defCompEquiv {A B C : U} (E : A ⟷ B) (F : B ⟷ C) : A ⟷[HasCompFun.compFun (HasEquivalences.toFun E) (HasEquivalences.toFun F),
                                                        HasCompFun.compFun (HasEquivalences.invFun F) (HasEquivalences.invFun E)] C)

namespace HasCompEquiv

  variable {U UU U_U : Universe} [HasFunctors U U UU] [HasCompFun U U U UU UU] [HasEquivalences U UU U_U] [HasCompEquiv U UU U_U]

  def compEquiv {A B C : U} (E : A ⟷ B) (F : B ⟷ C) : A ⟷ C := HasEquivalences.fromDefEquiv (defCompEquiv E F)

  instance hasCompEquiv' : HasCompEquiv' U UU :=
  ⟨λ E F => HasEquivalences.toFromExternal E ▸
            HasEquivalences.toFromExternal F ▸
            defCompEquiv (HasEquivalences.fromExternal E) (HasEquivalences.fromExternal F)⟩

end HasCompEquiv



class HasEmbeddedEquivalences (U : Universe.{u}) [HasEmbeddedFunctors.{u, w'} U] [HasEmbeddedProducts U]
  extends HasEquivalences.{u, u, u, w} U U U : Type (max u w w') where
(defElimFun (A B : U) : (A ⟷ B) ⟶[λ E => HasProducts.intro (HasEquivalences.toFun E) (HasEquivalences.invFun E)] (A ⟶ B) ⊓ (B ⟶ A))

namespace HasEmbeddedEquivalences

  variable {U : Universe} [HasEmbeddedFunctors U] [HasEmbeddedProducts U] [HasEmbeddedEquivalences U]

  @[reducible] def elimFun (A B : U) : (A ⟷ B) ⟶ (A ⟶ B) ⊓ (B ⟶ A) := defElimFun A B

end HasEmbeddedEquivalences



class HasEquivOp (U : Universe.{u}) [HasEmbeddedFunctors.{u, w'} U] [HasEmbeddedProducts.{u} U] [HasLinearFunOp U]
  extends HasEmbeddedEquivalences.{u, w} U : Type (max u w w') where
(defIdEquiv         (A : U)                             : A ⟷[HasLinearFunOp.idFun A, HasLinearFunOp.idFun A] A)
(defInvEquiv        {A B : U} (E : A ⟷ B)               : B ⟷[HasEquivalences.invFun E, HasEquivalences.toFun E] A)
(defInvEquivFun     (A B : U)                           : (A ⟷ B) ⟶[λ E => defInvEquiv E] (B ⟷ A))
(defCompEquiv       {A B C : U} (E : A ⟷ B) (F : B ⟷ C) : A ⟷[HasEquivalences.toFun F ⊙ HasEquivalences.toFun E, HasEquivalences.invFun E ⊙ HasEquivalences.invFun F] C)
(defCompEquivFun    {A B : U} (E : A ⟷ B) (C : U)       : (B ⟷ C) ⟶[λ F => defCompEquiv E F] (A ⟷ C))
(defCompEquivFunFun (A B C : U)                         : (A ⟷ B) ⟶[λ E => defCompEquivFun E C] ((B ⟷ C) ⟶ (A ⟷ C)))

namespace HasEquivOp

  variable {U : Universe.{u}} [HasEmbeddedFunctors U] [HasEmbeddedProducts U] [HasLinearFunOp U] [HasEquivOp U]

  instance hasIdEquiv : HasIdEquiv U U := ⟨defIdEquiv⟩

  @[reducible] def idEquiv (A : U) : A ⟷ A := defIdEquiv A

  instance hasInvEquiv : HasInvEquiv U U U := ⟨defInvEquiv⟩

  @[reducible] def invEquiv {A B : U} (E : A ⟷ B) : B ⟷ A := defInvEquiv E
  @[reducible] def invEquivFun (A B : U) : (A ⟷ B) ⟶ (B ⟷ A) := defInvEquivFun A B

  instance hasCompEquiv : HasCompEquiv U U U := ⟨defCompEquiv⟩

  @[reducible] def compEquiv {A B C : U} (E : A ⟷ B) (F : B ⟷ C) : A ⟷ C := defCompEquiv E F
  @[reducible] def compEquivFun {A B : U} (E : A ⟷ B) (C : U) : (B ⟷ C) ⟶ (A ⟷ C) := defCompEquivFun E C
  @[reducible] def compEquivFunFun (A B C : U) : (A ⟷ B) ⟶ (B ⟷ C) ⟶ (A ⟷ C) := defCompEquivFunFun A B C

end HasEquivOp

class HasEquivOpEq (U : Universe.{u}) [HasEmbeddedFunctors.{u, w} U] [HasEmbeddedProducts.{u} U] [HasLinearFunOp U]
                   [HasEquivOp U] [hasIdFun : HasIdFun U] [hasCompFun : HasCompFun U U U U U]
                   [hasLinearFunOpEq : HasLinearFunOpEq U] [hasIdEquiv : HasIdEquiv U U]
                   [hasInvEquiv : HasInvEquiv U U U] [hasCompEquiv : HasCompEquiv U U U] where
(defIdEquivEq (A : U) : HasLinearFunOpEq.idFunEq A ▸ HasEquivOp.defIdEquiv A = HasIdEquiv.defIdEquiv A)
(defInvEquivEq {A B : U} (E : A ⟷ B) : HasEquivOp.defInvEquiv E = HasInvEquiv.defInvEquiv E)
(defCompEquivEq {A B C : U} (E : A ⟷ B) (F : B ⟷ C) :
   HasLinearFunOpEq.compFunEq (HasEquivalences.toFun E) (HasEquivalences.toFun F) ▸ 
   HasLinearFunOpEq.compFunEq (HasEquivalences.invFun F) (HasEquivalences.invFun E) ▸
   HasEquivOp.defCompEquiv E F =
   HasCompEquiv.defCompEquiv E F)

namespace HasEquivOpEq

  instance std (U : Universe.{u}) [HasEmbeddedFunctors.{u, w} U] [HasEmbeddedProducts.{u} U] [HasLinearFunOp U]
               [HasEquivOp U] : HasEquivOpEq U :=
  { defIdEquivEq   := λ _   => rfl,
    defInvEquivEq  := λ _   => rfl,
    defCompEquivEq := λ _ _ => rfl }

  variable {U : Universe.{u}} [HasEmbeddedFunctors.{u, w} U] [HasEmbeddedProducts.{u} U] [HasLinearFunOp U]
           [HasEquivOp U] [HasIdFun U] [HasCompFun U U U U U] [HasLinearFunOpEq U]
           [HasIdEquiv U U] [HasInvEquiv U U U] [HasCompEquiv U U U] [HasEquivOpEq U]

  -- TODO
  --def idEquivEq (A : U) : HasEquivOp.idEquiv A = HasIdEquiv.idEquiv A :=
  --Eq.simp_rec_prop (congrArg HasEquivalences.fromDefEquiv (defIdEquivEq A))

  def invEquivEq {A B : U} (E : A ⟷ B) : HasEquivOp.invEquiv E = HasInvEquiv.invEquiv E :=
  congrArg HasEquivalences.fromDefEquiv (defInvEquivEq E)

  -- TODO
  --def compEquivEq {A B C : U} (E : A ⟷ B) (F : B ⟷ C) : HasEquivOp.compEquiv E F = HasCompEquiv.compEquiv E F :=
  --Eq.simp_rec_prop (Eq.simp_rec_prop (congrArg HasEquivalences.fromDefEquiv (defCompEquivEq E F)))

end HasEquivOpEq



class HasLinearCommonEquivalences (U : Universe) [HasEmbeddedFunctors U] [HasLinearFunOp U]
                                  [HasEmbeddedTop U] [HasEmbeddedProducts U] [HasEquivOp U] where
(defFunDomainEquiv      {A B : U} (E : A ⟷ B) (C : U) :
   (B ⟶ C) ⟷[HasLinearFunOp.compFunFun (HasEquivalences.toFun  E) C,
             HasLinearFunOp.compFunFun (HasEquivalences.invFun E) C] (A ⟶ C))
(defFunDomainEquivFun   (A B C : U)                   :
   (A ⟷ B) ⟶[λ E => defFunDomainEquiv E C] ((B ⟶ C) ⟷ (A ⟶ C)))
(defFunCodomainEquiv    {A B : U} (E : A ⟷ B) (C : U) :
   (C ⟶ A) ⟷[HasLinearFunOp.revCompFunFun C (HasEquivalences.toFun  E),
             HasLinearFunOp.revCompFunFun C (HasEquivalences.invFun E)] (C ⟶ B))
(defFunCodomainEquivFun (A B C : U)                   :
   (A ⟷ B) ⟶[λ E => defFunCodomainEquiv E C] ((C ⟶ A) ⟷ (C ⟶ B)))
(defSwapFunFunEquiv     (A B C : U)                   :
   (A ⟶ B ⟶ C) ⟷[HasLinearFunOp.swapFunFunFun A B C, HasLinearFunOp.swapFunFunFun B A C] (B ⟶ A ⟶ C))
(defTopElimEquiv        (A : U)                       :
   A ⟷[HasEmbeddedTop.elimFunFun A,
       HasEmbeddedTop.invElimFun A] (HasTop.Top U ⟶ A))
(defProdElimFunEquiv    (A B C : U)                   :
   (A ⟶ B ⟶ C) ⟷[HasEmbeddedProducts.elimFunFun A B C,
                 HasEmbeddedProducts.invElimFunFunFun A B C] (A ⊓ B ⟶ C))
(defProdFstEquiv        {A B : U} (E : A ⟷ B) (C : U) :
   A ⊓ C ⟷[HasEmbeddedProducts.replaceFstFun (HasEquivalences.toFun  E) C,
           HasEmbeddedProducts.replaceFstFun (HasEquivalences.invFun E) C] B ⊓ C)
(defProdFstEquivFun     (A B C : U)                   :
   (A ⟷ B) ⟶[λ E => defProdFstEquiv E C] (A ⊓ C ⟷ B ⊓ C))
(defProdSndEquiv        {A B : U} (E : A ⟷ B) (C : U) :
   C ⊓ A ⟷[HasEmbeddedProducts.replaceSndFun (HasEquivalences.toFun  E) C,
           HasEmbeddedProducts.replaceSndFun (HasEquivalences.invFun E) C] C ⊓ B)
(defProdSndEquivFun     (A B C : U)                   :
   (A ⟷ B) ⟶[λ E => defProdSndEquiv E C] (C ⊓ A ⟷ C ⊓ B))
(defProdCommEquiv       (A B : U)                     :
   A ⊓ B ⟷[HasEmbeddedProducts.commFun A B, HasEmbeddedProducts.commFun B A] B ⊓ A)
(defProdAssocEquiv      (A B C : U)                   :
   (A ⊓ B) ⊓ C ⟷[HasEmbeddedProducts.assocLRFun A B C, HasEmbeddedProducts.assocRLFun A B C] A ⊓ (B ⊓ C))
(defProdTopEquiv        (A : U)                       :
   A ⟷[HasEmbeddedProducts.prodTopIntroFun A,
       HasEmbeddedProducts.prodTopElimFun A] HasTop.Top U ⊓ A)
(defCompEquivEquiv      {A B : U} (E : A ⟷ B) (C : U) :
   (B ⟷ C) ⟷[HasEquivOp.compEquivFun E C, HasEquivOp.compEquivFun (HasEquivOp.invEquiv E) C] (A ⟷ C))
(defCompEquivEquivFun   (A B C : U)                   :
   (A ⟷ B) ⟶[λ E => defCompEquivEquiv E C] ((B ⟷ C) ⟷ (A ⟷ C)))
(defInvEquivEquiv       (A B : U)                     :
   (A ⟷ B) ⟷[HasEquivOp.invEquivFun A B, HasEquivOp.invEquivFun B A] (B ⟷ A))

namespace HasLinearCommonEquivalences

  variable {U : Universe.{u}} [HasEmbeddedFunctors U] [HasLinearFunOp U] [HasEmbeddedTop U]
           [HasEmbeddedProducts U] [HasEquivOp U] [HasLinearCommonEquivalences U]

  @[reducible] def funDomainEquiv {A B : U} (E : A ⟷ B) (C : U) : (B ⟶ C) ⟷ (A ⟶ C) := defFunDomainEquiv E C
  @[reducible] def funDomainEquivFun (A B C : U) : (A ⟷ B) ⟶ ((B ⟶ C) ⟷ (A ⟶ C)) := defFunDomainEquivFun A B C
  @[reducible] def funCodomainEquiv {A B : U} (E : A ⟷ B) (C : U) : (C ⟶ A) ⟷ (C ⟶ B) := defFunCodomainEquiv E C
  @[reducible] def funCodomainEquivFun (A B C : U) : (A ⟷ B) ⟶ ((C ⟶ A) ⟷ (C ⟶ B)) := defFunCodomainEquivFun A B C
  @[reducible] def swapFunFunEquiv (A B C : U) : (A ⟶ B ⟶ C) ⟷ (B ⟶ A ⟶ C) := defSwapFunFunEquiv A B C

  @[reducible] def topElimEquiv (A : U) : A ⟷ (HasTop.Top U ⟶ A) := defTopElimEquiv A

  @[reducible] def prodElimFunEquiv (A B C : U) : (A ⟶ B ⟶ C) ⟷ (A ⊓ B ⟶ C) := defProdElimFunEquiv A B C
  @[reducible] def prodFstEquiv {A B : U} (E : A ⟷ B) (C : U) : A ⊓ C ⟷ B ⊓ C := defProdFstEquiv E C
  @[reducible] def prodFstEquivFun (A B C : U) : (A ⟷ B) ⟶ (A ⊓ C ⟷ B ⊓ C) := defProdFstEquivFun A B C
  @[reducible] def prodSndEquiv {A B : U} (E : A ⟷ B) (C : U) : C ⊓ A ⟷ C ⊓ B := defProdSndEquiv E C
  @[reducible] def prodSndEquivFun (A B C : U) : (A ⟷ B) ⟶ (C ⊓ A ⟷ C ⊓ B) := defProdSndEquivFun A B C
  @[reducible] def prodCommEquiv (A B : U) : A ⊓ B ⟷ B ⊓ A := defProdCommEquiv A B
  @[reducible] def prodAssocEquiv (A B C : U) : (A ⊓ B) ⊓ C ⟷ A ⊓ (B ⊓ C) := defProdAssocEquiv A B C
  @[reducible] def prodTopEquiv (A : U) : A ⟷ HasTop.Top U ⊓ A := defProdTopEquiv A

  @[reducible] def compEquivEquiv {A B : U} (E : A ⟷ B) (C : U) : (B ⟷ C) ⟷ (A ⟷ C) := defCompEquivEquiv E C
  @[reducible] def compEquivEquivFun (A B C : U) : (A ⟷ B) ⟶ ((B ⟷ C) ⟷ (A ⟷ C)) := defCompEquivEquivFun A B C
  @[reducible] def invEquivEquiv (A B : U) : (A ⟷ B) ⟷ (B ⟷ A) := defInvEquivEquiv A B

end HasLinearCommonEquivalences

class HasNonLinearCommonEquivalences (U : Universe) [HasFunOp U] [HasEmbeddedTop U]
                                     [HasEmbeddedProducts U] [HasEquivOp U] where
(defProdDistrEquiv (A B C : U) :
   (A ⟶ B ⊓ C) ⟷[HasEmbeddedProducts.distrFun A B C,
                 HasEmbeddedProducts.invDistrFunFun A B C] (A ⟶ B) ⊓ (A ⟶ C))

namespace HasNonLinearCommonEquivalences

  variable {U : Universe} [HasFunOp U] [HasEmbeddedTop U] [HasEmbeddedProducts U]
           [HasEquivOp U] [HasNonLinearCommonEquivalences U]

  @[reducible] def prodDistrEquiv (A B C : U) : (A ⟶ B ⊓ C) ⟷ (A ⟶ B) ⊓ (A ⟶ C):= defProdDistrEquiv A B C

end HasNonLinearCommonEquivalences

class HasBotEquivalences (U : Universe) [HasEmbeddedFunctors U] [HasAffineFunOp U]
                         [HasEmbeddedTop U] [HasEmbeddedBot U] [HasEmbeddedProducts U]
                         [HasEquivOp U] where
(defBotNotTopEquiv         :
   HasBot.Bot U ⟷[HasEmbeddedBot.elimFun (HasEmbeddedBot.Not (HasTop.Top U)),
                  HasEmbeddedBot.notTopIntroFun] HasEmbeddedBot.Not (HasTop.Top U))
(defProdBotEquiv   (A : U) :
   HasBot.Bot U ⟷[HasEmbeddedBot.elimFun (HasBot.Bot U ⊓ A),
                  HasEmbeddedProducts.fstFun (HasBot.Bot U) A] HasBot.Bot U ⊓ A)
(defBotContraEquiv (A : U) :
   HasBot.Bot U ⟷[HasEmbeddedBot.elimFun (A ⊓ HasEmbeddedBot.Not A),
                  HasEmbeddedProducts.elimFun (HasEmbeddedBot.contraIntroFun A)] A ⊓ HasEmbeddedBot.Not A)

namespace HasBotEquivalences

  variable {U : Universe} [HasEmbeddedFunctors U] [HasAffineFunOp U] [HasEmbeddedTop U]
           [HasEmbeddedBot U] [HasEmbeddedProducts U] [HasEquivOp U] [HasBotEquivalences U]

  @[reducible] def botNotTopEquiv : HasBot.Bot U ⟷ HasEmbeddedBot.Not (HasTop.Top U) := defBotNotTopEquiv (U := U)
  @[reducible] def prodBotEquiv (A : U) : HasBot.Bot U ⟷ HasBot.Bot U ⊓ A := defProdBotEquiv A
  @[reducible] def botContraEquiv (A : U) : HasBot.Bot U ⟷ A ⊓ HasEmbeddedBot.Not A := defBotContraEquiv A

end HasBotEquivalences

class HasClassicalEquivalences (U : Universe) [HasEmbeddedFunctors U] [HasLinearFunOp U]
                               [HasEmbeddedBot U] [HasClassicalLogic U]
                               [HasEmbeddedProducts U] [HasEquivOp U] where
(defByContradictionEquiv (A : U) :
   A ⟷[HasEmbeddedBot.notNotFun A,
       HasClassicalLogic.byContradictionFun A] HasEmbeddedBot.Not (HasEmbeddedBot.Not A))

namespace HasClassicalEquivalences

  variable {U : Universe} [HasEmbeddedFunctors U] [HasLinearFunOp U] [HasEmbeddedBot U]
           [HasClassicalLogic U] [HasEmbeddedProducts U] [HasEquivOp U] [HasClassicalEquivalences U]

  @[reducible] def byContradictionEquiv (A : U) : A ⟷ HasEmbeddedBot.Not (HasEmbeddedBot.Not A) :=
  defByContradictionEquiv A

end HasClassicalEquivalences
