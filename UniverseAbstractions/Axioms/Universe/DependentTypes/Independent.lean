-- TODO: adapt
#exit



class HasPiFunEquiv (U : Universe.{u}) (V : Universe.{v}) (UV : Universe.{w}) (UVUV : Universe.{w'})
                    [HasDependentFunctors U V UV] [HasFunctors U V UV]
                    [HasFunctors UV UV UVUV] [HasEquivalenceCondition UV UVUV] where
(defPiFun      {A : U} {B : V} (F : Π A{B}) : A ⟶{λ a => F a} B)
(defPiFunFun   (A : U) (B : V)              : (Π A{B}) ⟶{λ F => defPiFun F} (A ⟶ B))
(defFunPi      {A : U} {B : V} (F : A ⟶ B)  : Π{λ a => F a} A{B})
(defFunPiFun   (A : U) (B : V)              : (A ⟶ B) ⟶{λ F => defFunPi F} (Π A{B}))
(defPiFunEquiv (A : U) (B : V)              : (Π A{B}) ⟷{defPiFunFun A B, defFunPiFun A B} (A ⟶ B))

namespace HasPiFunEquiv

  variable {U V UV UVUV UV_UV : Universe} [HasDependentFunctors U V UV] [HasFunctors U V UV]
           [HasFunctors UV UV UVUV] [HasEquivalences UV UVUV UV_UV] [HasPiFunEquiv U V UV UVUV]

  @[reducible] def piFun {A : U} {B : V} (F : Π A{B}) : A ⟶ B := defPiFun (UVUV := UVUV) F
  @[reducible] def piFunFun (A : U) (B : V) : (Π A{B}) ⟶ (A ⟶ B) := defPiFunFun A B
  @[reducible] def funPi {A : U} {B : V} (F : A ⟶ B) : Π A{B} := defFunPi (UVUV := UVUV) F
  @[reducible] def funPiFun (A : U) (B : V) : (A ⟶ B) ⟶ Π A{B} := defFunPiFun A B
  @[reducible] def piFunEquiv (A : U) (B : V) : (Π A{B}) ⟷ (A ⟶ B) := defPiFunEquiv A B

end HasPiFunEquiv



class HasSigmaProdEquiv (U : Universe.{u}) (V : Universe.{v}) (UxV : Universe.{w}) (UxVUxV : Universe.{w'})
                        [HasProperties U V] [HasDependentProducts U V UxV] [HasProducts U V UxV]
                        [HasFunctors UxV UxV UxVUxV] [HasEquivalenceCondition UxV UxVUxV] where
(defSigmaProdFun (A : U) (B : V) :
   (Σ A{B}) ⟶{λ P => HasProducts.intro (HasDependentProducts.fst P) (HasDependentProducts.snd P)} (A ⊓ B))
(defProdSigmaFun (A : U) (B : V) :
   (A ⊓ B) ⟶{λ φ => HasDependentProducts.intro (HasProducts.fst φ) (HasProducts.snd φ)} (Σ A{B}))
(defSigmaProdEquiv (A : U) (B : V) : (Σ A{B}) ⟷{defSigmaProdFun A B, defProdSigmaFun A B} (A ⊓ B))

namespace HasSigmaProdEquiv

  variable {U V UxV UxVUxV UxV_UxV : Universe} [HasProperties U V] [HasDependentProducts U V UxV] [HasProducts U V UxV]
           [HasFunctors UxV UxV UxVUxV] [HasEquivalences UxV UxVUxV UxV_UxV] [HasSigmaProdEquiv U V UxV UxVUxV]

  @[reducible] def sigmaProdFun (A : U) (B : V) : (Σ A{B}) ⟶ A ⊓ B := defSigmaProdFun A B
  @[reducible] def prodSigmaFun (A : U) (B : V) : A ⊓ B ⟶ Σ A{B} := defProdSigmaFun A B
  @[reducible] def sigmaProdEquiv (A : U) (B : V) : (Σ A{B}) ⟷ A ⊓ B := defSigmaProdEquiv A B

end HasSigmaProdEquiv
