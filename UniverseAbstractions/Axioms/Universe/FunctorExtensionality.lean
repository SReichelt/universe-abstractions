import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Relations
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.CategoryTheory.Basic
import UniverseAbstractions.Lemmas.DerivedFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v uv iu iv iuv



-- The following classes assert functor extensionality for all functors that are built purely from
-- combinators: In all cases where we can prove that two different functors map to equivalent
-- values, we demand that these functors are equivalent.
--
-- For SKI calculus, a list of sufficient axioms is given in
-- Hindley/Seldin: Lambda-Calculus and Combinators: An Introduction, definition 8.10.
-- The axioms roughly correspond to the following axioms/definitions in this file and
-- `DerivedFunctorExtensionality.lean`:
-- * E-ax 1: `substConst`/`rightConst`
-- * E-ax 2: `rightId`
-- * E-ax 3: `leftId`
-- * E-ax 4: `leftConst` and `dupConst`
-- * E-ax 5: `substAssoc`



class HasSubsingletonExt (U : Universe.{u}) (V : Universe.{v}) {UV : Universe.{uv}}
                         [HasIdentity V] [HasIdentity UV] [HasFunctors U V UV] where
(eqExt {A : U} {B : V} [h : HasInstanceEquivalences.IsSubsingleton B] (F₁ F₂ : A ⟶ B) :
   F₁ ≃[λ a => h.eq (F₁ a) (F₂ a)] F₂)

namespace HasSubsingletonExt

  open HasInstanceEquivalences

  variable {U V UV : Universe} [HasIdentity V] [HasIdentity UV] [HasFunctors U V UV]
           [HasSubsingletonExt U V]

  instance isSubsingleton (A : U) (B : V) [IsSubsingleton B] : IsSubsingleton (A ⟶ B) :=
  { eq := eqExt }

end HasSubsingletonExt



namespace HasLinearFunOp

  open MetaRelation HasFunctors HasCongrArg HasCongrFun

  variable (U : Universe.{u}) [HasIdentity.{u, iu} U] [HasInternalFunctors U] [HasLinearFunOp U]

  class HasLinearFunExt where
  (rightId {A B : U} (F : A ⟶ B) : F • idFun A ≃[λ _ => byArgDef • byDef] F)
  (leftId  {A B : U} (F : A ⟶ B) : idFun B • F ≃[λ _ => byDef    • byDef] F)
  (rightIdExt (A B : U) : compFunFun (idFun A) B
                          ≃[λ F => byDef⁻¹ • rightId F • byDef]
                          idFun (A ⟶ B))
  (leftIdExt  (A B : U) : revCompFunFun A (idFun B)
                          ≃[λ F => byDef⁻¹ • leftId  F • byDef]
                          idFun (A ⟶ B))
  (swapApp {A B : U} (F : A ⟶ B) : swapFun (appFunFun A B) F
                                   ≃[λ _ => byDef • byFunDef • byDef]
                                   F)
  (swapAppExt (A B : U) : swapFunFun (appFunFun A B)
                          ≃[λ F => byDef⁻¹ • swapApp F • byDef]
                          idFun (A ⟶ B))
  (swapCompFun {A B : U} (F : A ⟶ B) (a : A) (C : U) :
     swapFun (compFunFun F C) a
     ≃[λ _ => byDef⁻¹ • (byDef₂ • byDef)]
     appFun (F a) C)
  (swapCompFunExt {A B : U} (F : A ⟶ B) (C : U) :
     swapFunFun (compFunFun F C)
     ≃[λ a => (byDef • byDef)⁻¹ • swapCompFun F a C • byDef]
     appFunFun B C • F)
  (swapCompFunExtExt (A B C : U) :
     swapFunFunFun (B ⟶ C) A C • compFunFunFun A B C
     ≃[λ F => byDef⁻¹ • swapCompFunExt F C • (byDef • byArgDef • byDef)]
     revCompFunFun A (appFunFun B C))
  (swapRevCompFun {A B C : U} (F : B ⟶ C) (a : A) :
     swapFun (revCompFunFun A F) a
     ≃[λ _ => (byArgDef • byDef)⁻¹ • (byDef₂ • byDef)]
     F • appFun a B)
  (swapRevCompFunExt (A : U) {B C : U} (F : B ⟶ C) :
     swapFunFun (revCompFunFun A F)
     ≃[λ a => (byDef • byArgDef • byDef)⁻¹ • swapRevCompFun F a • byDef]
     revCompFunFun (A ⟶ B) F • appFunFun A B)
  (swapRevCompFunExtExt (A B C : U) :
     swapFunFunFun (A ⟶ B) A C • revCompFunFunFun A B C
     ≃[λ F => (byDef • byArgDef • byDef)⁻¹ • swapRevCompFunExt A F • (byDef • byArgDef • byDef)]
     compFunFun (appFunFun A B) ((A ⟶ B) ⟶ C) • revCompFunFunFun (A ⟶ B) B C)
  (compAssoc {A B C D : U} (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) :
     (H • G) • F
     ≃[λ _ => (byArgDef • byDef)⁻¹ • (byDef • byDef)]
     H • (G • F))
  (compAssocExt {A B C : U} (F : A ⟶ B) (G : B ⟶ C) (D : U) :
     compFunFun F D • compFunFun G D
     ≃[λ H => byDef⁻¹ • compAssoc F G H • (byDef • byArgDef • byDef)]
     compFunFun (G • F) D)
  (compAssocExtExt {A B : U} (F : A ⟶ B) (C D : U) :
     revCompFunFun (C ⟶ D) (compFunFun F D) • compFunFunFun B C D
     ≃[λ G => (byDef • byArgDef • byDef)⁻¹ • compAssocExt F G D • (byDef • byArgDef • byDef)]
     compFunFunFun A C D • compFunFun F C)
  (compAssocExtExtExt (A B C D : U) :
     compFunFun (compFunFunFun B C D) ((C ⟶ D) ⟶ (A ⟶ D)) •
     revCompFunFunFun (C ⟶ D) (B ⟶ D) (A ⟶ D) •
     compFunFunFun A B D
     ≃[λ F => (byDef • byArgDef • byDef)⁻¹ •
              compAssocExtExt F C D •
              (byDef • byArgDef • byArgDef₂ • byArgDef • byDef)]
     revCompFunFun (B ⟶ C) (compFunFunFun A C D) • compFunFunFun A B C)

  -- The axioms for composition and identity imply that types and functors form a (potentially
  -- higher) category.

  instance hasTransFun : HasTransFun (α := ⌈U⌉) Fun :=
  { defTransFun    := defCompFunFun,
    defTransFunFun := defCompFunFunFun }

  instance isCategoricalPreorder [h : HasLinearFunExt U] : IsCategoricalPreorder (α := ⌈U⌉) Fun :=
  { assoc          := h.compAssoc,
    rightId        := h.rightId,
    leftId         := h.leftId }

  instance isCategory [h : HasLinearFunExt U] : IsCategory (α := ⌈U⌉) Fun :=
  { assocExt       := h.compAssocExt,
    assocExtExt    := h.compAssocExtExt,
    assocExtExtExt := h.compAssocExtExtExt,
    rightIdExt     := h.rightIdExt,
    leftIdExt      := h.leftIdExt }

end HasLinearFunOp



namespace HasAffineFunOp

  open MetaRelation HasFunctors HasCongrArg HasLinearFunOp HasSubLinearFunOp

  variable (U : Universe.{u}) [HasIdentity.{u, iu} U] [HasInternalFunctors U] [HasAffineFunOp U]

  class HasAffineFunExt extends HasLinearFunExt U where
  (rightConst (A : U) {B C : U} (b : B) (F : B ⟶ C) : F • constFun A b
                                                      ≃[λ _ => byDef⁻¹ • (byArgDef • byDef)]
                                                      constFun A (F b))
  (leftConst {A B C : U} (F : A ⟶ B) (c : C) : constFun B c • F
                                               ≃[λ _ => byDef⁻¹ • (byDef • byDef)]
                                               constFun A c)
  (rightConstExt (A : U) {B : U} (b : B) (C : U) :
     compFunFun (constFun A b) C
     ≃[λ F => (byDef • byArgDef • byDef)⁻¹ • rightConst A b F • byDef]
     constFunFun A C • appFun b C)
  (leftConstExt {A B : U} (F : A ⟶ B) (C : U) :
     compFunFun F C • constFunFun B C
     ≃[λ c => byDef⁻¹ • leftConst F c • (byDef • byArgDef • byDef)]
     constFunFun A C)
  (rightConstExtExt (A B C : U) :
     compFunFunFun A B C • constFunFun A B
     ≃[λ b => (byDef • byArgDef • byDef)⁻¹ • rightConstExt A b C • (byDef • byArgDef • byDef)]
     revCompFunFun (B ⟶ C) (constFunFun A C) • appFunFun B C)
  (leftConstExtExt (A B C : U) :
     compFunFun (constFunFun B C) (A ⟶ C) • compFunFunFun A B C
     ≃[λ F => byDef⁻¹ • leftConstExt F C • (byDef • byArgDef • byDef)]
     constFun (A ⟶ B) (constFunFun A C))

end HasAffineFunOp



namespace HasFullFunOp

  open MetaRelation HasFunctors HasCongrArg HasCongrFun HasLinearFunOp HasSubLinearFunOp HasAffineFunOp HasNonLinearFunOp

  variable (U : Universe.{u}) [HasIdentity.{u, iu} U] [HasInternalFunctors U] [HasFullFunOp U]

  class HasFullFunExt extends HasAffineFunExt U where
  (dupSwap {A B : U} (F : A ⟶ A ⟶ B) : dupFun (swapFunFun F)
                                       ≃[λ _ => byDef⁻¹ • (byDef₂ • byDef)]
                                       dupFun F)
  (dupSwapExt (A B : U) : dupFunFun A B • swapFunFunFun A A B
                          ≃[λ F => byDef⁻¹ • dupSwap F • (byDef • byArgDef • byDef)]
                          dupFunFun A B)
  (dupConst {A B : U} (F : A ⟶ B) : dupFun (constFun A F)
                                    ≃[λ _ => byFunDef • byDef]
                                    F)
  (dupConstExt (A B : U) : dupFunFun A B • constFunFun A (A ⟶ B)
                           ≃[λ F => byDef⁻¹ • dupConst F • (byDef • byArgDef • byDef)]
                           idFun (A ⟶ B))
  (dupDup {A B : U} (F : A ⟶ A ⟶ A ⟶ B) :
     dupFun (dupFun F)
     ≃[λ _ => (byDef₂ • byFunDef • byDef)⁻¹ • (byFunDef • byDef)]
     dupFun (dupFunFun A B • F))
  (dupDupExt (A B : U) :
     dupFunFun A B • dupFunFun A (A ⟶ B)
     ≃[λ F => (byDef • byArgDef • byDef)⁻¹ • dupDup F • (byDef • byArgDef • byDef)]
     dupFunFun A B • revCompFunFun A (dupFunFun A B))
  (rightDup {A B C : U} (F : A ⟶ A ⟶ B) (G : B ⟶ C) :
     G • dupFun F
     ≃[λ _ => (byDef₂ • byFunDef • byDef)⁻¹ • (byArgDef • byDef)]
     dupFun (revCompFunFun A G • F))
  (rightDupExt {A B : U} (F : A ⟶ A ⟶ B) (C : U) :
     compFunFun (dupFun F) C
     ≃[λ G => (byDef • byArgDef • byArgDef₂ • byArgDef • byDef)⁻¹ • rightDup F G • byDef]
     dupFunFun A C • compFunFun F (A ⟶ C) • revCompFunFunFun A B C)
  (rightDupExtExt (A B C : U) :
     compFunFunFun A B C • dupFunFun A B
     ≃[λ F => (byDef • byArgDef • byArgDef₂ • byArgDef • byDef)⁻¹ •
              rightDupExt F C •
              (byDef • byArgDef • byDef)]
     revCompFunFun (B ⟶ C) (dupFunFun A C) •
     compFunFun (revCompFunFunFun A B C) (A ⟶ A ⟶ C) •
     compFunFunFun A (A ⟶ B) (A ⟶ C))
  (substDup {A B C : U} (F : A ⟶ B) (G : A ⟶ B ⟶ B ⟶ C) :
     substFun F (dupFunFun B C • G)
     ≃[λ _ => (byFunDef • byDef)⁻¹ • (byDef₂ • byFunDef • byDef)]
     substFun F (substFun F G))
  (substDupExt {A B : U} (F : A ⟶ B) (C : U) :
     substFunFun F C • revCompFunFun A (dupFunFun B C)
     ≃[λ G => (byDef • byArgDef • byDef)⁻¹ • substDup F G • (byDef • byArgDef • byDef)]
     substFunFun F C • substFunFun F (B ⟶ C))
  (substDupExtExt (A B C : U) :
     compFunFun (revCompFunFun A (dupFunFun B C)) (A ⟶ C) • substFunFunFun A B C
     ≃[λ F => (byDef₂ • congrFun byArgDef (substFunFun F C) • byFunDef • byArgDef • byDef)⁻¹ •
              substDupExt F C •
              (byDef • byArgDef • byDef)]
     substFun (substFunFunFun A B C) (compFunFunFun (A ⟶ B ⟶ B ⟶ C) (A ⟶ B ⟶ C) (A ⟶ C) •
     substFunFunFun A B (B ⟶ C)))

end HasFullFunOp



class HasStandardFunctors (U : Universe.{u}) [HasIdentity.{u, iu} U] extends
  HasInternalFunctors U, HasFullFunOp U, HasFullFunOp.HasFullFunExt U : Type (max u iu)
