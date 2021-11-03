import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Relations
import UniverseAbstractions.Axioms.Universe.Identity
import UniverseAbstractions.Axioms.Universe.Functors
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
   F₁ ≃{λ a => h.eq (F₁ a) (F₂ a)} F₂)

namespace HasSubsingletonExt

  open HasInstanceEquivalences

  variable {U V UV : Universe} [HasIdentity V] [HasIdentity UV] [HasFunctors U V UV]
           [HasSubsingletonExt U V]

  instance isSubsingleton (A : U) (B : V) [IsSubsingleton B] : IsSubsingleton (A ⟶ B) :=
  { eq := eqExt }

end HasSubsingletonExt



namespace HasLinearFunOp

  open HasFunctors HasCongrArg HasCongrFun

  variable (U : Universe.{u}) [HasIdentity.{u, iu} U] [hFun : HasInternalFunctors U] [HasLinearFunOp U]

  class HasLinearFunExt where
  (rightId {A B : U} (F : A ⟶ B) : F • idFun A ≃{byArgDef ▻|} F)
  (leftId  {A B : U} (F : A ⟶ B) : idFun B • F ≃{byDef    ▻|} F)
  (rightIdExt (A B : U) : compFunFun    (idFun A) B ≃{▻ λ F => rightId F ◅} idFun (A ⟶ B))
  (leftIdExt  (A B : U) : revCompFunFun A (idFun B) ≃{▻ λ F => leftId  F ◅} idFun (A ⟶ B))
  (swapRevApp {A B : U} (F : A ⟶ B) : swapFun (revAppFunFun A B) F ≃{byDef • byFunDef ▻|} appFun F)
  (swapRevAppExt (A B : U) : swapFunFun (revAppFunFun A B) ≃{▻ λ F => swapRevApp F ◅} appFunFun A B)
  (swapCompFun {A B : U} (F : A ⟶ B) (a : A) (C : U) :
     swapFun (compFunFun F C) a ≃{byDef₂ ▻-◅} revAppFun (F a) C)
  (swapCompFunExt {A B : U} (F : A ⟶ B) (C : U) :
     swapFunFun (compFunFun F C) ≃{▻ λ a => swapCompFun F a C ◅ byDef} revAppFunFun B C • F)
  (swapCompFunExtExt (A B C : U) :
     swapFunFunFun (B ⟶ C) A C • compFunFunFun A B C
     ≃{byDef • byArgDef ▻ λ F => swapCompFunExt F C ◅}
     revCompFunFun A (revAppFunFun B C))
  (swapRevCompFun {A B C : U} (F : B ⟶ C) (a : A) :
     swapFun (revCompFunFun A F) a ≃{byDef₂ ▻-◅ byArgDef} F • revAppFun a B)
  (swapRevCompFunExt (A : U) {B C : U} (F : B ⟶ C) :
     swapFunFun (revCompFunFun A F)
     ≃{▻ λ a => swapRevCompFun F a ◅ byDef • byArgDef}
     revCompFunFun (A ⟶ B) F • revAppFunFun A B)
  (swapRevCompFunExtExt (A B C : U) :
     swapFunFunFun (A ⟶ B) A C • revCompFunFunFun A B C
     ≃{byDef • byArgDef ▻ λ F => swapRevCompFunExt A F ◅ byDef • byArgDef}
     compFunFun (revAppFunFun A B) ((A ⟶ B) ⟶ C) • revCompFunFunFun (A ⟶ B) B C)
  (compAssoc {A B C D : U} (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) :
     (H • G) • F ≃{byDef ▻-◅ byArgDef} H • (G • F))
  (compAssocExt {A B C : U} (F : A ⟶ B) (G : B ⟶ C) (D : U) :
     compFunFun F D • compFunFun G D
     ≃{byDef • byArgDef ▻ λ H => compAssoc F G H ◅}
     compFunFun (G • F) D)
  (compAssocExtExt {A B : U} (F : A ⟶ B) (C D : U) :
     revCompFunFun (C ⟶ D) (compFunFun F D) • compFunFunFun B C D
     ≃{byDef • byArgDef ▻ λ G => compAssocExt F G D ◅ byDef • byArgDef}
     compFunFunFun A C D • compFunFun F C)
  (compAssocExtExtExt (A B C D : U) :
     compFunFun (compFunFunFun B C D) ((C ⟶ D) ⟶ (A ⟶ D)) •
     revCompFunFunFun (C ⟶ D) (B ⟶ D) (A ⟶ D) •
     compFunFunFun A B D
     ≃{byDef • byArgDef • byArgDef₂ • byArgDef ▻
       λ F => compAssocExtExt F C D
       ◅ byDef • byArgDef}
     revCompFunFun (B ⟶ C) (compFunFunFun A C D) • compFunFunFun A B C)

end HasLinearFunOp



namespace HasAffineFunOp

  open MetaRelation HasFunctors HasCongrArg HasLinearFunOp HasSubLinearFunOp

  variable (U : Universe.{u}) [HasIdentity.{u, iu} U] [HasInternalFunctors U] [HasAffineFunOp U]

  class HasAffineFunExt extends HasLinearFunExt U where
  (rightConst (A : U) {B C : U} (b : B) (F : B ⟶ C) :
     F • constFun A b ≃{byArgDef ▻-◅} constFun A (F b))
  (leftConst {A B C : U} (F : A ⟶ B) (c : C) :
     constFun B c • F ≃{byDef ▻-◅} constFun A c)
  (rightConstExt (A : U) {B : U} (b : B) (C : U) :
     compFunFun (constFun A b) C
     ≃{▻ λ F => rightConst A b F ◅ byDef • byArgDef}
     constFunFun A C • revAppFun b C)
  (leftConstExt {A B : U} (F : A ⟶ B) (C : U) :
     compFunFun F C • constFunFun B C
     ≃{byDef • byArgDef ▻ λ c => leftConst F c ◅}
     constFunFun A C)
  (rightConstExtExt (A B C : U) :
     compFunFunFun A B C • constFunFun A B
     ≃{byDef • byArgDef ▻ λ b => rightConstExt A b C ◅ byDef • byArgDef}
     revCompFunFun (B ⟶ C) (constFunFun A C) • revAppFunFun B C)
  (leftConstExtExt (A B C : U) :
     compFunFun (constFunFun B C) (A ⟶ C) • compFunFunFun A B C
     ≃{byDef • byArgDef ▻ λ F => leftConstExt F C ◅}
     constFun (A ⟶ B) (constFunFun A C))

end HasAffineFunOp



namespace HasFullFunOp

  open MetaRelation HasFunctors HasCongrArg HasCongrFun HasLinearFunOp HasSubLinearFunOp HasAffineFunOp HasNonLinearFunOp

  variable (U : Universe.{u}) [HasIdentity.{u, iu} U] [HasInternalFunctors U] [HasFullFunOp U]

  class HasFullFunExt extends HasAffineFunExt U where
  (dupSwap {A B : U} (F : A ⟶ A ⟶ B) : dupFun (swapFunFun F) ≃{byDef₂ ▻-◅} dupFun F)
  (dupSwapExt (A B : U) :
     dupFunFun A B • swapFunFunFun A A B
     ≃{byDef • byArgDef ▻ λ F => dupSwap F ◅}
     dupFunFun A B)
  (dupConst {A B : U} (F : A ⟶ B) : dupFun (constFun A F) ≃{byFunDef ▻|} F)
  (dupConstExt (A B : U) :
     dupFunFun A B • constFunFun A (A ⟶ B)
     ≃{byDef • byArgDef ▻ λ F => dupConst F ◅}
     idFun (A ⟶ B))
  (dupDup {A B : U} (F : A ⟶ A ⟶ A ⟶ B) :
     dupFun (dupFun F) ≃{byFunDef ▻-◅ byDef₂ • byFunDef} dupFun (dupFunFun A B • F))
  (dupDupExt (A B : U) :
     dupFunFun A B • dupFunFun A (A ⟶ B)
     ≃{byDef • byArgDef ▻ λ F => dupDup F ◅ byDef • byArgDef}
     dupFunFun A B • revCompFunFun A (dupFunFun A B))
  (rightDup {A B C : U} (F : A ⟶ A ⟶ B) (G : B ⟶ C) :
     G • dupFun F ≃{byArgDef ▻-◅ byDef₂ • byFunDef} dupFun (revCompFunFun A G • F))
  (rightDupExt {A B : U} (F : A ⟶ A ⟶ B) (C : U) :
     compFunFun (dupFun F) C
     ≃{▻ λ G => rightDup F G ◅ byDef • byArgDef • byArgDef₂ • byArgDef}
     dupFunFun A C • compFunFun F (A ⟶ C) • revCompFunFunFun A B C)
  (rightDupExtExt (A B C : U) :
     compFunFunFun A B C • dupFunFun A B
     ≃{byDef • byArgDef ▻ λ F => rightDupExt F C ◅ byDef • byArgDef • byArgDef₂ • byArgDef}
     revCompFunFun (B ⟶ C) (dupFunFun A C) •
     compFunFun (revCompFunFunFun A B C) (A ⟶ A ⟶ C) •
     compFunFunFun A (A ⟶ B) (A ⟶ C))
  (substDup {A B C : U} (F : A ⟶ B) (G : A ⟶ B ⟶ B ⟶ C) :
     substFun F (dupFunFun B C • G)
     ≃{byDef₂ • byFunDef ▻-◅ byFunDef}
     substFun F (substFun F G))
  (substDupExt {A B : U} (F : A ⟶ B) (C : U) :
     substFunFun F C • revCompFunFun A (dupFunFun B C)
     ≃{byDef • byArgDef ▻ λ G => substDup F G ◅ byDef • byArgDef}
     substFunFun F C • substFunFun F (B ⟶ C))
  (substDupExtExt (A B C : U) :
     compFunFun (revCompFunFun A (dupFunFun B C)) (A ⟶ C) • substFunFunFun A B C
     ≃{byDef • byArgDef ▻
       λ F => substDupExt F C
       ◅ byDef₂ • congrFun byArgDef _ • byFunDef • byArgDef}
     substFun (substFunFunFun A B C) (compFunFunFun (A ⟶ B ⟶ B ⟶ C) (A ⟶ B ⟶ C) (A ⟶ C) •
     substFunFunFun A B (B ⟶ C)))

end HasFullFunOp



class HasStandardFunctors (U : Universe.{u}) [HasIdentity.{u, iu} U] extends
  HasInternalFunctors U, HasFullFunOp U, HasFullFunOp.HasFullFunExt U : Type (max u iu)
