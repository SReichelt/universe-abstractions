import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.MetaRelations
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

  class HasLinearFunExt (U : Universe.{u}) [HasIdentity.{u, iu} U] [hFun : HasInternalFunctors U]
                        [HasLinearFunOp U] where
  (rightId {A B : U} (F : A ⟶ B) : F • idFun A ≃{byArgDef ▻|} F)
  (leftId  {A B : U} (F : A ⟶ B) : idFun B • F ≃{byDef    ▻|} F)
  (rightIdExt (A B : U) : compFunFun    (idFun A) B ≃{▻ λ F => rightId F ◅} idFun (A ⟶ B))
  (leftIdExt  (A B : U) : revCompFunFun A (idFun B) ≃{▻ λ F => leftId  F ◅} idFun (A ⟶ B))
  (swapRevApp {A B : U} (F : A ⟶ B) : swapFun (revAppFunFun A B) F ≃{byDef • byFunDef ▻-◅} appFun F)
  (swapRevAppExt (A B : U) : swapFunFun (revAppFunFun A B) ≃{▻ λ F => swapRevApp F ◅} appFunFun A B)
  (swapCompFun {A B : U} (F : A ⟶ B) (a : A) (C : U) :
     swapFun (compFunFun F C) a ≃{byDef₂ ▻-◅} revAppFun (F a) C)
  (swapCompFunExt {A B : U} (F : A ⟶ B) (C : U) :
     swapFunFun (compFunFun F C) ≃{▻ λ a => swapCompFun F a C ◅ byDef} revAppFunFun B C • F)
  (swapCompFunExtExt (A B C : U) :
     swapFunFunFun (B ⟶ C) A C • compFunFunFun A B C
     ≃{byDefDef ▻ λ F => swapCompFunExt F C ◅}
     revCompFunFun A (revAppFunFun B C))
  (swapRevCompFun {A B C : U} (F : B ⟶ C) (a : A) :
     swapFun (revCompFunFun A F) a ≃{byDef₂ ▻-◅ byArgDef} F • revAppFun a B)
  (swapRevCompFunExt (A : U) {B C : U} (F : B ⟶ C) :
     swapFunFun (revCompFunFun A F)
     ≃{▻ λ a => swapRevCompFun F a ◅ byDefDef}
     revCompFunFun (A ⟶ B) F • revAppFunFun A B)
  (swapRevCompFunExtExt (A B C : U) :
     swapFunFunFun (A ⟶ B) A C • revCompFunFunFun A B C
     ≃{byDefDef ▻ λ F => swapRevCompFunExt A F ◅ byDefDef}
     compFunFun (revAppFunFun A B) ((A ⟶ B) ⟶ C) • revCompFunFunFun (A ⟶ B) B C)
  (compAssoc {A B C D : U} (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) :
     (H • G) • F ≃{byDef ▻-◅ byArgDef} H • (G • F))
  (compAssocExt {A B C : U} (F : A ⟶ B) (G : B ⟶ C) (D : U) :
     compFunFun F D • compFunFun G D
     ≃{byDefDef ▻ λ H => compAssoc F G H ◅}
     compFunFun (G • F) D)
  (compAssocExtExt {A B : U} (F : A ⟶ B) (C D : U) :
     revCompFunFun (C ⟶ D) (compFunFun F D) • compFunFunFun B C D
     ≃{byDefDef ▻ λ G => compAssocExt F G D ◅ byDefDef}
     compFunFunFun A C D • compFunFun F C)
  (compAssocExtExtExt (A B C D : U) :
     compFunFun (compFunFunFun B C D) ((C ⟶ D) ⟶ (A ⟶ D)) •
     revCompFunFunFun (C ⟶ D) (B ⟶ D) (A ⟶ D) •
     compFunFunFun A B D
     ≃{byDefDefDef • byArgDef ▻ λ F => compAssocExtExt F C D ◅ byDefDef}
     revCompFunFun (B ⟶ C) (compFunFunFun A C D) • compFunFunFun A B C)

  namespace HasLinearFunExt

    variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasLinearFunOp U]
             [HasLinearFunExt U]

    instance rightId.isExtApp {A B : U} (F : A ⟶ B) : IsExtApp (A ⟶ B) (rightId F) :=
    IsExtApp.fromExt (rightIdExt A B) F

    instance leftId.isExtApp {A B : U} (F : A ⟶ B) : IsExtApp (A ⟶ B) (leftId F) :=
    IsExtApp.fromExt (leftIdExt A B) F

    instance swapRevApp.isExtApp {A B : U} (F : A ⟶ B) : IsExtApp (A ⟶ B) (swapRevApp F) :=
    IsExtApp.fromExt (swapRevAppExt A B) F

    instance swapCompFun.isExtApp {A B : U} (F : A ⟶ B) (a : A) (C : U) :
      IsExtApp A (swapCompFun F a C) :=
    IsExtApp.fromExt (swapCompFunExt F C) a

    instance swapCompFunExt.isExtApp {A B : U} (F : A ⟶ B) (C : U) :
      IsExtApp (A ⟶ B) (swapCompFunExt F C) :=
    IsExtApp.fromExt (swapCompFunExtExt A B C) F

    instance swapRevCompFun.isExtApp {A B C : U} (F : B ⟶ C) (a : A) :
      IsExtApp A (swapRevCompFun F a) :=
    IsExtApp.fromExt (swapRevCompFunExt A F) a

    instance swapRevCompFunExt.isExtApp (A : U) {B C : U} (F : B ⟶ C) :
      IsExtApp (B ⟶ C) (swapRevCompFunExt A F) :=
    IsExtApp.fromExt (swapRevCompFunExtExt A B C) F

    instance compAssoc.isExtApp {A B C D : U} (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) :
      IsExtApp (C ⟶ D) (compAssoc F G H) :=
    IsExtApp.fromExt (compAssocExt F G D) H

    instance compAssocExt.isExtApp {A B C : U} (F : A ⟶ B) (G : B ⟶ C) (D : U) :
      IsExtApp (B ⟶ C) (compAssocExt F G D) :=
    IsExtApp.fromExt (compAssocExtExt F C D) G

    instance compAssocExtExt.isExtApp {A B : U} (F : A ⟶ B) (C D : U) :
      IsExtApp (A ⟶ B) (compAssocExtExt F C D) :=
    IsExtApp.fromExt (compAssocExtExtExt A B C D) F

  end HasLinearFunExt

end HasLinearFunOp



namespace HasAffineFunOp

  open MetaRelation HasFunctors HasCongrArg HasCongrFun HasLinearFunOp HasSubLinearFunOp

  class HasAffineFunExt (U : Universe.{u}) [HasIdentity.{u, iu} U] [HasInternalFunctors U]
                        [HasAffineFunOp U] extends
    HasLinearFunExt U where
  (rightConst (A : U) {B C : U} (b : B) (G : B ⟶ C) :
     G • constFun A b ≃{byArgDef ▻-◅} constFun A (G b))
  (leftConst {A B C : U} (F : A ⟶ B) (c : C) :
     constFun B c • F ≃{byDef ▻-◅} constFun A c)
  (rightConstExt (A : U) {B : U} (b : B) (C : U) :
     compFunFun (constFun A b) C
     ≃{▻ λ F => rightConst A b F ◅ byDefDef}
     constFunFun A C • revAppFun b C)
  (leftConstExt {A B : U} (F : A ⟶ B) (C : U) :
     compFunFun F C • constFunFun B C
     ≃{byDefDef ▻ λ c => leftConst F c ◅}
     constFunFun A C)
  (rightConstExtExt (A B C : U) :
     compFunFunFun A B C • constFunFun A B
     ≃{byDefDef ▻ λ b => rightConstExt A b C ◅ byDefDef}
     revCompFunFun (B ⟶ C) (constFunFun A C) • revAppFunFun B C)
  (leftConstExtExt (A B C : U) :
     compFunFun (constFunFun B C) (A ⟶ C) • compFunFunFun A B C
     ≃{byDefDef ▻ λ F => leftConstExt F C ◅}
     constFun (A ⟶ B) (constFunFun A C))

  namespace HasAffineFunExt

    variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasAffineFunOp U]
             [HasAffineFunExt U]

    instance rightConst.isExtApp (A : U) {B C : U} (b : B) (G : B ⟶ C) :
      IsExtApp (B ⟶ C) (rightConst A b G) :=
    IsExtApp.fromExt (rightConstExt A b C) G

    instance rightConstExt.isExtApp (A : U) {B : U} (b : B) (C : U) :
      IsExtApp B (rightConstExt A b C) :=
    IsExtApp.fromExt (rightConstExtExt A B C) b

    instance leftConst.isExtApp {A B C : U} (F : A ⟶ B) (c : C) :
      IsExtApp C (leftConst F c) :=
    IsExtApp.fromExt (leftConstExt F C) c

    instance leftConstExt.isExtApp {A B : U} (F : A ⟶ B) (C : U) :
      IsExtApp (A ⟶ B) (leftConstExt F C) :=
    IsExtApp.fromExt (leftConstExtExt A B C) F

  end HasAffineFunExt

end HasAffineFunOp



namespace HasFullFunOp

  open MetaRelation HasFunctors HasCongrArg HasCongrFun HasLinearFunOp HasSubLinearFunOp
       HasAffineFunOp HasNonLinearFunOp

  class HasFullFunExt (U : Universe.{u}) [HasIdentity.{u, iu} U] [HasInternalFunctors U]
                      [HasFullFunOp U] extends
    HasAffineFunExt U where
  (dupSwap {A B : U} (F : A ⟶ A ⟶ B) : dupFun (swapFunFun F) ≃{byDef₂ ▻-◅} dupFun F)
  (dupSwapExt (A B : U) :
     dupFunFun A B • swapFunFunFun A A B
     ≃{byDefDef ▻ λ F => dupSwap F ◅}
     dupFunFun A B)
  (dupConst {A B : U} (F : A ⟶ B) : dupFun (constFun A F) ≃{byFunDef ▻|} F)
  (dupConstExt (A B : U) :
     dupFunFun A B • constFunFun A (A ⟶ B)
     ≃{byDefDef ▻ λ F => dupConst F ◅}
     idFun (A ⟶ B))
  (rightDup {A B C : U} (F : A ⟶ A ⟶ B) (G : B ⟶ C) :
     dupFun (revCompFunFun A G • F) ≃{byDef₂ • byFunDef ▻-◅ byArgDef} G • dupFun F)
  (rightDupExt {A B : U} (F : A ⟶ A ⟶ B) (C : U) :
     dupFunFun A C • compFunFun F (A ⟶ C) • revCompFunFunFun A B C
     ≃{byDefDefDef • byArgDef ▻ λ G => rightDup F G ◅}
     compFunFun (dupFun F) C)
  (rightDupExtExt (A B C : U) :
     revCompFunFun (B ⟶ C) (dupFunFun A C) •
     compFunFun (revCompFunFunFun A B C) (A ⟶ A ⟶ C) •
     compFunFunFun A (A ⟶ B) (A ⟶ C)
     ≃{byDefDefDef • byArgDef ▻ λ F => rightDupExt F C ◅ byDefDef}
     compFunFunFun A B C • dupFunFun A B)
  (substDup {A B C : U} (F : A ⟶ B) (G : A ⟶ B ⟶ B ⟶ C) :
     substFun F (dupFunFun B C • G)
     ≃{byDef₂ • byFunDef ▻-◅ byFunDef}
     substFun F (substFun F G))
  (substDupExt {A B : U} (F : A ⟶ B) (C : U) :
     substFunFun F C • revCompFunFun A (dupFunFun B C)
     ≃{byDefDef ▻ λ G => substDup F G ◅ byDefDef}
     substFunFun F C • substFunFun F (B ⟶ C))
  (substDupExtExt (A B C : U) :
     compFunFun (revCompFunFun A (dupFunFun B C)) (A ⟶ C) • substFunFunFun A B C
     ≃{byDefDef ▻
       λ F => substDupExt F C
       ◅ byDef₂ • congrFun byArgDef _ • byFunDef • byArgDef}
     substFun (substFunFunFun A B C) (compFunFunFun (A ⟶ B ⟶ B ⟶ C) (A ⟶ B ⟶ C) (A ⟶ C) •
     substFunFunFun A B (B ⟶ C)))

  namespace HasFullFunExt

    variable {U : Universe} [HasIdentity U] [HasInternalFunctors U] [HasFullFunOp U]
             [HasFullFunExt U]

    instance dupSwap.isExtApp {A B : U} (F : A ⟶ A ⟶ B) :
      IsExtApp (A ⟶ A ⟶ B) (dupSwap F) :=
    IsExtApp.fromExt (dupSwapExt A B) F

    instance dupConst.isExtApp {A B : U} (F : A ⟶ B) :
      IsExtApp (A ⟶ B) (dupConst F) :=
    IsExtApp.fromExt (dupConstExt A B) F

    instance rightDup.isExtApp {A B C : U} (F : A ⟶ A ⟶ B) (G : B ⟶ C) :
      IsExtApp (B ⟶ C) (rightDup F G) :=
    IsExtApp.fromExt (rightDupExt F C) G

    instance rightDupExt.isExtApp {A B : U} (F : A ⟶ A ⟶ B) (C : U) :
      IsExtApp (A ⟶ A ⟶ B) (rightDupExt F C) :=
    IsExtApp.fromExt (rightDupExtExt A B C) F

    instance substDup.isExtApp {A B C : U} (F : A ⟶ B) (G : A ⟶ B ⟶ B ⟶ C) :
      IsExtApp (A ⟶ B ⟶ B ⟶ C) (substDup F G) :=
    IsExtApp.fromExt (substDupExt F C) G

    instance substDupExt.isExtApp {A B : U} (F : A ⟶ B) (C : U) :
      IsExtApp (A ⟶ B) (substDupExt F C) :=
    IsExtApp.fromExt (substDupExtExt A B C) F

  end HasFullFunExt

end HasFullFunOp



class HasLinearFunctors (U : Universe.{u}) [HasIdentity.{u, iu} U] extends
  HasInternalFunctors U, HasLinearFunOp U, HasLinearFunOp.HasLinearFunExt U

class HasAffineFunctors (U : Universe.{u}) [HasIdentity.{u, iu} U] extends
  HasInternalFunctors U, HasAffineFunOp U, HasAffineFunOp.HasAffineFunExt U

instance HasAffineFunctors.hasLinearFunctors (U : Universe) [HasIdentity.{u, iu} U]
                                               [HasAffineFunctors U] :
  HasLinearFunctors U :=
⟨⟩

class HasStandardFunctors (U : Universe.{u}) [HasIdentity.{u, iu} U] extends
  HasInternalFunctors U, HasFullFunOp U, HasFullFunOp.HasFullFunExt U

instance HasStandardFunctors.hasAffineFunctors (U : Universe) [HasIdentity.{u, iu} U]
                                               [HasStandardFunctors U] :
  HasAffineFunctors U :=
⟨⟩
