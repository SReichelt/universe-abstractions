import UniverseAbstractions.Axioms.CategoryTheory.Basic
import UniverseAbstractions.Axioms.CategoryTheory.Functors
import UniverseAbstractions.Axioms.CategoryTheory.NaturalTransformations



set_option autoBoundImplicitLocal false
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 100000
--set_option pp.universes true

universe u u' u'' u''' v vv w ww iv iw ivv iww



namespace CategoryTheory

  open MetaRelation MetaFunctor MetaQuantification HasTransFun HasSymmFun IsAssociative IsCategoricalPreorder
       HasCatProp HasCatProp.Category HasFunProp HasFunProp.Functor HasNatRel HasNatOp HasNatOpEquiv HasNaturality
       HasFunctors HasCongrArg

  structure IsoDesc {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv, ivv} V] [HasCatProp.{u} V]
                    {A : Category.{u} V} (a b : A) :
    Sort (max 1 v iv) where
  (toHom  : a ⇾ b)
  (invHom : b ⇾ a)
  [isInv  : IsInv toHom invHom]

  namespace IsoDesc

    variable {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv, ivv} V] [HasCatProp.{u} V]
             {A : Category.{u} V}

    instance {a b : A} (e : IsoDesc a b) : IsInv e.toHom e.invHom := e.isInv

    def refl (a : A) : IsoDesc a a :=
    ⟨idHom a, idHom a⟩

    def symm {a b : A} (e : IsoDesc a b) : IsoDesc b a :=
    ⟨e.invHom, e.toHom⟩

    def trans {a b c : A} (e : IsoDesc a b) (f : IsoDesc b c) : IsoDesc a c :=
    ⟨f.toHom • e.toHom, e.invHom • f.invHom⟩

    def toInvEquiv {a b : A} {e₁ e₂ : IsoDesc a b} (h : e₁.toHom ≃ e₂.toHom) :
      e₁.invHom ≃ e₂.invHom :=
    (HalfInv.unique e₁.isInv.leftInv (HalfInv.congrArgLeft h e₂.isInv.rightInv))⁻¹

    def map [HasCatProp.{u'} V] {B : Category.{u'} V} [HasFunProp A B] (F : A ⮕ B) {a b : A}
            (e : IsoDesc a b) :
      IsoDesc (F a) (F b) :=
    { toHom  := mapHom F e.toHom,
      invHom := mapHom F e.invHom,
      isInv  := { leftInv  := mapHalfInv (preFun F) e.isInv.leftInv,
                  rightInv := mapHalfInv (preFun F) e.isInv.rightInv } }

  end IsoDesc

  class HasIsoRel {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv, ivv} V] [HasCatProp.{u} V]
                  (A : Category.{u} V) where
  (Iso                                  : MetaRelation A V)
  (desc {a b : A}                       : Iso a b → IsoDesc a b)
  (defToHomFun (a b : A)                : Iso a b ⟶{λ e => (desc e).toHom} (a ⇾ b))
  (toHomInj {a b : A} {e₁ e₂ : Iso a b} : (desc e₁).toHom ≃ (desc e₂).toHom → e₁ ≃ e₂)

  namespace HasIsoRel

    infix:20 " ⇿ " => CategoryTheory.HasIsoRel.Iso

    variable {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv, ivv} V] [HasCatProp.{u} V]

    section

      variable (A : Category.{u} V) [h : HasIsoRel A]

      def isoRel : BundledRelation V := ⟨h.Iso⟩

      def toHomMetaFunctor : MetaFunctor h.Iso (Hom A) := MetaFunctor.fromDefFun h.defToHomFun

    end

    section

      variable {A : Category.{u} V} [h : HasIsoRel A]

      @[reducible] def toHom  {a b : A} (e : a ⇿ b) : a ⇾ b := (h.desc e).toHom
      @[reducible] def invHom {a b : A} (e : a ⇿ b) : b ⇾ a := (h.desc e).invHom

      def leftInv  {a b : A} (e : a ⇿ b) : HalfInv (toHom e) (invHom e) :=
      (h.desc e).isInv.leftInv
      def rightInv {a b : A} (e : a ⇿ b) : HalfInv (invHom e) (toHom e) :=
      (h.desc e).isInv.rightInv

      def toHomCongrArg  {a b : A} {e₁ e₂ : a ⇿ b} (he : e₁ ≃ e₂) : toHom  e₁ ≃ toHom  e₂ :=
      defCongrArg (h.defToHomFun a b) he
      def invHomCongrArg {a b : A} {e₁ e₂ : a ⇿ b} (he : e₁ ≃ e₂) : invHom e₁ ≃ invHom e₂ :=
      IsoDesc.toInvEquiv (toHomCongrArg he)

      structure DefIso {a b : A} (desc : IsoDesc a b) where
      (e    : a ⇿ b)
      (toEq : toHom e ≃ desc.toHom)

      def byToDef  {a b : A} {desc : IsoDesc a b} {e : DefIso desc} : toHom  e.e ≃ desc.toHom  :=
      e.toEq
      def byInvDef {a b : A} {desc : IsoDesc a b} {e : DefIso desc} : invHom e.e ≃ desc.invHom :=
      IsoDesc.toInvEquiv e.toEq

    end

    class HasTrivialIsomorphismCondition (A : Category.{u} V) [h : HasIsoRel A] where
    (iso {a b : A} (desc : IsoDesc a b) : DefIso desc)

    namespace HasTrivialIsomorphismCondition

      variable {A : Category.{u} V} [HasIsoRel A]
               [h : HasTrivialIsomorphismCondition A]

      def defIso {a b : A} {desc : IsoDesc a b} : DefIso desc := h.iso desc

    end HasTrivialIsomorphismCondition

  end HasIsoRel

  class HasIsoOp {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv, ivv} V] [HasCatProp.{u} V]
                 (A : Category.{u} V) extends
    HasIsoRel A where
  (defRefl (a : A) : HasIsoRel.DefIso (IsoDesc.refl a))
  (defSymm {a b : A} (e : a ⇿ b) : HasIsoRel.DefIso (IsoDesc.symm (desc e)))
  (defTrans {a b c : A} (e : a ⇿ b) (f : b ⇿ c) :
     HasIsoRel.DefIso (IsoDesc.trans (desc e) (desc f)))

  namespace HasIsoOp

    open HasIsoRel

    variable {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv, ivv} V] [HasCatProp.{u} V]

    section

      variable (A : Category.{u} V)

      instance hasTrivialIsoOp [hIso : HasIsoRel A] [h : HasTrivialIsomorphismCondition A] :
        HasIsoOp A :=
      { defRefl  := λ _   => HasTrivialIsomorphismCondition.defIso,
        defSymm  := λ _   => HasTrivialIsomorphismCondition.defIso,
        defTrans := λ _ _ => HasTrivialIsomorphismCondition.defIso }

      variable [h : HasIsoOp A]

      instance isoIsPreorder : IsPreorder h.Iso :=
      { refl  := λ a   => (h.defRefl a).e,
        trans := λ e f => (h.defTrans e f).e }

      instance isoIsEquivalence : IsEquivalence h.Iso :=
      { symm := λ e => (h.defSymm e).e }

      instance toHomIsPreorderFunctor : IsPreorderFunctor (toHomMetaFunctor A) :=
      { reflEq  := λ a   => byToDef • byDef,
        transEq := λ e f => (congrArgTrans byDef byDef)⁻¹ • byToDef • byDef }

    end

    section

      variable {A : Category.{u} V} [h : HasIsoOp A]

      @[reducible] def idIso (a : A) : a ⇿ a := HasRefl.refl a

      def toHomReflEq (a : A) : toHom (idIso a) ≃ idHom a := byToDef
      def toHomSymmEq {a b : A} (e : a ⇿ b) : toHom e⁻¹ ≃ invHom e := byToDef
      def toHomTransEq {a b c : A} (e : a ⇿ b) (f : b ⇿ c) : toHom (f • e) ≃ toHom f • toHom e :=
      byToDef

      def invHomReflEq (a : A) : invHom (idIso a) ≃ idHom a := byInvDef
      def invHomSymmEq {a b : A} (e : a ⇿ b) : invHom e⁻¹ ≃ toHom e := byInvDef
      def invHomTransEq {a b c : A} (e : a ⇿ b) (f : b ⇿ c) : invHom (f • e) ≃ invHom e • invHom f :=
      byInvDef

      def isoAssoc {a b c d : A} (e : a ⇿ b) (f : b ⇿ c) (g : c ⇿ d) :
        (g • f) • e ≃ g • (f • e) :=
      h.toHomInj ((congrArgTransRight (toHomTransEq e f) (toHom g) •
                   toHomTransEq (f • e) g)⁻¹ •
                  assoc (toHom e) (toHom f) (toHom g) •
                  (congrArgTransLeft (toHom e) (toHomTransEq f g) •
                   toHomTransEq e (g • f)))

      def isoRightId {a b : A} (e : a ⇿ b) : e • idIso a ≃ e :=
      h.toHomInj (rightId (toHom e) •
                  (congrArgTransRight (toHomReflEq a) (toHom e) •
                   toHomTransEq (idIso a) e))

      def isoLeftId {a b : A} (e : a ⇿ b) : idIso b • e ≃ e :=
      h.toHomInj (leftId (toHom e) •
                  (congrArgTransLeft (toHom e) (toHomReflEq b) •
                   toHomTransEq e (idIso b)))

      def isoLeftInv {a b : A} (e : a ⇿ b) : e⁻¹ • e ≃ idIso a :=
      h.toHomInj ((toHomReflEq a)⁻¹ •
                  leftInv e •
                  (congrArgTransLeft (toHom e) (toHomSymmEq e) •
                   toHomTransEq e e⁻¹))

      def isoRightInv {a b : A} (e : a ⇿ b) : e • e⁻¹ ≃ idIso b :=
      h.toHomInj ((toHomReflEq b)⁻¹ •
                  rightInv e •
                  (congrArgTransRight (toHomSymmEq e) (toHom e) •
                   toHomTransEq e⁻¹ e))

    end

    section

      variable (A : Category.{u} V) [h : HasIsoOp A]

      instance isoIsCategoricalPreorder : IsCategoricalPreorder h.Iso :=
      { assoc   := isoAssoc,
        rightId := isoRightId,
        leftId  := isoLeftId }

      instance isoIsGroupoidEquivalence : IsGroupoidEquivalence h.Iso :=
      { leftInv  := isoLeftInv,
        rightInv := isoRightInv }

      def isoCatDesc [isoHasTransFun : HasTransFun h.Iso] : CatDesc (isoRel A) :=
      { homIsPreorder            := HasIsoOp.isoIsPreorder A,
        homHasTransFun           := isoHasTransFun,
        homIsCategoricalPreorder := isoIsCategoricalPreorder A }

      def isoGrpoidDesc [isoHasSymmFun : HasSymmFun h.Iso] [isoHasTransFun : HasTransFun h.Iso] :
        GrpoidDesc (isoRel A) :=
      { homIsEquivalence         := HasIsoOp.isoIsEquivalence A,
        homHasSymmFun            := isoHasSymmFun,
        homHasTransFun           := isoHasTransFun,
        homIsGroupoidEquivalence := isoIsGroupoidEquivalence A }

    end

  end HasIsoOp

  class HasIsomorphisms {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv, ivv} V] [HasCatProp.{u} V]
                        (A : Category.{u} V) extends
    HasIsoOp A where
  [isoHasSymmFun  : HasSymmFun  Iso]
  [isoHasTransFun : HasTransFun Iso]
  (defIsoCat      : DefCat (HasIsoOp.isoCatDesc A))

  namespace HasIsomorphisms

    open HasIsoRel HasIsoOp

    variable {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv, ivv} V] [HasCatProp.{u} V]

    section

      variable (A : Category.{u} V) [h : HasIsomorphisms A]

      instance : HasSymmFun  h.Iso := h.isoHasSymmFun
      instance : HasTransFun h.Iso := h.isoHasTransFun

      def iso : Category.{u} V := DefCat.toCategory h.defIsoCat

      @[reducible] def Iso' : MetaRelation A V := Hom (iso A)
      infix:20 " ⇿' " => CategoryTheory.HasIsomorphisms.Iso' _

    end

  end HasIsomorphisms

  namespace HasFunProp

    open HasIsomorphisms

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]
             [HasCatProp.{u} W] [HasCatProp.{v} W] (A : Category.{u} W) (B : Category.{v} W)
             [hAIso : HasIsomorphisms A] [hBIso : HasIsomorphisms B] [HasFunProp (iso A) (iso B)]

    def IsoFunctor := HasFunProp.Functor (iso A) (iso B)

    infixr:20 " ⮕⮕ " => CategoryTheory.HasFunProp.IsoFunctor

  end HasFunProp

  class HasIsoPreFun {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]
                     [HasCatProp.{u} W] [HasCatProp.{v} W] {A : Category.{u} W} {B : Category.{v} W}
                     [hAIso : HasIsoRel A] [hBIso : HasIsoRel B] [hFunProp : HasFunProp A B]
                     (F : A ⮕ B) where
  (defMapIso {a b : A} (e : a ⇿ b) : HasIsoRel.DefIso (IsoDesc.map F (hAIso.desc e)))
  (defMapIsoFun (a b : A) : (a ⇿ b) ⟶{λ e => (defMapIso e).e} (F a ⇿ F b))

  namespace HasIsoPreFun

    open HasIsoRel HasIsoOp HasIsomorphisms

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]
             [HasCatProp.{u} W] [HasCatProp.{v} W] {A : Category.{u} W} {B : Category.{v} W}
             [HasFunProp A B] (F : A ⮕ B)

    section

      variable [hAIso : HasIsoRel A] [hBIso : HasIsoRel B] [h : HasIsoPreFun F]

      def mapIso {a b : A} (e : a ⇿ b) : F a ⇿ F b := (h.defMapIso e).e

      @[reducible] def mapIsoFun (a b : A) : (a ⇿ b) ⟶ (F a ⇿ F b) := h.defMapIsoFun a b

      instance {a b : A} (e : a ⇿ b) : IsFunApp (a ⇿ b) (mapIso F e) :=
      { F := mapIsoFun F a b,
        a := e,
        e := byDef }

      def mapIsoCongrArg {a b : A} {e₁ e₂ : a ⇿ b} (e : e₁ ≃ e₂) : mapIso F e₁ ≃ mapIso F e₂ :=
      HasCongrArg.defCongrArg (h.defMapIsoFun a b) e

      def toHomComm  {a b : A} (e : a ⇿ b) : toHom  (mapIso F e) ≃ mapHom F (toHom  e) := byToDef
      def invHomComm {a b : A} (e : a ⇿ b) : invHom (mapIso F e) ≃ mapHom F (invHom e) := byInvDef

    end

    section

      variable [hAIso : HasIsoOp A] [hBIso : HasIsoOp B] [h : HasIsoPreFun F]

      def isoReflEq (a : A) : mapIso F (idIso a) ≃ idIso (F a) :=
      hBIso.toHomInj ((toHomReflEq (F a))⁻¹ •
                      reflEq F a •
                      (mapHomCongrArg F (toHomReflEq a) •
                       toHomComm F (idIso a)))

      def isoSymmEq {a b : A} (e : a ⇿ b) : mapIso F e⁻¹ ≃ (mapIso F e)⁻¹ :=
      hBIso.toHomInj ((invHomComm F e •
                       toHomSymmEq (mapIso F e))⁻¹ •
                      (mapHomCongrArg F (toHomSymmEq e) •
                       toHomComm F e⁻¹))

      def isoTransEq {a b c : A} (e : a ⇿ b) (f : b ⇿ c) :
        mapIso F (f • e) ≃ mapIso F f • mapIso F e :=
      hBIso.toHomInj ((congrArgTrans (toHomComm F e) (toHomComm F f) •
                       toHomTransEq (mapIso F e) (mapIso F f))⁻¹ •
                      transEq F (toHom e) (toHom f) •
                      (mapHomCongrArg F (toHomTransEq e f) •
                       toHomComm F (f • e)))

    end

    section

      variable [hAIso : HasIsomorphisms A] [hBIso : HasIsomorphisms B] [h : HasIsoPreFun F]

      def isoPreFun : PreFunctor hAIso.Iso hBIso.Iso F.φ := ⟨mapIsoFun F⟩

      instance isoPreFun.isReflFunctor : IsReflFunctor (isoPreFun F) :=
      ⟨λ a => isoReflEq F a • byDef⟩

      instance isoPreFun.isSymmFunctor : IsSymmFunctor (isoPreFun F) :=
      ⟨λ e => (congrArgSymm byDef)⁻¹ • isoSymmEq F e • byDef⟩

      instance isoPreFun.isTransFunctor : IsTransFunctor (isoPreFun F) :=
      ⟨λ e f => (congrArgTrans byDef byDef)⁻¹ • isoTransEq F e f • byDef⟩

      instance isoPreFun.isPreorderFunctor    : IsPreorderFunctor    (isoPreFun F) := ⟨⟩
      instance isoPreFun.isEquivalenceFunctor : IsEquivalenceFunctor (isoPreFun F) := ⟨⟩

      @[reducible] def isoPreFun' : PreFunctor (Hom (iso A)) (Hom (iso B)) F.φ := isoPreFun F

      instance isoPreFun'.isReflFunctor : IsReflFunctor (isoPreFun' F) :=
      ⟨λ a => (DefCat.catReflEq (A := hBIso.defIsoCat) (F a))⁻¹ •
              (isoPreFun.isReflFunctor F).reflEq a •
              congrArg (mapIsoFun F a a) (DefCat.catReflEq (A := hAIso.defIsoCat) a)⟩

      instance isoPreFun'.isTransFunctor : IsTransFunctor (isoPreFun' F) :=
      ⟨λ {a b c} e f => (DefCat.catTransEq (A := hBIso.defIsoCat) ((isoPreFun F) e) ((isoPreFun F) f))⁻¹ •
                        (isoPreFun.isTransFunctor F).transEq e f •
                        congrArg (mapIsoFun F a c) (DefCat.catTransEq (A := hAIso.defIsoCat) e f)⟩

      instance isoPreFun'.isPreorderFunctor : IsPreorderFunctor (isoPreFun' F) := ⟨⟩

      def isoFunDesc : FunDesc (A := iso A) (B := iso B) F.φ := ⟨isoPreFun' F⟩

    end

  end HasIsoPreFun

  class HasIsoFun {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]
                  [HasCatProp.{u} W] [HasCatProp.{v} W] {A : Category.{u} W} {B : Category.{v} W}
                  [hAIso : HasIsomorphisms A] [hBIso : HasIsomorphisms B]
                  [hFunProp : HasFunProp A B]
                  [hIsoFunProp : HasFunProp (HasIsomorphisms.iso A) (HasIsomorphisms.iso B)]
                  (F : A ⮕ B) extends
    HasIsoPreFun F where
  (defIsoFun : HasFunProp.DefFun (HasIsoPreFun.isoFunDesc F))

  namespace HasIsoFun

    open HasIsomorphisms HasIsoPreFun

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]
             [HasCatProp.{u} W] [HasCatProp.{v} W] {A : Category.{u} W} {B : Category.{v} W}
             [hAIso : HasIsomorphisms A] [hBIso : HasIsomorphisms B] [HasFunProp A B]
             [HasFunProp (iso A) (iso B)] (F : A ⮕ B) [h : HasIsoFun F]

    @[reducible] def isoFunctor : A ⮕⮕ B := DefFun.toFunctor h.defIsoFun

    def mapIso' {a b : A} (e : a ⇿ b) : F a ⇿ F b := mapHom (isoFunctor F) e

    def mapIsoEq {a b : A} (e : a ⇿ b) : mapIso' F e ≃ mapIso F e := DefFun.byMapHomDef

  end HasIsoFun

  class HasIsoFunctoriality {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]
                            [HasCatProp.{u} W] [HasCatProp.{v} W] (A : Category.{u} W) (B : Category.{v} W)
                            [hAIso : HasIsomorphisms A] [hBIso : HasIsomorphisms B] where
  [hasFunProp    : HasFunProp A B]
  [hasIsoFunProp : HasFunProp (HasIsomorphisms.iso A) (HasIsomorphisms.iso B)]
  [hasIsoFun (F : A ⮕ B) : HasIsoFun F]

  namespace HasIsoFunctoriality

    open HasIsoRel HasIsomorphisms HasIsoPreFun

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]

    section

      variable [HasCatProp.{u} W] [HasCatProp.{v} W] {A : Category.{u} W} {B : Category.{v} W}
               [hAIso : HasIsomorphisms A] [hBIso : HasIsomorphisms B]
               [h : HasIsoFunctoriality A B]

      instance : HasFunProp A B := h.hasFunProp
      instance : HasFunProp (iso A) (iso B) := h.hasIsoFunProp

      instance (F : A ⮕ B) : HasIsoFun F := h.hasIsoFun F

      def mapIso (F : A ⮕ B) {a b : A} (e : a ⇿ b) : F a ⇿ F b := HasIsoPreFun.mapIso F e

      def mapHomToMapIso {φ : A → B} {F G : h.hasFunProp.Fun φ} {a b : A} {e : a ⇿ b} :
        mapHom ⟨F⟩ (toHom e) ≃ mapHom ⟨G⟩ (toHom e) →
        mapIso ⟨F⟩ e         ≃ mapIso ⟨G⟩ e :=
      λ h₁ => hBIso.toHomInj ((toHomComm ⟨G⟩ e)⁻¹ • h₁ • (toHomComm ⟨F⟩ e))

    end

  end HasIsoFunctoriality



  structure NatIsoDesc {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]
                       [HasCatProp.{u} W] [HasCatProp.{v} W] {A : Category.{u} W} {B : Category.{v} W}
                       [hBIso : HasIsomorphisms B] [hFunProp : HasFunProp A B] (F G : A ⮕ B) :
    Sort (max 1 u w iw) where
  -- Note: `isInvNat` is redundant (see `construct`), but we include it anyway because in strict
  -- cases, it contains a much simpler term.
  (η        : MetaQuantification hBIso.Iso F.φ G.φ)
  [isToNat  : IsNatural (preFun F) (preFun G) (λ a => HasIsoRel.toHom  (η a))]
  [isInvNat : IsNatural (preFun G) (preFun F) (λ a => HasIsoRel.invHom (η a))]

  namespace NatIsoDesc

    open HasIsoRel HasIsoOp HasIsomorphisms HasIsoPreFun HasIsoFun

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]
             [HasCatProp.{u} W] [HasCatProp.{v} W] {A : Category.{u} W} {B : Category.{v} W}
             [hBIso : HasIsomorphisms B] [hFunProp : HasFunProp A B]

    -- It would be nice if we could just use the corresponding code from `Meta.lean` here.
    -- However, we are in the special situation that only terms involving `η` are invertible,
    -- but `mapHom F f` and `mapHom G f` are not. The code in `Meta.lean` currently cannot deal
    -- with this; all operations that involve invertible elements ultimately rely on `HasSymm` for
    -- the entire relation.

    def construct {F G : A ⮕ B} (η : MetaQuantification hBIso.Iso F.φ G.φ)
                  [isToNat : IsNatural (preFun F) (preFun G) (λ a => HasIsoRel.toHom (η a))] :
      NatIsoDesc F G :=
    { η        := η,
      isToNat  := isToNat,
      isInvNat := { nat := λ {a b} f => (cancelLeftId (mapHom F f • invHom (η a)) (leftInv (η b)) •
                                         (assoc (mapHom F f • invHom (η a)) (toHom (η b)) (invHom (η b)))⁻¹) •
                                        congrArgTransRight (assoc (invHom (η a)) (mapHom F f) (toHom (η b)))
                                                           (invHom (η b)) •
                                        assoc (invHom (η a)) (toHom (η b) • mapHom F f) (invHom (η b)) •
                                        congrArgTransLeft (invHom (η a))
                                                          (congrArgTransRight (isToNat.nat f)⁻¹
                                                                              (invHom (η b)) •
                                                           assoc (toHom (η a)) (mapHom G f) (invHom (η b))) •
                                        (cancelRightId (rightInv (η a)) (invHom (η b) • mapHom G f) •
                                         assoc (invHom (η a)) (toHom (η a)) (invHom (η b) • mapHom G f))⁻¹ } }

    def strict {φ : A → B} {F G : hFunProp.Fun φ} (hEq : NatDesc.StrictNaturality F G) :
      NatIsoDesc ⟨F⟩ ⟨G⟩ :=
    { η        := λ a => idIso (φ a),
      isToNat  := { nat := λ {a b} f => (cancelRightId (toHomReflEq (φ a)) (mapHom ⟨G⟩ f))⁻¹ •
                                        hEq f •
                                        cancelLeftId (mapHom ⟨F⟩ f) (toHomReflEq (φ b)) }
      isInvNat := { nat := λ {a b} f => (cancelRightId (invHomReflEq (φ a)) (mapHom ⟨F⟩ f))⁻¹ •
                                        (hEq f)⁻¹ •
                                        cancelLeftId (mapHom ⟨G⟩ f) (invHomReflEq (φ b)) }, }

    def refl (F : A ⮕ B) : NatIsoDesc F F :=
    { η        := MetaQuantification.refl hBIso.Iso F.φ,
      isToNat  := { nat := λ {a b} f => (cancelRightId (toHomReflEq (F a)) (mapHom F f))⁻¹ •
                                        cancelLeftId (mapHom F f) (toHomReflEq (F b)) },
      isInvNat := { nat := λ {a b} f => (cancelRightId (invHomReflEq (F a)) (mapHom F f))⁻¹ •
                                        cancelLeftId (mapHom F f) (invHomReflEq (F b)) } }

    def symm {F G : A ⮕ B} (η : NatIsoDesc F G) : NatIsoDesc G F :=
    { η        := MetaQuantification.symm hBIso.Iso η.η,
      isToNat  := { nat := λ {a b} f => (congrArgTransRight (toHomSymmEq (η.η a)) (mapHom F f))⁻¹ •
                                        η.isInvNat.nat f •
                                        congrArgTransLeft (mapHom G f) (toHomSymmEq (η.η b)) },
      isInvNat := { nat := λ {a b} f => (congrArgTransRight (invHomSymmEq (η.η a)) (mapHom G f))⁻¹ •
                                        η.isToNat.nat f •
                                        congrArgTransLeft (mapHom F f) (invHomSymmEq (η.η b)) } }

    def trans {F G H : A ⮕ B} (η : NatIsoDesc F G) (ε : NatIsoDesc G H) : NatIsoDesc F H :=
    { η        := MetaQuantification.trans hBIso.Iso η.η ε.η,
      isToNat  := { nat := λ {a b} f => (congrArgTransRight (toHomTransEq (η.η a) (ε.η a)) (mapHom H f))⁻¹ •
                                        (IsNatural.trans _ _ (hη := η.isToNat) (hε := ε.isToNat)).nat f •
                                        congrArgTransLeft (mapHom F f) (toHomTransEq (η.η b) (ε.η b)) },
      isInvNat := { nat := λ {a b} f => (congrArgTransRight (invHomTransEq (η.η a) (ε.η a)) (mapHom F f))⁻¹ •
                                        (IsNatural.trans _ _ (hη := ε.isInvNat) (hε := η.isInvNat)).nat f •
                                        congrArgTransLeft (mapHom H f) (invHomTransEq (η.η b) (ε.η b)) } }

    variable {F G : A ⮕ B} (η : NatIsoDesc F G)

    @[reducible] def natIso    (a : A) : F a ⇿ G a := η.η a
    @[reducible] def natToHom  (a : A) : F a ⇾ G a := toHom  (natIso η a)
    @[reducible] def natInvHom (a : A) : G a ⇾ F a := invHom (natIso η a)

    def toNatDesc : NatDesc F G :=
    { η     := natToHom η,
      isNat := η.isToNat }

    def invNatDesc : NatDesc G F :=
    { η     := natInvHom η,
      isNat := η.isInvNat }

    structure IsoDescBuilder [hNatOp : HasNatOp A B] where
    (defToNat  : DefNat (toNatDesc  η))
    (defInvNat : DefNat (invNatDesc η))
    (leftInv   : NatEquiv (defInvNat.η • defToNat.η) (HasRefl.refl F)
                          (λ a => (natReflEq F a)⁻¹ •
                                  leftInv (η.η a) •
                                  congrArgTrans byNatDef byNatDef •
                                  natTransEq defToNat.η defInvNat.η a))
    (rightInv  : NatEquiv (defToNat.η • defInvNat.η) (HasRefl.refl G)
                          (λ b => (natReflEq G b)⁻¹ •
                                  rightInv (η.η b) •
                                  congrArgTrans byNatDef byNatDef •
                                  natTransEq defInvNat.η defToNat.η b))

    namespace IsoDescBuilder

      variable [HasCatProp.{max 1 u v w} W] [hNat : HasNaturality A B] (e : IsoDescBuilder η)

      def isoDesc : IsoDesc (A := A ⮕' B) F G :=
      { toHom  := e.defToNat.η,
        invHom := e.defInvNat.η,
        isInv  := { leftInv  := (DefCat.catReflEq (A := hNat.defFunCat) F)⁻¹ •
                                e.leftInv •
                                DefCat.catTransEq (A := hNat.defFunCat) e.defToNat.η e.defInvNat.η,
                    rightInv := (DefCat.catReflEq (A := hNat.defFunCat) G)⁻¹ •
                                e.rightInv •
                                DefCat.catTransEq (A := hNat.defFunCat) e.defInvNat.η e.defToNat.η } }

    end IsoDescBuilder

    section

      variable [hAIso : HasIsomorphisms A] [HasFunProp (iso A) (iso B)] [HasIsoFun F] [HasIsoFun G]

      def isoNaturality {a b : A} (e : a ⇿ b) :
        natIso η b • mapIso F e ≃ mapIso G e • natIso η a :=
      hBIso.toHomInj ((congrArgTransLeft (natToHom η a) (toHomComm G e) •
                      toHomTransEq (natIso η a) (mapIso G e))⁻¹ •
                     η.isToNat.nat (toHom e) •
                     (congrArgTransRight (toHomComm F e) (natToHom η b) •
                      toHomTransEq (mapIso F e) (natIso η b)))

      instance natIso.isNat :
        IsNatural (preFun (isoFunctor F)) (preFun (isoFunctor G)) (natIso η) :=
      ⟨λ {a b} e => (congrArgTransLeft (natIso η a) (mapIsoEq G e) •
                     DefCat.catTransEq (A := hBIso.defIsoCat) (natIso η a) (mapIso' G e))⁻¹ •
                    isoNaturality η e •
                    (congrArgTransRight (mapIsoEq F e) (natIso η b) •
                     DefCat.catTransEq (A := hBIso.defIsoCat) (mapIso' F e) (natIso η b))⟩

      def toIsoNatDesc : NatDesc (isoFunctor F) (isoFunctor G) :=
      { η     := natIso       η,
        isNat := natIso.isNat η }

    end

  end NatIsoDesc

  namespace HasNaturality

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]
             [HasCatProp.{u} W] [HasCatProp.{v} W] [HasCatProp.{max 1 u v w} W]
             {A : Category.{u} W} {B : Category.{v} W} [HasFunProp A B] [h : HasNaturality A B]
             {F G : A ⮕' B}

    def natHalfInv {η : F ⇾ G} {ε : G ⇾ F} (e : HalfInv η ε) (a : A) :
      HalfInv (nat η a) (nat ε a) :=
    natReflEq' F a • natCongrArg e a • (natTransEq' η ε a)⁻¹

    instance natIsInv (η : F ⇾ G) (ε : G ⇾ F) [isInv : IsInv η ε] (a : A) :
      IsInv (nat η a) (nat ε a) :=
    { leftInv  := natHalfInv isInv.leftInv  a,
      rightInv := natHalfInv isInv.rightInv a }

    def natIsoDesc (η : IsoDesc F G) (a : A) : IsoDesc (F a) (G a) :=
    { toHom  := nat η.toHom  a,
      invHom := nat η.invHom a,
      isInv  := natIsInv η.toHom η.invHom (isInv := η.isInv) a }

  end HasNaturality

  class HasIsoNat {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]
                  [HasCatProp.{u} W] [HasCatProp.{v} W] [HasCatProp.{max 1 u v w} W]
                  {A : Category.{u} W} {B : Category.{v} W}
                  [hFunProp : HasFunProp A B] [hNat : HasNaturality A B]
                  [hBIso : HasIsomorphisms B] [hABIso : HasIsomorphisms (A ⮕' B)]
                  (F G : A ⮕' B) where
  (defNatIso (η : F ⇿ G) (a : A) : HasIsoRel.DefIso (natIsoDesc (hABIso.desc η) a))
  (defNatIsoFun (a : A) : (F ⇿ G) ⟶{λ η => (defNatIso η a).e} (F a ⇿ G a))

  namespace HasIsoNat

    open HasIsoRel HasIsoOp HasIsoPreFun

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]
             [HasCatProp.{u} W] [HasCatProp.{v} W] [HasCatProp.{max 1 u v w} W]
             {A : Category.{u} W} {B : Category.{v} W}

    section

      variable [hBIso : HasIsomorphisms B] [HasFunProp A B] [HasNaturality A B]
               [HasIsomorphisms (A ⮕' B)]

      def natIso {F G : A ⮕' B} [h : HasIsoNat F G] (η : F ⇿ G) (a : A) : F a ⇿ G a :=
      (h.defNatIso η a).e

      @[reducible] def natIsoFun (F G : A ⮕' B) [h : HasIsoNat F G] (a : A) :
        (F ⇿ G) ⟶ (F a ⇿ G a) :=
      h.defNatIsoFun a

      variable {F G : A ⮕' B} [h : HasIsoNat F G]

      instance (η : F ⇿ G) (a : A) : IsFunApp (F ⇿ G) (natIso η a) :=
      { F := natIsoFun F G a,
        a := η,
        e := byDef }

      def natIsoCongrArg {η₁ η₂ : F ⇿ G} (e : η₁ ≃ η₂) (a : A) :
        natIso η₁ a ≃ natIso η₂ a :=
      defCongrArg (h.defNatIsoFun a) e

      def natIsoToHomComm (η : F ⇿ G) (a : A) :
        toHom (natIso η a) ≃ nat (toHom η) a :=
      byToDef

      def natIsoInvHomComm (η : F ⇿ G) (a : A) :
        invHom (natIso η a) ≃ nat (invHom η) a :=
      byInvDef

      def natIsoEq {η₁ η₂ : F ⇿ G} {a : A} :
        nat (toHom η₁) a ≃ nat (toHom η₂) a → natIso η₁ a ≃ natIso η₂ a :=
      λ e => hBIso.toHomInj ((natIsoToHomComm η₂ a)⁻¹ • e • natIsoToHomComm η₁ a)

    end

    section

      variable [hAIso : HasIsomorphisms A] [hBIso : HasIsomorphisms B] [hIsoFun : HasIsoFunctoriality A B]
               [HasNaturality A B] [HasIsomorphisms (A ⮕' B)]

      section

        variable {F G : A ⮕' B} [h : HasIsoNat F G]

        def natIsoDesc (η : F ⇿ G) : NatIsoDesc F G :=
        { η        := natIso η,
          isToNat  := { nat := λ {a b} f => congrArgTransRight (natIsoToHomComm η a)⁻¹ (mapHom G f) •
                                            naturality (toHom η) f •
                                            congrArgTransLeft (mapHom F f) (natIsoToHomComm η b) },
          isInvNat := { nat := λ {a b} f => congrArgTransRight (natIsoInvHomComm η a)⁻¹ (mapHom F f) •
                                            naturality (invHom η) f •
                                            congrArgTransLeft (mapHom G f) (natIsoInvHomComm η b) } }

        def isoNaturality (η : F ⇿ G) {a b : A} (e : a ⇿ b) :
          natIso η b • mapIso F e ≃ mapIso G e • natIso η a :=
        NatIsoDesc.isoNaturality (natIsoDesc η) e

        structure DefNatIso (desc : NatIsoDesc F G) where
        (η             : F ⇿ G)
        (natEq (a : A) : natIso η a ≃ NatIsoDesc.natIso desc a)

        def byNatIsoDef {desc : NatIsoDesc F G} {η : DefNatIso desc} {a : A} :
          natIso η.η a ≃ NatIsoDesc.natIso desc a :=
        η.natEq a

        def byNatIsoToHomDef {desc : NatIsoDesc F G} {η : DefNatIso desc} {a : A} :
          nat (toHom η.η) a ≃ NatIsoDesc.natToHom desc a :=
        toHomCongrArg byNatIsoDef • (natIsoToHomComm η.η a)⁻¹

        def byNatIsoInvHomDef {desc : NatIsoDesc F G} {η : DefNatIso desc} {a : A} :
          nat (invHom η.η) a ≃ NatIsoDesc.natInvHom desc a :=
        invHomCongrArg byNatIsoDef • (natIsoInvHomComm η.η a)⁻¹

      end

      def byStrictNatIsoDef {φ : A → B} {F G : hIsoFun.hasFunProp.Fun φ} [h : HasIsoNat ⟨F⟩ ⟨G⟩]
                            {hEq : NatDesc.StrictNaturality F G}
                            {η : DefNatIso (NatIsoDesc.strict hEq)} {a : A} :
        natIso η.η a ≃ idIso (φ a) :=
      byNatIsoDef

      def byStrictNatIsoToHomDef {φ : A → B} {F G : hIsoFun.hasFunProp.Fun φ} [h : HasIsoNat ⟨F⟩ ⟨G⟩]
                                 {hEq : NatDesc.StrictNaturality F G}
                                 {η : DefNatIso (NatIsoDesc.strict hEq)} {a : A} :
        nat (toHom η.η) a ≃ idHom (φ a) :=
      toHomReflEq (φ a) • byNatIsoToHomDef

      def byStrictNatIsoInvHomDef {φ : A → B} {F G : hIsoFun.hasFunProp.Fun φ} [h : HasIsoNat ⟨F⟩ ⟨G⟩]
                                  {hEq : NatDesc.StrictNaturality F G}
                                  {η : DefNatIso (NatIsoDesc.strict hEq)} {a : A} :
        nat (invHom η.η) a ≃ idHom (φ a) :=
      invHomReflEq (φ a) • byNatIsoInvHomDef

    end

  end HasIsoNat

  class HasIsoNaturality {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]
                         [HasCatProp.{u} W] [HasCatProp.{v} W] [HasCatProp.{max 1 u v w} W]
                         (A : Category.{u} W) (B : Category.{v} W)
                         [hBIso : HasIsomorphisms B] [hFunProp : HasFunProp A B] where
  [hasNat    : HasNaturality A B]
  [hasNatIso : HasIsomorphisms (A ⮕' B)]
  [hasIsoNat (F G : A ⮕' B) : HasIsoNat F G]

  namespace HasIsoNaturality

    open HasIsoRel HasIsoOp HasIsomorphisms HasIsoPreFun HasIsoNat

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W]

    section

      variable [HasCatProp.{u} W] [HasCatProp.{v} W] [HasCatProp.{max 1 u v w} W]
               (A : Category.{u} W) (B : Category.{v} W) [hBIso : HasIsomorphisms B]
               [HasFunProp A B] [h : HasIsoNaturality A B]

      instance : HasNaturality A B        := h.hasNat
      instance : HasIsomorphisms (A ⮕' B) := h.hasNatIso

    end

    section

      variable [HasCatProp.{u} W] [HasCatProp.{v} W] [HasCatProp.{max 1 u v w} W]
               {A : Category.{u} W} {B : Category.{v} W} [hBIso : HasIsomorphisms B]
               [HasFunProp A B] [h : HasIsoNaturality A B]

      instance (F G : A ⮕' B) : HasIsoNat F G := h.hasIsoNat F G

      def natIsoReflEq (F : A ⮕' B) (a : A) : natIso (idIso F) a ≃ idIso (F a) :=
      hBIso.toHomInj ((toHomReflEq (F a))⁻¹ •
                      natReflEq' F a •
                      (natCongrArg (toHomReflEq F) a •
                       natIsoToHomComm (idIso F) a))

      def natIsoSymmEq {F G : A ⮕' B} (η : F ⇿ G) (a : A) : natIso η⁻¹ a ≃ (natIso η a)⁻¹ :=
      hBIso.toHomInj ((natIsoInvHomComm η a •
                       toHomSymmEq (natIso η a))⁻¹ •
                      (natCongrArg (toHomSymmEq η) a •
                       natIsoToHomComm η⁻¹ a))

      def natIsoTransEq {F G H : A ⮕' B} (η : F ⇿ G) (ε : G ⇿ H) (a : A) :
        natIso (ε • η) a ≃ natIso ε a • natIso η a :=
      hBIso.toHomInj ((congrArgTrans (natIsoToHomComm η a) (natIsoToHomComm ε a) •
                       toHomTransEq (natIso η a) (natIso ε a))⁻¹ •
                      natTransEq' (toHom η) (toHom ε) a •
                      (natCongrArg (toHomTransEq η ε) a •
                       natIsoToHomComm (ε • η) a))

    end

    class HasTrivialNaturalityCondition [HasCatProp.{u} W] [HasCatProp.{v} W]
                                        [HasCatProp.{max 1 u v w} W]
                                        (A : Category.{u} W) (B : Category.{v} W)
                                        [hAIso : HasIsomorphisms A] [hBIso : HasIsomorphisms B]
                                        [hIsoFun : HasIsoFunctoriality A B]
                                        [h : HasIsoNaturality A B] where
    (natIso {F G : A ⮕' B} (desc : NatIsoDesc F G) : DefNatIso desc)

    namespace HasTrivialNaturalityCondition

      variable [HasCatProp.{u} W] [HasCatProp.{v} W] [HasCatProp.{max 1 u v w} W]
               {A : Category.{u} W} {B : Category.{v} W} [HasIsomorphisms A] [HasIsomorphisms B]
               [HasIsoFunctoriality A B] [HasIsoNaturality A B]
               [h : HasTrivialNaturalityCondition A B]

      def defNatIso {F G : A ⮕' B} {desc : NatIsoDesc F G} : DefNatIso desc := h.natIso desc

    end HasTrivialNaturalityCondition

    section

      variable [HasCatProp.{u} W] [HasCatProp.{u'} W] [HasCatProp.{u''} W] [HasCatProp.{max 1 u' u'' w} W]
               {A : Category.{u} W} {B : Category.{u'} W} {C : Category.{u''} W}
               [hAIso : HasIsomorphisms A] [hBIso : HasIsomorphisms B] [hCIso : HasIsomorphisms C]
               [hIsoFunBC : HasIsoFunctoriality B C] [hIsoNatBC : HasIsoNaturality B C]
               [hIsoFunABC : HasIsoFunctoriality A (B ⮕' C)]

      structure NatNatIsoDesc (F G : A ⮕ B ⮕' C) (η : ∀ a, F a ⇿ G a) where
      (toDesc  : NatNatDesc F G (λ a => toHom  (η a)))
      (invDesc : NatNatDesc G F (λ a => invHom (η a)))

      namespace NatNatIsoDesc

        def strict {φ : A → B → C} {F' G' : ∀ a, hIsoFunBC.hasFunProp.Fun (φ a)}
                   {hEq : ∀ a, NatDesc.StrictNaturality (F' a) (G' a)}
                   {η : ∀ a, DefNatIso (NatIsoDesc.strict (hEq a))}
                   {F : hIsoFunABC.hasFunProp.Fun (λ a => ⟨F' a⟩)}
                   {G : hIsoFunABC.hasFunProp.Fun (λ a => ⟨G' a⟩)}
                   (hNatEq : NatNatDesc.StrictNaturality₂ F G) :
          NatNatIsoDesc ⟨F⟩ ⟨G⟩ (λ a => (η a).η) :=
        { toDesc  := { natEq := λ {a₁ a₂} f b => (cancelRightId (byStrictNatIsoToHomDef (hEq := hEq a₁))
                                                                (nat (mapHom ⟨G⟩ f) b))⁻¹ •
                                                 hNatEq f b •
                                                 cancelLeftId (nat (mapHom ⟨F⟩ f) b)
                                                              (byStrictNatIsoToHomDef (hEq := hEq a₂)) },
          invDesc := { natEq := λ {a₁ a₂} f b => (cancelRightId (byStrictNatIsoInvHomDef (hEq := hEq a₁))
                                                                (nat (mapHom ⟨F⟩ f) b))⁻¹ •
                                                 (hNatEq f b)⁻¹ •
                                                 cancelLeftId (nat (mapHom ⟨G⟩ f) b)
                                                              (byStrictNatIsoInvHomDef (hEq := hEq a₂)) } }

      end NatNatIsoDesc

      variable {F G : A ⮕ B ⮕' C} {η : ∀ a, F a ⇿ G a}

      structure DefNatNatIsoBase (desc : NatNatIsoDesc F G η) where
      (toDef  : DefNatNatBase desc.toDesc)
      (invDef : DefNatNatBase desc.invDesc)

      namespace DefNatNatIsoBase

        def trivial {desc : NatNatIsoDesc F G η} [HasTrivialNatEquiv B C] : DefNatNatIsoBase desc :=
        { toDef  := DefNatNatBase.trivial,
          invDef := DefNatNatBase.trivial }

        variable {desc : NatNatIsoDesc F G η} (ε : DefNatNatIsoBase desc)

        def natIsoDesc : NatIsoDesc F G :=
        { η        := η,
          isToNat  := { nat := ε.toDef.natEquiv },
          isInvNat := { nat := ε.invDef.natEquiv } }

      end DefNatNatIsoBase

      structure DefNatNatIso [HasCatProp.{max 1 u u' u'' w} W]
                             [hIsoNatABC : HasIsoNaturality A (B ⮕' C)]
                             (desc : NatNatIsoDesc F G η) extends
        DefNatNatIsoBase desc where
      (defNatNatIso : DefNatIso (DefNatNatIsoBase.natIsoDesc toDefNatNatIsoBase))

      namespace DefNatNatIso

        variable [HasCatProp.{max 1 u u' u'' w} W] [HasIsoNaturality A (B ⮕' C)]
                 {desc : NatNatIsoDesc F G η}

        def trivial (ε : DefNatNatIsoBase desc) [HasTrivialNaturalityCondition A (B ⮕' C)] :
          DefNatNatIso desc :=
        { toDefNatNatIsoBase := ε,
          defNatNatIso       := HasTrivialNaturalityCondition.defNatIso }

      end DefNatNatIso

    end

  end HasIsoNaturality



  class IsIsoUniverse (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw, iww} W]
                      [hCatUniv : IsCatUniverse.{u} W] [hFunUniv : IsFunUniverse.{u} W]
                      [hNatUniv : IsNatUniverse.{u} W] where
  [hasIso (A : Category W) : HasIsomorphisms A]
  [hasIsoFun {A B : Category W} (F : A ⮕ B) : HasIsoFun F]
  [hasIsoNat {A B : Category W} (F G : A ⮕ B) : HasIsoNat F G]

  namespace IsIsoUniverse

    open HasIsoRel HasIsoOp HasIsoPreFun HasIsomorphisms HasIsoNat HasIsoNaturality
         HasLinearFunOp HasSubLinearFunOp HasNonLinearFunOp

    section

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W] [IsCatUniverse.{u} W]
               [IsFunUniverse.{u} W] [IsNatUniverse.{u} W] [h : IsIsoUniverse.{u} W]

      instance (A : Category W) : HasIsomorphisms A := h.hasIso A

      instance hasIsoFunctoriality (A B : Category W) : HasIsoFunctoriality A B :=
      { hasIsoFun := h.hasIsoFun }

      instance hasIsoNaturality (A B : Category W) : HasIsoNaturality A B :=
      { hasIsoNat := h.hasIsoNat }

      instance hasEquivalenceRelation (A : univ W) : HasEquivalenceRelation A W :=
      { R := (hasIso A).Iso,
        h := isoIsEquivalence A }

    end

    section

      variable (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw, iww} W] [IsCatUniverse.{u} W]
               [IsFunUniverse.{u} W] [IsNatUniverse.{u} W] [h : IsIsoUniverse.{u} W]

      instance hasInstanceEquivalences : HasInstanceEquivalences (univ W) W :=
      ⟨hasEquivalenceRelation⟩

      instance hasCongrArg : HasCongrArg (univ W) (univ W) := ⟨λ {_ _} F {_ _} e => mapIso F e⟩
      instance hasCongrFun : HasCongrFun (univ W) (univ W) := ⟨λ e a => natIso e a⟩

      instance hasInternalFunctors : HasInternalFunctors (univ W) := ⟨⟩

      instance hasLinearFunOp [IsFunUniverse.HasLinearFunctors W] [IsNatUniverse.HasLinearFunctors W] :
        HasLinearFunOp (univ W) :=
      { defIdFun         := λ A     => toDefFun (IsNatUniverse.HasLinearFunctors.idFun A),
        defRevAppFun     := λ a B   => toDefFun (IsNatUniverse.HasLinearFunctors.revAppFun a B),
        defRevAppFunFun  := λ A B   => toDefFun (IsNatUniverse.HasLinearFunctors.revAppFunFun A B),
        defCompFun       := λ F G   => toDefFun (IsNatUniverse.HasLinearFunctors.compFun F G),
        defCompFunFun    := λ F C   => toDefFun (IsNatUniverse.HasLinearFunctors.compFunFun F C),
        defCompFunFunFun := λ A B C => toDefFun (IsNatUniverse.HasLinearFunctors.compFunFunFun A B C) }

      instance hasAffineFunOp [HasSubLinearFunOp W] [IsFunUniverse.HasAffineFunctors W]
                              [IsNatUniverse.HasAffineFunctors W] :
        HasAffineFunOp (univ W) :=
      { defConstFun    := λ A {_} b => toDefFun (IsNatUniverse.HasAffineFunctors.constFun A b),
        defConstFunFun := λ A B     => toDefFun (IsNatUniverse.HasAffineFunctors.constFunFun A B) }

      instance hasFullFunOp [HasSubLinearFunOp W] [HasNonLinearFunOp W] [IsFunUniverse.HasAffineFunctors W]
                            [IsNatUniverse.HasFullFunctors W] :
        HasFullFunOp (univ W) :=
      { defDupFun    := λ F   => toDefFun (IsNatUniverse.HasFullFunctors.dupFun F),
        defDupFunFun := λ A B => toDefFun (IsNatUniverse.HasFullFunctors.dupFunFun A B) }

      class HasTrivialNaturalIsomorphisms where
      [hasTrivialNatEquiv (A B : Category W) : HasTrivialNatEquiv A B]
      [hasTrivialIsoNat   (A B : Category W) : HasIsoNaturality.HasTrivialNaturalityCondition A B]

      namespace HasTrivialNaturalIsomorphisms

        variable [h : HasTrivialNaturalIsomorphisms W]

        instance (A B : Category W) : HasTrivialNatEquiv A B                             := h.hasTrivialNatEquiv A B
        instance (A B : Category W) : HasIsoNaturality.HasTrivialNaturalityCondition A B := h.hasTrivialIsoNat A B

      end HasTrivialNaturalIsomorphisms

    end

    section

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw, iww} W] [IsCatUniverse.{u} W]
               [IsFunUniverse.{u} W] [IsNatUniverse.{u} W] [h : IsIsoUniverse.{u} W]

      section

        variable [IsFunUniverse.HasLinearFunctors W] [IsNatUniverse.HasLinearFunctors W]

        def byIdFunDef {A : univ W} {a₁ a₂ : A} {f : a₁ ⇾ a₂} :
          mapHom (idFun A) f ≃' f :=
        DefFun.byMapHomDef

        def byAppFunFunDef {A B : univ W} {F₁ F₂ : A ⟶ B} {η : F₁ ⇾ F₂} {a : A} :
          nat (mapHom (appFunFun A B) η) a ≃' nat η a :=
        natCongrArg byIdFunDef a

        def byRevAppFunDef {A B : univ W} {a : A} {F₁ F₂ : A ⟶ B} {η : F₁ ⇾ F₂} :
          mapHom (revAppFun a B) η ≃' nat η a :=
        DefFun.byMapHomDef

        def byRevAppFunFunDef {A B : univ W} {a₁ a₂ : A} {f : a₁ ⇾ a₂} {F : A ⟶ B} :
          nat (mapHom (revAppFunFun A B) f) F ≃' mapHom F f :=
        DefFunFun.byFunFunDef

        def byCompFunDef {A B C : univ W} {F : A ⟶ B} {G : B ⟶ C} {a₁ a₂ : A} {f : a₁ ⇾ a₂} :
          mapHom (G • F) f ≃' mapHom G (mapHom F f) :=
        DefFun.byMapHomDef

        def byCompFunFunDef {A B C : univ W} {F : A ⟶ B} {G₁ G₂ : B ⟶ C} {ε : G₁ ⇾ G₂} {a : A} :
          nat (mapHom (compFunFun F C) ε) a ≃' nat ε (F a) :=
        DefFunFun.byFunFunDef

        def byCompFunFunFunDef {A B C : univ W} {F₁ F₂ : A ⟶ B} {η : F₁ ⇾ F₂} {G : B ⟶ C} {a : A} :
          nat (nat (mapHom (compFunFunFun A B C) η) G) a ≃' mapHom G (nat η a) :=
        DefFunFunFun.byFunFunFunDef

        def bySwapFunDef {A B C : univ W} {F : A ⟶ B ⟶ C} {b : B} {a₁ a₂ : A} {f : a₁ ⇾ a₂} :
          mapHom (swapFun F b) f ≃' nat (mapHom F f) b :=
        byRevAppFunDef • byCompFunDef

        def bySwapFunFunDef {A B C : univ W} {F : A ⟶ B ⟶ C} {b₁ b₂ : B} {g : b₁ ⇾ b₂} {a : A} :
          nat (mapHom (swapFunFun F) g) a ≃' mapHom (F a) g :=
        byRevAppFunFunDef • byCompFunFunDef • natCongrArg byCompFunDef a

        def bySwapFunFunFunDef {A B C : univ W} {F₁ F₂ : A ⟶ B ⟶ C} {η : F₁ ⇾ F₂} {a : A} {b : B} :
          nat (nat (mapHom (swapFunFunFun A B C) η) b) a ≃' nat (nat η a) b :=
        byRevAppFunDef •
        byCompFunFunFunDef •
        natCongrArg (byCompFunFunDef • natCongrArg byCompFunDef b) a

        def byRevCompFunFunDef {A B C : univ W} {G : B ⟶ C} {F₁ F₂ : A ⟶ B} {η : F₁ ⇾ F₂} {a : A} :
          nat (mapHom (revCompFunFun A G) η) a ≃' mapHom G (nat η a) :=
        byCompFunFunFunDef • natCongrArg bySwapFunDef a

        def byRevCompFunFunFunDef {A B C : univ W} {G₁ G₂ : B ⟶ C} {ε : G₁ ⇾ G₂} {F : A ⟶ B} {a : A} :
          nat (nat (mapHom (revCompFunFunFun A B C) ε) F) a ≃' nat ε (F a) :=
        byCompFunFunDef • natCongrArg bySwapFunFunDef a

        def rightIdNatDesc {A B : univ W} (F : A ⟶ B) : NatIsoDesc (F • idFun A) F :=
        NatIsoDesc.strict (λ _ => mapHomCongrArg F byIdFunDef • byCompFunDef)

        class HasRightIdNat (A B : univ W) where
        (defRightIdNat (F : A ⟶ B) : DefNatIso (rightIdNatDesc F))

        def rightIdNatNatDesc (A B : univ W) [h : HasRightIdNat A B] :
          NatNatIsoDesc (compFunFun (idFun A) B) (idFun (A ⟶ B)) (λ F => (h.defRightIdNat F).η) :=
        NatNatIsoDesc.strict (λ _ _ => byAppFunFunDef⁻¹ • byCompFunFunDef)

        class HasRightIdNatNat (A B : univ W) extends HasRightIdNat A B where
        (defRightIdNatNat : DefNatNatIso (rightIdNatNatDesc A B))

        def leftIdNatDesc {A B : univ W} (F : A ⟶ B) : NatIsoDesc (idFun B • F) F :=
        NatIsoDesc.strict (λ _ => byIdFunDef • byCompFunDef)

        class HasLeftIdNat (A B : univ W) where
        (defLeftIdNat (F : A ⟶ B) : DefNatIso (leftIdNatDesc F))

        def leftIdNatNatDesc (A B : univ W) [h : HasLeftIdNat A B] :
          NatNatIsoDesc (revCompFunFun A (idFun B)) (idFun (A ⟶ B)) (λ F => (h.defLeftIdNat F).η) :=
        NatNatIsoDesc.strict (λ _ _ => byAppFunFunDef⁻¹ • byIdFunDef • byRevCompFunFunDef)

        class HasLeftIdNatNat (A B : univ W) extends HasLeftIdNat A B where
        (defLeftIdNatNat : DefNatNatIso (leftIdNatNatDesc A B))

        def swapRevAppNatDesc {A B : univ W} (F : A ⟶ B) :
          NatIsoDesc (swapFun (revAppFunFun A B) F) F :=
        NatIsoDesc.strict (λ _ => byRevAppFunFunDef • bySwapFunDef)

        class HasSwapRevAppNat (A B : univ W) where
        (defSwapRevAppNat (F : A ⟶ B) : DefNatIso (swapRevAppNatDesc F))

        def swapRevAppNatNatDesc (A B : univ W) [h : HasSwapRevAppNat A B] :
          NatNatIsoDesc (swapFunFun (revAppFunFun A B)) (appFunFun A B) (λ F => (h.defSwapRevAppNat F).η) :=
        NatNatIsoDesc.strict (λ _ _ => byAppFunFunDef⁻¹ • byRevAppFunDef • bySwapFunFunDef)

        class HasSwapRevAppNatNat (A B : univ W) extends HasSwapRevAppNat A B where
        (defSwapRevAppNatNat : DefNatNatIso (swapRevAppNatNatDesc A B))

        def swapCompFunNatDesc {A B : univ W} (F : A ⟶ B) (a : A) (C : univ W) :
          NatIsoDesc (swapFun (compFunFun F C) a) (revAppFun (F a) C) :=
        NatIsoDesc.strict (λ _ => byRevAppFunDef⁻¹ • byCompFunFunDef • bySwapFunDef)

        class HasSwapCompFunNat (A B C : univ W) where
        (defSwapCompFunNat (F : A ⟶ B) (a : A) : DefNatIso (swapCompFunNatDesc F a C))

        class HasSwapCompFunNatNat (A B C : univ W) extends HasSwapCompFunNat A B C

        class HasSwapCompFunNatNatNat (A B C : univ W) extends HasSwapCompFunNatNat A B C

        def swapRevCompFunNatDesc {A B C : univ W} (F : B ⟶ C) (a : A) :
          NatIsoDesc (swapFun (revCompFunFun A F) a) (F • revAppFun a B) :=
        NatIsoDesc.strict (λ _ => (mapHomCongrArg F byRevAppFunDef • byCompFunDef)⁻¹ •
                                  byRevCompFunFunDef • bySwapFunDef)

        class HasSwapRevCompFunNat (A B C : univ W) where
        (defSwapRevCompFunNat (F : B ⟶ C) (a : A) : DefNatIso (swapRevCompFunNatDesc F a))

        class HasSwapRevCompFunNatNat (A B C : univ W) extends HasSwapRevCompFunNat A B C

        class HasSwapRevCompFunNatNatNat (A B C : univ W) extends HasSwapRevCompFunNatNat A B C

        def compAssocNatDesc {A B C D : univ W} (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) :
          NatIsoDesc ((H • G) • F) (H • (G • F)) :=
        NatIsoDesc.strict (λ _ => (mapHomCongrArg H byCompFunDef • byCompFunDef)⁻¹ •
                                  byCompFunDef • byCompFunDef)

        class HasCompAssocNat (A B C D : univ W) where
        (defCompAssocNat (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) : DefNatIso (compAssocNatDesc F G H))

        class HasCompAssocNatNat (A B C D : univ W) extends HasCompAssocNat A B C D

        class HasCompAssocNatNatNat (A B C D : univ W) extends HasCompAssocNatNat A B C D

        class HasCompAssocNatNatNatNat (A B C D : univ W) extends HasCompAssocNatNatNat A B C D

      end

      section

        variable [HasSubLinearFunOp W] [IsFunUniverse.HasAffineFunctors W]
                 [IsNatUniverse.HasAffineFunctors W]

        def byConstFunDef {A B : univ W} {b : B} {a₁ a₂ : A} {f : a₁ ⇾ a₂} :
          mapHom (constFun A b) f ≃' idHom b :=
        DefFun.byMapHomDef

        def byConstFunFunDef {A B : univ W} {b₁ b₂ : B} {g : b₁ ⇾ b₂} {a : A} :
          nat (mapHom (constFunFun A B) g) a ≃' g :=
        DefFunFun.byFunFunDef

        def rightConstNatDesc (A : univ W) {B C : univ W} (b : B) (G : B ⟶ C) :
          NatIsoDesc (G • constFun A b) (constFun A (G b)) :=
        NatIsoDesc.strict (λ _ => byConstFunDef⁻¹ •
                                  reflEq G b • mapHomCongrArg G byConstFunDef • byCompFunDef)

        class HasRightConstNat (A B C : univ W) where
        (defRightConstNat (b : B) (G : B ⟶ C) : DefNatIso (rightConstNatDesc A b G))

        class HasRightConstNatNat (A B C : univ W) extends HasRightConstNat A B C

        class HasRightConstNatNatNat (A B C : univ W) extends HasRightConstNatNat A B C

        def leftConstNatDesc {A B C : univ W} (F : A ⟶ B) (c : C) :
          NatIsoDesc (constFun B c • F) (constFun A c) :=
        NatIsoDesc.strict (λ _ => byConstFunDef⁻¹ • byConstFunDef • byCompFunDef)

        class HasLeftConstNat (A B C : univ W) where
        (defLeftConstNat (F : A ⟶ B) (c : C) : DefNatIso (leftConstNatDesc F c))

        class HasLeftConstNatNat (A B C : univ W) extends HasLeftConstNat A B C

        class HasLeftConstNatNatNat (A B C : univ W) extends HasLeftConstNatNat A B C

      end

      section

        variable [HasSubLinearFunOp W] [HasNonLinearFunOp W] [IsFunUniverse.HasAffineFunctors W]
                 [IsNatUniverse.HasFullFunctors W]

        def byDupFunDef {A B : univ W} {F : A ⟶ A ⟶ B} {a₁ a₂ : A} {f : a₁ ⇾ a₂} :
          mapHom (dupFun F) f ≃' mapDupHom F f :=
        DefFun.byMapHomDef

        def byDupFunDef' {A B : univ W} {F : A ⟶ A ⟶ B} {a₁ a₂ : A} {f : a₁ ⇾ a₂} :
          mapHom (dupFun F) f ≃' mapDupHom' F f :=
        (mapDupHomEq F f)⁻¹ • byDupFunDef

        def byDupFunFunDef {A B : univ W} {F₁ F₂ : A ⟶ A ⟶ B} {η : F₁ ⇾ F₂} {a : A} :
          nat (mapHom (dupFunFun A B) η) a ≃' nat (nat η a) a :=
        DefFunFun.byFunFunDef

        def bySubstFunDef {A B C : univ W} {F : A ⟶ B} {G : A ⟶ B ⟶ C} {a₁ a₂ : A} {f : a₁ ⇾ a₂} :
          mapHom (substFun F G) f ≃' mapHom (G a₂) (mapHom F f) • nat (mapHom G f) (F a₁) :=
        congrArgTrans (byCompFunFunDef • natCongrArg byCompFunDef a₁) byCompFunDef • byDupFunDef

        def bySubstFunDef' {A B C : univ W} {F : A ⟶ B} {G : A ⟶ B ⟶ C} {a₁ a₂ : A} {f : a₁ ⇾ a₂} :
          mapHom (substFun F G) f ≃' nat (mapHom G f) (F a₂) • mapHom (G a₁) (mapHom F f) :=
        congrArgTrans byCompFunDef (byCompFunFunDef • natCongrArg byCompFunDef a₂) • byDupFunDef'

        def dupSwapNatDesc {A B : univ W} (F : A ⟶ A ⟶ B) :
          NatIsoDesc (dupFun (swapFunFun F)) (dupFun F) :=
        NatIsoDesc.strict (λ _ => byDupFunDef⁻¹ •
                                  congrArgTrans bySwapFunDef bySwapFunFunDef •
                                  byDupFunDef')

        class HasDupSwapNat (A B : univ W) where
        (defDupSwapNat (F : A ⟶ A ⟶ B) : DefNatIso (dupSwapNatDesc F))

        def dupSwapNatNatDesc (A B : univ W) [h : HasDupSwapNat A B] :
          NatNatIsoDesc (dupFunFun A B • swapFunFunFun A A B) (dupFunFun A B)
                        (λ F => (h.defDupSwapNat F).η) :=
        NatNatIsoDesc.strict (λ _ a => byDupFunFunDef⁻¹ •
                                       bySwapFunFunFunDef •
                                       byDupFunFunDef •
                                       natCongrArg byCompFunDef a)

        class HasDupSwapNatNat (A B : univ W) extends HasDupSwapNat A B where
        (defDupSwapNatNat : DefNatNatIso (dupSwapNatNatDesc A B))

        def dupConstNatDesc {A B : univ W} (F : A ⟶ B) :
          NatIsoDesc (dupFun (constFun A F)) F :=
        NatIsoDesc.strict (λ {a b} f => rightId (mapHom F f) •
                                        congrArgTransRight (natReflEq' F a • natCongrArg byConstFunDef a)
                                                           (mapHom F f) •
                                        byDupFunDef)

        class HasDupConstNat (A B : univ W) where
        (defDupConstNat (F : A ⟶ B) : DefNatIso (dupConstNatDesc F))

        def dupConstNatNatDesc (A B : univ W) [h : HasDupConstNat A B] :
          NatNatIsoDesc (dupFunFun A B • constFunFun A (A ⟶ B)) (idFun (A ⟶ B))
                        (λ F => (h.defDupConstNat F).η) :=
        NatNatIsoDesc.strict (λ f a => natCongrArg (byIdFunDef⁻¹ • byConstFunFunDef) a •
                                       byDupFunFunDef •
                                       natCongrArg byCompFunDef a)

        class HasDupConstNatNat (A B : univ W) extends HasDupConstNat A B where
        (defDupConstNatNat : DefNatNatIso (dupConstNatNatDesc A B))

      end

    end

    section

      variable (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw, iww} W] [IsCatUniverse.{u} W]
               [IsFunUniverse.{u} W] [IsNatUniverse.{u} W] [h : IsIsoUniverse.{u} W]

      class HasLinearNaturalIsomorphisms [hLinFun : IsFunUniverse.HasLinearFunctors W]
                                         [hNatLinFun : IsNatUniverse.HasLinearFunctors W] where
      [hasRightIdNatNat           (A B     : Category W) : HasRightIdNatNat           A B]
      [hasLeftIdNatNat            (A B     : Category W) : HasLeftIdNatNat            A B]
      [hasSwapRevAppNatNat        (A B     : Category W) : HasSwapRevAppNatNat        A B]
      [hasSwapCompFunNatNatNat    (A B C   : Category W) : HasSwapCompFunNatNatNat    A B C]
      [hasSwapRevCompFunNatNatNat (A B C   : Category W) : HasSwapRevCompFunNatNatNat A B C]
      [hasCompAssocNatNatNatNat   (A B C D : Category W) : HasCompAssocNatNatNatNat   A B C D]

      namespace HasLinearNaturalIsomorphisms

        variable [IsFunUniverse.HasLinearFunctors W] [IsNatUniverse.HasLinearFunctors W]

        instance trivial [h : HasTrivialNaturalIsomorphisms W] : HasLinearNaturalIsomorphisms W :=
        { hasRightIdNatNat           := λ _ _     => { defRightIdNat        := λ _ => HasTrivialNaturalityCondition.defNatIso,
                                                       defRightIdNatNat     := DefNatNatIso.trivial DefNatNatIsoBase.trivial },
          hasLeftIdNatNat            := λ _ _     => { defLeftIdNat         := λ _ => HasTrivialNaturalityCondition.defNatIso,
                                                       defLeftIdNatNat      := DefNatNatIso.trivial DefNatNatIsoBase.trivial },
          hasSwapRevAppNatNat        := λ _ _     => { defSwapRevAppNat     := λ _ => HasTrivialNaturalityCondition.defNatIso,
                                                       defSwapRevAppNatNat  := DefNatNatIso.trivial DefNatNatIsoBase.trivial },
          hasSwapCompFunNatNatNat    := λ _ _ _   => { defSwapCompFunNat    := λ _ _ => HasTrivialNaturalityCondition.defNatIso },
          hasSwapRevCompFunNatNatNat := λ _ _ _   => { defSwapRevCompFunNat := λ _ _ => HasTrivialNaturalityCondition.defNatIso },
          hasCompAssocNatNatNatNat   := λ _ _ _ _ => { defCompAssocNat      := λ _ _ _ => HasTrivialNaturalityCondition.defNatIso } }

        instance hasLinearFunExt [h : HasLinearNaturalIsomorphisms W] :
          HasLinearFunOp.HasLinearFunExt (univ W) :=
        { rightId              := λ {A B} F         => ((h.hasRightIdNatNat A B).defRightIdNat F).η,
          rightIdExt           := λ A B             => (h.hasRightIdNatNat A B).defRightIdNatNat.defNatNatIso.η,
          leftId               := λ {A B} F         => ((h.hasLeftIdNatNat A B).defLeftIdNat F).η,
          leftIdExt            := λ A B             => (h.hasLeftIdNatNat A B).defLeftIdNatNat.defNatNatIso.η,
          swapRevApp           := λ {A B} F         => ((h.hasSwapRevAppNatNat A B).defSwapRevAppNat F).η,
          swapRevAppExt        := λ A B             => (h.hasSwapRevAppNatNat A B).defSwapRevAppNatNat.defNatNatIso.η,
          swapCompFun          := λ {A B} F a C     => ((h.hasSwapCompFunNatNatNat A B C).defSwapCompFunNat F a).η,
          swapCompFunExt       := λ {A B} F C       => sorry,
          swapCompFunExtExt    := λ A B C           => sorry,
          swapRevCompFun       := λ {A B C} F a     => ((h.hasSwapRevCompFunNatNatNat A B C).defSwapRevCompFunNat F a).η,
          swapRevCompFunExt    := λ A {B C} F       => sorry,
          swapRevCompFunExtExt := λ A B C           => sorry,
          compAssoc            := λ {A B C D} F G H => ((h.hasCompAssocNatNatNatNat A B C D).defCompAssocNat F G H).η,
          compAssocExt         := λ {A B C} F G D   => sorry,
          compAssocExtExt      := λ {A B} F C D     => sorry,
          compAssocExtExtExt   := λ A B C D         => sorry }

      end HasLinearNaturalIsomorphisms

      class HasAffineNaturalIsomorphisms [HasSubLinearFunOp W]
                                         [hAffFun : IsFunUniverse.HasAffineFunctors W]
                                         [hNatAffFun : IsNatUniverse.HasAffineFunctors W] extends
        HasLinearNaturalIsomorphisms W where
      [hasRightConstNatNatNat (A B C : Category W) : HasRightConstNatNatNat A B C]
      [hasLeftConstNatNatNat  (A B C : Category W) : HasLeftConstNatNatNat  A B C]

      namespace HasAffineNaturalIsomorphisms

        variable [HasSubLinearFunOp W] [IsFunUniverse.HasAffineFunctors W]
                 [IsNatUniverse.HasAffineFunctors W]

        instance trivial [h : HasTrivialNaturalIsomorphisms W] : HasAffineNaturalIsomorphisms W :=
        { hasRightConstNatNatNat := λ _ _ _ => { defRightConstNat := λ _ _ => HasTrivialNaturalityCondition.defNatIso },
          hasLeftConstNatNatNat  := λ _ _ _ => { defLeftConstNat  := λ _ _ => HasTrivialNaturalityCondition.defNatIso } }

        instance hasAffineFunExt [h : HasAffineNaturalIsomorphisms W] :
          HasAffineFunOp.HasAffineFunExt (univ W) :=
        { rightConst       := λ A {B C} b G => ((h.hasRightConstNatNatNat A B C).defRightConstNat b G).η,
          rightConstExt    := λ A {B} b C   => sorry,
          rightConstExtExt := λ A B C       => sorry,
          leftConst        := λ {A B C} F c => ((h.hasLeftConstNatNatNat A B C).defLeftConstNat F c).η,
          leftConstExt     := λ {A B} F C   => sorry,
          leftConstExtExt  := λ A B C       => sorry }

      end HasAffineNaturalIsomorphisms

      class HasFullNaturalIsomorphisms [HasSubLinearFunOp W] [HasNonLinearFunOp W]
                                       [hAffFun : IsFunUniverse.HasAffineFunctors W]
                                       [hNatFullFun : IsNatUniverse.HasFullFunctors W] extends
        HasAffineNaturalIsomorphisms W where
      [hasDupSwapNatNat  (A B : Category W) : HasDupSwapNatNat  A B]
      [hasDupConstNatNat (A B : Category W) : HasDupConstNatNat A B]

      namespace HasFullNaturalIsomorphisms

        variable [HasSubLinearFunOp W] [HasNonLinearFunOp W] [IsFunUniverse.HasAffineFunctors W]
                 [IsNatUniverse.HasFullFunctors W]

        instance trivial [h : HasTrivialNaturalIsomorphisms W] : HasFullNaturalIsomorphisms W :=
        { hasDupSwapNatNat  := λ _ _ => { defDupSwapNat     := λ _ => HasTrivialNaturalityCondition.defNatIso,
                                          defDupSwapNatNat  := DefNatNatIso.trivial DefNatNatIsoBase.trivial },
          hasDupConstNatNat := λ _ _ => { defDupConstNat    := λ _ => HasTrivialNaturalityCondition.defNatIso,
                                          defDupConstNatNat := DefNatNatIso.trivial DefNatNatIsoBase.trivial } }

        instance hasFullFunExt [h : HasFullNaturalIsomorphisms W] :
          HasFullFunOp.HasFullFunExt (univ W) :=
        { dupSwap        := λ {A B} F     => ((h.hasDupSwapNatNat A B).defDupSwapNat F).η,
          dupSwapExt     := λ A B         => (h.hasDupSwapNatNat A B).defDupSwapNatNat.defNatNatIso.η,
          dupConst       := λ {A B} F     => ((h.hasDupConstNatNat A B).defDupConstNat F).η,
          dupConstExt    := λ A B         => (h.hasDupConstNatNat A B).defDupConstNatNat.defNatNatIso.η,
          rightDup       := λ {A B C} F G => sorry,
          rightDupExt    := λ {A B} F C   => sorry,
          rightDupExtExt := λ A B C       => sorry,
          substDup       := λ {A B C} F G => sorry,
          substDupExt    := λ {A B} F C   => sorry,
          substDupExtExt := λ A B C       => sorry }

      end HasFullNaturalIsomorphisms

      instance hasStandardFunctors [HasSubLinearFunOp W] [HasNonLinearFunOp W]
                                   [IsFunUniverse.HasAffineFunctors W] [IsNatUniverse.HasFullFunctors W]
                                   [h : HasFullNaturalIsomorphisms W] :
        HasStandardFunctors (univ W) :=
      ⟨⟩

    end

  end IsIsoUniverse

end CategoryTheory
