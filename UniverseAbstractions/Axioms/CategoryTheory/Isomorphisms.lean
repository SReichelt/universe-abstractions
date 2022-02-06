import UniverseAbstractions.Axioms.CategoryTheory.Extended



set_option autoBoundImplicitLocal false
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 100000
--set_option pp.universes true

universe u u' u'' u''' v vv w ww iv iw



namespace CategoryTheory

  open MetaRelation MetaFunctor MetaQuantification HasTransFun HasSymmFun IsAssociative
       IsCategoricalPreorder IsGroupoidEquivalence IsCategory
       HasFunProp HasFunProp.Functor HasNatRel HasNatOp HasNatOpEquiv HasNaturality
       HasFunctors HasCongrArg

  namespace IsCategory

    structure IsoDesc {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv} V] {α : Sort u}
                      [hα : IsCategory V α] (a b : α) :
      Sort (max 1 v iv) where
    (toHom  : a ⇾ b)
    (invHom : b ⇾ a)
    [isInv  : IsInv hα.Hom toHom invHom]

    namespace IsoDesc

      open IsCategoryFunctor

      variable {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv} V] {α : Sort u}
               [hα : IsCategory V α]

      instance {a b : α} (e : IsoDesc a b) : IsInv hα.Hom e.toHom e.invHom := e.isInv

      def refl (a : α) : IsoDesc a a :=
      ⟨idHom a, idHom a⟩

      def symm {a b : α} (e : IsoDesc a b) : IsoDesc b a :=
      ⟨e.invHom, e.toHom⟩

      def trans {a b c : α} (e : IsoDesc a b) (f : IsoDesc b c) : IsoDesc a c :=
      ⟨f.toHom • e.toHom, e.invHom • f.invHom⟩

      def toInvEquiv {a b : α} {e₁ e₂ : IsoDesc a b} (h : e₁.toHom ≃ e₂.toHom) :
        e₁.invHom ≃ e₂.invHom :=
      (HalfInv.unique hα.Hom e₁.isInv.leftInv (HalfInv.congrArgLeft hα.Hom h e₂.isInv.rightInv))⁻¹

      def map {β : Sort u'} [hβ : IsCategory V β] (F : MorphismFunctor α β)
              [h : IsCategoryFunctor F] {a b : α} (e : IsoDesc a b) :
        IsoDesc (F.φ a) (F.φ b) :=
      { toHom  := F.F e.toHom,
        invHom := F.F e.invHom,
        isInv  := { leftInv  := mapHalfInv F e.isInv.leftInv,
                    rightInv := mapHalfInv F e.isInv.rightInv } }

    end IsoDesc

    class HasIsoRel {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv} V]
                    (α : Sort u) [hα : IsCategory V α] where
    (Iso                                  : MetaRelation α V)
    (desc {a b : α}                       : Iso a b → IsoDesc a b)
    (defToHomFun (a b : α)                : Iso a b ⟶{λ e => (desc e).toHom} (a ⇾ b))
    (toHomInj {a b : α} {e₁ e₂ : Iso a b} : (desc e₁).toHom ≃ (desc e₂).toHom → e₁ ≃ e₂)

    namespace HasIsoRel

      infix:20 " ⇿ " => CategoryTheory.IsCategory.HasIsoRel.Iso

      variable {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv} V]

      section

        variable (α : Sort u) [hα : IsCategory V α] [h : HasIsoRel α]

        def isoMorphisms : HasMorphisms V α := ⟨h.Iso⟩

        def toHomMetaFunctor : MetaFunctor h.Iso hα.Hom := MetaFunctor.fromDefFun h.defToHomFun

      end

      section

        variable {α : Sort u} [hα : IsCategory V α] [h : HasIsoRel α]

        @[reducible] def toHom  {a b : α} (e : a ⇿ b) : a ⇾ b := (h.desc e).toHom
        @[reducible] def invHom {a b : α} (e : a ⇿ b) : b ⇾ a := (h.desc e).invHom

        def leftInv  {a b : α} (e : a ⇿ b) : HalfInv hα.Hom (toHom e) (invHom e) :=
        (h.desc e).isInv.leftInv
        def rightInv {a b : α} (e : a ⇿ b) : HalfInv hα.Hom (invHom e) (toHom e) :=
        (h.desc e).isInv.rightInv

        def toHomCongrArg  {a b : α} {e₁ e₂ : a ⇿ b} (he : e₁ ≃ e₂) : toHom  e₁ ≃ toHom  e₂ :=
        defCongrArg (h.defToHomFun a b) he
        def invHomCongrArg {a b : α} {e₁ e₂ : a ⇿ b} (he : e₁ ≃ e₂) : invHom e₁ ≃ invHom e₂ :=
        IsoDesc.toInvEquiv (toHomCongrArg he)

        structure DefIso {a b : α} (desc : IsoDesc a b) where
        (e    : a ⇿ b)
        (toEq : toHom e ≃ desc.toHom)

        def byToDef  {a b : α} {desc : IsoDesc a b} {e : DefIso desc} : toHom  e.e ≃ desc.toHom  :=
        e.toEq
        def byInvDef {a b : α} {desc : IsoDesc a b} {e : DefIso desc} : invHom e.e ≃ desc.invHom :=
        IsoDesc.toInvEquiv e.toEq

      end

      class HasTrivialIsomorphismCondition (α : Sort u) [hα : IsCategory V α] [h : HasIsoRel α] where
      (iso {a b : α} (desc : IsoDesc a b) : DefIso desc)

      namespace HasTrivialIsomorphismCondition

        variable {α : Sort u} [hα : IsCategory V α] [HasIsoRel α]
                 [h : HasTrivialIsomorphismCondition α]

        def defIso {a b : α} {desc : IsoDesc a b} : DefIso desc := h.iso desc

      end HasTrivialIsomorphismCondition

    end HasIsoRel

    class HasIsoOp {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv} V]
                   (α : Sort u) [hα : IsCategory V α] extends
      HasIsoRel α where
    (defRefl (a : α) : HasIsoRel.DefIso (IsoDesc.refl a))
    (defSymm {a b : α} (e : a ⇿ b) : HasIsoRel.DefIso (IsoDesc.symm (desc e)))
    (defTrans {a b c : α} (e : a ⇿ b) (f : b ⇿ c) :
       HasIsoRel.DefIso (IsoDesc.trans (desc e) (desc f)))

    namespace HasIsoOp

      open HasIsoRel

      variable {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv} V]

      section

        variable (α : Sort u) [hα : IsCategory V α]

        instance hasTrivialIsoOp [hIso : HasIsoRel α] [h : HasTrivialIsomorphismCondition α] :
          HasIsoOp α :=
        { defRefl  := λ _   => HasTrivialIsomorphismCondition.defIso,
          defSymm  := λ _   => HasTrivialIsomorphismCondition.defIso,
          defTrans := λ _ _ => HasTrivialIsomorphismCondition.defIso }

        variable [h : HasIsoOp α]

        instance isoIsEquivalence : IsEquivalence h.Iso :=
        { refl  := λ a   => (h.defRefl a).e,
          symm  := λ e   => (h.defSymm e).e,
          trans := λ e f => (h.defTrans e f).e }

        instance toHomIsPreorderFunctor : IsPreorderFunctor (toHomMetaFunctor α) :=
        { reflEq  := λ a   => byToDef • byDef,
          transEq := λ e f => (congrArgTrans hα.Hom byDef byDef)⁻¹ • byToDef • byDef }

      end

      section

        variable {α : Sort u} [hα : IsCategory V α] [h : HasIsoOp α]

        @[reducible] def idIso (a : α) : a ⇿ a := HasRefl.refl a

        def toHomReflEq (a : α) : toHom (idIso a) ≃ idHom a := byToDef
        def toHomSymmEq {a b : α} (e : a ⇿ b) : toHom e⁻¹ ≃ invHom e := byToDef
        def toHomTransEq {a b c : α} (e : a ⇿ b) (f : b ⇿ c) : toHom (f • e) ≃ toHom f • toHom e :=
        byToDef

        def invHomReflEq (a : α) : invHom (idIso a) ≃ idHom a := byInvDef
        def invHomSymmEq {a b : α} (e : a ⇿ b) : invHom e⁻¹ ≃ toHom e := byInvDef
        def invHomTransEq {a b c : α} (e : a ⇿ b) (f : b ⇿ c) : invHom (f • e) ≃ invHom e • invHom f :=
        byInvDef

        def isoAssoc {a b c d : α} (e : a ⇿ b) (f : b ⇿ c) (g : c ⇿ d) :
          (g • f) • e ≃ g • (f • e) :=
        h.toHomInj ((congrArgTransRight hα.Hom (toHomTransEq e f) (toHom g) •
                     toHomTransEq (f • e) g)⁻¹ •
                    assoc (toHom e) (toHom f) (toHom g) •
                    (congrArgTransLeft hα.Hom (toHom e) (toHomTransEq f g) •
                     toHomTransEq e (g • f)))

        def isoRightId {a b : α} (e : a ⇿ b) : e • idIso a ≃ e :=
        h.toHomInj (rightId (toHom e) •
                    (congrArgTransRight hα.Hom (toHomReflEq a) (toHom e) •
                     toHomTransEq (idIso a) e))

        def isoLeftId {a b : α} (e : a ⇿ b) : idIso b • e ≃ e :=
        h.toHomInj (leftId (toHom e) •
                    (congrArgTransLeft hα.Hom (toHom e) (toHomReflEq b) •
                     toHomTransEq e (idIso b)))

        def isoLeftInv {a b : α} (e : a ⇿ b) : e⁻¹ • e ≃ idIso a :=
        h.toHomInj ((toHomReflEq a)⁻¹ •
                    leftInv e •
                    (congrArgTransLeft hα.Hom (toHom e) (toHomSymmEq e) •
                     toHomTransEq e e⁻¹))

        def isoRightInv {a b : α} (e : a ⇿ b) : e • e⁻¹ ≃ idIso b :=
        h.toHomInj ((toHomReflEq b)⁻¹ •
                    rightInv e •
                    (congrArgTransRight hα.Hom (toHomSymmEq e) (toHom e) •
                     toHomTransEq e⁻¹ e))

      end

      section

        variable (α : Sort u) [hα : IsCategory V α] [h : HasIsoOp α]

        instance isoIsGroupoidEquivalence : IsGroupoidEquivalence h.Iso :=
        { assoc    := isoAssoc,
          rightId  := isoRightId,
          leftId   := isoLeftId,
          leftInv  := isoLeftInv,
          rightInv := isoRightInv }

      end

    end HasIsoOp

    class HasIsomorphisms {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv} V]
                          (α : Sort u) [hα : IsCategory V α] extends
      HasIsoOp α where
    [isoHasSymmFun  : HasSymmFun  Iso]
    [isoHasTransFun : HasTransFun Iso]

    namespace HasIsomorphisms

      open HasIsoRel HasIsoOp

      variable {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv} V]

      section

        variable (α : Sort u) [hα : IsCategory V α] [h : HasIsomorphisms α]

        instance : HasSymmFun  h.Iso := h.isoHasSymmFun
        instance : HasTransFun h.Iso := h.isoHasTransFun

        def isoGroupoid : IsGroupoid V α :=
        { toHasMorphisms           := HasIsoRel.isoMorphisms α,
          homIsEquivalence         := HasIsoOp.isoIsEquivalence α,
          homHasSymmFun            := h.isoHasSymmFun,
          homHasTransFun           := h.isoHasTransFun,
          homIsGroupoidEquivalence := isoIsGroupoidEquivalence α }

        def isoCategory : IsCategory V α := IsGroupoid.isCategory (h := isoGroupoid α)

        def isoSemicategory : IsSemicategory V α := IsCategory.isSemicategory (h := isoCategory α)

      end

    end HasIsomorphisms

  end IsCategory



  namespace IsGroupoid

    open HasIsoRel

    variable {V : Universe.{v, vv}} [IsHomUniverse.{v, vv, iv} V] (α : Sort u)
             [hα : IsGroupoid V α]

    def isoDesc {a b : α} (e : a ⇾ b) : IsoDesc a b := ⟨e, e⁻¹⟩

    instance hasIsoRel : HasIsoRel α :=
    { Iso         := hα.Hom,
      desc        := isoDesc α,
      defToHomFun := λ a b => HasIdFun.defIdFun (a ⇾ b),
      toHomInj    := id }

    instance : HasTrivialIsomorphismCondition α :=
    ⟨λ e => { e    := e.toHom,
              toEq := HasInstanceEquivalences.refl e.toHom }⟩

    instance hasIsomorphisms : HasIsomorphisms α :=
    { isoHasSymmFun  := hα.homHasSymmFun,
      isoHasTransFun := hα.homHasTransFun }

  end IsGroupoid



  namespace HasFunProp

    open HasIsomorphisms

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
             (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
             [hαIso : HasIsomorphisms α] [hβIso : HasIsomorphisms β]
             [HasFunProp α β (hα := isoCategory α) (hβ := isoCategory β)]

    def IsoFunctor := HasFunProp.Functor α β (hα := isoCategory α) (hβ := isoCategory β)

    infixr:20 " ⮕⮕ " => CategoryTheory.HasFunProp.IsoFunctor

  end HasFunProp

  class HasIsoPreFun {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                     {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
                     [hαIso : HasIsomorphisms α] [hβIso : HasIsomorphisms β]
                     [hFunProp : HasFunProp α β] (F : α ⮕ β) where
  (defMapIso {a b : α} (e : a ⇿ b) : HasIsoRel.DefIso (IsoDesc.map (morFun F) (hαIso.desc e)))
  (defMapIsoFun (a b : α) : (a ⇿ b) ⟶{λ e => (defMapIso e).e} (F.φ a ⇿ F.φ b))

  namespace HasIsoPreFun

    open HasIsoRel HasIsoOp HasIsomorphisms

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
             {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
             [hαIso : HasIsomorphisms α] [hβIso : HasIsomorphisms β] [HasFunProp α β]
             (F : α ⮕ β) [h : HasIsoPreFun F]

    def mapIso {a b : α} (e : a ⇿ b) : F.φ a ⇿ F.φ b := (h.defMapIso e).e

    @[reducible] def mapIsoFun (a b : α) : (a ⇿ b) ⟶ (F.φ a ⇿ F.φ b) := h.defMapIsoFun a b

    instance {a b : α} (e : a ⇿ b) : IsFunApp (a ⇿ b) (mapIso F e) :=
    { F := mapIsoFun F a b,
      a := e,
      e := byDef }

    def isoPreFun : PreFunctor hαIso.Iso hβIso.Iso F.φ := ⟨mapIsoFun F⟩

    def mapIsoCongrArg {a b : α} {e₁ e₂ : a ⇿ b} (e : e₁ ≃ e₂) : mapIso F e₁ ≃ mapIso F e₂ :=
    HasCongrArg.defCongrArg (h.defMapIsoFun a b) e

    def toHomComm  {a b : α} (e : a ⇿ b) : toHom  (mapIso F e) ≃ mapHom F (toHom  e) := byToDef
    def invHomComm {a b : α} (e : a ⇿ b) : invHom (mapIso F e) ≃ mapHom F (invHom e) := byInvDef

    def isoReflEq (a : α) : mapIso F (idIso a) ≃ idIso (F.φ a) :=
    hβIso.toHomInj ((toHomReflEq (F.φ a))⁻¹ •
                    reflEq F a •
                    (mapHomCongrArg F (toHomReflEq a) •
                     toHomComm F (idIso a)))

    def isoSymmEq {a b : α} (e : a ⇿ b) : mapIso F e⁻¹ ≃ (mapIso F e)⁻¹ :=
    hβIso.toHomInj ((invHomComm F e •
                     toHomSymmEq (mapIso F e))⁻¹ •
                    (mapHomCongrArg F (toHomSymmEq e) •
                     toHomComm F e⁻¹))

    def isoTransEq {a b c : α} (e : a ⇿ b) (f : b ⇿ c) :
      mapIso F (f • e) ≃ mapIso F f • mapIso F e :=
    hβIso.toHomInj ((congrArgTrans hβ.Hom (toHomComm F e) (toHomComm F f) •
                     toHomTransEq (mapIso F e) (mapIso F f))⁻¹ •
                    transEq F (toHom e) (toHom f) •
                    (mapHomCongrArg F (toHomTransEq e f) •
                     toHomComm F (f • e)))

    instance isReflFunctor : IsReflFunctor (isoPreFun F) :=
    ⟨λ a => isoReflEq F a •
            hβIso.toHomInj (toHomCongrArg byDef)⟩

    instance isSymmFunctor : IsSymmFunctor (isoPreFun F) :=
    ⟨λ e => hβIso.toHomInj (toHomCongrArg (congrArgSymm hβIso.Iso byDef))⁻¹ •
            isoSymmEq F e •
            hβIso.toHomInj (toHomCongrArg byDef)⟩

    instance isTransFunctor : IsTransFunctor (isoPreFun F) :=
    ⟨λ e f => hβIso.toHomInj (toHomCongrArg (congrArgTrans hβIso.Iso byDef byDef))⁻¹ •
              isoTransEq F e f •
              hβIso.toHomInj (toHomCongrArg byDef)⟩

    instance isPreorderFunctor    : IsPreorderFunctor    (isoPreFun F) := ⟨⟩
    instance isEquivalenceFunctor : IsEquivalenceFunctor (isoPreFun F) := ⟨⟩

    @[reducible] def isoFun : MorphismFunctor α β (hα := isoMorphisms α) (hβ := isoMorphisms β) :=
    let _ := isoMorphisms α;
    let _ := isoMorphisms β;
    ⟨isoPreFun F⟩

    instance isCategoryFunctor :
      IsCategoryFunctor (hα := isoCategory α) (hβ := isoCategory β) (isoFun F) :=
    IsCategoryFunctor.mk (hα := isoCategory α) (hβ := isoCategory β)
                         (toIsPreorderFunctor := isPreorderFunctor F)

    instance isGroupoidFunctor :
      IsGroupoidFunctor (hα := isoGroupoid α) (hβ := isoGroupoid β) (isoFun F) :=
    let _ := isoGroupoid α;
    let _ := isoGroupoid β;
    { toIsEquivalenceFunctor := isEquivalenceFunctor F }

    def isoFunDesc : FunDesc F.φ (hα := isoCategory α) (hβ := isoCategory β) :=
    FunDesc.mk (hα := isoCategory α) (hβ := isoCategory β) (isoPreFun F)

  end HasIsoPreFun

  class HasIsoFun {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                  {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
                  [hαIso : HasIsomorphisms α] [hβIso : HasIsomorphisms β]
                  [hFunProp : HasFunProp α β]
                  [hIsoFunProp : HasFunProp α β (hα := HasIsomorphisms.isoCategory α)
                                                (hβ := HasIsomorphisms.isoCategory β)]
                  (F : α ⮕ β) extends
    HasIsoPreFun F where
  (defIsoFun : HasFunProp.DefFun (hα := HasIsomorphisms.isoCategory α)
                                 (hβ := HasIsomorphisms.isoCategory β)
                                 (HasIsoPreFun.isoFunDesc F))

  namespace HasIsoFun

    open HasIsomorphisms HasIsoPreFun

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
             {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
             [hαIso : HasIsomorphisms α] [hβIso : HasIsomorphisms β] [HasFunProp α β]
             [HasFunProp α β (hα := isoCategory α) (hβ := isoCategory β)]
             (F : α ⮕ β) [h : HasIsoFun F]

    @[reducible] def isoFunctor : α ⮕⮕ β :=
    DefFun.toFunctor (hα := isoCategory α) (hβ := isoCategory β) h.defIsoFun

    def mapIso' {a b : α} (e : a ⇿ b) : F.φ a ⇿ F.φ b :=
    mapHom (hα := isoCategory α) (hβ := isoCategory β) (isoFunctor F) e

    def mapIsoEq {a b : α} (e : a ⇿ b) :
      mapIso' F e ≃ mapIso F e :=
    DefFun.byMapHomDef (hα := isoCategory α) (hβ := isoCategory β)

  end HasIsoFun

  class HasIsoFunctoriality {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                            (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
                            [hαIso : HasIsomorphisms α] [hβIso : HasIsomorphisms β] where
  [hasFunProp    : HasFunProp α β]
  [hasIsoFunProp : HasFunProp α β (hα := HasIsomorphisms.isoCategory α)
                                  (hβ := HasIsomorphisms.isoCategory β)]
  [hasIsoFun (F : α ⮕ β) : HasIsoFun F]

  namespace HasIsoFunctoriality

    open HasIsoRel HasIsomorphisms HasIsoPreFun

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]

    section

      variable {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
               [hαIso : HasIsomorphisms α] [hβIso : HasIsomorphisms β]
               [h : HasIsoFunctoriality α β]

      instance : HasFunProp α β := h.hasFunProp
      instance : HasFunProp α β (hα := HasIsomorphisms.isoCategory α)
                                (hβ := HasIsomorphisms.isoCategory β) := h.hasIsoFunProp

      instance (F : α ⮕ β) : HasIsoFun F := h.hasIsoFun F

      def mapIso (F : α ⮕ β) {a b : α} (e : a ⇿ b) : F.φ a ⇿ F.φ b := HasIsoPreFun.mapIso F e

      def mapHomToMapIso {φ : α → β} {F G : h.hasFunProp.Fun φ} {a b : α} {e : a ⇿ b} :
        mapHom ⟨F⟩ (toHom e) ≃ mapHom ⟨G⟩ (toHom e) →
        mapIso ⟨F⟩ e         ≃ mapIso ⟨G⟩ e :=
      λ h₁ => hβIso.toHomInj ((toHomComm ⟨G⟩ e)⁻¹ • h₁ • (toHomComm ⟨F⟩ e))

    end

  end HasIsoFunctoriality



  structure NatIsoDesc {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                       {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
                       [hβIso : HasIsomorphisms β] [hFunProp : HasFunProp α β] (F G : α ⮕ β) :
    Sort (max 1 u w iw) where
  -- Note: `isInvNat` is redundant (see `construct`), but we include it anyway because in strict
  -- cases, it contains a much simpler term.
  (η        : MetaQuantification hβIso.Iso F.φ G.φ)
  [isToNat  : IsNaturalTransformation (F := morFun F) (G := morFun G) (λ a => HasIsoRel.toHom  (η a))]
  [isInvNat : IsNaturalTransformation (F := morFun G) (G := morFun F) (λ a => HasIsoRel.invHom (η a))]

  namespace NatIsoDesc

    open HasIsoRel HasIsoOp HasIsomorphisms HasIsoPreFun HasIsoFun

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
             {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
             [hβIso : HasIsomorphisms β] [hFunProp : HasFunProp α β]

    -- It would be nice if we could just use the corresponding code from `Meta.lean` here.
    -- However, we are in the special situation that only terms involving `η` are invertible,
    -- but `mapHom F f` and `mapHom G f` are not. The code in `Meta.lean` currently cannot deal
    -- with this; all operations that involve invertible elements ultimately rely on `HasSymm` for
    -- the entire relation.

    def construct {F G : α ⮕ β} (η : MetaQuantification hβIso.Iso F.φ G.φ)
                  [isToNat : IsNaturalTransformation (F := morFun F) (G := morFun G) (λ a => HasIsoRel.toHom (η a))] :
      NatIsoDesc F G :=
    { η        := η,
      isToNat  := isToNat,
      isInvNat := { nat := λ {a b} f => (cancelLeftId hβ.Hom (mapHom F f • invHom (η a)) (leftInv (η b)) •
                                         (assoc (mapHom F f • invHom (η a)) (toHom (η b)) (invHom (η b)))⁻¹) •
                                        congrArgTransRight hβ.Hom (assoc (invHom (η a)) (mapHom F f) (toHom (η b)))
                                                                  (invHom (η b)) •
                                        assoc (invHom (η a)) (toHom (η b) • mapHom F f) (invHom (η b)) •
                                        congrArgTransLeft hβ.Hom (invHom (η a))
                                                                 (congrArgTransRight hβ.Hom (isToNat.nat f)⁻¹
                                                                                            (invHom (η b)) •
                                                                  assoc (toHom (η a)) (mapHom G f) (invHom (η b))) •
                                        (cancelRightId hβ.Hom (rightInv (η a)) (invHom (η b) • mapHom G f) •
                                         assoc (invHom (η a)) (toHom (η a)) (invHom (η b) • mapHom G f))⁻¹ } }

    def strict {φ : α → β} {F G : hFunProp.Fun φ} (hEq : NatDesc.StrictNaturality F G) :
      NatIsoDesc ⟨F⟩ ⟨G⟩ :=
    { η        := λ a => idIso (φ a),
      isToNat  := { nat := λ {a b} f => (cancelRightId hβ.Hom (toHomReflEq (φ a)) (mapHom ⟨G⟩ f))⁻¹ •
                                        hEq f •
                                        cancelLeftId hβ.Hom (mapHom ⟨F⟩ f) (toHomReflEq (φ b)) }
      isInvNat := { nat := λ {a b} f => (cancelRightId hβ.Hom (invHomReflEq (φ a)) (mapHom ⟨F⟩ f))⁻¹ •
                                        (hEq f)⁻¹ •
                                        cancelLeftId hβ.Hom (mapHom ⟨G⟩ f) (invHomReflEq (φ b)) }, }

    def refl (F : α ⮕ β) : NatIsoDesc F F :=
    { η        := MetaQuantification.refl hβIso.Iso F.φ,
      isToNat  := { nat := λ {a b} f => (cancelRightId hβ.Hom (toHomReflEq (F.φ a)) (mapHom F f))⁻¹ •
                                        cancelLeftId hβ.Hom (mapHom F f) (toHomReflEq (F.φ b)) },
      isInvNat := { nat := λ {a b} f => (cancelRightId hβ.Hom (invHomReflEq (F.φ a)) (mapHom F f))⁻¹ •
                                        cancelLeftId hβ.Hom (mapHom F f) (invHomReflEq (F.φ b)) } }

    def symm {F G : α ⮕ β} (η : NatIsoDesc F G) : NatIsoDesc G F :=
    { η        := MetaQuantification.symm hβIso.Iso η.η,
      isToNat  := { nat := λ {a b} f => (congrArgTransRight hβ.Hom (toHomSymmEq (η.η a)) (mapHom F f))⁻¹ •
                                        η.isInvNat.nat f •
                                        congrArgTransLeft hβ.Hom (mapHom G f) (toHomSymmEq (η.η b)) },
      isInvNat := { nat := λ {a b} f => (congrArgTransRight hβ.Hom (invHomSymmEq (η.η a)) (mapHom G f))⁻¹ •
                                        η.isToNat.nat f •
                                        congrArgTransLeft hβ.Hom (mapHom F f) (invHomSymmEq (η.η b)) } }

    def trans {F G H : α ⮕ β} (η : NatIsoDesc F G) (ε : NatIsoDesc G H) : NatIsoDesc F H :=
    { η        := MetaQuantification.trans hβIso.Iso η.η ε.η,
      isToNat  := { nat := λ {a b} f => (congrArgTransRight hβ.Hom (toHomTransEq (η.η a) (ε.η a)) (mapHom H f))⁻¹ •
                                        (IsNaturalTransformation.trans _ _ (hη := η.isToNat) (hε := ε.isToNat)).nat f •
                                        congrArgTransLeft hβ.Hom (mapHom F f) (toHomTransEq (η.η b) (ε.η b)) },
      isInvNat := { nat := λ {a b} f => (congrArgTransRight hβ.Hom (invHomTransEq (η.η a) (ε.η a)) (mapHom F f))⁻¹ •
                                        (IsNaturalTransformation.trans _ _ (hη := ε.isInvNat) (hε := η.isInvNat)).nat f •
                                        congrArgTransLeft hβ.Hom (mapHom H f) (invHomTransEq (η.η b) (ε.η b)) } }

    variable {F G : α ⮕ β} (η : NatIsoDesc F G)

    @[reducible] def natIso    (a : α) : F.φ a ⇿ G.φ a := η.η a
    @[reducible] def natToHom  (a : α) : F.φ a ⇾ G.φ a := toHom  (natIso η a)
    @[reducible] def natInvHom (a : α) : G.φ a ⇾ F.φ a := invHom (natIso η a)

    def toNatDesc : NatDesc F G :=
    { η     := natToHom η,
      isNat := η.isToNat }

    def invNatDesc : NatDesc G F :=
    { η     := natInvHom η,
      isNat := η.isInvNat }

    structure IsoDescBuilder [hNat : HasNaturality α β] where
    (defToNat  : DefNat (toNatDesc  η))
    (defInvNat : DefNat (invNatDesc η))
    (leftInv   : NatEquiv (defInvNat.η • defToNat.η) (HasRefl.refl F)
                          (λ a => (natReflEq F a)⁻¹ •
                                  leftInv (η.η a) •
                                  congrArgTrans hβ.Hom byNatDef byNatDef •
                                  natTransEq defToNat.η defInvNat.η a))
    (rightInv  : NatEquiv (defToNat.η • defInvNat.η) (HasRefl.refl G)
                          (λ b => (natReflEq G b)⁻¹ •
                                  rightInv (η.η b) •
                                  congrArgTrans hβ.Hom byNatDef byNatDef •
                                  natTransEq defInvNat.η defToNat.η b))

    namespace IsoDescBuilder

      variable [hNat : HasNaturality α β] (e : IsoDescBuilder η)

      instance isInv : IsInv (funHasMorphisms α β).Hom e.defToNat.η e.defInvNat.η :=
      { leftInv  := e.leftInv,
        rightInv := e.rightInv }
  
      def isoDesc : IsoDesc F G := ⟨e.defToNat.η, e.defInvNat.η⟩

    end IsoDescBuilder

    section

      variable [hαIso : HasIsomorphisms α]
               [HasFunProp α β (hα := HasIsomorphisms.isoCategory α) (hβ := HasIsomorphisms.isoCategory β)]
               [HasIsoFun F] [HasIsoFun G]

      def isoNaturality {a b : α} (e : a ⇿ b) :
        natIso η b • mapIso F e ≃ mapIso G e • natIso η a :=
      hβIso.toHomInj ((congrArgTransLeft hβ.Hom (natToHom η a) (toHomComm G e) •
                      toHomTransEq (natIso η a) (mapIso G e))⁻¹ •
                     η.isToNat.nat (toHom e) •
                     (congrArgTransRight hβ.Hom (toHomComm F e) (natToHom η b) •
                      toHomTransEq (mapIso F e) (natIso η b)))

      def toIsoNatDesc : NatDesc (hα := isoCategory α) (hβ := isoCategory β) (isoFunctor F) (isoFunctor G) :=
      NatDesc.mk (hα := isoCategory α) (hβ := isoCategory β)
                η.η
                (isNat := IsNaturalTransformation.mk (hα := isoMorphisms α) (hβ := isoSemicategory β)
                                                      (toIsNatural := IsNatural.mk (λ {a b : α} (e : a ⇿ b) =>
                                                                                    congrArgTransLeft hβIso.Iso (natIso η a) (mapIsoEq G e)⁻¹ •
                                                                                    isoNaturality η e •
                                                                                    congrArgTransRight hβIso.Iso (mapIsoEq F e) (natIso η b))))

    end

  end NatIsoDesc

  namespace HasNaturality

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
             {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
             [HasFunProp α β] [h : HasNaturality α β] {F G : α ⮕ β}

    def natHalfInv {η : F ⇾ G} {ε : G ⇾ F} (e : HalfInv h.Nat η ε) (a : α) :
      HalfInv hβ.Hom (nat η a) (nat ε a) :=
    natReflEq F a • natCongrArg e a • (natTransEq η ε a)⁻¹

    instance natIsInv (η : F ⇾ G) (ε : G ⇾ F) [isInv : IsInv h.Nat η ε] (a : α) :
      IsInv hβ.Hom (nat η a) (nat ε a) :=
    { leftInv  := natHalfInv isInv.leftInv  a,
      rightInv := natHalfInv isInv.rightInv a }

    def natIsoDesc (η : IsoDesc F G) (a : α) : IsoDesc (F.φ a) (G.φ a) :=
    { toHom  := nat η.toHom  a,
      invHom := nat η.invHom a,
      isInv  := natIsInv η.toHom η.invHom (isInv := η.isInv) a }

  end HasNaturality

  class HasIsoNat {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                  {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
                  [hFunProp : HasFunProp α β] [hNat : HasNaturality α β]
                  [hβIso : HasIsomorphisms β] [hαβIso : HasIsomorphisms (α ⮕ β)]
                  (F G : α ⮕ β) where
  (defNatIso (η : F ⇿ G) (a : α) :
     HasIsoRel.DefIso (natIsoDesc (hαβIso.desc η) a))
  (defNatIsoFun (a : α) :
     (F ⇿ G) ⟶{λ η => (defNatIso η a).e} (F.φ a ⇿ G.φ a))

  namespace HasIsoNat

    open HasIsoRel HasIsoOp HasIsoPreFun

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
             {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]

    section

      variable [hβIso : HasIsomorphisms β] [HasFunProp α β] [HasNaturality α β]
               [HasIsomorphisms (α ⮕ β)]

      def natIso {F G : α ⮕ β} [h : HasIsoNat F G] (η : F ⇿ G) (a : α) : F.φ a ⇿ G.φ a :=
      (h.defNatIso η a).e

      @[reducible] def natIsoFun (F G : α ⮕ β) [h : HasIsoNat F G] (a : α) :
        (F ⇿ G) ⟶ (F.φ a ⇿ G.φ a) :=
      h.defNatIsoFun a

      variable {F G : α ⮕ β} [h : HasIsoNat F G]

      instance (η : F ⇿ G) (a : α) : IsFunApp (F ⇿ G) (natIso η a) :=
      { F := natIsoFun F G a,
        a := η,
        e := byDef }

      def natIsoCongrArg {η₁ η₂ : F ⇿ G} (e : η₁ ≃ η₂) (a : α) :
        natIso η₁ a ≃ natIso η₂ a :=
      defCongrArg (h.defNatIsoFun a) e

      def natIsoToHomComm (η : F ⇿ G) (a : α) :
        toHom (natIso η a) ≃ nat (toHom η) a :=
      byToDef

      def natIsoInvHomComm (η : F ⇿ G) (a : α) :
        invHom (natIso η a) ≃ nat (invHom η) a :=
      byInvDef

      def natIsoEq {η₁ η₂ : F ⇿ G} {a : α} :
        nat (toHom η₁) a ≃ nat (toHom η₂) a → natIso η₁ a ≃ natIso η₂ a :=
      λ e => hβIso.toHomInj ((natIsoToHomComm η₂ a)⁻¹ • e • natIsoToHomComm η₁ a)

    end

    section

      variable [hαIso : HasIsomorphisms α] [hβIso : HasIsomorphisms β] [hIsoFun : HasIsoFunctoriality α β]
               [HasNaturality α β] [HasIsomorphisms (α ⮕ β)]

      section

        variable {F G : α ⮕ β} [h : HasIsoNat F G]

        def natIsoDesc (η : F ⇿ G) : NatIsoDesc F G :=
        { η        := natIso η,
          isToNat  := { nat := λ {a b} f => congrArgTransRight hβ.Hom (natIsoToHomComm η a)⁻¹ (mapHom G f) •
                                            naturality (toHom η) f •
                                            congrArgTransLeft hβ.Hom (mapHom F f) (natIsoToHomComm η b) },
          isInvNat := { nat := λ {a b} f => congrArgTransRight hβ.Hom (natIsoInvHomComm η a)⁻¹ (mapHom F f) •
                                            naturality (invHom η) f •
                                            congrArgTransLeft hβ.Hom (mapHom G f) (natIsoInvHomComm η b) } }

        def isoNaturality (η : F ⇿ G) {a b : α} (e : a ⇿ b) :
          natIso η b • mapIso F e ≃ mapIso G e • natIso η a :=
        NatIsoDesc.isoNaturality (natIsoDesc η) e

        structure DefNatIso (desc : NatIsoDesc F G) where
        (η             : F ⇿ G)
        (natEq (a : α) : natIso η a ≃ NatIsoDesc.natIso desc a)

        def byNatIsoDef {desc : NatIsoDesc F G} {η : DefNatIso desc} {a : α} :
          natIso η.η a ≃ NatIsoDesc.natIso desc a :=
        η.natEq a

        def byNatIsoToHomDef {desc : NatIsoDesc F G} {η : DefNatIso desc} {a : α} :
          nat (toHom η.η) a ≃ NatIsoDesc.natToHom desc a :=
        toHomCongrArg byNatIsoDef • (natIsoToHomComm η.η a)⁻¹

        def byNatIsoInvHomDef {desc : NatIsoDesc F G} {η : DefNatIso desc} {a : α} :
          nat (invHom η.η) a ≃ NatIsoDesc.natInvHom desc a :=
        invHomCongrArg byNatIsoDef • (natIsoInvHomComm η.η a)⁻¹

      end

      def byStrictNatIsoDef {φ : α → β} {F G : hIsoFun.hasFunProp.Fun φ} [h : HasIsoNat ⟨F⟩ ⟨G⟩]
                            {hEq : NatDesc.StrictNaturality F G}
                            {η : DefNatIso (NatIsoDesc.strict hEq)} {a : α} :
        natIso η.η a ≃ idIso (φ a) :=
      byNatIsoDef

      def byStrictNatIsoToHomDef {φ : α → β} {F G : hIsoFun.hasFunProp.Fun φ} [h : HasIsoNat ⟨F⟩ ⟨G⟩]
                                 {hEq : NatDesc.StrictNaturality F G}
                                 {η : DefNatIso (NatIsoDesc.strict hEq)} {a : α} :
        nat (toHom η.η) a ≃ idHom (φ a) :=
      toHomReflEq (φ a) • byNatIsoToHomDef

      def byStrictNatIsoInvHomDef {φ : α → β} {F G : hIsoFun.hasFunProp.Fun φ} [h : HasIsoNat ⟨F⟩ ⟨G⟩]
                                  {hEq : NatDesc.StrictNaturality F G}
                                  {η : DefNatIso (NatIsoDesc.strict hEq)} {a : α} :
        nat (invHom η.η) a ≃ idHom (φ a) :=
      invHomReflEq (φ a) • byNatIsoInvHomDef

    end

  end HasIsoNat

  class HasIsoNaturality {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                         (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
                         [hβIso : HasIsomorphisms β] [hFunProp : HasFunProp α β] where
  [hasNat    : HasNaturality α β]
  [hasNatIso : HasIsomorphisms (α ⮕ β)]
  [hasIsoNat (F G : α ⮕ β) : HasIsoNat F G]

  namespace HasIsoNaturality

    open HasIsoRel HasIsoOp HasIsomorphisms HasIsoPreFun HasIsoNat

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]

    section

      variable (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
               [hβIso : HasIsomorphisms β] [HasFunProp α β] [h : HasIsoNaturality α β]

      instance : HasNaturality α β       := h.hasNat
      instance : HasIsomorphisms (α ⮕ β) := h.hasNatIso

    end

    section

      variable {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
               [hβIso : HasIsomorphisms β] [HasFunProp α β] [h : HasIsoNaturality α β]

      instance (F G : α ⮕ β) : HasIsoNat F G := h.hasIsoNat F G

      def natIsoReflEq (F : α ⮕ β) (a : α) : natIso (idIso F) a ≃ idIso (F.φ a) :=
      hβIso.toHomInj ((toHomReflEq (F.φ a))⁻¹ •
                      natReflEq F a •
                      (natCongrArg (toHomReflEq F) a •
                       natIsoToHomComm (idIso F) a))

      def natIsoSymmEq {F G : α ⮕ β} (η : F ⇿ G) (a : α) : natIso η⁻¹ a ≃ (natIso η a)⁻¹ :=
      hβIso.toHomInj ((natIsoInvHomComm η a •
                       toHomSymmEq (natIso η a))⁻¹ •
                      (natCongrArg (toHomSymmEq η) a •
                       natIsoToHomComm η⁻¹ a))

      def natIsoTransEq {F G H : α ⮕ β} (η : F ⇿ G) (ε : G ⇿ H) (a : α) :
        natIso (ε • η) a ≃ natIso ε a • natIso η a :=
      hβIso.toHomInj ((congrArgTrans hβ.Hom (natIsoToHomComm η a) (natIsoToHomComm ε a) •
                       toHomTransEq (natIso η a) (natIso ε a))⁻¹ •
                      natTransEq (toHom η) (toHom ε) a •
                      (natCongrArg (toHomTransEq η ε) a •
                       natIsoToHomComm (ε • η) a))

    end

    class HasTrivialNaturalityCondition (α : Sort u) (β : Sort v)
                                        [hα : IsCategory W α] [hβ : IsCategory W β]
                                        [hαIso : HasIsomorphisms α] [hβIso : HasIsomorphisms β]
                                        [hIsoFun : HasIsoFunctoriality α β]
                                        [h : HasIsoNaturality α β] where
    (natIso {F G : α ⮕ β} (desc : NatIsoDesc F G) : DefNatIso desc)

    namespace HasTrivialNaturalityCondition

      variable {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
               [HasIsomorphisms α] [HasIsomorphisms β] [HasIsoFunctoriality α β]
               [HasIsoNaturality α β] [h : HasTrivialNaturalityCondition α β]

      def defNatIso {F G : α ⮕ β} {desc : NatIsoDesc F G} : DefNatIso desc := h.natIso desc

    end HasTrivialNaturalityCondition

    section

      variable {α : Sort u} {β : Sort u'} {γ : Sort u''}
               [hα : IsCategory W α] [hβ : IsCategory W β] [hγ : IsCategory W γ]
               [hαIso : HasIsomorphisms α] [hβIso : HasIsomorphisms β] [hγIso : HasIsomorphisms γ]
               [hIsoFunβγ : HasIsoFunctoriality β γ] [hIsoNatβγ : HasIsoNaturality β γ]
               [hIsoFunαβγ : HasIsoFunctoriality α (β ⮕ γ)]

      structure NatNatIsoDesc (F G : α ⮕ β ⮕ γ) (η : ∀ a, F.φ a ⇿ G.φ a) where
      (toDesc  : NatNatDesc F G (λ a => toHom  (η a)))
      (invDesc : NatNatDesc G F (λ a => invHom (η a)))

      namespace NatNatIsoDesc

        def strict {φ : α → β → γ} {F' G' : ∀ a, hIsoFunβγ.hasFunProp.Fun (φ a)}
                   {hEq : ∀ a, NatDesc.StrictNaturality (F' a) (G' a)}
                   {η : ∀ a, DefNatIso (NatIsoDesc.strict (hEq a))}
                   {F : hIsoFunαβγ.hasFunProp.Fun (λ a => ⟨F' a⟩)}
                   {G : hIsoFunαβγ.hasFunProp.Fun (λ a => ⟨G' a⟩)}
                   (hNatEq : NatNatDesc.StrictNaturality₂ F G) :
          NatNatIsoDesc ⟨F⟩ ⟨G⟩ (λ a => (η a).η) :=
        { toDesc  := { natEq := λ {a₁ a₂} f b => (cancelRightId hγ.Hom (byStrictNatIsoToHomDef (hEq := hEq a₁))
                                                                       (nat (mapHom ⟨G⟩ f) b))⁻¹ •
                                                 hNatEq f b •
                                                 cancelLeftId hγ.Hom (nat (mapHom ⟨F⟩ f) b)
                                                                     (byStrictNatIsoToHomDef (hEq := hEq a₂)) },
          invDesc := { natEq := λ {a₁ a₂} f b => (cancelRightId hγ.Hom (byStrictNatIsoInvHomDef (hEq := hEq a₁))
                                                                       (nat (mapHom ⟨F⟩ f) b))⁻¹ •
                                                 (hNatEq f b)⁻¹ •
                                                 cancelLeftId hγ.Hom (nat (mapHom ⟨G⟩ f) b)
                                                                     (byStrictNatIsoInvHomDef (hEq := hEq a₂)) } }

        def strict' {φ : α → β → γ} {F' G' : ∀ a, hIsoFunβγ.hasFunProp.Fun (φ a)}
                    {hEq : ∀ a, NatDesc.StrictNaturality (F' a) (G' a)}
                    {η : ∀ a, DefNatIso (NatIsoDesc.strict (hEq a))}
                    {F : hIsoFunαβγ.hasFunProp.Fun (λ a => ⟨F' a⟩)}
                    {G : hIsoFunαβγ.hasFunProp.Fun (λ a => ⟨G' a⟩)}
                    (hNatEq : NatNatDesc.StrictNaturality₂' F G) :
          NatNatIsoDesc ⟨F⟩ ⟨G⟩ (λ a => (η a).η) :=
        strict (NatNatDesc.StrictNaturality₂.split hNatEq)

      end NatNatIsoDesc

      variable {F G : α ⮕ β ⮕ γ} {η : ∀ a, F.φ a ⇿ G.φ a}

      structure DefNatNatIsoBase (desc : NatNatIsoDesc F G η) where
      (toDef  : DefNatNatBase desc.toDesc)
      (invDef : DefNatNatBase desc.invDesc)

      namespace DefNatNatIsoBase

        variable {desc : NatNatIsoDesc F G η} (ε : DefNatNatIsoBase desc)

        def natIsoDesc : NatIsoDesc F G :=
        { η        := η,
          isToNat  := { nat := ε.toDef.natEquiv },
          isInvNat := { nat := ε.invDef.natEquiv } }

      end DefNatNatIsoBase

      structure DefNatNatIso [hIsoNatαβγ : HasIsoNaturality α (β ⮕ γ)]
                             (desc : NatNatIsoDesc F G η) extends
        DefNatNatIsoBase desc where
      (defNatNatIso : DefNatIso (DefNatNatIsoBase.natIsoDesc toDefNatNatIsoBase))

    end

    section

      variable {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
               [HasIsomorphisms α] [HasIsomorphisms β] [HasFunProp α α]
               [HasIsoFunctoriality α β] [HasIdFun α] [HasCompFun α α β]

      def rightIdNatDesc (F : α ⮕ β) : NatIsoDesc (F ⭗ HasFunProp.HasIdFun.idFun α) F :=
      NatIsoDesc.strict (λ _ => mapHomCongrArg F DefFun.byMapHomDef • DefFun.byMapHomDef)

    end

    class HasRightIdNat (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
                        [HasIsomorphisms α] [HasIsomorphisms β] [HasFunProp α α]
                        [HasIsoFunctoriality α β] [HasIsoNaturality α β] [HasIdFun α]
                        [HasCompFun α α β] where
    (defRightIdNat (F : α ⮕ β) : DefNatIso (rightIdNatDesc F))

    namespace HasRightIdNat

      variable (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
               [HasIsomorphisms α] [HasIsomorphisms β] [HasFunProp α α]
               [HasIsoFunctoriality α β] [HasIsoNaturality α β]
               [HasIsoFunctoriality (α ⮕ β) (α ⮕ β)] [HasIdFun α] [HasCompFun α α β]
               [HasCompFunFun α α β] [HasIdFun (α ⮕ β)] [h : HasRightIdNat α β]

      def rightIdNatNatDesc :
        NatNatIsoDesc (HasNaturality.HasCompFunFun.compFunFun α α β (HasFunProp.HasIdFun.idFun α))
                      (HasFunProp.HasIdFun.idFun (α ⮕ β))
                      (λ F => (h.defRightIdNat F).η) :=
      NatNatIsoDesc.strict' (λ η a => { g  := nat η a,
                                        e₁ := DefFunFun.byFunFunDef,
                                        e₂ := natCongrArg DefFun.byMapHomDef a })

    end HasRightIdNat

    class HasRightIdNatNat (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
                           [HasIsomorphisms α] [HasIsomorphisms β] [HasFunProp α α]
                           [HasIsoFunctoriality α β] [HasIsoNaturality α β]
                           [HasIsoFunctoriality (α ⮕ β) (α ⮕ β)] [HasIsoNaturality (α ⮕ β) (α ⮕ β)]
                           [HasIdFun α] [HasCompFun α α β] [HasCompFunFun α α β] [HasIdFun (α ⮕ β)]
                           extends
      HasRightIdNat α β where
    (defRightIdNatNat : DefNatNatIso (HasRightIdNat.rightIdNatNatDesc α β))

    section

      variable {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
               [HasIsomorphisms α] [HasIsomorphisms β] [HasIsoFunctoriality α β]
               [HasFunProp β β] [HasCompFun α β β] [HasIdFun β]

      def leftIdNatDesc (F : α ⮕ β) : NatIsoDesc (HasFunProp.HasIdFun.idFun β ⭗ F) F :=
      NatIsoDesc.strict (λ _ => DefFun.byMapHomDef • DefFun.byMapHomDef)

    end

    class HasLeftIdNat (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
                       [HasIsomorphisms α] [HasIsomorphisms β] [HasIsoFunctoriality α β]
                       [HasFunProp β β] [HasIsoNaturality α β] [HasCompFun α β β] [HasIdFun β] where
    (defLeftIdNat (F : α ⮕ β) : DefNatIso (leftIdNatDesc F))

    section

      variable {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
               [HasIsomorphisms α] [HasIsomorphisms β] [HasIsoFunctoriality α β] [HasNaturality α β]
               [HasFunProp (α ⮕ β) β] [HasNaturality (α ⮕ β) β] [HasFunProp α ((α ⮕ β) ⮕ β)]
               [HasFunProp ((α ⮕ β) ⮕ β) β] [HasRevAppFunFun α β] [HasRevAppFun (α ⮕ β) β]
               [HasCompFun α ((α ⮕ β) ⮕ β) β]

      def swapRevAppNatDesc (F : α ⮕ β) :
        NatIsoDesc (HasNaturality.swapFun α (α ⮕ β) β (HasRevAppFunFun.revAppFunFun α β) F) F :=
      NatIsoDesc.strict (λ _ => byNatDef •
                                DefFun.byMapHomDef •
                                mapHomCongrArg (HasNaturality.HasRevAppFun.revAppFun (α ⮕ β) β F)
                                               DefFun.byMapHomDef •
                                DefFun.byMapHomDef)

    end

    class HasSwapRevAppNat (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
                           [HasIsomorphisms α] [HasIsomorphisms β] [HasIsoFunctoriality α β]
                           [HasIsoNaturality α β] [HasFunProp (α ⮕ β) β] [HasNaturality (α ⮕ β) β]
                           [HasFunProp α ((α ⮕ β) ⮕ β)] [HasFunProp ((α ⮕ β) ⮕ β) β]
                           [HasRevAppFunFun α β] [HasRevAppFun (α ⮕ β) β]
                           [HasCompFun α ((α ⮕ β) ⮕ β) β] where
    (defSwapRevAppNat (F : α ⮕ β) : DefNatIso (swapRevAppNatDesc F))

    section

      variable {α : Sort u} {β : Sort u'} {γ : Sort u''} {δ : Sort u'''}
               [hα : IsCategory W α] [hβ : IsCategory W β] [hγ : IsCategory W γ] [hδ : IsCategory W δ]
               [HasIsomorphisms α] [HasIsomorphisms δ] [HasIsoFunctoriality α δ]
               [HasFunProp α β] [HasFunProp α γ] [HasFunProp β γ] [HasFunProp β δ] [HasFunProp γ δ]
               [HasFunProp.HasCompFun α β γ] [HasFunProp.HasCompFun α β δ]
               [HasFunProp.HasCompFun α γ δ] [HasFunProp.HasCompFun β γ δ]

      def compAssocNatDesc (F : α ⮕ β) (G : β ⮕ γ) (H : γ ⮕ δ) :
        NatIsoDesc ((H ⭗ G) ⭗ F) (H ⭗ (G ⭗ F)) :=
      NatIsoDesc.strict (λ _ => (congrArg _ DefFun.byMapHomDef • DefFun.byMapHomDef)⁻¹ •
                                DefFun.byMapHomDef • DefFun.byMapHomDef)

    end

    class HasCompAssocNat (α : Sort u) (β : Sort u') (γ : Sort u'') (δ : Sort u''')
                          [hα : IsCategory W α] [hβ : IsCategory W β] [hγ : IsCategory W γ]
                          [hδ : IsCategory W δ] [HasIsomorphisms α] [HasIsomorphisms δ]
                          [HasIsoFunctoriality α δ] [HasIsoNaturality α δ] [HasFunProp α β]
                          [HasFunProp α γ] [HasFunProp β γ] [HasFunProp β δ] [HasFunProp γ δ]
                          [HasFunProp.HasCompFun α β γ] [HasFunProp.HasCompFun α β δ]
                          [HasFunProp.HasCompFun α γ δ] [HasFunProp.HasCompFun β γ δ] where
    (defCompAssocNat (F : α ⮕ β) (G : β ⮕ γ) (H : γ ⮕ δ) : DefNatIso (compAssocNatDesc F G H))

  end HasIsoNaturality



  class IsIsoUniverse (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw} W]
                      [hFunUniv : IsFunUniverse.{u} W] [hNatUniv : IsNatUniverse.{u} W] where
  [hasIso (α : Sort (max 1 u w)) [hα : IsCategory W α] : HasIsomorphisms α]
  [hasIsoFun {α β : Sort (max 1 u w)} [hα : IsCategory W α] [hβ : IsCategory W β]
     (F : α ⮕ β) : HasIsoFun F (hIsoFunProp := hFunUniv.hasFun α β
                                  (hα := HasIsomorphisms.isoCategory α) (hβ := HasIsomorphisms.isoCategory β))]
  [hasIsoNat {α β : Sort (max 1 u w)} [hα : IsCategory W α] [hβ : IsCategory W β]
     (F G : α ⮕ β) : HasIsoNat F G]

  namespace IsIsoUniverse

    section

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
               [IsFunUniverse.{u} W] [IsNatUniverse.{u} W] [h : IsIsoUniverse.{u} W]

      instance (α : Sort (max 1 u w)) [IsCategory W α] : HasIsomorphisms α := h.hasIso α

      instance hasIsoFunctoriality (α β : Sort (max 1 u w)) [IsCategory W α] [IsCategory W β] :
        HasIsoFunctoriality α β :=
      { hasIsoFun := h.hasIsoFun }

      instance hasIsoNaturality (α β : Sort (max 1 u w)) [IsCategory W α] [IsCategory W β] :
        HasIsoNaturality α β :=
      { hasIsoNat := h.hasIsoNat }

    end

    class HasLinearNaturalIsomorphisms (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw} W]
                                       [hFunUniv : IsFunUniverse.{u} W]
                                       [hLinFun : IsFunUniverse.HasLinearFunctors W]
                                       [hNatUniv : IsNatUniverse.{u} W]
                                       [hNatLinFun : IsNatUniverse.HasLinearFunctors W]
                                       [hIsoUniv : IsIsoUniverse.{u} W] where
    [hasRightIdNatNat (α β : Sort max 1 u w) [hα : IsCategory W α] [hβ : IsCategory W β] :
       HasIsoNaturality.HasRightIdNatNat α β]
    [hasLeftIdNat (α β : Sort max 1 u w) [hα : IsCategory W α] [hβ : IsCategory W β] :
       HasIsoNaturality.HasLeftIdNat α β]
    [hasSwapRevAppNat (α β : Sort max 1 u w) [hα : IsCategory W α] [hβ : IsCategory W β] :
       HasIsoNaturality.HasSwapRevAppNat α β]
    [hasCompAssocNat (α β γ δ : Sort max 1 u w) [hα : IsCategory W α] [hβ : IsCategory W β]
                     [hγ : IsCategory W γ] [hδ : IsCategory W δ] :
       HasIsoNaturality.HasCompAssocNat α β γ δ]

    class HasAffineNaturalIsomorphisms (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw} W]
                                       [HasSubLinearFunOp W]
                                       [hFunUniv : IsFunUniverse.{u} W]
                                       [hLinFun : IsFunUniverse.HasAffineFunctors W]
                                       [hNatUniv : IsNatUniverse.{u} W]
                                       [hNatLinFun : IsNatUniverse.HasAffineFunctors W]
                                       [hIsoUniv : IsIsoUniverse.{u} W] extends
      HasLinearNaturalIsomorphisms W

    class HasFullNaturalIsomorphisms (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw} W]
                                     [HasSubLinearFunOp W] [HasNonLinearFunOp W]
                                     [hFunUniv : IsFunUniverse.{u} W]
                                     [hLinFun : IsFunUniverse.HasAffineFunctors W]
                                     [hNatUniv : IsNatUniverse.{u} W]
                                     [hNatLinFun : IsNatUniverse.HasFullFunctors W]
                                     [hIsoUniv : IsIsoUniverse.{u} W] extends
      HasAffineNaturalIsomorphisms W

  end IsIsoUniverse

end CategoryTheory
