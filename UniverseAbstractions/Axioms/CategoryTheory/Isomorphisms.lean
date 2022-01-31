import UniverseAbstractions.Axioms.CategoryTheory.Extended



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u u' v vv w ww iv iw



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

        def isoLeftInv  {a b : α} (e : a ⇿ b) : e⁻¹ • e ≃ idIso a :=
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
    DefFun.byMapHomDef (hα := isoCategory α) (hβ := isoCategory β) byDef

  end HasIsoFun

  class HasIsoFunctoriality {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                            (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
                            [hαIso : HasIsomorphisms α] [hβIso : HasIsomorphisms β]
                            [hFunProp : HasFunProp α β]
                            [hIsoFunProp : HasFunProp α β (hα := HasIsomorphisms.isoCategory α)
                                                          (hβ := HasIsomorphisms.isoCategory β)]
                            where
  [hasIsoFun (F : α ⮕ β) : HasIsoFun F]

  namespace HasIsoFunctoriality

    open HasIsoRel HasIsomorphisms HasIsoPreFun

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]

    section

      variable {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
               [hαIso : HasIsomorphisms α] [hβIso : HasIsomorphisms β] [hFunProp : HasFunProp α β]
               [HasFunProp α β (hα := isoCategory α) (hβ := isoCategory β)]
               [h : HasIsoFunctoriality α β]

      instance (F : α ⮕ β) : HasIsoFun F := h.hasIsoFun F

      def mapIso (F : α ⮕ β) {a b : α} (e : a ⇿ b) : F.φ a ⇿ F.φ b := HasIsoPreFun.mapIso F e

      def mapHomToMapIso {φ : α → β} {F G : hFunProp.Fun φ} {a b : α} {e : a ⇿ b} :
        mapHom ⟨F⟩ (toHom e) ≃ mapHom ⟨G⟩ (toHom e) →
        mapIso ⟨F⟩ e         ≃ mapIso ⟨G⟩ e :=
      λ h₁ => hβIso.toHomInj ((toHomComm ⟨G⟩ e)⁻¹ • h₁ • (toHomComm ⟨F⟩ e))

    end

  end HasIsoFunctoriality



  structure NatIsoDesc {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                       {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
                       [hαIso : HasIsomorphisms α] [hβIso : HasIsomorphisms β]
                       [hFunProp : HasFunProp α β]
                       [hIsoFunProp : HasFunProp α β (hα := HasIsomorphisms.isoCategory α)
                                                     (hβ := HasIsomorphisms.isoCategory β)]
                       [hIsoFun : HasIsoFunctoriality α β] (F G : α ⮕ β) :
    Sort (max 1 u w iw) where
  (η     : Quantification (hα := HasIsoRel.isoMorphisms α)
                          (hβ := HasIsomorphisms.isoSemicategory β)
                          (HasIsoPreFun.isoFun F) (HasIsoPreFun.isoFun G))
  [isNat : IsNaturalTransformation (F := morFun F) (G := morFun G) (λ a => HasIsoRel.toHom (η a))]

  namespace NatIsoDesc

    open HasIsoRel HasIsoOp HasIsomorphisms HasIsoPreFun HasIsoFun

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
             {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
             [hαIso : HasIsomorphisms α] [hβIso : HasIsomorphisms β] [hFunProp : HasFunProp α β]
             [HasFunProp α β (hα := isoCategory α) (hβ := isoCategory β)]
             [hIsoFun : HasIsoFunctoriality α β]

    def strict {φ : α → β} (F G : hFunProp.Fun φ)
               (hEq : ∀ {a b : α} (f : a ⇾ b), mapHom ⟨F⟩ f ≃ mapHom ⟨G⟩ f) :
      NatIsoDesc ⟨F⟩ ⟨G⟩ :=
    { η     := λ a => idIso (φ a),
      isNat := { toIsNatural := ⟨λ {a b} f => (cancelRightId hβ.Hom (toHomReflEq (φ a)) (mapHom ⟨G⟩ f))⁻¹ •
                                              hEq f •
                                              cancelLeftId hβ.Hom (mapHom ⟨F⟩ f) (toHomReflEq (φ b))⟩ } }

    variable {F G : α ⮕ β} (desc : NatIsoDesc F G)

    @[reducible] def natIso (a : α) : F.φ a ⇿ G.φ a := desc.η a
    @[reducible] def natToHom (a : α) : F.φ a ⇾ G.φ a := toHom (natIso desc a)

    def toNatDesc : NatDesc F G :=
    { η     := natToHom desc
      isNat := desc.isNat }

    def isoNaturality {a b : α} (e : a ⇿ b) :
      natIso desc b • mapIso F e ≃ mapIso G e • natIso desc a :=
    hβIso.toHomInj ((congrArgTransLeft hβ.Hom (natToHom desc a) (toHomComm G e) •
                     toHomTransEq (natIso desc a) (mapIso G e))⁻¹ •
                    desc.isNat.nat (toHom e) •
                    (congrArgTransRight hβ.Hom (toHomComm F e) (natToHom desc b) •
                     toHomTransEq (mapIso F e) (natIso desc b)))

    def toIsoNatDesc : NatDesc (hα := isoCategory α) (hβ := isoCategory β)
                               (isoFunctor F) (isoFunctor G) :=
    NatDesc.mk (hα := isoCategory α) (hβ := isoCategory β)
               desc.η
               (isNat := IsNaturalTransformation.mk (hα := isoMorphisms α) (hβ := isoSemicategory β)
                                                    (toIsNatural := IsNatural.mk (λ {a b : α} (e : a ⇿ b) =>
                                                                                  congrArgTransLeft hβIso.Iso (natIso desc a) (mapIsoEq G e)⁻¹ •
                                                                                  isoNaturality desc e •
                                                                                  congrArgTransRight hβIso.Iso (mapIsoEq F e) (natIso desc b))))

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

  class HasIsoNaturality {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                         (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
                         [hFunProp : HasFunProp α β] [hNat : HasNaturality α β]
                         [hβIso : HasIsomorphisms β] [hαβIso : HasIsomorphisms (α ⮕ β)] where
  (defNatIso {F G : α ⮕ β} (η : F ⇿ G) (a : α) :
     HasIsoRel.DefIso (natIsoDesc (hαβIso.desc η) a))
  (defNatIsoFun (F G : α ⮕ β) (a : α) :
     (F ⇿ G) ⟶{λ η => (defNatIso η a).e} (F.φ a ⇿ G.φ a))

  namespace HasIsoNaturality

    open HasIsoRel HasIsoOp HasIsomorphisms HasIsoPreFun

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
             {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
             [HasFunProp α β] [HasNaturality α β] [hβIso : HasIsomorphisms β]
             [hαβIso : HasIsomorphisms (α ⮕ β)] [h : HasIsoNaturality α β]

    def natIso {F G : α ⮕ β} (η : F ⇿ G) (a : α) : F.φ a ⇿ G.φ a := (h.defNatIso η a).e

    @[reducible] def natIsoFun (F G : α ⮕ β) (a : α) : (F ⇿ G) ⟶ (F.φ a ⇿ G.φ a) :=
    h.defNatIsoFun F G a

    instance {F G : α ⮕ β} (η : F ⇿ G) (a : α) : IsFunApp (F ⇿ G) (natIso η a) :=
    { F := natIsoFun F G a,
      a := η,
      e := byDef }

    def natIsoCongrArg {F G : α ⮕ β} {η₁ η₂ : F ⇿ G} (e : η₁ ≃ η₂) (a : α) :
      natIso η₁ a ≃ natIso η₂ a :=
    defCongrArg (defNatIsoFun F G a) e

    def natIsoToHomComm {F G : α ⮕ β} (η : F ⇿ G) (a : α) :
      toHom (natIso η a) ≃ nat (toHom η) a :=
    byToDef

    def natIsoInvHomComm {F G : α ⮕ β} (η : F ⇿ G) (a : α) :
      invHom (natIso η a) ≃ nat (invHom η) a :=
    byInvDef

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

    variable [HasIsomorphisms α] [HasFunProp α β (hα := isoCategory α) (hβ := isoCategory β)]
             [HasIsoFunctoriality α β]

    def natIsoDesc {F G : α ⮕ β} (η : F ⇿ G) : NatIsoDesc F G :=
    { η     := natIso η,
      isNat := { nat := λ {a b} f => congrArgTransRight hβ.Hom (natIsoToHomComm η a)⁻¹ (mapHom G f) •
                                     naturality (toHom η) f •
                                     congrArgTransLeft hβ.Hom (mapHom F f) (natIsoToHomComm η b) } }

    def isoNaturality {F G : α ⮕ β} (η : F ⇿ G) {a b : α} (e : a ⇿ b) :
      natIso η b • mapIso F e ≃ mapIso G e • natIso η a :=
    NatIsoDesc.isoNaturality (natIsoDesc η) e

    structure IsoDefNat {F G : α ⮕ β} (desc : NatIsoDesc F G) where
    (η             : F ⇿ G)
    (natEq (a : α) : natIso η a ≃ NatIsoDesc.natIso desc a)

    def byIsoNatDef {F G : α ⮕ β} {desc : NatIsoDesc F G} {η : IsoDefNat desc} (a : α) :
      natIso η.η a ≃ NatIsoDesc.natIso desc a :=
    η.natEq a

  end HasIsoNaturality



  class IsIsoUniverse (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw} W]
                      [hFunUniv : IsFunUniverse.{u} W] [hNatUniv : IsNatUniverse.{u} W] where
  [hasIso (α : Sort (max 1 u w)) [IsCategory W α] : HasIsomorphisms α]
  [hasIsoFun (α β : Sort (max 1 u w)) [IsCategory W α] [IsCategory W β] : HasIsoFunctoriality α β]
  [hasIsoNat (α β : Sort (max 1 u w)) [IsCategory W α] [IsCategory W β] : HasIsoNaturality α β]

  namespace IsIsoUniverse

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
             [IsFunUniverse.{u} W] [IsNatUniverse.{u} W] [h : IsIsoUniverse.{u} W]

    instance (α : Sort (max 1 u w)) [IsCategory W α] : HasIsomorphisms α := h.hasIso α

    instance (α β : Sort (max 1 u w)) [IsCategory W α] [IsCategory W β] : HasIsoFunctoriality α β :=
    h.hasIsoFun α β

    instance (α β : Sort (max 1 u w)) [IsCategory W α] [IsCategory W β] : HasIsoNaturality α β :=
    h.hasIsoNat α β

  end IsIsoUniverse

end CategoryTheory
