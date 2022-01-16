import UniverseAbstractions.Axioms.CategoryTheory.Extended



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universe u v vv w ww iv iw



namespace CategoryTheory

  open MetaRelation MetaFunctor MetaQuantification HasTransFun HasSymmFun IsAssociative
       IsCategoricalPreorder IsGroupoidEquivalence IsCategory
       HasFunProp HasFunProp.Functor HasNatRel HasNatOp HasNaturality
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

      def map {β : Sort u} [hβ : IsCategory V β] (φ : α → β) [hφ : IsCategoryFunctor φ]
              {a b : α} (e : IsoDesc a b) :
        IsoDesc (φ a) (φ b) :=
      { toHom  := hφ.F e.toHom,
        invHom := hφ.F e.invHom,
        isInv  := { leftInv  := mapHalfInv φ e.isInv.leftInv,
                    rightInv := mapHalfInv φ e.isInv.rightInv } }

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

        def toHomEq  {a b : α} {e₁ e₂ : a ⇿ b} (he : e₁ ≃ e₂) : toHom  e₁ ≃ toHom  e₂ :=
        defCongrArg (h.defToHomFun a b) he
        def invHomEq {a b : α} {e₁ e₂ : a ⇿ b} (he : e₁ ≃ e₂) : invHom e₁ ≃ invHom e₂ :=
        IsoDesc.toInvEquiv (toHomEq he)

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

    instance hasIsoGroupoid : HasIsomorphisms α :=
    { isoHasSymmFun  := hα.homHasSymmFun,
      isoHasTransFun := hα.homHasTransFun }

  end IsGroupoid



  class IsIsoFunctor {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                     {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
                     [hαIso : HasIsomorphisms α] [hβIso : HasIsomorphisms β]
                     (φ : α → β) [hφ : IsCategoryFunctor φ] where
  (F : PreFunctor hαIso.Iso hβIso.Iso φ)
  (toHomCongr {a b : α} (e : a ⇿ b) : HasIsoRel.toHom (F e) ≃ hφ.F (HasIsoRel.toHom e))

  namespace IsIsoFunctor

    open HasIsoRel HasIsoOp HasIsomorphisms

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
             {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
             [hαIso : HasIsomorphisms α] [hβIso : HasIsomorphisms β]
             (φ : α → β) [hφ : IsCategoryFunctor φ] [h : IsIsoFunctor φ]

    @[reducible] def preFunctor : PreFunctor hαIso.Iso hβIso.Iso φ := h.F

    def invHomCongr {a b : α} (e : a ⇿ b) : invHom (h.F e) ≃ hφ.F (invHom e) :=
    HalfInv.unique hβ.Hom (hφ.hPreorder.reflEq a •
                           HasCongrArg.congrArg (hφ.F.baseFun a a) (leftInv e) •
                           (hφ.hPreorder.transEq (toHom e) (invHom e))⁻¹ •
                           congrArgTransRight hβ.Hom (h.toHomCongr e) (hφ.F (invHom e)))
                          (rightInv (h.F e))

    instance isReflFunctor : IsReflFunctor h.F :=
    ⟨λ a => hβIso.toHomInj ((toHomReflEq (φ a))⁻¹ •
                            hφ.hPreorder.reflEq a •
                            HasCongrArg.congrArg (hφ.F.baseFun a a) (toHomReflEq a) •
                            h.toHomCongr (idIso a))⟩

    instance isSymmFunctor : IsSymmFunctor h.F :=
    ⟨λ {a b} e => hβIso.toHomInj ((invHomCongr φ e •
                                   toHomSymmEq (h.F e))⁻¹ •
                                  HasCongrArg.congrArg (hφ.F.baseFun b a) (toHomSymmEq e) •
                                  h.toHomCongr e⁻¹)⟩

    instance isTransFunctor : IsTransFunctor h.F :=
    ⟨λ {a b c} e f => hβIso.toHomInj ((congrArgTrans hβ.Hom (h.toHomCongr e) (h.toHomCongr f) •
                                       toHomTransEq (h.F e) (h.F f))⁻¹ •
                                      hφ.hPreorder.transEq (toHom e) (toHom f) •
                                      HasCongrArg.congrArg (hφ.F.baseFun a c) (toHomTransEq e f) •
                                      h.toHomCongr (f • e))⟩

    instance isPreorderFunctor    : IsPreorderFunctor    h.F := ⟨⟩
    instance isEquivalenceFunctor : IsEquivalenceFunctor h.F := ⟨⟩

    instance isMorphismFunctor :
      IsMorphismFunctor (hα := isoMorphisms α) (hβ := isoMorphisms β) φ :=
    IsMorphismFunctor.mk (hα := isoMorphisms α) (hβ := isoMorphisms β) h.F

    instance isGroupoidFunctor :
      IsGroupoidFunctor (hα := isoGroupoid α) (hβ := isoGroupoid β) φ :=
    IsGroupoidFunctor.mk (hα := isoGroupoid α) (hβ := isoGroupoid β)
                         (hEquivalence := isEquivalenceFunctor φ)

  end IsIsoFunctor



  class HasIsoFunctoriality {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
                            (α : Sort u) (β : Sort v) [hα : IsCategory W α] [hβ : IsCategory W β]
                            [hαIso : HasIsomorphisms α] [hβIso : HasIsomorphisms β]
                            [hFunProp : HasFunProp α β] where
  [isIsoFun (F : α ⮕ β) : IsIsoFunctor F.φ]

  namespace HasIsoFunctoriality

    open HasIsoRel

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
             {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
             [HasIsomorphisms α] [HasIsomorphisms β] [HasFunProp α β]
             [h : HasIsoFunctoriality α β]

    instance (F : α ⮕ β) : IsIsoFunctor F.φ := h.isIsoFun F

    @[reducible] def mapIso (F : α ⮕ β) {a b : α} (e : a ⇿ b) : F.φ a ⇿ F.φ b :=
    (IsIsoFunctor.preFunctor F.φ) e

    def byMapTo  {F : α ⮕ β} {a b : α} {e : a ⇿ b} :
      toHom (mapIso F e) ≃ mapHom F (toHom e) :=
    (h.isIsoFun F).toHomCongr e

    def byMapInv {F : α ⮕ β} {a b : α} {e : a ⇿ b} :
      invHom (mapIso F e) ≃ mapHom F (invHom e) :=
    IsIsoFunctor.invHomCongr F.φ e

  end HasIsoFunctoriality



  namespace HasNaturality

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
             {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
             [HasFunProp α β] [h : HasNaturality α β] [HasIsomorphisms (α ⮕ β)]
             [HasIsomorphisms β] {F G : α ⮕ β}

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
                         [hαβIso : HasIsomorphisms (α ⮕ β)] [hβIso : HasIsomorphisms β] where
  (defNatIso {F G : α ⮕ β} (η : F ⇿ G) (a : α) :
     HasIsoRel.DefIso (natIsoDesc (hαβIso.desc η) a))
  (defNatIsoFun (F G : α ⮕ β) (a : α) :
     (F ⇿ G) ⟶{λ η => (defNatIso η a).e} (F.φ a ⇿ G.φ a))

  namespace HasIsoNaturality

    open HasIsoRel HasIsoOp HasIsomorphisms HasIsoFunctoriality

    variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
             {α : Sort u} {β : Sort v} [hα : IsCategory W α] [hβ : IsCategory W β]
             [HasFunProp α β] [HasNaturality α β] [hαβIso : HasIsomorphisms (α ⮕ β)]
             [hβIso : HasIsomorphisms β] [h : HasIsoNaturality α β]

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

    def isoNaturality [HasIsomorphisms α] [HasIsoFunctoriality α β]
                      {F G : α ⮕ β} (η : F ⇿ G) {a b : α} (e : a ⇿ b) :
      mapIso G e • natIso η a ≃ natIso η b • mapIso F e :=
    hβIso.toHomInj ((congrArgTrans hβ.Hom byMapTo byToDef •
                     toHomTransEq (mapIso F e) (natIso η b))⁻¹ •
                    naturality (toHom η) (toHom e) •
                    (congrArgTrans hβ.Hom byToDef byMapTo •
                     toHomTransEq (natIso η a) (mapIso G e)))

    def natIsoReflEq (F : α ⮕ β) (a : α) : natIso (idIso F) a ≃ idIso (F.φ a) :=
    hβIso.toHomInj ((toHomReflEq (F.φ a))⁻¹ •
                    natReflEq F a •
                    (natCongrArg byToDef a • byToDef))

    def natIsoSymmEq {F G : α ⮕ β} (η : F ⇿ G) (a : α) :
      natIso η⁻¹ a ≃ (natIso η a)⁻¹ :=
    hβIso.toHomInj ((byInvDef •
                     toHomSymmEq (natIso η a))⁻¹ •
                    (natCongrArg byToDef a • byToDef))

    def natIsoTransEq {F G H : α ⮕ β} (η : F ⇿ G) (ε : G ⇿ H) (a : α) :
      natIso (ε • η) a ≃ natIso ε a • natIso η a :=
    hβIso.toHomInj ((congrArgTrans hβ.Hom byToDef byToDef •
                     toHomTransEq (natIso η a) (natIso ε a))⁻¹ •
                    natTransEq (toHom η) (toHom ε) a •
                    (natCongrArg byToDef a • byToDef))

  end HasIsoNaturality



  class IsIsoUniverse (W : Universe.{w, ww}) [IsHomUniverse.{w, ww, iw} W]
                      [hFunUniv : IsFunUniverse.{u} W] [hNatUniv : IsNatUniverse.{u} W] where
  [hasIso (α : Sort (max 1 u w)) [IsCategory W α] : HasIsomorphisms α]
  [hasIsoFun (α β : Sort (max 1 u w)) [IsCategory W α] [IsCategory W β] : HasIsoFunctoriality α β]
  [hasIsoNat (α β : Sort (max 1 u w)) [IsCategory W α] [IsCategory W β] : HasIsoNaturality α β]

  namespace IsIsoUniverse

    section

      variable {W : Universe.{w, ww}} [IsHomUniverse.{w, ww, iw} W]
               [IsFunUniverse.{u} W] [IsNatUniverse.{u} W] [h : IsIsoUniverse.{u} W]

      instance (α : Sort (max 1 u w)) [IsCategory W α] : HasIsomorphisms α := h.hasIso α

      instance (α β : Sort (max 1 u w)) [IsCategory W α] [IsCategory W β] : HasIsoFunctoriality α β :=
      h.hasIsoFun α β

      instance (α β : Sort (max 1 u w)) [IsCategory W α] [IsCategory W β] : HasIsoNaturality α β :=
      h.hasIsoNat α β

    end

end IsIsoUniverse
