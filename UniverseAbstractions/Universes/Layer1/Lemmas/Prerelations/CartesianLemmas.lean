import UniverseAbstractions.Universes.Layer1.Axioms.Prerelations.Cartesian



namespace UniverseAbstractions.Layer1

set_option autoImplicit false

universe u



namespace HasPreorderRelation

  variable {V : Universe} [HasLinearLogic V] {α : Sort u} [hα : HasPreorderRelation V α]


  namespace HasProductObjects

    variable [HasProductObjects α]

    @[reducible] def prodIntroHom {a b c : α} (f : a ⟶ b) (g : a ⟶ c) : a ⟶ b ⊗ c :=
      (prodIntroFun₂ a b c) f g

    def prodDupIntroHom (a : α) : a ⟶ a ⊗ a := prodIntroHom (idHom a) (idHom a)

    def prodReplaceFstHom {a b : α} (f : a ⟶ b) (c : α) : a ⊗ c ⟶ b ⊗ c :=
      prodIntroHom (f • fstHom a c) (sndHom a c)
    def prodReplaceSndHom (a : α) {b c : α} (f : b ⟶ c) : a ⊗ b ⟶ a ⊗ c :=
      prodIntroHom (fstHom a b) (f • sndHom a b)
    def prodReplaceBothHom {a b c d : α} (f : a ⟶ b) (g : c ⟶ d) : a ⊗ c ⟶ b ⊗ d :=
      prodIntroHom (f • fstHom a c) (g • sndHom a c)

    def fst₃LHom (a b c : α) : (a ⊗ b) ⊗ c ⟶ a := fstHom a b • fstHom (a ⊗ b) c
    def snd₃LHom (a b c : α) : (a ⊗ b) ⊗ c ⟶ b := sndHom a b • fstHom (a ⊗ b) c
    def trd₃LHom (a b c : α) : (a ⊗ b) ⊗ c ⟶ c := sndHom (a ⊗ b) c

    def fst₃RHom (a b c : α) : a ⊗ (b ⊗ c) ⟶ a := fstHom a (b ⊗ c)
    def snd₃RHom (a b c : α) : a ⊗ (b ⊗ c) ⟶ b := fstHom b c • sndHom a (b ⊗ c)
    def trd₃RHom (a b c : α) : a ⊗ (b ⊗ c) ⟶ c := sndHom b c • sndHom a (b ⊗ c)

    def prodIntro₃LHom {a b c d : α} (f : a ⟶ b) (g : a ⟶ c) (h : a ⟶ d) : a ⟶ (b ⊗ c) ⊗ d :=
      prodIntroHom (prodIntroHom f g) h

    def prodIntro₃RHom {a b c d : α} (f : a ⟶ b) (g : a ⟶ c) (h : a ⟶ d) : a ⟶ b ⊗ (c ⊗ d) :=
      prodIntroHom f (prodIntroHom g h)

    def prodCommHom (a b : α) : a ⊗ b ⟶ b ⊗ a := prodIntroHom (sndHom a b) (fstHom a b)

    def prodAssocLRHom (a b c : α) : (a ⊗ b) ⊗ c ⟶ a ⊗ (b ⊗ c) :=
      prodIntro₃RHom (fst₃LHom a b c) (snd₃LHom a b c) (trd₃LHom a b c)
    def prodAssocRLHom (a b c : α) : a ⊗ (b ⊗ c) ⟶ (a ⊗ b) ⊗ c :=
      prodIntro₃LHom (fst₃RHom a b c) (snd₃RHom a b c) (trd₃RHom a b c)

    def prodIndirFst {a b c : α} (f : a ⟶ b ⊗ c) : a ⟶ b := fstHom b c • f
    def prodIndirSnd {a b c : α} (f : a ⟶ b ⊗ c) : a ⟶ c := sndHom b c • f

    def prodTopIntroHom [h : HasTerminalObject α] (a : α) : a ⟶ ⊤α ⊗ a :=
      prodIntroHom (h.trmIntroHom a) (idHom a)

  end HasProductObjects


  namespace HasExponentialObjects

    variable [HasProductObjects α] [HasExponentialObjects α]

    @[reducible] def curryHom {a b c : α} (f : a ⊗ b ⟶ c) : a ⟶ c ⌃ b :=
      (curryFun a b c) f

    def uncurryHom {a b c : α} (f : a ⟶ c ⌃ b) : a ⊗ b ⟶ c :=
      evalHom b c • HasProductObjects.prodReplaceFstHom f b

  end HasExponentialObjects

  -- TODO: Translate standard equivalences to isomorphisms.
  -- TODO: Define a universe based on a Cartesian closed precategory.

end HasPreorderRelation
