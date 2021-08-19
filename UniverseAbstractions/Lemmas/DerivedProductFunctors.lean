import UniverseAbstractions.Axioms.Universes
import UniverseAbstractions.Axioms.Universe.Functors
import UniverseAbstractions.Axioms.Universe.Singletons
import UniverseAbstractions.Axioms.Universe.Products
import UniverseAbstractions.Lemmas.DerivedFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true



namespace HasFunctorialProducts

  open HasEmbeddedProducts

  variable {U : Universe} [HasEmbeddedFunctors U] [HasFunctorialProducts U]

  def defFstFun [HasSubLinearFunOp U] (α β : U) : α ⊓ β ⟶[λ P => fst P] α :=
  elimFun (HasSubLinearFunOp.constFunFun β α)
  ◄ λ _ => by simp

  def defSndFun [HasAffineFunOp    U] (α β : U) : α ⊓ β ⟶[λ P => snd P] β :=
  elimFun (HasSubLinearFunOp.constFun α (HasLinearFunOp.idFun β))
  ◄ λ _ => by simp

  @[reducible] def fstFun [HasSubLinearFunOp U] (α β : U) : α ⊓ β ⟶ α := defFstFun α β
  @[reducible] def sndFun [HasAffineFunOp    U] (α β : U) : α ⊓ β ⟶ β := defSndFun α β

  def defDupIntroFun [HasNonLinearFunOp U] (α : U) : α ⟶[λ a => intro a a] α ⊓ α :=
  HasNonLinearFunOp.dupFun (introFunFun α α)
  ◄ λ _ => by simp

  @[reducible] def dupIntroFun [HasNonLinearFunOp U] (α : U) : α ⟶ α ⊓ α := defDupIntroFun α

  def defRevIntroFun [HasLinearFunOp U] (α : U) {β : U} (b : β) : α ⟶[λ a => intro a b] α ⊓ β :=
  HasLinearFunOp.swapFun (introFunFun α β) b
  ◄ λ _ => by simp

  @[reducible] def revIntroFun [HasLinearFunOp U] (α : U) {β : U} (b : β) : α ⟶ α ⊓ β := defRevIntroFun α b

  def defRevIntroFunFun [HasLinearFunOp U] (α β : U) : β ⟶[λ b => revIntroFun α b] (α ⟶ α ⊓ β) :=
  HasLinearFunOp.swapFunFun (introFunFun α β)
  ◄ λ _ => by simp [revIntroFun, defRevIntroFun]

  @[reducible] def revIntroFunFun [HasLinearFunOp U] (α β : U) : β ⟶ α ⟶ α ⊓ β := defRevIntroFunFun α β

  def defRevElimFun [HasLinearFunOp U] {α β γ : U} (F : β ⟶ α ⟶ γ) :
    α ⊓ β ⟶[λ P => F (snd P) (fst P)] γ :=
  elimFun (HasLinearFunOp.swapFunFun F)
  ◄ λ _ => by simp

  @[reducible] def revElimFun [HasLinearFunOp U] {α β γ : U} (F : β ⟶ α ⟶ γ) : α ⊓ β ⟶ γ := defRevElimFun F

  def defRevElimFunFun [HasLinearFunOp U] (α β γ : U) : (β ⟶ α ⟶ γ) ⟶[λ F => revElimFun F] (α ⊓ β ⟶ γ) :=
  elimFunFun α β γ ⊙ HasLinearFunOp.swapFunFunFun β α γ
  ◄ λ _ => by simp [revElimFun, defRevElimFun]

  @[reducible] def revElimFunFun [HasLinearFunOp U] (α β γ : U) : (β ⟶ α ⟶ γ) ⟶ (α ⊓ β ⟶ γ) := defRevElimFunFun α β γ

  def invElim [HasLinearFunOp U] {α β γ : U} (F : α ⊓ β ⟶ γ) (a : α) (b : β) : γ := F (intro a b)

  def defInvElimFun [HasLinearFunOp U] {α β γ : U} (F : α ⊓ β ⟶ γ) (a : α) : β ⟶[λ b => invElim F a b] γ :=
  F ⊙ introFun a β
  ◄ λ _ => by simp [invElim]

  @[reducible] def invElimFun [HasLinearFunOp U] {α β γ : U} (F : α ⊓ β ⟶ γ) (a : α) : β ⟶ γ := defInvElimFun F a

  def defInvElimFunFun [HasLinearFunOp U] {α β γ : U} (F : α ⊓ β ⟶ γ) : α ⟶[λ a => invElimFun F a] (β ⟶ γ) :=
  HasLinearFunOp.revCompFunFun β F ⊙ introFunFun α β
  ◄ λ _ => by simp [invElimFun, defInvElimFun]

  @[reducible] def invElimFunFun [HasLinearFunOp U] {α β γ : U} (F : α ⊓ β ⟶ γ) : α ⟶ β ⟶ γ := defInvElimFunFun F

  def defInvElimFunFunFun [HasLinearFunOp U] (α β γ : U) : (α ⊓ β ⟶ γ) ⟶[λ P => invElimFunFun P] (α ⟶ β ⟶ γ) :=
  HasLinearFunOp.compFunFun (introFunFun α β) (β ⟶ γ) ⊙ HasLinearFunOp.revCompFunFunFun β (α ⊓ β) γ
  ◄ λ _ => by simp [invElimFunFun, defInvElimFunFun]

  @[reducible] def invElimFunFunFun [HasLinearFunOp U] (α β γ : U) : (α ⊓ β ⟶ γ) ⟶ (α ⟶ β ⟶ γ) :=
  defInvElimFunFunFun α β γ

  def defReplaceFstFun [HasLinearFunOp U] {α β : U} (F : α ⟶ β) (γ : U) :
    α ⊓ γ ⟶[λ P => intro (F (fst P)) (snd P)] β ⊓ γ :=
  elimFun (introFunFun β γ ⊙ F)
  ◄ λ _ => by simp

  @[reducible] def replaceFstFun [HasLinearFunOp U] {α β : U} (F : α ⟶ β) (γ : U) : α ⊓ γ ⟶ β ⊓ γ :=
  defReplaceFstFun F γ

  def defReplaceFstFunFun [HasLinearFunOp U] (α β γ : U) :
    (α ⟶ β) ⟶[λ F => replaceFstFun F γ] (α ⊓ γ ⟶ β ⊓ γ) :=
  elimFunFun α γ (β ⊓ γ) ⊙ HasLinearFunOp.revCompFunFun α (introFunFun β γ)
  ◄ λ _ => by simp [replaceFstFun, defReplaceFstFun]

  @[reducible] def replaceFstFunFun [HasLinearFunOp U] (α β γ : U) : (α ⟶ β) ⟶ (α ⊓ γ ⟶ β ⊓ γ) :=
  defReplaceFstFunFun α β γ

  def defReplaceSndFun [HasLinearFunOp U] {α β : U} (F : α ⟶ β) (γ : U) :
    γ ⊓ α ⟶[λ P => intro (fst P) (F (snd P))] γ ⊓ β :=
  revElimFun (revIntroFunFun γ β ⊙ F)
  ◄ λ _ => by simp

  @[reducible] def replaceSndFun [HasLinearFunOp U] {α β : U} (F : α ⟶ β) (γ : U) : γ ⊓ α ⟶ γ ⊓ β :=
  defReplaceSndFun F γ

  def defReplaceSndFunFun [HasLinearFunOp U] (α β γ : U) :
    (α ⟶ β) ⟶[λ F => replaceSndFun F γ] (γ ⊓ α ⟶ γ ⊓ β) :=
  revElimFunFun γ α (γ ⊓ β) ⊙ HasLinearFunOp.revCompFunFun α (revIntroFunFun γ β)
  ◄ λ _ => by simp [replaceSndFun, defReplaceSndFun]

  @[reducible] def replaceSndFunFun [HasLinearFunOp U] (α β γ : U) : (α ⟶ β) ⟶ (γ ⊓ α ⟶ γ ⊓ β) :=
  defReplaceSndFunFun α β γ

  def defCommFun [HasLinearFunOp U] (α β : U) : α ⊓ β ⟶[λ P => intro (snd P) (fst P)] β ⊓ α :=
  elimFun (revIntroFunFun β α)
  ◄ λ _ => by simp

  @[reducible] def commFun [HasLinearFunOp U] (α β : U) : α ⊓ β ⟶ β ⊓ α := defCommFun α β

  def intro₃LFunFun [HasLinearFunOp U] (α β γ : U) : α ⟶ β ⟶ γ ⟶ (α ⊓ β) ⊓ γ :=
  HasLinearFunOp.revCompFunFun β (introFunFun (α ⊓ β) γ) ⊙ introFunFun α β
  def intro₃RFunFun [HasLinearFunOp U] (α β γ : U) : α ⟶ β ⟶ γ ⟶ α ⊓ (β ⊓ γ) :=
  invElimFunFunFun β γ (α ⊓ (β ⊓ γ)) ⊙ introFunFun α (β ⊓ γ)

  def elim₃LFun                    {α β γ δ : U} (F : α ⟶ β ⟶ γ ⟶ δ) : (α ⊓ β) ⊓ γ ⟶ δ := elimFun (elimFun F)
  def elim₃RFun [HasLinearFunOp U] {α β γ δ : U} (F : α ⟶ β ⟶ γ ⟶ δ) : α ⊓ (β ⊓ γ) ⟶ δ := elimFun (elimFunFun β γ δ ⊙ F)

  def defAssocLRFun [HasLinearFunOp U] (α β γ : U) :
    (α ⊓ β) ⊓ γ ⟶[λ P => intro (fst (fst P)) (intro (snd (fst P)) (snd P))] α ⊓ (β ⊓ γ) :=
  elim₃LFun (intro₃RFunFun α β γ)
  ◄ λ _ => by simp [elim₃LFun, intro₃RFunFun, invElimFunFun, defInvElimFunFun]

  def defAssocRLFun [HasLinearFunOp U] (α β γ : U) :
    α ⊓ (β ⊓ γ) ⟶[λ P => intro (intro (fst P) (fst (snd P))) (snd (snd P))] (α ⊓ β) ⊓ γ :=
  elim₃RFun (intro₃LFunFun α β γ)
  ◄ λ _ => by simp [elim₃RFun, intro₃LFunFun]

  @[reducible] def assocLRFun [HasLinearFunOp U] (α β γ : U) : (α ⊓ β) ⊓ γ ⟶ α ⊓ (β ⊓ γ) := defAssocLRFun α β γ
  @[reducible] def assocRLFun [HasLinearFunOp U] (α β γ : U) : α ⊓ (β ⊓ γ) ⟶ (α ⊓ β) ⊓ γ := defAssocRLFun α β γ

  def defMergeFun [HasFullFunOp U] {α β γ : U} (F : α ⟶ β) (G : α ⟶ γ) :
    α ⟶[λ a => intro (F a) (G a)] β ⊓ γ :=
  HasFullFunOp.substFun F (revIntroFunFun β γ ⊙ G)
  ◄ λ _ => by simp

  @[reducible] def mergeFun [HasFullFunOp U] {α β γ : U} (F : α ⟶ β) (G : α ⟶ γ) : α ⟶ β ⊓ γ := defMergeFun F G

  def defMergeFunFun [HasFullFunOp U] {α β : U} (F : α ⟶ β) (γ : U) :
    (α ⟶ γ) ⟶[λ G => mergeFun F G] (α ⟶ β ⊓ γ) :=
  HasFullFunOp.substFunFun F (β ⊓ γ) ⊙ HasLinearFunOp.revCompFunFun α (revIntroFunFun β γ)
  ◄ λ _ => by simp [mergeFun, defMergeFun]

  @[reducible] def mergeFunFun [HasFullFunOp U] {α β : U} (F : α ⟶ β) (γ : U) : (α ⟶ γ) ⟶ (α ⟶ β ⊓ γ) :=
  defMergeFunFun F γ

  def defMergeFunFunFun [HasFullFunOp U] (α β γ : U) : (α ⟶ β) ⟶[λ F => mergeFunFun F γ] ((α ⟶ γ) ⟶ (α ⟶ β ⊓ γ)) :=
  HasLinearFunOp.compFunFun (HasLinearFunOp.revCompFunFun α (revIntroFunFun β γ)) (α ⟶ β ⊓ γ) ⊙
  HasFullFunOp.substFunFunFun α β (β ⊓ γ)
  ◄ λ _ => by simp [mergeFunFun, defMergeFunFun]

  @[reducible] def mergeFunFunFun [HasFullFunOp U] (α β γ : U) : (α ⟶ β) ⟶ (α ⟶ γ) ⟶ (α ⟶ β ⊓ γ) :=
  defMergeFunFunFun α β γ

  def distr [HasAffineFunOp U] {α β γ : U} (F : α ⟶ β ⊓ γ) : (α ⟶ β) ⊓ (α ⟶ γ) :=
  intro (fstFun β γ ⊙ F) (sndFun β γ ⊙ F) -- TODO: Rewrite using tactic, as a test

  def defDistrFun [HasFullFunOp U] (α β γ : U) : (α ⟶ β ⊓ γ) ⟶[λ F => distr F] (α ⟶ β) ⊓ (α ⟶ γ) :=
  mergeFun (HasLinearFunOp.revCompFunFun α (fstFun β γ)) (HasLinearFunOp.revCompFunFun α (sndFun β γ))
  ◄ λ _ => by simp [distr]

  @[reducible] def distrFun [HasFullFunOp U] (α β γ : U) : (α ⟶ β ⊓ γ) ⟶ (α ⟶ β) ⊓ (α ⟶ γ) := defDistrFun α β γ

  def invDistrFun [HasFullFunOp U] {α β γ : U} (P : (α ⟶ β) ⊓ (α ⟶ γ)) : α ⟶ β ⊓ γ :=
  mergeFun (fst P) (snd P)

  def defInvDistrFunFun [HasFullFunOp U] (α β γ : U) : (α ⟶ β) ⊓ (α ⟶ γ) ⟶[λ P => invDistrFun P] (α ⟶ β ⊓ γ) :=
  elimFun (mergeFunFunFun α β γ)
  ◄ λ _ => by simp [invDistrFun]

  @[reducible] def invDistrFunFun [HasFullFunOp U] (α β γ : U) : (α ⟶ β) ⊓ (α ⟶ γ) ⟶ (α ⟶ β ⊓ γ) :=
  defInvDistrFunFun α β γ

  def defProdTopIntroFun [HasEmbeddedTop U] (α : U) :
    α ⟶[λ a => HasEmbeddedProducts.intro (HasEmbeddedTop.top U) a] HasEmbeddedTop.Top U ⊓ α :=
  defIntroFun (HasEmbeddedTop.top U) α

  @[reducible] def prodTopIntroFun [HasEmbeddedTop U] (α : U) : α ⟶ HasEmbeddedTop.Top U ⊓ α :=
  defProdTopIntroFun α

  def defProdTopElimFun [HasLinearFunOp U] [HasFunctorialTop U] (α : U) :
    HasEmbeddedTop.Top U ⊓ α ⟶[λ P => HasEmbeddedProducts.snd P] α :=
  elimFun (HasFunctorialTop.elimFun (HasLinearFunOp.idFun α))
  ◄ λ _ => by simp [HasFunctorialTop.elimFun]

  @[reducible] def prodTopElimFun [HasLinearFunOp U] [HasFunctorialTop U] (α : U) :
    HasEmbeddedTop.Top U ⊓ α ⟶ α :=
  defProdTopElimFun α

end HasFunctorialProducts
