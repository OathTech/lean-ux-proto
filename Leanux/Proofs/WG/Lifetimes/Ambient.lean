import Leanux.Proofs.WG.Lifetimes.KeypairAccess
import Leanux.Proofs.WG.Lifetimes.Acquire
import Leanux.Proofs.Framing.WGTime

/-! Caller contracts separate a history-dependent invariant from temporary
predicates about resolved identities. Native observers use the actual WG and
Ambient stack; projected contracts retain arbitrary actual product actions.
Source coverage remains a separate obligation. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

abbrev AmbientSpec (I : List LifetimeEvent → WGWorld → Prop)
    (P : IdentityView → Prop) (g : MixedM α) (Q : α → IdentityView → Prop) :=
  StatePrefixEnsures (fun h w _ => I h w ∧ P (identityView w)) LifetimeEvent.Safe g
    (fun x h w _ => I h w ∧ Q x (identityView w))

/-- An actual-state contract, also applicable to the runner's product World.
The invariant may observe components beyond the WG projection. -/
abbrev ProjectedAmbientSpec {S : Type} (project : S → WGWorld)
    (I : List LifetimeEvent → S → Prop) (P : IdentityView → Prop)
    (g : PrefixT LifetimeEvent S α) (Q : α → IdentityView → Prop) :=
  PrefixEnsures (fun h w => I h w ∧ P (identityView (project w))) LifetimeEvent.Safe g
    (fun x h w => I h w ∧ Q x (identityView (project w)))

structure AmbientContracts (I : List LifetimeEvent → WGWorld → Prop) : Prop where
  safe : ∀ h w, I h w → LifetimeEvent.Safe h
  storeStable : ∀ h w v, wgStoreView v = wgStoreView w → I h w → I h v
  getPeer : ∀ P id, AmbientSpec I P (getPeerMixed id)
    (fun p s => P s ∧ s.1.slots id = some p.internalId)
  getKeypair : ∀ P id, AmbientSpec I P (getKeypairPrefix id)
    (fun k s => P s ∧ s.2.1 id = some k.internalId)
  getRx : ∀ P id, AmbientSpec I P (getRxSkbPrefix id)
    (fun _ s => P s ∧ ∃ stamp, s.2.2 (.inr id) = some stamp)
  setPeer : ∀ P id p, AmbientSpec I (fun s => P s ∧ s.1.slots id = some p.internalId)
    (setPeerMixed id p) (fun _ => P)
  setKeypair : ∀ P id k, AmbientSpec I (fun s => P s ∧ s.2.1 id = some k.internalId)
    (setKeypairPrefix id k) (fun _ => P)
  setRx : ∀ P id f, AmbientSpec I P (setRxSkbPrefix id f) (fun _ => P)
  peerGet : ∀ id, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (peerGetMixed id)
  peerPut : ∀ id, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (peerPutMixed id)

namespace AmbientContracts

theorem projectedPure {S : Type} (project : S → WGWorld)
    (I : List LifetimeEvent → S → Prop)
    (safe : ∀ h w, I h w → LifetimeEvent.Safe h) (P : IdentityView → Prop) (x : α) :
    ProjectedAmbientSpec project I P (pure x) (fun _ => P) :=
  PrefixEnsures.pure (fun h w hi => safe h w hi.1) (fun _ _ hi => hi)

theorem projectedForget {S : Type} {project : S → WGWorld}
    {I : List LifetimeEvent → S → Prop} {P : IdentityView → Prop}
    {g : PrefixT LifetimeEvent S α} {Q R : α → IdentityView → Prop}
    (hg : ProjectedAmbientSpec project I P g Q) (hq : ∀ x s, Q x s → R x s) :
    ProjectedAmbientSpec project I P g R :=
  hg.consequence (fun _ _ hi => hi) (fun x _ _ hi => ⟨hi.1, hq x _ hi.2⟩)

theorem projectedDrop {S : Type} {project : S → WGWorld}
    {I : List LifetimeEvent → S → Prop} {g : PrefixT LifetimeEvent S α}
    {Q : α → IdentityView → Prop}
    (hg : ProjectedAmbientSpec project I (fun _ => True) g Q) :
    PrefixPreserves I LifetimeEvent.Safe g :=
  (hg.consequence (fun _ _ hi => ⟨hi, True.intro⟩) (fun _ _ _ hi => hi.1)).preserves

/-- The observation is arbitrary: at the product boundary it can be the
original 43-field store. Its WG factor suffices for resolved identities.
The action itself retains its actual state and monad, and the lift emits no access. -/
theorem projectedStore {S V : Type} (project : S → WGWorld) (observe : S → V)
    (factor : V → WGStoreView) (hf : ∀ w, wgStoreView (project w) = factor (observe w))
    (I : List LifetimeEvent → S → Prop)
    (safe : ∀ h w, I h w → LifetimeEvent.Safe h)
    (stable : ∀ h w v, observe v = observe w → I h w → I h v)
    (P : IdentityView → Prop) (a : StateT S (Except Stop) α) (ha : SameView observe a) :
    ProjectedAmbientSpec project I P (liftPrefix a) (fun _ => P) := by
  have hi := identity_sameWGStore (ha.of_factor factor (fun w => wgStoreView (project w)) hf)
  apply PrefixEnsures.lift a (fun h w hp => safe h w hp.1)
  intro h w x v hp hr
  exact ⟨stable h w v ((ProjectedAction.iff_run _ _ _).mp ha w x v hr) hp.1,
    ((ProjectedAction.iff_run _ _ _).mp hi w x v hr) ▸ hp.2⟩

theorem pure (c : AmbientContracts I) (P : IdentityView → Prop) (x : α) :
    AmbientSpec I P (pure x) (fun _ => P) :=
  StatePrefixEnsures.pure x (fun h w _ hi => c.safe h w hi.1) (fun _ _ _ hi => hi)

theorem forget (hg : AmbientSpec I P g Q) (hq : ∀ x s, Q x s → R x s) :
    AmbientSpec I P g R :=
  hg.consequence (fun _ _ _ hi => hi) (fun x _ _ _ hi => ⟨hi.1, hq x _ hi.2⟩)

theorem drop (hg : AmbientSpec I (fun _ => True) g Q) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe g :=
  hg.consequence (fun _ _ _ hi => ⟨hi, True.intro⟩) (fun _ _ _ _ hi => hi.1)

/-- Native counterpart of the projected lift rule. The two Ambient endpoints
are quantified by the actual native execution, including arbitrary input records. -/
theorem store (c : AmbientContracts I) (P : IdentityView → Prop)
    (a : WG.M α) (ha : SameView wgStoreView a) :
    AmbientSpec I P (liftWGPrefix a) (fun _ => P) := by
  apply StatePrefixEnsures.lift a (fun h w _ hi => c.safe h w hi.1)
  intro h w ambient x v ambient' hi hr
  exact ⟨c.storeStable h w v ((ProjectedAction.iff_run_ambient _ _ _).mp ha
      w ambient x v ambient' hr) hi.1,
    ((ProjectedAction.iff_run_ambient _ _ _).mp (identity_sameWGStore (project := id) ha)
      w ambient x v ambient' hr) ▸ hi.2⟩

theorem branch (c : AmbientContracts I) (P : IdentityView → Prop) (d : Decision) (b : Bool) :
    AmbientSpec I P (liftWGPrefix (Leanux.branch d b)) (fun _ => P) := by
  apply c.store
  intro initial
  exact hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)

theorem branchCmp (c : AmbientContracts I) (P : IdentityView → Prop)
    (d : Decision) (b : Bool) (lhs rhs : Int) :
    AmbientSpec I P (liftWGPrefix (Leanux.branchCmp d b lhs rhs)) (fun _ => P) := by
  apply c.store
  intro initial
  exact hoare_liftAmbient (AmbientM.branchCmp d b lhs rhs) (fun w => wgStoreView w = initial)

theorem invariant (c : AmbientContracts I) (P : IdentityView → Prop) (why : String) :
    AmbientSpec I P (liftWGPrefix (Leanux.invariant (α := α) why)) (fun _ => P) := by
  apply StatePrefixEnsures.lift _ (fun h w _ hi => c.safe h w hi.1)
  intro h w ambient x v ambient' hi hr
  simp [Leanux.invariant, AmbientM.invariant] at hr
  cases hr

theorem getKeypair_frame (c : AmbientContracts I) (P : IdentityView → Prop) (id : KeypairId) :
    AmbientSpec I P (getKeypairPrefix id) (fun _ => P) :=
  forget (c.getKeypair P id) (fun _ _ hi => hi.1)

end AmbientContracts

theorem mixedAmbient : AmbientContracts MixedInv where
  safe := fun _ _ hi => hi.safe
  storeStable := by
    intro h w v he hi
    have hd := congrArg WGStoreView.dev he
    have hc := congrArg WGStoreView.peerCounter he
    apply hi.congr
    unfold identityView Peers.snapshot keypairResidents packetResidents
    simp only [wgStoreView] at hd hc
    rw [hd, hc]
  getPeer := mixed_getPeer
  getKeypair := mixed_getKeypair
  getRx := mixed_getRxSkb
  setPeer := mixed_setPeer
  setKeypair := mixed_setKeypair
  setRx := mixed_setRxSkb
  peerGet := peerGetMixed_preserves
  peerPut := peerPutMixed_preserves

end Leanux.Proofs.WG.Lifetimes
