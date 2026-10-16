import Leanux.Proofs.WG.Lifetimes.IndexOwnerAccess
import Leanux.Proofs.Framing.Product

/-! Contracts at the actual product boundary. Invariants may observe every
World component; native leaves are executed once by the real WG adapter.
The stability premise retains the original 43-field store observation. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

abbrev ProductAmbientSpec (I : List LifetimeEvent → World → Prop)
    (P : IdentityView → Prop) (g : PrefixM LifetimeEvent α) (Q : α → IdentityView → Prop) :=
  ProjectedAmbientSpec World.wg I P g Q

structure ProductAmbientContracts (I : List LifetimeEvent → World → Prop) : Prop where
  safe : ∀ h w, I h w → LifetimeEvent.Safe h
  storeStable : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v
  getPeer : ∀ P id, ProductAmbientSpec I P (liftWGObserver (getPeerMixed id))
    (fun p s => P s ∧ s.1.slots id = some p.internalId)
  getKeypair : ∀ P id, ProductAmbientSpec I P (liftWGObserver (getKeypairPrefix id))
    (fun k s => P s ∧ s.2.1 id = some k.internalId)
  getRx : ∀ P id, ProductAmbientSpec I P (liftWGObserver (getRxSkbPrefix id))
    (fun _ s => P s ∧ ∃ stamp, s.2.2 (.inr id) = some stamp)
  setPeer : ∀ P id p, ProductAmbientSpec I (fun s => P s ∧ s.1.slots id = some p.internalId)
    (liftWGObserver (setPeerMixed id p)) (fun _ => P)
  setKeypair : ∀ P id k, ProductAmbientSpec I (fun s => P s ∧ s.2.1 id = some k.internalId)
    (liftWGObserver (setKeypairPrefix id k)) (fun _ => P)
  setRx : ∀ P id f, ProductAmbientSpec I P (liftWGObserver (setRxSkbPrefix id f)) (fun _ => P)
  peerGet : ∀ id, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (peerGetMixed id))
  peerPut : ∀ id, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (peerPutMixed id))

@[simp] theorem liftWGObserver_pure (x : α) :
    liftWGObserver (pure x : WGPrefix E α) = pure x := rfl

@[simp] theorem liftWGObserver_lift (a : WG.M α) :
    liftWGObserver (liftWGPrefix a : WGPrefix E α) = liftPrefix (liftWG a) := by
  funext w h
  change runPrefix (liftWGObserver (liftWGPrefix a)) w h =
    runPrefix (liftPrefix (liftWG a)) w h
  rw [liftWGObserver_run, runWGPrefix_lift, runPrefix_lift, liftWG_run]

namespace ProductAmbientContracts

theorem ofNative (c : AmbientContracts I) :
    ProductAmbientContracts (fun h w => I h w.wg) where
  safe := fun h w hi => c.safe h w.wg hi
  storeStable := by
    intro h w v he hi
    exact c.storeStable h w.wg v.wg (congrArg (fun s : ProductStore43 => s.2.2.2) he) hi
  getPeer := fun P id => (c.getPeer P id).liftWGObserver
  getKeypair := fun P id => (c.getKeypair P id).liftWGObserver
  getRx := fun P id => (c.getRx P id).liftWGObserver
  setPeer := fun P id p => (c.setPeer P id p).liftWGObserver
  setKeypair := fun P id k => (c.setKeypair P id k).liftWGObserver
  setRx := fun P id f => (c.setRx P id f).liftWGObserver
  peerGet := fun id => (c.peerGet id).liftWGObserver
  peerPut := fun id => (c.peerPut id).liftWGObserver

theorem pure (c : ProductAmbientContracts I) (P : IdentityView → Prop) (x : α) :
    ProductAmbientSpec I P (pure x) (fun _ => P) :=
  AmbientContracts.projectedPure World.wg I c.safe P x

theorem forget (hg : ProductAmbientSpec I P g Q) (hq : ∀ x s, Q x s → R x s) :
    ProductAmbientSpec I P g R := AmbientContracts.projectedForget hg hq

theorem drop (hg : ProductAmbientSpec I (fun _ => True) g Q) :
    PrefixPreserves I LifetimeEvent.Safe g := AmbientContracts.projectedDrop hg

theorem store (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (a : Leanux.M α) (ha : SameProductStore a) :
    ProductAmbientSpec I P (liftPrefix a) (fun _ => P) :=
  AmbientContracts.projectedStore World.wg productStoreView (fun s => s.2.2.2)
    (fun _ => rfl) I c.safe c.storeStable P a ha

theorem nativeStore (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (a : WG.M α) (ha : SameWGStore a) :
    ProductAmbientSpec I P (liftWGObserver (liftWGPrefix a)) (fun _ => P) := by
  rw [liftWGObserver_lift]
  exact c.store P (liftWG a) (liftWG_sameProductStore a ha)

theorem ambient (c : ProductAmbientContracts I) (P : IdentityView → Prop) (a : AmbientM α) :
    ProductAmbientSpec I P (liftPrefix (liftAmbient a)) (fun _ => P) := by
  apply c.store
  intro initial
  exact productAmbient_spec a (fun w => productStoreView w = initial) (fun _ _ hi => hi)

theorem branch (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (d : Decision) (b : Bool) :
    ProductAmbientSpec I P (liftPrefix (Leanux.branch d b)) (fun _ => P) :=
  c.ambient P (AmbientM.branch d b)

theorem invariant (c : ProductAmbientContracts I) (P : IdentityView → Prop) (why : String) :
    ProductAmbientSpec I P (liftPrefix (Leanux.invariant (α := α) why)) (fun _ => P) :=
  c.ambient P (AmbientM.invariant why)

theorem getKeypair_frame (c : ProductAmbientContracts I) (P : IdentityView → Prop) (id : KeypairId) :
    ProductAmbientSpec I P (liftWGObserver (getKeypairPrefix id)) (fun _ => P) :=
  forget (c.getKeypair P id) (fun _ _ hi => hi.1)

theorem peerDeref (c : ProductAmbientContracts I) (P : IdentityView → Prop) (owner : IndexOwner) :
    ProductAmbientSpec I P (liftWGObserver (peerDerefPrefix owner)) (fun _ => P) := by
  have word : ProductAmbientSpec I P (liftWGObserver (peerWordPrefix owner)) (fun _ => P) := by
    cases owner with
    | handshake pid =>
      simp only [peerWordPrefix, liftWGObserver_bind, liftWGObserver_pure]
      apply PrefixEnsures.bind (c.getPeer P pid)
      intro p
      exact forget (c.pure (fun s => P s ∧ s.1.slots pid = some p.internalId) p.handshakeEntryPeer)
        (fun _ _ hi => hi.1)
    | keypair kp =>
      simp only [peerWordPrefix, liftWGObserver_bind, liftWGObserver_pure]
      apply PrefixEnsures.bind (c.getKeypair P kp)
      intro k
      exact forget (c.pure (fun s => P s ∧ s.2.1 kp = some k.internalId) k.peer)
        (fun _ _ hi => hi.1)
  simp only [peerDerefPrefix, liftWGObserver_bind]
  apply PrefixEnsures.bind word
  intro peer
  cases peer with
  | none =>
    apply c.nativeStore
    intro initial
    exact hoare_liftAmbient (AmbientM.unsupported _) (fun w => wgStoreView w = initial)
  | some pid =>
    simpa only [liftWGObserver_pure] using c.pure P pid

end ProductAmbientContracts
end Leanux.Proofs.WG.Lifetimes

