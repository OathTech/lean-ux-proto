import Leanux.Proofs.WG.Lifetimes.AllocationReleases

/-! Allocation bounds instantiate the existing ambient caller contracts. The
access-only leaves preserve both metadata and released sets; the reference
leaves instead use the explicit retention and release-origin theorem. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def SameReleases (h g : List LifetimeEvent) : Prop :=
  (∀ s, AccessEvent.Released (g.filterMap LifetimeEvent.peer?) s ↔
    AccessEvent.Released (h.filterMap LifetimeEvent.peer?) s) ∧
  (∀ s, AccessEvent.Released (g.filterMap LifetimeEvent.keypair?) s ↔
    AccessEvent.Released (h.filterMap LifetimeEvent.keypair?) s) ∧
  (∀ s, AccessEvent.Released (g.filterMap LifetimeEvent.packet?) s ↔
    AccessEvent.Released (h.filterMap LifetimeEvent.packet?) s)

private theorem getPeer_sameReleases (id : PeerId) (w : World) (h : List LifetimeEvent) :
    SameReleases h (runPrefix (getPeerMixed id) w h).2 := by
  rw [getPeerMixed_run]
  cases (getPeer id).run w <;>
    simp [SameReleases, List.filterMap_append, LifetimeEvent.peer?, LifetimeEvent.keypair?,
      LifetimeEvent.packet?, AccessEvent.Released]

private theorem getKeypair_sameReleases (id : KeypairId) (w : World) (h : List LifetimeEvent) :
    SameReleases h (runPrefix (getKeypairPrefix id) w h).2 := by
  rw [getKeypairPrefix_run]
  cases (getKeypair id).run w <;>
    simp [SameReleases, List.filterMap_append, LifetimeEvent.peer?, LifetimeEvent.keypair?,
      LifetimeEvent.packet?, AccessEvent.Released]

private theorem getRx_sameReleases (id : SkbId) (w : World) (h : List LifetimeEvent) :
    SameReleases h (runPrefix (getRxSkbPrefix id) w h).2 := by
  rw [getRxSkbPrefix_run]
  cases (getRxSkb id).run w <;>
    simp [SameReleases, List.filterMap_append, LifetimeEvent.peer?, LifetimeEvent.keypair?,
      LifetimeEvent.packet?, AccessEvent.Released]

private theorem setPeer_sameReleases (id : PeerId) (p : Peer) (w : World) (h : List LifetimeEvent) :
    SameReleases h (runPrefix (setPeerMixed id p) w h).2 := by
  rw [setPeerMixed_run]
  split <;>
    simp [SameReleases, List.filterMap_append, LifetimeEvent.peer?, LifetimeEvent.keypair?,
      LifetimeEvent.packet?, AccessEvent.Released]

private theorem setKeypair_sameReleases (id : KeypairId) (k : Keypair) (w : World) (h : List LifetimeEvent) :
    SameReleases h (runPrefix (setKeypairPrefix id k) w h).2 := by
  rw [setKeypairPrefix_run]
  split <;>
    simp [SameReleases, List.filterMap_append, LifetimeEvent.peer?, LifetimeEvent.keypair?,
      LifetimeEvent.packet?, AccessEvent.Released]

private theorem setRx_sameReleases (id : SkbId) (f : RxPacket → RxPacket) (w : World) (h : List LifetimeEvent) :
    SameReleases h (runPrefix (setRxSkbPrefix id f) w h).2 := by
  rw [setRxSkbPrefix_run]
  cases (getRxSkb id).run w <;>
    simp [SameReleases, List.filterMap_append, LifetimeEvent.peer?, LifetimeEvent.keypair?,
      LifetimeEvent.packet?, AccessEvent.Released]

private theorem access_frame (hg : AmbientSpec ReleaseInv P g Q) (he : ErasesPrefix g a)
    (hv : ∀ w x v, P (identityView w) → a.run w = .ok (x, v) →
      (identityView v, allocationMetadata v) = (identityView w, allocationMetadata w))
    (hs : ∀ w h, SameReleases h (runPrefix g w h).2) : AmbientSpec AllocationInv P g Q :=
  allocation_access hg he hv (fun w h => (hs w h).1)
    (fun w h => (hs w h).2.1) (fun w h => (hs w h).2.2)

theorem allocationAmbient : AmbientContracts AllocationInv where
  safe := fun _ _ hi => hi.safe
  kernelStable := fun _ _ _ he hi => hi.kernel he
  getPeer := by
    intro P id
    apply access_frame (releaseAmbient.getPeer P id) (getPeerMixed_erases id)
    · intro w p v _ hr
      rw [(Peers.getPeer_current id w v p hr).1]
    · exact getPeer_sameReleases id
  getKeypair := by
    intro P id
    apply access_frame (releaseAmbient.getKeypair P id) (getKeypairPrefix_erases id)
    · intro w k v _ hr
      rw [(Keypairs.getKeypair_current id w v k hr).1]
    · exact getKeypair_sameReleases id
  getRx := by
    intro P id
    apply access_frame (releaseAmbient.getRx P id) (getRxSkbPrefix_erases id)
    · intro w p v _ hr
      rw [(Packets.getRxSkb_current id w v p hr).1]
    · exact getRx_sameReleases id
  setPeer := by
    intro P id p
    apply access_frame (releaseAmbient.setPeer P id p) (setPeerMixed_erases id p)
    · intro w x v hi hr
      cases x
      exact Prod.ext (setPeer_identity id p w v hi.2 hr) (setPeer_metadata id p w () v hr)
    · exact setPeer_sameReleases id p
  setKeypair := by
    intro P id k
    apply access_frame (releaseAmbient.setKeypair P id k) (setKeypairPrefix_erases id k)
    · intro w x v hi hr
      cases x
      exact Prod.ext (setKeypair_identity id k w v hi.2 hr) (setKeypair_metadata id k w () v hr)
    · exact setKeypair_sameReleases id k
  setRx := by
    intro P id f
    apply access_frame (releaseAmbient.setRx P id f) (setRxSkbPrefix_erases id f)
    · intro w x v _ hr
      exact Prod.ext (setRxSkb_identity id f w x v hr) (setRxSkb_metadata id f w x v hr)
    · exact setRx_sameReleases id f
  peerGet := peerGetMixed_allocation
  peerPut := peerPutMixed_allocation

theorem decryptQueue_allocation (ring : PtrRing SkbId) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe
      (liftPrefix (modifyDev fun d => {d with decryptQueue := ring})) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.safe)
  intro h w x v hi hr
  exact hi.congr (decryptQueue_identity ring w x v hr)
    (metadata_modifyDev (fun d => {d with decryptQueue := ring}) (fun _ => rfl) w x v hr)

theorem enqueuePerPeerRxPrefix_allocation
    (hi : PrefixPreserves AllocationInv LifetimeEvent.Safe irq) (id : SkbId) (state : PacketState) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (enqueuePerPeerRxPrefix irq id state) :=
  enqueuePerPeerRxPrefix_preserves_ambient allocationAmbient hi id state

theorem decryptPacketPrefix_allocation (pkt : RxPacket) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (decryptPacketPrefix pkt) :=
  AmbientContracts.drop (decryptPacketPrefix_spec_ambient allocationAmbient (fun _ => True) pkt)

theorem decryptIterPrefix_allocation
    (hs : PrefixPreserves AllocationInv LifetimeEvent.Safe softirq)
    (hi : PrefixPreserves AllocationInv LifetimeEvent.Safe irq)
    (hr : PrefixPreserves AllocationInv LifetimeEvent.Safe needResched) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (decryptIterPrefix softirq irq needResched) :=
  decryptIterPrefix_preserves_ambient allocationAmbient decryptQueue_allocation hs hi hr

theorem keypairGetPrefix_allocation (kp : Option KeypairId) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (keypairGetPrefix kp) :=
  AmbientContracts.drop (keypairGetPrefix_spec_ambient allocationAmbient (fun _ => True) kp)

theorem keypairsClearPrefix_allocation (pid : PeerId) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (keypairsClearPrefix pid) :=
  keypairsClearPrefix_preserves_ambient allocationAmbient keypairPutPrefix_allocation pid

namespace ReleaseCall

theorem preserves_allocation (c : ReleaseCall) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe c.observed := by
  cases c with
  | acquire kp =>
    exact PrefixPreserves.bind (keypairGetPrefix_allocation kp)
      (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.safe) ())
  | put kp now => exact keypairPutPrefix_allocation kp now
  | freeTx id => exact freeTxSkbPrefix_allocation id
  | freeRx id => exact freeRxSkbPrefix_allocation id
  | clear pid => exact keypairsClearPrefix_allocation pid

theorem observe_preserves_allocation (cs : List ReleaseCall) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (observe cs) := by
  induction cs with
  | nil => exact PrefixPreserves.pure (fun _ _ hi => hi.safe) ()
  | cons c cs ih => exact PrefixPreserves.bind c.preserves_allocation (fun _ => ih)

end ReleaseCall

end Leanux.Proofs.WG.Lifetimes
