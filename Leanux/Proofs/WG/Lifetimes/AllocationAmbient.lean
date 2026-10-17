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

private theorem getPeer_sameReleases (id : PeerId) (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) :
    SameReleases h (runStatePrefix (getPeerMixed id) w ambient h).2 := by
  rw [getPeerMixed_run]
  cases ((getPeer id).run w).run ambient <;>
    simp [SameReleases, List.filterMap_append, LifetimeEvent.peer?, LifetimeEvent.keypair?,
      LifetimeEvent.packet?, AccessEvent.Released]

private theorem getKeypair_sameReleases (id : KeypairId) (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) :
    SameReleases h (runStatePrefix (getKeypairPrefix id) w ambient h).2 := by
  rw [getKeypairPrefix_run]
  cases ((getKeypair id).run w).run ambient <;>
    simp [SameReleases, List.filterMap_append, LifetimeEvent.peer?, LifetimeEvent.keypair?,
      LifetimeEvent.packet?, AccessEvent.Released]

private theorem getRx_sameReleases (id : SkbId) (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) :
    SameReleases h (runStatePrefix (getRxSkbPrefix id) w ambient h).2 := by
  rw [getRxSkbPrefix_run]
  cases ((getRxSkb id).run w).run ambient <;>
    simp [SameReleases, List.filterMap_append, LifetimeEvent.peer?, LifetimeEvent.keypair?,
      LifetimeEvent.packet?, AccessEvent.Released]

private theorem setPeer_sameReleases (id : PeerId) (p : Peer) (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) :
    SameReleases h (runStatePrefix (setPeerMixed id p) w ambient h).2 := by
  rw [setPeerMixed_run]
  split <;>
    simp [SameReleases, List.filterMap_append, LifetimeEvent.peer?, LifetimeEvent.keypair?,
      LifetimeEvent.packet?, AccessEvent.Released]

private theorem setKeypair_sameReleases (id : KeypairId) (k : Keypair) (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) :
    SameReleases h (runStatePrefix (setKeypairPrefix id k) w ambient h).2 := by
  rw [setKeypairPrefix_run]
  split <;>
    simp [SameReleases, List.filterMap_append, LifetimeEvent.peer?, LifetimeEvent.keypair?,
      LifetimeEvent.packet?, AccessEvent.Released]

private theorem setRx_sameReleases (id : SkbId) (f : RxPacket → RxPacket) (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) :
    SameReleases h (runStatePrefix (setRxSkbPrefix id f) w ambient h).2 := by
  rw [setRxSkbPrefix_run]
  cases ((getRxSkb id).run w).run ambient <;>
    simp [SameReleases, List.filterMap_append, LifetimeEvent.peer?, LifetimeEvent.keypair?,
      LifetimeEvent.packet?, AccessEvent.Released]

private theorem access_frame {S α : Type} {project : S → WGWorld}
    {g : PrefixT LifetimeEvent S α} {a : StateT S (Except Stop) α}
    {P : IdentityView → Prop} {Q : α → IdentityView → Prop}
    (hg : ProjectedAmbientSpec project (fun h w => ReleaseInv h (project w)) P g Q)
    (he : ErasesPrefix g a)
    (hv : ∀ w x v, P (identityView (project w)) → a.run w = .ok (x, v) →
      (identityView (project v), allocationMetadata (project v)) =
        (identityView (project w), allocationMetadata (project w)))
    (hs : ∀ w h, SameReleases h (runPrefix g w h).2) :
    ProjectedAmbientSpec project (fun h w => AllocationInv h (project w)) P g Q :=
  allocation_access hg he hv (fun w h => (hs w h).1)
    (fun w h => (hs w h).2.1) (fun w h => (hs w h).2.2)

private theorem access_state_frame {g : MixedM α} {a : WG.M α}
    (hg : AmbientSpec ReleaseInv P g Q) (he : ErasesStatePrefix g a)
    (hv : ∀ w ambient x v ambient', P (identityView w) →
      (a.run w).run ambient = .ok ((x, v), ambient') →
      (identityView v, allocationMetadata v) = (identityView w, allocationMetadata w))
    (hs : ∀ w ambient h, SameReleases h (runStatePrefix g w ambient h).2) :
    AmbientSpec AllocationInv P g Q :=
  allocation_state_access hg he hv (fun w ambient h => (hs w ambient h).1)
    (fun w ambient h => (hs w ambient h).2.1) (fun w ambient h => (hs w ambient h).2.2)

theorem allocationAmbient : AmbientContracts AllocationInv where
  safe := fun _ _ hi => hi.safe
  storeStable := fun _ _ _ he hi => hi.store he
  getPeer := by
    intro P id
    apply access_state_frame (releaseAmbient.getPeer P id) (getPeerMixed_erases id)
    · intro w ambient p v ambient' _ hr
      rw [(Peers.getPeer_current id w v p ambient ambient' hr).1]
    · exact getPeer_sameReleases id
  getKeypair := by
    intro P id
    apply access_state_frame (releaseAmbient.getKeypair P id) (getKeypairPrefix_erases id)
    · intro w ambient k v ambient' _ hr
      rw [(Keypairs.getKeypair_current id w v ambient ambient' k hr).1]
    · exact getKeypair_sameReleases id
  getRx := by
    intro P id
    apply access_state_frame (releaseAmbient.getRx P id) (getRxSkbPrefix_erases id)
    · intro w ambient p v ambient' _ hr
      rw [(Packets.getRxSkb_current id w v p ambient ambient' hr).1]
    · exact getRx_sameReleases id
  setPeer := by
    intro P id p
    apply access_state_frame (releaseAmbient.setPeer P id p) (setPeerMixed_erases id p)
    · intro w ambient x v ambient' hi hr
      cases x
      exact Prod.ext (setPeer_identity id p w v ambient ambient' hi.2 hr)
        ((ProjectedAction.iff_run_ambient _ _ _).mp (setPeer_metadata id p) w ambient () v ambient' hr)
    · exact setPeer_sameReleases id p
  setKeypair := by
    intro P id k
    apply access_state_frame (releaseAmbient.setKeypair P id k) (setKeypairPrefix_erases id k)
    · intro w ambient x v ambient' hi hr
      cases x
      exact Prod.ext (setKeypair_identity id k w v ambient ambient' hi.2 hr)
        ((ProjectedAction.iff_run_ambient _ _ _).mp (setKeypair_metadata id k) w ambient () v ambient' hr)
    · exact setKeypair_sameReleases id k
  setRx := by
    intro P id f
    apply access_state_frame (releaseAmbient.setRx P id f) (setRxSkbPrefix_erases id f)
    · intro w ambient x v ambient' _ hr
      exact Prod.ext ((ProjectedAction.iff_run_ambient _ _ _).mp (setRxSkb_identity id f) w ambient x v ambient' hr)
        ((ProjectedAction.iff_run_ambient _ _ _).mp (setRxSkb_metadata id f) w ambient x v ambient' hr)
    · exact setRx_sameReleases id f
  peerGet := peerGetMixed_allocation
  peerPut := peerPutMixed_allocation

theorem decryptQueue_allocation (ring : PtrRing SkbId) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe
      (liftWGPrefix (modifyDev fun d => {d with decryptQueue := ring})) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.safe)
  intro h w ambient x v ambient' hi hr
  exact hi.congr
    ((ProjectedAction.iff_run_ambient _ _ _).mp (decryptQueue_identity ring) w ambient x v ambient' hr)
    ((ProjectedAction.iff_run_ambient _ _ _).mp
      (metadata_modifyDev (fun d => {d with decryptQueue := ring}) (fun _ => rfl))
      w ambient x v ambient' hr)

theorem enqueuePerPeerRxPrefix_allocation
    (hi : PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe irq) (id : SkbId) (state : PacketState) :
    PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe (enqueuePerPeerRxPrefix irq id state) :=
  enqueuePerPeerRxPrefix_preserves_ambient (ProductAmbientContracts.ofNative allocationAmbient) hi id state

theorem decryptPacketPrefix_allocation (pkt : RxPacket) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe (decryptPacketPrefix pkt) :=
  AmbientContracts.drop (decryptPacketPrefix_spec_ambient allocationAmbient (fun _ => True) pkt)

theorem decryptIterPrefix_allocation
    (hs : PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe softirq)
    (hi : PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe irq)
    (hr : PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe needResched) :
    PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe (decryptIterPrefix softirq irq needResched) :=
  decryptIterPrefix_preserves_ambient (ProductAmbientContracts.ofNative allocationAmbient)
    (fun ring => (decryptQueue_allocation ring).liftWGObserver) hs hi hr

theorem keypairGetPrefix_allocation (kp : Option KeypairId) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe (keypairGetPrefix kp) :=
  AmbientContracts.drop (keypairGetPrefix_spec_ambient allocationAmbient (fun _ => True) kp)

theorem keypairsClearPrefix_allocation (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe (keypairsClearPrefix pid) :=
  keypairsClearPrefix_preserves_ambient allocationAmbient keypairPutPrefix_allocation pid

namespace ReleaseCall

theorem preserves_allocation (c : ReleaseCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe c.observed := by
  cases c with
  | acquire kp =>
    exact StatePrefixEnsures.bind (keypairGetPrefix_allocation kp)
      (fun _ => StatePrefixEnsures.pure () (fun _ _ _ hi => hi.safe) (fun _ _ _ hi => hi))
  | put kp now => exact keypairPutPrefix_allocation kp now
  | freeTx id => exact freeTxSkbPrefix_allocation id
  | freeRx id => exact freeRxSkbPrefix_allocation id
  | clear pid => exact keypairsClearPrefix_allocation pid

theorem observe_preserves_allocation (cs : List ReleaseCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe (observe cs) := by
  induction cs with
  | nil => exact StatePrefixEnsures.pure () (fun _ _ _ hi => hi.safe) (fun _ _ _ hi => hi)
  | cons c cs ih => exact StatePrefixEnsures.bind c.preserves_allocation (fun _ => ih)

end ReleaseCall

end Leanux.Proofs.WG.Lifetimes
