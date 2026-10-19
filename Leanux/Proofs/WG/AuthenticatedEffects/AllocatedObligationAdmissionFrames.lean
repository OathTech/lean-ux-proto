import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationMixedAllocation
import Leanux.Proofs.WG.TransmitSecurity.PacketOriginFrames
import Leanux.Proofs.WG.RetirementSecurity.TxCoverageCreate

/-! Exact native frames before createData's refusal frees. Admission and DEAD
publication may change queue ownership and packet marks, but they preserve
every allocation cell's immutable material and device epoch. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.Admission
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity
open PacketOrigins
set_option maxHeartbeats 600000

private theorem store {action : WG.M α} (same : SameWGStore action) :
    SameView snapshot action :=
  same.of_factor (fun s => snapshot {dev := s.dev}) snapshot (fun _ => rfl)

private theorem read_peer (pid : PeerId) : SameView snapshot (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  exact congrArg snapshot (Peers.getPeer_current pid w v result a b run).1

theorem publication (items : List SkbId) (state : PacketState) :
    SameView snapshot (enqueuePerPeerTx items state) :=
  snapshot_pair (epoch_ring (TxRing.enqueuePeer_frame items state)) (PacketMaterial.publish items state)

theorem enqueue (pid : PeerId) (items : List SkbId) :
    SameView snapshot (enqueuePerDeviceAndPeer pid items) := by
  intro initial
  let P := fun w => snapshot w = initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have mark (id : SkbId) :=
    (snapshot_pair (skb_epoch _) (PacketMaterial.set_tx id (fun p => {p with state := .uncrypted})
      (fun _ => rfl))).wp (fun s => s = initial)
  have edit (f : Device → Device) (epochs : ∀ d, (f d).ifindex = d.ifindex)
      (packets : ∀ d, (f d).txSkbs = d.txSkbs) :=
    (PacketOrigins.modify f epochs packets).wp (fun s => s = initial)
  change Preserves P _
  unfold enqueuePerDeviceAndPeer cpumaskNextOnlineFrom
  repeat' first
    | (allocation_release_head getPeer; exact (read_peer _).wp (fun s => s = initial))
    | (allocation_release_head getDev; exact (store getDev_sameWGStore).wp (fun s => s = initial))
    | (allocation_release_head setPeer; unfold setPeer)
    | (allocation_release_head modifyDev; exact edit _ (fun _ => rfl) (fun _ => rfl))
    | (allocation_release_head setTxSkb; exact mark _)
    | (allocation_release_head branch; exact ambient (AmbientM.branch _ _))
    | (allocation_release_head invariant; exact ambient (AmbientM.invariant _))
    | (allocation_release_head queueDeviceWork; exact ambient (AmbientM.queueDeviceWork _))
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | allocation_release_step

theorem native_front (pid : PeerId) (items : List SkbId) :
    SameView snapshot (RxCredits.createReturnSource pid items) := by
  intro initial
  change Preserves (fun w => snapshot w = initial) _
  unfold RxCredits.createReturnSource RxCredits.createPublishReturn
  repeat' first
    | (allocation_release_head getPeer; exact (read_peer _).wp (fun s => s = initial))
    | (allocation_release_head enqueuePerDeviceAndPeer; exact (enqueue _ _).wp (fun s => s = initial))
    | (allocation_release_head enqueuePerPeerTx; exact (publication _ _).wp (fun s => s = initial))
    | (allocation_release_head branch; exact hoare_liftAmbient (AmbientM.branch _ _) _)
    | allocation_release_step

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.Admission
