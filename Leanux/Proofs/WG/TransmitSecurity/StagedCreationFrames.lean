import Leanux.Proofs.WG.TransmitSecurity.StagedReservationFrames
import Leanux.Proofs.WG.Queues.RxRingCallbackFrames

/-! Packet allocation and native queue publication retain the sources of all
surviving staged plaintexts. Final peer release may remove its staged queue. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem Exact.skb (action : SkbM α) : SameView stagedAt (liftSkb action) := by
  intro initial
  apply hoare_liftSkb
  intro w d store before device
  rw [← before]
  funext pid
  simp only [stagedAt,device,Option.bind_some]

theorem acquire_peer (pid : PeerId) : Frame (peerGet pid) :=
  of_view _ (Exact.peer_get pid)

macro "staged_creation_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head getTxSkb; exact skb _ $initial)
  | (rx_retention_head setTxSkb; exact skb _ $initial)
  | (rx_retention_head freeTxSkb; exact skb _ $initial)
  | (rx_retention_head peerGet; exact acquire_peer _ $initial)
  | (rx_retention_head keypairPut; exact key_put _ _ $initial)
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (Retains $initial)
     intro x b
     change Preserves (Retains $initial) _)
  | rxstack_preserves_join
  | staged_native_step $initial)

theorem choose_cpu (pid : PeerId) : Frame (cpumaskChooseOnline pid) := by
  intro initial
  unfold cpumaskChooseOnline
  simp (config := {zeta := false}) only [branch,Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' staged_creation_step initial

theorem publish (items : List SkbId) (state : PacketState) : Frame (enqueuePerPeerTx items state) := by
  intro initial
  unfold enqueuePerPeerTx
  simp (config := {zeta := false}) only [peekQueuedUnit,recordQueued,invariant]
  repeat' first
    | (rx_retention_head cpumaskChooseOnline; exact choose_cpu _ initial)
    | staged_creation_step initial

theorem enqueue (pid : PeerId) (items : List SkbId) : Frame (enqueuePerDeviceAndPeer pid items) := by
  intro initial
  unfold enqueuePerDeviceAndPeer
  split
  · apply preserves_bind (skb _ initial)
    intro _
    let P := fun s : PeerId → Option (Nat × List Packet) =>
      ∀ q value, s q = some value → stagedAt initial q = some value
    apply hoare_bind _ _ (read_saved P pid)
    intro peer
    apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .enqueuePeerQueueFull
      (peer.txQueue.count ≥ MAX_QUEUED_PACKETS)) _)
    intro full
    split
    · exact hoare_consequence (hoare_pure _ _) (fun _ hi => hi.1) (fun _ _ hi => hi.2)
    · apply hoare_bind _ _ (write_saved P pid {peer with txQueue := peer.txQueue.enqueue items})
      intro _
      change Preserves (Retains initial) _
      simp (config := {zeta := false}) only [cpumaskNextOnlineFrom,branch,queueDeviceWork]
      repeat' staged_creation_step initial
  · exact hoare_liftAmbient (AmbientM.invariant "an empty ring item") _

theorem create (pid : PeerId) (items : List SkbId) : Frame (createData pid items) := by
  intro initial
  unfold createData
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head enqueuePerDeviceAndPeer; exact enqueue _ _ initial)
    | (rx_retention_head enqueuePerPeerTx; exact publish _ _ initial)
    | staged_creation_step initial

theorem Origins.create_epoch (pid : PeerId) (items : List SkbId) : SameView Packets.epoch (createData pid items) :=
  (RxRing.createData_cell pid items).of_factor (fun cell => cell.map Prod.fst) Packets.epoch
    (fun w => by simp only [RxRing.nativeCell,Packets.epoch,Option.map_map,Function.comp_def])

theorem Origins.Native.create (pid : PeerId) (items : List SkbId) :
    Preserves (Origins.Inv h) (createData pid items) :=
  Origins.frame (Origins.create_epoch pid items) (Staged.create pid items)

end Leanux.Proofs.WG.TransmitSecurity.Staged
