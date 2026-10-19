import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveAllocation
import Leanux.Proofs.WG.HandshakeSecurity.TimestampDriverSource

/-! Actual send-side timestamp archive frames. Queue writes use native saved
peer reads; nonce/key updates and packet allocation leave this projection alone. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Origins TransmitSecurity
set_option maxHeartbeats 800000

theorem peer_get (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (peerGet pid) := by
  simp only [peerGet,requireNotPending,pure_bind]
  apply hoare_bind _ _ (read_saved pid history)
  intro p
  have refcount (P : WGWorld → Prop) : Framing.Preserves P (refcountInc p.refcount : WG.M Unit) := by
    unfold refcountInc
    simp (config := {zeta := false}) only [branch,branchCmp,unsupported]
    repeat' first
      | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ P)
      | rx_retention_step
  apply hoare_bind _ _ (refcount _)
  intro _
  exact write_saved pid p (fun current => {current with refcount := p.refcount + 1})
    (fun _ => ⟨rfl,rfl⟩) history

macro "archive_traffic_step " history:term : tactic => `(tactic| first
  | (rx_retention_head peerGet; exact peer_get _ $history)
  | (rx_retention_head keypairGet; exact key_get _ $history)
  | (rx_retention_head keypairPut; exact key_put _ _ $history)
  | (rx_retention_head branchExpired; exact frame_world $history _ (branchExpired_sameWGWorld _ _ _ _))
  | (rx_retention_head getTxSkb; exact skb _ $history)
  | (rx_retention_head setTxSkb; exact skb _ $history)
  | (rx_retention_head freeTxSkb; exact skb _ $history)
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (StateInv $history)
     intro x b
     change Framing.Preserves (StateInv $history) _)
  | archive_handshake_step $history)

theorem queued (pid : PeerId) (retry : Bool) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (sendQueuedHandshakeInitiation pid retry) := by
  unfold sendQueuedHandshakeInitiation
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' archive_traffic_step history

theorem choose_cpu (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (cpumaskChooseOnline pid) := by
  unfold cpumaskChooseOnline
  simp (config := {zeta := false}) only [branch,Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' archive_traffic_step history

theorem enqueue_peer (item : List SkbId) (state : PacketState) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (enqueuePerPeerTx item state) := by
  unfold enqueuePerPeerTx
  simp (config := {zeta := false}) only [peekQueuedUnit,recordQueued,invariant]
  repeat' first
    | (rx_retention_head cpumaskChooseOnline; exact choose_cpu _ history)
    | archive_traffic_step history

theorem enqueue_device (pid : PeerId) (item : List SkbId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (enqueuePerDeviceAndPeer pid item) := by
  unfold enqueuePerDeviceAndPeer
  cases item with
  | nil => exact hoare_liftAmbient (AmbientM.invariant _) _
  | cons first rest =>
    simp only [List.head?_cons]
    apply preserves_bind (skb _ history)
    intro _
    apply hoare_bind _ _ (read_saved pid history)
    intro p
    apply hoare_bind _ _ (hoare_liftAmbient
      (AmbientM.branch .enqueuePeerQueueFull (p.txQueue.count ≥ MAX_QUEUED_PACKETS)) _)
    intro full
    cases full with
    | true => exact hoare_consequence (preserves_pure _) (fun _ hi => hi.1) (fun _ _ hi => hi)
    | false =>
      apply hoare_bind _ _ (write_saved pid p (fun current =>
        {current with txQueue := p.txQueue.enqueue (first :: rest)}) (fun _ => ⟨rfl,rfl⟩) history)
      intro _
      change Framing.Preserves (StateInv history) _
      simp (config := {zeta := false}) only [cpumaskNextOnlineFrom,queueDeviceWork,branch]
      repeat' archive_traffic_step history

theorem create (pid : PeerId) (item : List SkbId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (createData pid item) := by
  unfold createData
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head enqueuePerDeviceAndPeer; exact enqueue_device _ _ history)
    | (rx_retention_head enqueuePerPeerTx; exact enqueue_peer _ _ history)
    | archive_traffic_step history

theorem reserve (kid : KeypairId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (Nonce.reserveNative kid) := by
  unfold Nonce.reserveNative
  repeat' archive_traffic_step history

theorem allocate_packets (packets : List DataPacket) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (packets.mapM newTxSkb) := by
  induction packets with
  | nil => exact preserves_pure _
  | cons p ps ih =>
    simp only [List.mapM_cons]
    exact preserves_bind (skb (SkbStore.newTx p) history) (fun id =>
      preserves_bind ih (fun ids => preserves_pure (id :: ids)))

theorem restore (pid : PeerId) (packets : List Packet) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (do
      setPeer pid {(← getPeer pid) with staged := packets ++ (← getPeer pid).staged}) := by
  apply hoare_bind _ _ (read_saved pid history)
  intro p
  apply hoare_bind _ _ (show Framing.Preserves
      (fun w => StateInv history w ∧ Responder.SavedNativePeer pid p w) (getPeer pid) from
    by
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w a result v b hi run
      rw [(getPeer_normal pid w v result a b run).1]
      exact hi)
  intro current
  exact write_saved pid p (fun p => {p with staged := packets ++ current.staged}) (fun _ => ⟨rfl,rfl⟩) history

theorem out_no_key (pid : PeerId) (packets : List Packet) (kid : Option KeypairId)
    (invalid : Bool) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (stagedOutNokey pid packets kid invalid) := by
  have factor : stagedOutNokey pid packets kid invalid = (do
      if invalid then
        let some id := kid | invariant "unreachable"
        let k ← getKeypair id
        setKeypair id {k with sending := {k.sending with isValid := false}}
      keypairPut kid false
      for _ in packets do _ ← branch .stagedOrphanWalk true
      _ ← branch .stagedOrphanWalk false
      (do setPeer pid {(← getPeer pid) with staged := packets ++ (← getPeer pid).staged})
      sendQueuedHandshakeInitiation pid false) := by
    cases invalid <;> cases kid <;>
      simp only [stagedOutNokey,Bool.false_eq_true,ite_false,ite_true,bind_assoc]
  rw [factor]
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (env_bind_head getPeer; exact restore pid packets history)
    | (rx_retention_head sendQueuedHandshakeInitiation; exact queued _ _ history)
    | archive_traffic_step history

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
