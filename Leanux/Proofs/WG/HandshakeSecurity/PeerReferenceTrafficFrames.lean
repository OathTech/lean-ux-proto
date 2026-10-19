import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceHandshakeFrames
import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveTrafficFrames

/-! Native TX references and queues preserve positivity. Packet allocation,
nonce reservation and normal queue-failure cleanup are included. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Origins TransmitSecurity

theorem peer_get (pid : PeerId) : Preserves Inv (peerGet pid) := by
  simp only [peerGet,requireNotPending,pure_bind]
  apply hoare_bind _ _ (read_saved pid)
  intro p
  have refcount : Preserves (fun w => Inv w ∧ 0 < p.refcount)
      (refcountInc p.refcount : WG.M Unit) := by
    unfold refcountInc
    simp (config := {zeta := false}) only [branch,branchCmp,unsupported]
    repeat' first
      | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
      | rx_retention_step
  apply hoare_bind _ _ refcount
  intro _
  exact hoare_consequence (write_positive pid {p with refcount := p.refcount + 1} (by simp))
    (fun _ before => before.1) (fun _ _ before => before)

macro "peer_reference_traffic_step" : tactic => `(tactic| first
  | (rx_retention_head peerGet; exact peer_get _)
  | (rx_retention_head keypairGet; exact key_get _)
  | (rx_retention_head keypairPut; exact key_put _ _)
  | (rx_retention_head branchExpired; exact world (branchExpired_sameWGWorld _ _ _ _))
  | (rx_retention_head getTxSkb; exact skb _)
  | (rx_retention_head setTxSkb; exact skb _)
  | (rx_retention_head freeTxSkb; exact skb _)
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id Inv
     intro x b
     change Framing.Preserves Inv _)
  | peer_reference_handshake_step)

theorem queued (pid : PeerId) (retry : Bool) :
    Framing.Preserves Inv (sendQueuedHandshakeInitiation pid retry) := by
  unfold sendQueuedHandshakeInitiation
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' peer_reference_traffic_step

theorem choose_cpu (pid : PeerId) :
    Framing.Preserves Inv (cpumaskChooseOnline pid) := by
  unfold cpumaskChooseOnline
  simp (config := {zeta := false}) only [branch,Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' peer_reference_traffic_step

theorem enqueue_peer (item : List SkbId) (state : PacketState) :
    Framing.Preserves Inv (enqueuePerPeerTx item state) := by
  unfold enqueuePerPeerTx
  simp (config := {zeta := false}) only [peekQueuedUnit,recordQueued,invariant]
  repeat' first
    | (rx_retention_head cpumaskChooseOnline; exact choose_cpu _)
    | peer_reference_traffic_step

theorem enqueue_device (pid : PeerId) (item : List SkbId) :
    Framing.Preserves Inv (enqueuePerDeviceAndPeer pid item) := by
  unfold enqueuePerDeviceAndPeer
  cases item with
  | nil => exact hoare_liftAmbient (AmbientM.invariant _) _
  | cons first rest =>
    simp only [List.head?_cons]
    apply preserves_bind (skb _)
    intro _
    apply hoare_bind _ _ (read_saved pid)
    intro p
    apply hoare_bind _ _ (hoare_liftAmbient
      (AmbientM.branch .enqueuePeerQueueFull (p.txQueue.count ≥ MAX_QUEUED_PACKETS)) _)
    intro full
    cases full with
    | true => exact hoare_consequence (preserves_pure _) (fun _ hi => hi.1) (fun _ _ hi => hi)
    | false =>
      apply hoare_bind _ _ (write_saved pid p (fun current =>
        {current with txQueue := p.txQueue.enqueue (first :: rest)}) (fun _ => rfl))
      intro _
      change Framing.Preserves Inv _
      simp (config := {zeta := false}) only [cpumaskNextOnlineFrom,queueDeviceWork,branch]
      repeat' peer_reference_traffic_step

theorem create (pid : PeerId) (item : List SkbId) :
    Framing.Preserves Inv (createData pid item) := by
  unfold createData
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head enqueuePerDeviceAndPeer; exact enqueue_device _ _)
    | (rx_retention_head enqueuePerPeerTx; exact enqueue_peer _ _)
    | peer_reference_traffic_step

theorem reserve (kid : KeypairId) :
    Framing.Preserves Inv (Nonce.reserveNative kid) := by
  unfold Nonce.reserveNative
  repeat' peer_reference_traffic_step

theorem allocate_packets (packets : List DataPacket) :
    Framing.Preserves Inv (packets.mapM newTxSkb) := by
  induction packets with
  | nil => exact preserves_pure _
  | cons p ps ih =>
    simp only [List.mapM_cons]
    exact preserves_bind (skb (SkbStore.newTx p)) (fun id =>
      preserves_bind ih (fun ids => preserves_pure (id :: ids)))

theorem restore (pid : PeerId) (packets : List Packet) :
    Framing.Preserves Inv (do
      setPeer pid {(← getPeer pid) with staged := packets ++ (← getPeer pid).staged}) := by
  apply hoare_bind _ _ (read_saved pid)
  intro p
  apply hoare_bind _ _ (show Framing.Preserves
      (fun w => Inv w ∧ 0 < p.refcount) (getPeer pid) from
    by
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w a result v b hi run
      rw [(getPeer_normal pid w v result a b run).1]
      exact hi)
  intro current
  exact write_saved pid p (fun p => {p with staged := packets ++ current.staged}) (fun _ => rfl)

theorem out_no_key (pid : PeerId) (packets : List Packet) (kid : Option KeypairId)
    (invalid : Bool) :
    Framing.Preserves Inv (stagedOutNokey pid packets kid invalid) := by
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
    | (env_bind_head getPeer; exact restore pid packets)
    | (rx_retention_head sendQueuedHandshakeInitiation; exact queued _ _)
    | peer_reference_traffic_step

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
