import Leanux.Proofs.WG.TransmitSecurity.NonceFrames
import Leanux.Proofs.WG.Lifetimes.TxStaging

/-! Native send refusal and queue operations preserve the allocation history.
Only the reservation block increments the sending counter; releasing a key
removes obligations for its resident state, never its historical allocations. -/
set_option maxHeartbeats 600000
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
namespace Frames

theorem loop {α β : Type} (xs : List α) (b : β) (f : α → β → WG.M (ForInStep β))
    (P : WGWorld → Prop) (hf : ∀ x b, Preserves P (f x b)) :
    Preserves P (forIn xs b f) := by
  induction xs generalizing b with
  | nil => exact preserves_pure b
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply preserves_bind (hf x b)
    intro step
    cases step with
    | done b => exact preserves_pure b
    | yield b => exact ih b

macro "nonce_preserves_step " h:term : tactic => `(tactic| first
  | rxstack_preserves_join
  | (rx_retention_head getPeer; exact native_frame $h (peer_read _))
  | (rx_retention_head getKeypair; exact native_frame $h (key_read _))
  | (rx_retention_head getDev; exact native_frame $h device_read)
  | (rx_retention_head setPeer; exact native_frame $h (peer_write _ _))
  | (rx_retention_head getTxSkb; exact native_frame $h (packet_read _))
  | (rx_retention_head setTxSkb; exact native_frame $h (packet_write _ _))
  | (rx_retention_head freeTxSkb; exact native_frame $h (packet_free _))
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (rx_retention_head WG.peerGet; exact native_frame $h (peerGet _))
  | (rx_retention_head WG.peerPut; exact native_frame $h (peerPut _))
  | (rx_retention_head keypairPut; exact key_put _ _ $h)
  | (rx_retention_head modifyDev
     apply native_frame $h (update _ ?_)
     intro d; rfl)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (allocation_release_lift_from IndexM; exact native_frame $h (index _))
  | (allocation_release_lift_from SkbM; exact native_frame $h (skb _))
  | (first | rx_retention_head throw | rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b hi hr
     cases hr)
  | (rx_retention_head ForIn.forIn; apply loop; intro x b)
  | rx_retention_step)

theorem outNokey (pid : PeerId) (packets : List Packet) (kp : Option KeypairId)
    (invalid : Bool) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (stagedOutNokey pid packets kp invalid) := by
  have tail : Preserves (fun w => Inv (view w) h) (do
      keypairPut kp false
      for _ in packets do _ ← branch .stagedOrphanWalk true
      _ ← branch .stagedOrphanWalk false
      setPeer pid {(← getPeer pid) with staged := packets ++ (← getPeer pid).staged}
      sendQueuedHandshakeInitiation pid false) := by
    simp only [branch]
    repeat' first
      | (rx_retention_head sendQueuedHandshakeInitiation; exact native_frame h (queuedHandshake _ _))
      | nonce_preserves_step h
  cases invalid
  · exact tail
  · cases kp with
    | none => exact hoare_liftAmbient (AmbientM.invariant _) _
    | some id =>
      have write := native_frame h (update_key id
        (fun k => {k with sending := {k.sending with isValid := false}}) (fun _ => rfl))
      simpa only [stagedOutNokey,bind_assoc,Bool.true_eq,↓reduceIte] using preserves_bind write (fun _ => tail)

theorem chooseCpu (pid : PeerId) : SameView view (cpumaskChooseOnline pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold cpumaskChooseOnline
  simp only [branch,Nat.mod_one,Std.Legacy.Range.forIn_eq_forIn_range',
    show (Std.Legacy.Range.mk 0 0 1 (by decide)).size = 0 from rfl,
    List.range'_zero,List.forIn_nil,pure_bind]
  repeat' nonce_frame_step initial

theorem enqueuePeer (item : List SkbId) (state : PacketState) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (enqueuePerPeerTx item state) := by
  unfold enqueuePerPeerTx
  simp only [invariant,peekQueuedUnit,recordQueued]
  repeat' first
    | (rx_retention_head cpumaskChooseOnline; exact native_frame h (chooseCpu _))
    | nonce_preserves_step h

theorem enqueueDevice (pid : PeerId) (item : List SkbId) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (enqueuePerDeviceAndPeer pid item) := by
  unfold enqueuePerDeviceAndPeer cpumaskNextOnlineFrom
  simp only [branch,invariant,queueDeviceWork]
  repeat' nonce_preserves_step h

theorem create (pid : PeerId) (item : List SkbId) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (createData pid item) := by
  unfold createData
  simp only [branch,invariant]
  repeat' first
    | (rx_retention_head enqueuePerDeviceAndPeer; exact enqueueDevice _ _ h)
    | (rx_retention_head enqueuePerPeerTx; exact enqueuePeer _ _ h)
    | nonce_preserves_step h

end Frames
end Leanux.Proofs.WG.TransmitSecurity.Nonce
