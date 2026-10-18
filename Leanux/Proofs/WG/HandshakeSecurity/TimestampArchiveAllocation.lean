import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveHandshake

/-! Actual peer creation starts a fresh timestamp incarnation while keeping the
archive of deleted allocations. Saved writes use their real getter witness. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Origins

theorem reset_sent (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (resetLastSentHandshake pid) := by
  unfold resetLastSentHandshake
  simp (config := {zeta := false}) only [hiddenClock64]
  repeat' archive_handshake_step history

theorem precompute (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (precomputeStaticStatic pid) := by
  let P := StateInv history
  have ambient {α : Type} (a : AmbientM α) (Q : WGWorld → Prop) :
      Framing.Preserves Q (StateT.lift a) := hoare_liftAmbient a Q
  have clear : Framing.Preserves P (do
      let current ← getPeer pid
      setPeer pid {current with precomputedStaticStatic := List.replicate 32 0}) :=
    update_peer pid (fun p => {p with precomputedStaticStatic := List.replicate 32 0}) (fun _ => ⟨rfl,rfl⟩) history
  simp only [precomputeStaticStatic,requireNotPending,pure_bind]
  apply hoare_bind _ _ (frame_store history _ getDev_sameWGStore)
  intro d
  apply hoare_bind _ _ (read_saved pid history)
  intro p
  apply hoare_bind _ _ (ambient (AmbientM.branch .precomputeNoIdentity !d.staticIdentity.hasIdentity)
    (fun w => P w ∧ Responder.SavedNativePeer pid p w))
  intro noIdentity
  cases noIdentity with
  | true => exact hoare_consequence clear (fun _ h => h.1) (fun _ _ h => h)
  | false =>
    apply hoare_bind _ _ (write_saved pid p (fun current => {current with precomputedStaticStatic :=
      (curve25519 d.staticIdentity.staticPrivate p.remoteStatic).1}) (fun _ => ⟨rfl,rfl⟩) history)
    intro _
    apply preserves_bind (ambient (AmbientM.branch .precomputeNullPoint
      !(curve25519 d.staticIdentity.staticPrivate p.remoteStatic).2) P)
    intro zero
    cases zero
    · exact preserves_pure _
    · exact clear

theorem handshake_init (pid : PeerId) (psk : Option Key) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (handshakeInit pid psk) := by
  unfold handshakeInit
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head IndexOwner.setPeerWord; exact owner_write _ _ history)
    | (rx_retention_head precomputeStaticStatic; exact precompute _ history)
    | archive_handshake_step history

theorem cache_reset (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (dstCacheReset pid) := by
  unfold dstCacheReset
  simp (config := {zeta := false}) only [hiddenJiffies]
  repeat' first
    | (rx_retention_head getAmbient; exact hoare_liftAmbient (get : AmbientM Ambient) _)
    | archive_handshake_step history

theorem creation_core (pid : PeerId) (key : Key) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (Peers.peerCreateCore pid key) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  rw [Peers.peerCreateCore_run] at run
  cases run
  exact state_allocate hi pid key

/-- The entire native peer constructor preserves the allocation-indexed archive,
including numeric slot reuse. It assumes no allocation-core contract. -/
theorem peer_create (key : Key) (psk : Option Key) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (peerCreate key psk) := by
  rw [← Peers.peerCreateFactored_eq]
  unfold Peers.peerCreateFactored
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenAlloc]
  repeat' first
    | (rx_retention_head Peers.peerCreateCore; exact creation_core _ _ history)
    | (rx_retention_head dstCacheReset; exact cache_reset _ history)
    | (rx_retention_head handshakeInit; exact handshake_init _ _ history)
    | (rx_retention_head resetLastSentHandshake; exact reset_sent _ history)
    | archive_handshake_step history

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
