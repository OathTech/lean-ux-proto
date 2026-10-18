import Leanux.Proofs.WG.HandshakeSecurity.Projection
import Leanux.Proofs.WG.HandshakeSecurity.ReceiptClaims

namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem write_effect (pid : PeerId) (t : List UInt8) (r : WGRunWitness Unit)
    (valid : r.Valid (writeTimestamp pid t)) :
    ∃ d p, r.before.dev = some d ∧ d.peers[pid]? = some p ∧
      r.after = { r.before with dev := some { d with
        peers := d.peers.insert pid { p with latestTimestamp := t } } } ∧
      r.ambientAfter = r.ambientBefore := by
  change ((writeTimestamp pid t).run r.before).run r.ambientBefore =
    .ok ((r.value, r.after), r.ambientAfter) at valid
  rw [writeTimestamp, MaterialOrigin.bind_ok_ambient] at valid
  obtain ⟨p, read, ambient, getter, setter⟩ := valid
  obtain ⟨rfl, rfl, d, hd, hp⟩ := Queues.getPeer_normal pid r.before read p
    r.ambientBefore ambient getter
  change Except.ok (((), { r.before with dev := (r.before.dev.map (fun d => { d with peers := d.peers.insert pid { p with latestTimestamp := t } })) }),
    r.ambientBefore) = .ok ((r.value, r.after), r.ambientAfter) at setter
  simp only [hd, Option.map_some, Except.ok.injEq, Prod.mk.injEq] at setter
  exact ⟨d, p, hd, hp, setter.1.2.symm, setter.2.symm⟩

theorem receipt_written_view (r : TimestampReceipt) (valid : r.Valid) :
    ∃ p, peerView r.execution.before r.peer = some (handshakeView p) ∧
      peerView r.execution.after r.peer =
        some { handshakeView p with timestamp := r.received } := by
  obtain ⟨d, p, hd, hp, after, _⟩ := write_effect r.peer r.received r.execution valid
  refine ⟨p, ?_, ?_⟩
  · simp [peerView, hd, hp]
  · simp [peerView, after, handshakeView]

theorem stale_timestamp_step (pid : PeerId) (old t : List UInt8) (w : WGWorld)
    (a : Ambient) (stale : memcmp t old ≠ .gt) :
    ((timestampStep pid old t).run w).run a =
      .ok (((), w), CounterWindow.record a .consumeNewerTimestamp false) := by
  have hf : (memcmp t old == .gt) = false := by simp [stale]
  have he := timestamp_erases pid old t w a []
  change (runWGPrefix (timestampObserved pid old t) w a []).1 = _ at he
  rw [timestamp_run] at he
  simpa only [hf, Bool.false_eq_true, ite_false] using he.symm

end Leanux.Proofs.WG.HandshakeSecurity
