import Leanux.Proofs.WG.Cookies.Gate

/-! Constructors for the original under-load result, from the queue threshold
or a still-live recorded decay clock. Signed deadline wrap is retained. -/
namespace Leanux.Proofs.WG.Cookies
open Leanux Leanux.WG Leanux.Proofs.WG.CounterWindow Leanux.Proofs.WG.KeyTimes

theorem load_queue (w u : World) (d : Device) (now : Int64)
    (hd : w.k.wg = some d)
    (hq : d.handshakeQueueLen ≥ MAX_QUEUED_INCOMING_HANDSHAKES / 8)
    (hc : (hiddenClock64 .underLoadNow).run (recordCmp w .hsUnderLoad true (Int.ofNat d.handshakeQueueLen) (Int.ofNat (MAX_QUEUED_INCOMING_HANDSHAKES / 8))) = .ok (now, u)) :
    loadPhase.run w = .ok (true, {u with lastUnderLoad := some now}) := by
  have hg : getDev.run w = .ok (d, w) := by simp [getDev, getK, hd]
  simp [MAX_QUEUED_INCOMING_HANDSHAKES] at hq hc
  simp [loadPhase, MAX_QUEUED_INCOMING_HANDSHAKES, StateT.run_bind, hg, hq, hc]
  rfl

theorem load_decay (w u : World) (d : Device) (last now : Int64)
    (hd : w.k.wg = some d)
    (hq : ¬d.handshakeQueueLen ≥ MAX_QUEUED_INCOMING_HANDSHAKES / 8)
    (hl : w.lastUnderLoad = some last)
    (hc : (hiddenClock64 .birthdateExpired).run
      (record (recordCmp w .hsUnderLoad false (Int.ofNat d.handshakeQueueLen) (Int.ofNat (MAX_QUEUED_INCOMING_HANDSHAKES / 8))) .hsWasUnderLoad true) = .ok (now, u))
    (hn : ¬deadline last 1 ≤ now) :
    loadPhase.run w = .ok (true,
      recordCmp u .hsDecayExpired false (deadline last 1).toInt now.toInt) := by
  have hg : getDev.run w = .ok (d, w) := by simp [getDev, getK, hd]
  change ¬512 ≤ d.handshakeQueueLen at hq
  simp [MAX_QUEUED_INCOMING_HANDSHAKES] at hc
  simp only [deadline] at hn
  simp [record, recordCmp, hl] at hc
  simp [loadPhase, StateT.run_bind, hg, hq, hl, record, recordCmp, MAX_QUEUED_INCOMING_HANDSHAKES, birthdateTest, deadline, hc, hn]

end Leanux.Proofs.WG.Cookies
