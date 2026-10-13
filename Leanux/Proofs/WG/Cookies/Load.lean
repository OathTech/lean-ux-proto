import Leanux.Proofs.WG.Cookies.Gate

/-! Constructors for the original under-load result, from the queue threshold
or a still-live recorded decay clock. Signed deadline wrap is retained. -/
namespace Leanux.Proofs.WG.Cookies
open Leanux Leanux.WG Leanux.Proofs.WG.CounterWindow Leanux.Proofs.WG.KeyTimes

theorem load_queue (w u : World) (d : Device) (now : Int64)
    (hd : w.k.wg = some d)
    (hq : d.handshakeQueueLen ≥ MAX_QUEUED_INCOMING_HANDSHAKES / 8)
    (hc : (hiddenClock64 .underLoadNow).run (record w .hsUnderLoad true) = .ok (now, u)) :
    loadPhase.run w = .ok (true, {u with lastUnderLoad := some now}) := by
  have hg : getDev.run w = .ok (d, w) := by simp [getDev, getK, hd]
  simp [loadPhase, StateT.run_bind, hg, hq, hc]
  rfl

theorem load_decay (w u : World) (d : Device) (last now : Int64)
    (hd : w.k.wg = some d)
    (hq : ¬d.handshakeQueueLen ≥ MAX_QUEUED_INCOMING_HANDSHAKES / 8)
    (hl : w.lastUnderLoad = some last)
    (hc : (hiddenClock64 .birthdateExpired).run
      (record (record w .hsUnderLoad false) .hsWasUnderLoad true) = .ok (now, u))
    (hn : ¬deadline last 1 ≤ now) :
    loadPhase.run w = .ok (true,
      recordCmp u .hsDecayExpired false (deadline last 1).toInt now.toInt) := by
  have hg : getDev.run w = .ok (d, w) := by simp [getDev, getK, hd]
  simp only [deadline] at hn
  simp [loadPhase, StateT.run_bind, hg, hq, hl, record, birthdateTest, deadline] at hc ⊢
  simp [hc, hn, deadline]

end Leanux.Proofs.WG.Cookies
