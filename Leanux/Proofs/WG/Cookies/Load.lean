import Leanux.Proofs.WG.Cookies.Gate

/-! Constructors for the original under-load result, from the queue threshold
or a still-live recorded decay clock. Signed deadline wrap is retained. -/
namespace Leanux.Proofs.WG.Cookies
open Leanux Leanux.WG Leanux.Proofs.WG.CounterWindow Leanux.Proofs.WG.KeyTimes

theorem load_queue (w u : WGWorld) (a b : Ambient) (d : Device) (now : Int64)
    (hd : w.dev = some d)
    (hq : d.handshakeQueueLen ≥ MAX_QUEUED_INCOMING_HANDSHAKES / 8)
    (hc : (((hiddenClock64 .underLoadNow : WG.M Int64).run w).run
      (recordCmp a .hsUnderLoad true (Int.ofNat d.handshakeQueueLen)
        (Int.ofNat (MAX_QUEUED_INCOMING_HANDSHAKES / 8)))) = .ok ((now, u), b)) :
    (loadPhase.run w).run a = .ok ((true, {u with lastUnderLoad := some now}), b) := by
  have hg (ambient : Ambient) : (getDev.run w).run ambient = .ok ((d, w), ambient) := by
    simp [getDev, hd]
  simp [MAX_QUEUED_INCOMING_HANDSHAKES] at hq hc
  simp [loadPhase, MAX_QUEUED_INCOMING_HANDSHAKES, StateT.run_bind, hg, hq, hc,
    branchCmp, branchCmp_run]
  rfl

theorem load_decay (w u : WGWorld) (a b : Ambient) (d : Device) (last now : Int64)
    (hd : w.dev = some d)
    (hq : ¬d.handshakeQueueLen ≥ MAX_QUEUED_INCOMING_HANDSHAKES / 8)
    (hl : w.lastUnderLoad = some last)
    (hc : (((hiddenClock64 .birthdateExpired : WG.M Int64).run w).run
      (record (recordCmp a .hsUnderLoad false (Int.ofNat d.handshakeQueueLen)
        (Int.ofNat (MAX_QUEUED_INCOMING_HANDSHAKES / 8))) .hsWasUnderLoad true)) =
      .ok ((now, u), b))
    (hn : ¬deadline last 1 ≤ now) :
    (loadPhase.run w).run a = .ok ((true, u),
      recordCmp b .hsDecayExpired false (deadline last 1).toInt now.toInt) := by
  have hg (ambient : Ambient) : (getDev.run w).run ambient = .ok ((d, w), ambient) := by
    simp [getDev, hd]
  change ¬512 ≤ d.handshakeQueueLen at hq
  simp [MAX_QUEUED_INCOMING_HANDSHAKES] at hc
  simp only [deadline] at hn
  simp [record, recordCmp] at hc
  simp [loadPhase, StateT.run_bind, hg, hq, hl, record, recordCmp,
    MAX_QUEUED_INCOMING_HANDSHAKES, birthdateTest, deadline, hc, hn,
    branch, branchCmp, branch_run, branchCmp_run]

end Leanux.Proofs.WG.Cookies
