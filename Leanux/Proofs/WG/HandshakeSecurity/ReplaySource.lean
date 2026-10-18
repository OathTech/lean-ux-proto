import Leanux.Proofs.WG.HandshakeSecurity.Source

/-! The authenticated initiation suffix, beginning at the timestamp comparison.
The flood clock is read before the replay branch; replay short-circuits the
flood comparison and reaches only the original failed-consumption release. -/
namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG Leanux.Proofs.Logged

def replayRefusal (peer : Option PeerId) : WG.M (Option PeerId) := do
  let _ ← hiddenClock64 .floodNow
  let _ ← branch .consumeReplay true
  Queues.RxCredits.HandshakeLoans.initiationOut peer none

private theorem native_branch (decision : Decision) (value : Bool) (w : WGWorld) (a : Ambient) :
    ((branch decision value : WG.M Bool).run w).run a =
      .ok ((value, w), CounterWindow.record a decision value) := rfl

theorem checked_stale (msg e ck hash t : List UInt8) (peer : Option PeerId)
    (pid : PeerId) (p : Peer) (stale : memcmp t p.latestTimestamp ≠ .gt) :
    checkedWith (fun a => a) timestampStep msg e ck hash t peer pid p = replayRefusal peer := by
  have hb : (memcmp t p.latestTimestamp != .gt) = true := by simp [stale]
  funext w a
  simp only [checkedWith, replayRefusal, hb, WG.orM]
  rfl

theorem replayRefusal_returns_none (peer : Option PeerId) (w v : WGWorld)
    (a b : Ambient) (result : Option PeerId)
    (run : ((replayRefusal peer).run w).run a = .ok ((result, v), b)) :
    result = none := by
  rw [replayRefusal, MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨now, read, clockAmbient, _, rest⟩ := run
  simp only [StateT.run_bind, native_branch, CounterWindow.except_ok_bind] at rest
  unfold Queues.RxCredits.HandshakeLoans.initiationOut at rest
  simp only [Option.isNone_none, StateT.run_bind, native_branch,
    CounterWindow.except_ok_bind, ite_true] at rest
  cases hr : ((peerPut peer).run read).run
      (CounterWindow.record (CounterWindow.record clockAmbient .consumeReplay true) .consumeFailedPut true) with
  | error stop => simp [hr] at rest
  | ok out =>
    rcases out with ⟨⟨x, state⟩, ambient⟩
    simp only [hr, CounterWindow.except_ok_bind] at rest
    cases rest
    rfl

end Leanux.Proofs.WG.HandshakeSecurity
