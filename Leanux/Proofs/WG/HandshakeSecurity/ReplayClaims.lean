import Leanux.Proofs.WG.HandshakeSecurity.ReplaySource
import Leanux.Proofs.WG.HandshakeSecurity.RetentionFrames

namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing

private theorem native_branch (decision : Decision) (value : Bool) (w : WGWorld) (a : Ambient) :
    ((branch decision value : WG.M Bool).run w).run a =
      .ok ((value, w), CounterWindow.record a decision value) := rfl

theorem replayRefusal_retains (peer : Option PeerId) (w v : WGWorld)
    (a b : Ambient) (result : Option PeerId)
    (run : ((replayRefusal peer).run w).run a = .ok ((result, v), b)) :
    RetainsHandshake w v := by
  rw [replayRefusal, MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨now, read, clockAmbient, clock, rest⟩ := run
  have unchanged : read = w := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.hiddenClock64 .floodNow) (fun g : WGWorld => g = w))
    w a now read clockAmbient rfl clock
  subst read
  simp only [StateT.run_bind, native_branch, CounterWindow.except_ok_bind] at rest
  unfold Queues.RxCredits.HandshakeLoans.initiationOut at rest
  simp only [Option.isNone_none, StateT.run_bind, native_branch,
    CounterWindow.except_ok_bind, ite_true] at rest
  cases hr : ((peerPut peer).run w).run
      (CounterWindow.record (CounterWindow.record clockAmbient .consumeReplay true) .consumeFailedPut true) with
  | error stop => simp [hr] at rest
  | ok out =>
    rcases out with ⟨⟨x, state⟩, ambient⟩
    simp only [hr, CounterWindow.except_ok_bind] at rest
    cases rest
    exact peerPut_retains_handshake peer w _ _ _ x hr

theorem checked_stale_result (msg e ck hash t : List UInt8) (peer : Option PeerId)
    (pid : PeerId) (p : Peer) (w v : WGWorld) (a b : Ambient) (result : Option PeerId)
    (stale : memcmp t p.latestTimestamp ≠ .gt)
    (run : ((checkedWith (fun a => a) timestampStep msg e ck hash t peer pid p).run w).run a =
      .ok ((result, v), b)) :
    result = none ∧ RetainsHandshake w v := by
  rw [checked_stale msg e ck hash t peer pid p stale] at run
  exact ⟨replayRefusal_returns_none peer w v a b result run,
    replayRefusal_retains peer w v a b result run⟩

end Leanux.Proofs.WG.HandshakeSecurity
