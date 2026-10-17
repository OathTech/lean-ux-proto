import Leanux.Proofs.WG.TimerDiscipline.FireUnitSource
import Leanux.Proofs.WG.TimerDiscipline.Model
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env

/-- Arbitrary malformed metadata: actual wheel selection and an accepted unit
prefix do not entail a logical expiry. No reachability or completed-callback claim. -/
theorem dispatch_prefix_without_logical_expiry :
    ∃ (d : Device) (p : Peer) (we : WheelEntry),
      d.peers[0]? = some p ∧ d.peerList = [0] ∧
      p.timerRetransmitHandshake = none ∧ duePeers d .retransmitHandshake 2 = [] ∧
      TimerWheel.nextDue d 2 = some (0, .retransmitHandshake, we) ∧
      Campaign2.Product.Observes
        (timerDispatchPrefix_variant .timerRetransmit 0 .retransmitHandshake we none)
        (fun initial => initial.wg.device = some d ∧ initial.ambient.hidden = none)
        (fun initial out => out = .ok ((), initial)) := by
  let we : WheelEntry := ⟨0, 1, 1⟩
  let p : Peer := {
    remoteStatic := [], presharedKey := [], precomputedStaticStatic := []
    internalId := 0, wheelRetransmitHandshake := some we}
  let d : Device := {
    ifindex := 0, ifname := "wg0", peerList := [0]
    peers := ({} : Std.TreeMap PeerId Peer).insert 0 p}
  refine ⟨d, p, we, by simp [d], rfl, rfl, ?_, ?_, ?_⟩
  · simp [duePeers, d, p, Peer.timer]
  · simp [TimerWheel.nextDue, TimerWheel.due, d, p, PeerTimer.all, Peer.wheel, we,
      timeBeforeEq, timeAfterEq]
  · intro initial pre
    have hidden : initial.ambient.hidden = none := pre.2
    have absentPeek : (peekUnit .timerRetransmit : Leanux.M (Option Nat)).run initial =
        .ok (none, initial) := by
      change ((AmbientM.peekUnit .timerRetransmit).run initial.ambient >>= _) = _
      have native : (AmbientM.peekUnit .timerRetransmit).run initial.ambient =
          .ok (none, initial.ambient) := by
        simp [AmbientM.peekUnit, AmbientM.skipAmbient, hidden]
        rfl
      rw [native]
      rfl
    have actual : (timerDispatchPrefix_variant .timerRetransmit 0 .retransmitHandshake we none).run initial =
        .ok ((), initial) := by
      have worker : timerWorker .retransmitHandshake = pure Worker.timerRetransmit := rfl
      simp only [timerDispatchPrefix_variant, worker, pure_bind]
      change ((do
        if let some unit ← (peekUnit .timerRetransmit : Leanux.M (Option Nat)) then
          match (← (getWG : Leanux.M WGWorld)).timerUnits.find? (·.1 == unit) with
          | some (_, picked, timer) =>
            if picked != 0 || timer != .retransmitHandshake then
              throw (.hidden s!"the wheel runs peer {0}'s {repr PeerTimer.retransmitHandshake} timer next; the section names peer {picked}'s {repr timer}")
          | none => throw (.hidden s!"a section of {Worker.timerRetransmit.symbol} for a timer the mirror never armed ({unit})")
        pure () : Leanux.M Unit).run initial) = _
      rw [StateT.run_bind, absentPeek]
      rfl
    rw [actual]
    rfl

end Leanux.Proofs.WG.TimerDiscipline
