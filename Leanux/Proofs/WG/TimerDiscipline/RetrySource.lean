import Leanux.Proofs.WG.TimerDiscipline.RetryFrames
import Leanux.Proofs.WG.TimerDiscipline.Model
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

theorem expiredRetransmit_source (pid : PeerId) :
    expiredRetransmitHandshake pid = (do
      let attempts := (← getPeer pid).timerHandshakeAttempts
      if ← branchCmp .retransmitGiveUp (attempts > MAX_TIMER_HANDSHAKES) attempts MAX_TIMER_HANDSHAKES then
        retransmitGiveUp pid
      else
        let p ← getPeer pid
        setPeer pid { p with timerHandshakeAttempts := p.timerHandshakeAttempts + 1 }
        clearPeerEndpointSrc pid
        sendQueuedHandshakeInitiation pid true) := rfl

theorem expiredRetransmit_retryView (pid : PeerId) (identity attempts : Nat)
    (timer : Option UInt64) :
    Ensures (expiredRetransmitHandshake pid)
      (fun g => retryAt g pid = some (identity, attempts, timer))
      (fun _ g => retryAt g pid = some (identity, nextAttempts attempts, timer)) := by
  rw [expiredRetransmit_source]
  let P : WGWorld → Prop := fun g => retryAt g pid = some (identity, attempts, timer)
  let Q : Unit → WGWorld → Prop := fun _ g => retryAt g pid = some (identity, nextAttempts attempts, timer)
  change Ensures _ P Q
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid P)) ?_
  intro p g ambient result final after pre run
  have value : retryView p = (identity, attempts, timer) := by
    simpa [P, retryAt, pre.2] using pre.1
  have count : p.timerHandshakeAttempts = attempts := congrArg (fun n : RetryView => n.2.1) value
  change (((if decide (p.timerHandshakeAttempts > MAX_TIMER_HANDSHAKES) then retransmitGiveUp pid else do
    let p ← getPeer pid
    setPeer pid {p with timerHandshakeAttempts := p.timerHandshakeAttempts + 1}
    clearPeerEndpointSrc pid
    sendQueuedHandshakeInitiation pid true).run g).run _) = _ at run
  by_cases exceeded : attempts > MAX_TIMER_HANDSHAKES
  · simp only [count, exceeded, decide_true, ite_true] at run
    have done := (ensures_iff _ _ _).mpr (retransmitGiveUp_retryView pid (identity, attempts, timer))
      g _ result final after pre.1 run
    simpa [Q, nextAttempts, exceeded] using done
  · simp only [count, exceeded, decide_false, Bool.false_eq_true, ite_false] at run
    have increment : Ensures (do
        let p ← getPeer pid
        setPeer pid {p with timerHandshakeAttempts := p.timerHandshakeAttempts + 1})
        P (fun _ g => retryAt g pid = some (identity, attempts + 1, timer)) := by
      refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid P)) ?_
      intro peer start inputs out done last hp hr
      have fields : retryView peer = (identity, attempts, timer) := by
        simpa [P, retryAt, hp.2] using hp.1
      cases hr
      cases device : start.dev with
      | none => simp [peerAt, device] at hp
      | some d =>
        simp only [retryView, Prod.mk.injEq] at fields
        simp [retryAt, peerAt, device, retryView, fields.1, fields.2.1, fields.2.2]
    have continued : Ensures (do
        (do let p ← getPeer pid; setPeer pid {p with timerHandshakeAttempts := p.timerHandshakeAttempts + 1})
        clearPeerEndpointSrc pid
        sendQueuedHandshakeInitiation pid true) P
        (fun _ g => retryAt g pid = some (identity, attempts + 1, timer)) :=
      ensures_bind _ _ increment (fun _ => ensures_bind _ _
        ((ensures_iff _ _ _).mpr (clearEndpoint_retryView pid (identity, attempts + 1, timer)))
        (fun _ => (ensures_iff _ _ _).mpr (sendQueuedRetry_retryView pid (identity, attempts + 1, timer))))
    have execution := continued g _ result final after pre.1 (by simpa only [bind_assoc] using run)
    simpa [Q, nextAttempts, exceeded] using execution

end Leanux.Proofs.WG.TimerDiscipline
