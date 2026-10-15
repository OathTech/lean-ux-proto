import Leanux.Proofs.WG.TimerDiscipline.RetryFrames
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
      (fun w => retryAt w pid = some (identity, attempts, timer))
      (fun _ w => retryAt w pid = some (identity, nextAttempts attempts, timer)) := by
  have hq := sendQueuedRetry_retryView pid (identity, attempts + 1, timer)
  have hc := clearEndpoint_retryView pid (identity, attempts + 1, timer)
  have hg := retransmitGiveUp_retryView pid (identity, attempts, timer)
  rw [expiredRetransmit_source, ensures_iff]
  mvcgen [getPeer, getDev, getK, setPeer, modifyDev, modifyK,
    branchCmp, invariant, hq, hc, hg]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [retryAt, retryView, peerAt, nextAttempts]
  all_goals grind only

end Leanux.Proofs.WG.TimerDiscipline
