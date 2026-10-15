import Leanux.Proofs.WG.TimerDiscipline.SectionFrames
import Leanux.Proofs.WG.TimerDiscipline.FireSource
import Leanux.Proofs.WG.Noise.KernelFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

def retryKernel (k : Kernel) (pid : PeerId) : Option RetryView :=
  (k.wg.bind fun d => d.peers[pid]?).map retryView

theorem detach_retransmit (pid : PeerId) (identity attempts : Nat) (timer : Option UInt64) :
    ⦃fun w => ⌜retryAt w pid = some (identity, attempts, timer)⌝⦄ delTimer pid .retransmitHandshake
      ⦃⇓? _ w => ⌜retryAt w pid = some (identity, attempts, none)⌝⦄ := by
  mvcgen [delTimer, getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [retryAt, retryView, peerAt, Peer.setTimer]
  all_goals grind only

theorem fireSelected_retransmit (pid : PeerId) (identity attempts : Nat) (timer : Option UInt64) :
    Ensures (fireSelected .timerRetransmit pid .retransmitHandshake)
      (fun w => retryAt w pid = some (identity, attempts, timer))
      (fun _ w => retryAt w pid = some (identity, nextAttempts attempts, none)) := by
  have hd := detach_retransmit pid identity attempts timer
  have hc := (ensures_iff _ _ _).mp (expiredRetransmit_retryView pid identity attempts none)
  have hs := runTimerSection_kernel_contract .timerRetransmit (expiredRetransmitHandshake pid)
    (fun k => retryKernel k pid = some (identity, attempts, none))
    (fun k => retryKernel k pid = some (identity, nextAttempts attempts, none)) hc
  rw [ensures_iff]
  simp only [fireSelected, timerCallback]
  mvcgen [hd, hs]

end Leanux.Proofs.WG.TimerDiscipline
