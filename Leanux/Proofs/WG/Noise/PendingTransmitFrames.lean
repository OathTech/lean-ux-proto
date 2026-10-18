import Leanux.Proofs.WG.Noise.PendingMaintenanceSource
import Leanux.Proofs.WG.Noise.PendingPollFrames
import Leanux.Proofs.WG.Queues.CurrentSlotTransmit
import Leanux.Proofs.WG.Origins.CurrentEnvironment
import Leanux.Proofs.WG.TimerDiscipline.DataDoneSource
import Leanux.Proofs.WG.TimerDiscipline.ArmingPrefixesSource
import Leanux.Proofs.WG.Noise.PendingTimerFrames

/-! The original encrypted-data completion and transmit step retain pending
allocation history on normal return. Source order and final releasing puts
are preserved; no incoming session-history or successful-run premise is added. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingTickets
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing TimerDiscipline Std.Do

theorem send4_cached_frame (pid : PeerId) (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) :
    SameView view (send4 e (some pid) bytes ds exactRx) :=
  frame_from_sendWork _ pid (send4_sendWorkView pid e bytes ds exactRx)
    (Keypairs.WGFrames.send4_sameSnapshot e (some pid) bytes ds exactRx)

theorem send6_cached_frame (pid : PeerId) (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) :
    SameView view (send6 e (some pid) bytes ds exactRx) :=
  frame_from_sendWork _ pid (send6_sendWorkView pid e bytes ds exactRx)
    (Keypairs.WGFrames.send6_sameSnapshot e (some pid) bytes ds exactRx)

theorem timersDataSent_frame (pid : PeerId) : SameView view (timersDataSent pid) := by
  have read : SameView view (getPeer pid) := by
    intro initial
    exact hoare_consequence (getPeer_spec pid (fun w => view w = initial))
      (fun _ h => h) (fun _ _ h => h.1)
  rw [dataSent_source]
  unfold dataSentPrefix
  simp only [bind_assoc]
  apply read.bind
  intro p
  apply (frame_ambient (AmbientM.branch .timersDataSentNotPending !(p.timerPending .newHandshake))).bind
  intro ready
  cases ready with
  | false => exact SameView.pure view ()
  | true =>
    unfold jitteredArm
    exact ((callerJiffies_sameWGWorld .timerJiffiesDataSent).factor view).bind (fun caller =>
      ((jitterBelowRekeyTimeout_sameWGWorld .newHandshakeJitter).factor view).bind (fun jitter =>
        guardedArm_pending_frame pid .newHandshake
          (KEEPALIVE_TIMEOUT_TICKS + REKEY_TIMEOUT_TICKS + jitter) caller))

end Leanux.Proofs.WG.Noise.PendingTickets
