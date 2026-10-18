import Leanux.Proofs.WG.Index.TimerCoreFrames
import Leanux.Proofs.WG.Index.StagingIndexSource
import Leanux.Proofs.WG.Index.CallbackRulesSource
import Leanux.Proofs.WG.Queues.HolderTimerCallbacks

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.TimerCore
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem queued_core (pid : PeerId) (retry : Bool) :
    Ensures (sendQueuedHandshakeInitiation pid retry) Reached.Core (fun _ => Reached.Core) := by
  intro w a result v b core run
  obtain ⟨delta,step⟩ := (Transfers.iff_run_ambient _).mp (sendQueued_transfers pid retry)
    w a result v b run
  exact StagingRich.core_handoff ((ensures_iff _ _ _).mpr
    (StagingRich.sendQueuedHandshakeInitiation_rich pid retry w)
      w a result v b (StagingRich.refl w) run) step core

theorem queued (pid : PeerId) (retry : Bool) :
    Ensures (sendQueuedHandshakeInitiation pid retry) Ready (fun _ => Ready) :=
  ready_of_core _ (CurrentSlots.sendQueuedHandshakeInitiation_preserves pid retry)
    (queued_core pid retry)

theorem keepalive (pid : PeerId) :
    Ensures (sendKeepalive pid) Ready (fun _ => Ready) := by
  intro w a result v b pre run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.SlotTimers.«0».Leanux.Proofs.WG.CurrentSlots.Timer.keepalive) pid)
    w a result v b pre.1 run,StagingRich.keepalive_core pid w a result v b pre run⟩

theorem contracts (pid : PeerId) : CallbackRules.Contracts pid Ready (Held pid) :=
  ⟨update pid _ (fun _ => rfl) (fun _ => rfl),
   update pid _ (fun _ => rfl) (fun _ => rfl),
   endpoint pid,purge pid,del pid .sendKeepalive,
   fun site timer delay => arm site pid timer delay,
   queued pid,keepalive pid,acquire pid,repay pid,enqueue pid⟩

theorem callback (pid : PeerId) (timer : PeerTimer) :
    Ensures (timerCallback pid timer) Ready (fun _ => Ready) :=
  CallbackRules.callback (contracts pid) timer

theorem callback_boundary (pid : PeerId) (timer : PeerTimer)
    (cs : Ledger) (loans : Reservations) :
    Ensures (timerCallback pid timer)
      (fun w => DurableHolders.Boundary cs loans w ∧ Ready w)
      (fun _ w => DurableHolders.Boundary cs loans w ∧ Ready w) := by
  intro w a result v b pre run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (HolderTimers.callback_boundary pid timer)
    w a result v b pre.1 run, callback pid timer w a result v b pre.2 run⟩

end Leanux.Proofs.WG.Index.TimerCore
