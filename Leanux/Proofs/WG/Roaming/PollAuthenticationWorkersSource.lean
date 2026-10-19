import Leanux.Proofs.WG.Roaming.PollAuthenticationQuietSource
import Leanux.Proofs.WG.Packets.PublicationWorkers
import Leanux.Proofs.WG.Packets.PublicationEncrypt
import Leanux.Proofs.WG.Packets.PublicationHandshakeObserved
import Leanux.Proofs.WG.Packets.PublicationTransmit

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.PollAuthentication
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Queues Lifetimes
variable {α : Type}

theorem pending :
    PrefixPreserves Reached PublicSafe
      (RxHistory.mixed (liftWGObserver RxNapi.pendingPrefix)) :=
  mixed _
    (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationWorkers.«0».Leanux.Proofs.WG.PublicationJoint.pending)

theorem scheduled :
    PrefixPreserves Reached PublicSafe
      (RxHistory.mixed (liftWGObserver RxNapi.scheduledPrefix)) :=
  mixed _
    (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationWorkers.«0».Leanux.Proofs.WG.PublicationJoint.scheduled)

theorem napiSoftirq : PrefixPreserves Reached PublicSafe RxHistory.napiSoftirq :=
  RxNapi.softirq_preserves reached_safe reached_store pending observePoll

theorem pollScheduledInline : PrefixPreserves Reached PublicSafe RxHistory.pollScheduledInline :=
  RxNapi.inline_preserves reached_safe reached_store pending observePoll

theorem napiIrqExit : PrefixPreserves Reached PublicSafe RxHistory.napiIrqExit :=
  RxNapi.irqExit_preserves reached_safe reached_store scheduled napiSoftirq

theorem prepare : PrefixPreserves Reached PublicSafe Origins.HistoryAdapters.prepare :=
  origin _ PublicationJoint.prepare

theorem receiveStep : PrefixPreserves Reached PublicSafe Origins.HistoryAdapters.receiveStep :=
  origin _ PublicationJoint.receiveStep

theorem receiveIteration :
    PrefixPreserves Reached PublicSafe Origins.HistoryAdapters.receiveIteration := by
  apply workerIterPrefix_preserves _ _ reached_safe receiveStep
  exact quiet_store _ (condResched_sameKernel .receiveWorker)

theorem repay (pid : PeerId) :
    PrefixPreserves Reached PublicSafe
      (RxHistory.mixed (liftWGObserver (peerPutMixed (some pid)))) :=
  mixed _
    ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationWorkers.«0».Leanux.Proofs.WG.PublicationJoint.pay) pid)

theorem decryptStep : PrefixPreserves Reached PublicSafe RxHistory.decryptStep := by
  unfold RxHistory.decryptStep RxWorkers.decryptWith
  apply PrefixPreserves.bind napiSoftirq
  intro _
  apply PrefixPreserves.bind prepare
  intro result
  cases result with
  | none => exact PrefixPreserves.pure reached_safe false
  | some pid =>
    exact napiIrqExit.bind (fun _ => (repay pid).bind (fun _ =>
      napiSoftirq.bind (fun _ => PrefixPreserves.pure reached_safe true)))

theorem decryptIteration : PrefixPreserves Reached PublicSafe RxHistory.decryptIteration := by
  apply workerIterPrefix_preserves _ _ reached_safe decryptStep
  apply PrefixPreserves.bind (quiet_store _ (condResched_sameKernel _))
  intro b
  exact quiet_store _ (by
    intro initial
    exact productAmbient_spec (AmbientM.branch .decWorkerNeedResched b) _ (fun _ _ hi => hi))

theorem encryptIteration : PrefixPreserves Reached PublicSafe RxHistory.encryptIteration := by
  unfold RxHistory.encryptIteration
  exact (mixed _
    (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationEncrypt.«0».Leanux.Proofs.WG.PublicationJoint.encryptPoll)).bind
    (fun item => napiSoftirq.bind (fun _ => mixed _
      ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationEncrypt.«0».Leanux.Proofs.WG.PublicationJoint.encryptTail) item)))

theorem txIteration (pid : PeerId) :
    PrefixPreserves Reached PublicSafe
      (RxHistory.mixed (txIterPrefix pid (liftPrefix (Env.condResched .txWorker)))) :=
  mixed _ (PublicationJoint.txIteration pid)

end Leanux.Proofs.WG.Roaming.PollAuthentication
