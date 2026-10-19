import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAfterXmitPath

/-! The first crypt scheduler is an actual source continuation of the
initialized post-transmit callback. Delivery and the original drain check
remain after it, including when that scheduler or its later suffix stops. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.AfterXmit
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal RunnerSource

def afterScheduled : PrefixM Event Unit := do
  hooks.deliver
  let d ← liftPrefix (liftWG getDev)
  liftPrefix (Env.requireDrained "wg_xmit queued" [!d.encryptQueue.empty,!d.txWorkQueue.isEmpty])
  Driver.sendWorkersObserved hooks

theorem crypt_schedule_factor :
    tail (some true) = (Driver.scheduleObserved hooks none >>= fun _=>afterScheduled) := by
  simp only [tail,cryptTail,Driver.cryptObserved,afterScheduled,↓reduceIte,bind_assoc]

theorem Caller.schedule_continuation (caller : Caller trace placeholders operationIndex world history)
    (performed : runPrefix front world history=(.ok (some true,v),last)) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (resume trace operationIndex caller.path.op caller.path.state caller.path.ret
        v (Driver.scheduleObserved hooks none >>= fun _=>afterScheduled)) last := by
  rw [caller.front_continuation performed,crypt_schedule_factor]

theorem Caller.schedule_entry (caller : Caller trace placeholders operationIndex world history)
    (performed : runPrefix front world history=(.ok (some true,v),last)) :
    CompletePrefix.With CompleteProduct.Carrier CompleteProduct.Safe last v :=
  caller.front_entry performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.AfterXmit
