import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerScheduler
import Leanux.Proofs.WG.Queues.HolderAuxSend

/-! Crypt and send waits retain the original auxiliary invariant together
with the exact peer account on one removal history. The unresolved actor
contracts are those of the actual scheduler. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Deferred
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Queues Queues.RxCredits Auxiliary

theorem crypt (actors : Scheduler.Actors initial loans before) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe RxHistory.runCryptWorkers := by
  rw [RxHistory.DeferredSource.crypt_factor]
  exact RxHistory.DeferredSource.crypt_preserves (I:=Inv initial loans before)
    (fun _ _ hi => hi.safe) (fun _ _ _ same hi => store hi same) _
    (Scheduler.schedule_preserves initial loans before actors none)

theorem drained (what : String) (flags : List Bool) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe
      (RxHistory.mixed (requireDrainedPrefix what flags)) :=
  pair_preserves _ (HolderAuxDeferred.drained initial loans before what flags)
    (TimerEnvironment.atoms.drained what flags)

theorem sendOne : PrefixPreserves (Inv initial loans before) OwnerChecks.Safe
    (RxHistory.audit runOneSendWorkerAudit) :=
  pair_preserves _ (HolderAuxSend.sendOne initial loans before) TimerEnvironment.sendOne_at

theorem runSendWorkers (actors : Scheduler.Actors initial loans before) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe RxHistory.runSendWorkers := by
  have safe : ∀ h w, Inv initial loans before h w → OwnerChecks.Safe h := fun _ _ hi => hi.safe
  have saved : ∀ h w v, productStoreView v=productStoreView w →
      Inv initial loans before h w → Inv initial loans before h v := fun _ _ _ same hi => store hi same
  unfold RxHistory.runSendWorkers
  repeat' first
    | (scheduler_preserve_at runOneSendWorkerAudit; exact sendOne)
    | (scheduler_preserve_at RxHistory.schedule; exact Scheduler.schedule_preserves initial loans before actors _)
    | deferred_raw_steps safe saved

theorem afterXmit (actors : Scheduler.Actors initial loans before) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe RxHistory.afterXmit := by
  have safe : ∀ h w, Inv initial loans before h w → OwnerChecks.Safe h := fun _ _ hi => hi.safe
  have saved : ∀ h w v, productStoreView v=productStoreView w →
      Inv initial loans before h w → Inv initial loans before h v := fun _ _ _ same hi => store hi same
  unfold RxHistory.afterXmit
  repeat' first
    | (scheduler_preserve_at RxHistory.runCryptWorkers; exact crypt actors)
    | (scheduler_preserve_at RxHistory.runSendWorkers; exact runSendWorkers actors)
    | (scheduler_preserve_at requireDrainedPrefix; exact drained _ _)
    | deferred_raw_steps safe saved

/-- Successful draining empties the same residual carrier ledger used by
both conjuncts. This is derived from the real guard and ring flag. -/
theorem drained_empty (hi : Inv initial loans before h w)
    (ringFlag : ∀ d, w.wg.dev=some d → (!d.decryptQueue.empty)∈flags)
    (run : runPrefix (RxHistory.mixed (requireDrainedPrefix what flags)) w h=(.ok ((),v),k)) :
    ∃ prior, h=before++prior ∧ remaining initial (NapiCarrier.removedPackets prior)=[] ∧
      (∀ (d : Device) (id : SkbId) (packet : RxPacket), v.wg.dev=some d → d.rxSkbs[id]?≠some packet) ∧
      Inv initial loans before k v := by
  obtain ⟨prior,history,empty,absent,_⟩ := HolderAuxDeferred.drained_empty hi.1 ringFlag run
  have post := (drained what flags w h hi).choose_spec.2.2
  rw [run] at post
  exact ⟨prior,history,empty,absent,post⟩

/-- The output uses the exact original observer, including its actual suffix. -/
theorem normal (g : RxHistory.Obs α) (a : Leanux.M α) (erase : ErasesPrefix g a)
    (keeps : PrefixPreserves (Inv initial loans before) OwnerChecks.Safe g)
    (hi : Inv initial loans before h w) (run : a.run w = .ok (x,v)) :
    Inv initial loans before (runPrefix g w h).2 v := by
  have actual := (erase w h).trans run
  have post := (keeps w h hi).choose_spec.2.2
  simpa only [actual] using post

theorem crypt_normal (actors : Scheduler.Actors initial loans before)
    (hi : Inv initial loans before h w) (run : Env.runCryptWorkers.run w=.ok ((),v)) :
    Inv initial loans before (runPrefix RxHistory.runCryptWorkers w h).2 v :=
  normal _ _ RxHistory.runCryptWorkers_erases (crypt actors) hi run

theorem runSendWorkers_normal (actors : Scheduler.Actors initial loans before)
    (hi : Inv initial loans before h w) (run : Env.runSendWorkers.run w=.ok ((),v)) :
    Inv initial loans before (runPrefix RxHistory.runSendWorkers w h).2 v :=
  normal _ _ RxHistory.runSendWorkers_erases (runSendWorkers actors) hi run

theorem afterXmit_normal (actors : Scheduler.Actors initial loans before)
    (hi : Inv initial loans before h w) (run : Env.afterXmit.run w=.ok ((),v)) :
    Inv initial loans before (runPrefix RxHistory.afterXmit w h).2 v :=
  normal _ _ RxHistory.afterXmit_erases (afterXmit actors) hi run

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Deferred
