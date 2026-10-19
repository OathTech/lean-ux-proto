import Leanux.Proofs.WG.RetirementSecurity.AllRxDisposal
import Leanux.Proofs.WG.RetirementSecurity.Invalidation
import Leanux.Proofs.WG.RetirementSecurity.TimerRetirementOrigin
import Leanux.Proofs.WG.KeyLifetime.Statements
import Leanux.Proofs.WG.LifetimeSafety.Statements

/-! T6 is a composition of universal original-source contracts. Check-site
safety has no dispatch premise. Operational progress uses the real timer and
worker calls; unpublication is separate from final reference release. The
initialized credit and allocation-lifetime claims keep their exact domains.
This package adds no observer and assumes no whole-run retirement invariant. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits

/-- The native clauses of reference-aware retirement. Function arguments
expose each actual-run condition; no fairness or maximum worker latency is
assumed. In particular, final RX release covers authenticated packets too. -/
structure Outcome : Prop where
  txChecks : ∀ pid w a, ∀ r∈(runStatePrefix (KeyTimes.stagingObserved pid) w a []).2,
    r.Valid
  rxChecks : ∀ pkt w a, ∀ r∈(runStatePrefix (KeyTimes.receiveAttemptsObserved pkt) w a []).2,
    r.Valid
  ageCheck : ∀ birthday seconds w v a b result,
    ((birthdateTest birthday seconds).run w).run a=.ok ((result,v),b) ↔
      ∃ now, ((hiddenClock64 .birthdateExpired : WG.M Int64).run w).run a=.ok ((now,v),b) ∧
        result=(decide (KeyTimes.deadline birthday seconds≤now),
          (KeyTimes.deadline birthday seconds).toInt,now.toInt)
  sendingRejection : ∀ pid packets id,
    Hoare (stagedOutNokey pid packets (some id) true) (fun _=>True)
      (fun _=>Invalidation.SendingInvalid id)
  receivingRejection : ∀ pkt w entered checked v a enteredAmbient checkedAmbient b key out,
    ((getKeypair pkt.keypair).run w).run (CounterWindow.record a .decNoKeypair false)=
      .ok ((key,entered),enteredAmbient)→
    ((KeyTimes.receiveReject key).run entered).run enteredAmbient=
      .ok ((true,checked),checkedAmbient)→
    ((decryptPacket pkt).run w).run a=.ok ((out,v),b)→
    out=none ∧ Invalidation.ReceivingInvalid pkt.keypair v
  initializedAccess : ∀ trace placeholders,
    AuditSafe (runPrefixOuter (executeTraceAudit trace placeholders) []).2
  initializedCredits : ∀ trace placeholders result w h,
    runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h)→
    HolderAccount [] w.wg
  derivedArm : ∀ pid w v a b,
    ((timersSessionDerived pid).run w).run a=.ok (((),v),b)→
    ∃ caller u c,
      ((callerJiffies .timerJiffiesSessionDerived).run w).run a=.ok ((caller,u),c) ∧
      (((modPeerTimerGuard pid).run u).run c=.ok ((false,v),b) ∨
        ∃ t e, ((modPeerTimerGuard pid).run u).run c=.ok ((true,t),e) ∧
          ((armTimer pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS caller).run t).run e=.ok (((),v),b))
  selectedArm : ∀ trace placeholders pre post receipt,
    (runPrefixOuter (AuthenticatedEffects.CausalJournal.execute trace placeholders) []).2=
      pre++AuthenticatedEffects.CausalJournal.Event.old (.timerSelected receipt)::post→
    receipt.timer=.zeroKeyMaterial→
    receipt.Valid ∧ ∃ before after arm stamp expires,
      pre=before++AuthenticatedEffects.CausalJournal.Event.armed arm::after ∧ arm.Valid ∧
      AuthenticatedEffects.TimerOccurrences.Changed arm ∧ arm.peer=receipt.peer ∧ arm.timer=.zeroKeyMaterial ∧
      AuthenticatedEffects.TimerSlots.Pending arm.run.after receipt.peer .zeroKeyMaterial stamp expires receipt.entry ∧
      AuthenticatedEffects.TimerSlots.Pending receipt.before.wg receipt.peer .zeroKeyMaterial stamp expires receipt.entry
  timerDispatch : ∀ kind pid entry prior,
    Hoare (timerDispatchUnit kind pid .zeroKeyMaterial entry prior)
      (fun w=>ZeroTimerDispatch.Live pid w.wg) (fun _ w=>ZeroTimerDispatch.Queued pid w.wg)
  workerUnpublishes : ∀ pid p w v a b, peerAt w pid=some p→
    ((runFlushedClearWork pid).run w).run a=.ok (((),v),b)→
    SlotsCleared pid v ∧ ∀id∈Unpublication.SlotEntries p,Unpublished id v
  workerAccounts : ∀ pid temporary, Preserves (HolderAccount temporary) (runFlushedClearWork pid)
  releaseRetains : ∀ word now w v a b,
    ((keypairPut word now).run w).run a=.ok (((),v),b)→Retains w v
  finalRelease : ∀ id k w v now a b,keyAt w id=some k→k.refcount=1→
    ((keypairPut (some id) now).run w).run a=.ok (((),v),b)→
    keyAt v id=none ∧ Unpublished id v
  rxFinalRelease : ∀ id pkt flag w v k a b,keyAt w pkt.keypair=some k→k.refcount=1→
    ((cleanup id pkt flag).run w).run a=.ok (((),v),b)→keyAt v pkt.keypair=none
  authenticatedCredit : ∀ temporary pid pkt endpoint,
    Hoare (consumeDataDone pid pkt endpoint)
      (fun w=>HolderAccount temporary w ∧ Packets.Inv w ∧ KeyCompatible pid pkt.keypair w)
      (fun _ w=>HolderAccount temporary w)
  removedRead : ∀ id w v k a b,keyAt w id=none→
    ((getKeypair id).run w).run a=.ok ((k,v),b)→False
  removedAcquire : ∀ id w v out a b,keyAt w id=none→
    ((keypairGet (some id)).run w).run a=.ok ((out,v),b)→False

theorem outcome : Outcome where
  txChecks := KeyLifetime.original_staging_admissions
  rxChecks := KeyLifetime.original_receive_attempt_admission
  ageCheck := KeyLifetime.original_age_test
  sendingRejection := Invalidation.sending_rejection
  receivingRejection := fun pkt w entered checked v a enteredAmbient checkedAmbient b key _=>
    Invalidation.receiving_rejected pkt w entered checked v a enteredAmbient checkedAmbient b key
  initializedAccess := LifetimeSafety.runner_initialized_access_safety
  initializedCredits := fun trace placeholders _ _ _ run=>HolderInitialized.account trace placeholders run
  derivedArm := fun pid _ _ a b run=>DerivedZeroTimer.native pid a b run
  selectedArm := TimerRetirementOrigin.initialized
  timerDispatch := ZeroTimerDispatch.dispatch
  workerUnpublishes := fun pid p w v a b found run=>Unpublication.flushed pid p found a b run
  workerAccounts := flushed_holders
  releaseRetains := put_retains
  finalRelease := fun _ _ _ _ now a b found last run=>FinalDisposal.put_one found last now a b run
  rxFinalRelease := fun id pkt flag _ _ _ a b found last run=>AllRxDisposal.final_reference id pkt flag found last a b run
  authenticatedCredit := by
    intro temporary pid pkt endpoint
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b before run
    exact before.1.receive_done before.2.1 before.2.2 endpoint a b run
  removedRead := fun _ _ _ _ a b gone run=>InitializedRetirement.removed_cannot_read gone a b run
  removedAcquire := fun _ _ _ _ a b gone run=>InitializedRetirement.removed_cannot_acquire gone a b run

end Leanux.Proofs.WG.RetirementSecurity
