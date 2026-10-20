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
assumed. These eighteen fields mix local contracts and initialized endpoints;
runner-level retirement under supplied dispatch/worker/release premises is
exported separately. Previously admitted packets may encrypt after expiry or
unpublication, with no time or count bound proved here. This package does not
link a delayed AEAD to an admission certificate. -/
structure Outcome : Prop where
  /-- Every recorded native staging admission satisfies the TX validity/age/count check at
  admission. Earlier admissions are not cancelled. -/
  txChecks : ∀ pid w a, ∀ r∈(runStatePrefix (KeyTimes.stagingObserved pid) w a []).2,
    r.Valid
  /-- Every recorded decryption attempt satisfies the RX validity/age/count check immediately
  before decryption. -/
  rxChecks : ∀ pkt w a, ∀ r∈(runStatePrefix (KeyTimes.receiveAttemptsObserved pkt) w a []).2,
    r.Valid
  /-- Each normal age-test call returns the exact signed deadline comparison with its recorded
  clock; no progress premise is used. -/
  ageCheck : ∀ birthday seconds w v a b result,
    ((birthdateTest birthday seconds).run w).run a=.ok ((result,v),b) ↔
      ∃ now, ((hiddenClock64 .birthdateExpired : WG.M Int64).run w).run a=.ok ((now,v),b) ∧
        result=(decide (KeyTimes.deadline birthday seconds≤now),
          (KeyTimes.deadline birthday seconds).toInt,now.toInt)
  /-- The native rejection arm leaves the selected sending key invalid on normal return; this
  is a function-level contract. -/
  sendingRejection : ∀ pid packets id,
    Hoare (stagedOutNokey pid packets (some id) true) (fun _=>True)
      (fun _=>Invalidation.SendingInvalid id)
  /-- A normal decrypt call whose actual pre-decryption check rejected returns no plaintext
  and marks the receiving key invalid. -/
  receivingRejection : ∀ pkt w entered checked v a enteredAmbient checkedAmbient b key out,
    ((getKeypair pkt.keypair).run w).run (CounterWindow.record a .decNoKeypair false)=
      .ok ((key,entered),enteredAmbient)→
    ((KeyTimes.receiveReject key).run entered).run enteredAmbient=
      .ok ((true,checked),checkedAmbient)→
    ((decryptPacket pkt).run w).run a=.ok ((out,v),b)→
    out=none ∧ Invalidation.ReceivingInvalid pkt.keypair v
  /-- R2 access safety holds for the initialized audit journal, including its retained stopped
  prefix. -/
  initializedAccess : ∀ trace placeholders,
    AuditSafe (runPrefixOuter (executeTraceAudit trace placeholders) []).2
  /-- A successfully completed initialized accounting run has the holder/reference invariant
  at its final world; no interior or stopped endpoint is asserted here. -/
  initializedCredits : ∀ trace placeholders result w h,
    runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h)→
    HolderAccount [] w.wg
  /-- A completed session-derived timer call either takes the original guard refusal or arms
  the zero-key timer using its actual caller clock. -/
  derivedArm : ∀ pid w v a b,
    ((timersSessionDerived pid).run w).run a=.ok (((),v),b)→
    ∃ caller u c,
      ((callerJiffies .timerJiffiesSessionDerived).run w).run a=.ok ((caller,u),c) ∧
      (((modPeerTimerGuard pid).run u).run c=.ok ((false,v),b) ∨
        ∃ t e, ((modPeerTimerGuard pid).run u).run c=.ok ((true,t),e) ∧
          ((armTimer pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS caller).run t).run e=.ok (((),v),b))
  /-- Each initialized zero-key timer selection has an earlier changed arm and the stated
  pending entries at the named cuts. -/
  selectedArm : ∀ trace placeholders pre post receipt,
    (runPrefixOuter (AuthenticatedEffects.CausalJournal.execute trace placeholders) []).2=
      pre++AuthenticatedEffects.CausalJournal.Event.old (.timerSelected receipt)::post→
    receipt.timer=.zeroKeyMaterial→
    receipt.Valid ∧ ∃ before after arm stamp expires,
      pre=before++AuthenticatedEffects.CausalJournal.Event.armed arm::after ∧ arm.Valid ∧
      AuthenticatedEffects.TimerOccurrences.Changed arm ∧ arm.peer=receipt.peer ∧ arm.timer=.zeroKeyMaterial ∧
      AuthenticatedEffects.TimerSlots.Pending arm.run.after receipt.peer .zeroKeyMaterial stamp expires receipt.entry ∧
      AuthenticatedEffects.TimerSlots.Pending receipt.before.wg receipt.peer .zeroKeyMaterial stamp expires receipt.entry
  /-- A normal native zero-key dispatch queues clearing under the explicit live-device
  precondition; no dispatch is promised. -/
  timerDispatch : ∀ kind pid entry prior,
    Hoare (timerDispatchUnit kind pid .zeroKeyMaterial entry prior)
      (fun w=>ZeroTimerDispatch.Live pid w.wg) (fun _ w=>ZeroTimerDispatch.Queued pid w.wg)
  /-- A completed native clear worker clears this peer's slots and unpublishes their old keys
  at its return; future persistence is not asserted. -/
  workerUnpublishes : ∀ pid p w v a b, peerAt w pid=some p→
    ((runFlushedClearWork pid).run w).run a=.ok (((),v),b)→
    SlotsCleared pid v ∧ ∀id∈Unpublication.SlotEntries p,Unpublished id v
  /-- A completed clear-worker call preserves a supplied holder account, including its
  explicit temporary holders. -/
  workerAccounts : ∀ pid temporary, Preserves (HolderAccount temporary) (runFlushedClearWork pid)
  /-- Each normal key release retains the material of any surviving key. Packet references may
  therefore outlive expiry or unpublication. -/
  releaseRetains : ∀ word now w v a b,
    ((keypairPut word now).run w).run a=.ok (((),v),b)→Retains w v
  /-- A successful key release with entry refcount exactly one removes and unpublishes that
  key at its return. -/
  finalRelease : ∀ id k w v now a b,keyAt w id=some k→k.refcount=1→
    ((keypairPut (some id) now).run w).run a=.ok (((),v),b)→
    keyAt v id=none ∧ Unpublished id v
  /-- A successful native RX cleanup with entry refcount exactly one removes its key, for
  either cleanup flag. -/
  rxFinalRelease : ∀ id pkt flag w v k a b,keyAt w pkt.keypair=some k→k.refcount=1→
    ((cleanup id pkt flag).run w).run a=.ok (((),v),b)→keyAt v pkt.keypair=none
  /-- Normal authenticated-data completion preserves the supplied holder account under packet
  ownership and key compatibility premises. -/
  authenticatedCredit : ∀ temporary pid pkt endpoint,
    Hoare (consumeDataDone pid pkt endpoint)
      (fun w=>HolderAccount temporary w ∧ Packets.Inv w ∧ KeyCompatible pid pkt.keypair w)
      (fun _ w=>HolderAccount temporary w)
  /-- A key absent at this read's entry cannot be read successfully; this is a local failure
  contract, not permanent non-reappearance. -/
  removedRead : ∀ id w v k a b,keyAt w id=none→
    ((getKeypair id).run w).run a=.ok ((k,v),b)→False
  /-- A key absent at this acquisition's entry cannot be acquired successfully; this is a
  local failure contract. -/
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
