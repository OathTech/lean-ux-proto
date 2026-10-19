import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerDeferredOuterNative
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTxEncryptHistoryFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRxDecryptHistoryFrames

/-! The last two actor contracts follow from their exact original runs.
Decryption obtains physical ownership from the same auxiliary entry; its
publication loan and NAPI removals are not supplied by another history. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Outer
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Queues Queues.RxCredits

theorem crypt (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    Crypt initial loans before := by
  constructor
  · intro w h hi result v run
    exact ExactAt.encrypt_normal hi.2 (Prod.ext run rfl)
  · intro w h hi result v run
    exact RetiredPeer.Decrypt.iteration_normal hi.2 hi.1.1.2 (Prod.ext run rfl)

theorem actors (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    Scheduler.Actors initial loans before := (crypt initial loans before).actors

namespace Closed

theorem schedule (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (stack : Option Worker) :
    PrefixPreserves (Auxiliary.Inv initial loans before) OwnerChecks.Safe (RxHistory.schedule stack) :=
  Scheduler.schedule_preserves initial loans before (actors initial loans before) stack

theorem deferred (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (call : EnvDeferredCall) :
    PrefixPreserves (Auxiliary.Inv initial loans before) OwnerChecks.Safe (RxHistory.deferred call) :=
  DeferredTimers.deferred (actors initial loans before) call

theorem sendAll : PrefixEnsures
    (fun h w => h=before ∧ Inv cs loans h w) OwnerChecks.Safe RxHistory.runSendWorkers
    (fun _ k v => ∃ suffix,k=before++suffix ∧ Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v) :=
  Deferred.sendAll (crypt cs loans before)

theorem idle : PrefixEnsures
    (fun h w => h=before ∧ Inv cs loans h w) OwnerChecks.Safe RxHistory.idleTimers
    (fun _ k v => ∃ suffix,k=before++suffix ∧ Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v) :=
  Deferred.idle (crypt cs loans before)

theorem afterXmit : PrefixEnsures
    (fun h w => h=before ∧ Inv cs loans h w) OwnerChecks.Safe RxHistory.afterXmit
    (fun _ k v => ∃ suffix,k=before++suffix ∧ Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v) :=
  Deferred.afterXmit (crypt cs loans before)

theorem afterAdvance : PrefixEnsures
    (fun h w => h=before ∧ Inv cs loans h w) OwnerChecks.Safe RxHistory.afterAdvance
    (fun _ k v => ∃ suffix,k=before++suffix ∧ Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v) :=
  Deferred.afterAdvance (crypt cs loans before)

theorem sendAll_boundary : Preserves Boundary Env.runSendWorkers :=
  Deferred.sendAll_boundary (fun cs h => crypt cs [] h)

theorem idle_boundary : Preserves Boundary Env.idleTimers :=
  Deferred.idle_boundary (fun cs h => crypt cs [] h)

theorem afterXmit_boundary : Preserves Boundary Env.afterXmit :=
  Deferred.afterXmit_boundary (fun cs h => crypt cs [] h)

theorem afterAdvance_boundary : Preserves Boundary Env.afterAdvance :=
  Deferred.afterAdvance_boundary (fun cs h => crypt cs [] h)

end Closed
end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Outer
