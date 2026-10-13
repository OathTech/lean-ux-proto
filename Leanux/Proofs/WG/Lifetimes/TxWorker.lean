import Leanux.Proofs.WG.Lifetimes.TxCompletion
import Leanux.Proofs.WG.Lifetimes.ReceivePoll
import Leanux.Proofs.Logged.PrefixWorkers

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! The complete original TX worker step and iteration. The saved head supplies
the numeric keypair reference at cleanup; each later store access still resolves
afresh. These results do not assert saved-reference ownership or batch identity. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def txDropPeekedPrefix (pid : PeerId) : MixedM Unit := do
  setPeerMixed pid {(← getPeerMixed pid) with txQueue := (← getPeerMixed pid).txQueue.dropPeeked}

theorem txDropPeekedPrefix_erases (pid : PeerId) :
    ErasesPrefix (txDropPeekedPrefix pid)
      (do setPeer pid {(← getPeer pid) with txQueue := (← getPeer pid).txQueue.dropPeeked}) :=
  erasesPrefix_bind (getPeerMixed_erases _) (fun _ =>
    erasesPrefix_bind (getPeerMixed_erases _) (fun _ => setPeerMixed_erases _ _))

theorem txDropPeekedPrefix_preserves (c : AmbientContracts I) (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (txDropPeekedPrefix pid) := by
  apply AmbientContracts.drop (Q := fun _ _ => True)
  apply PrefixEnsures.bind (c.getPeer (fun _ => True) pid)
  intro p
  apply PrefixEnsures.bind (c.getPeer_frame (fun s => True ∧ s.1.slots pid = some p.internalId) pid)
  intro q
  exact c.setPeer (fun _ => True) pid {p with txQueue := q.txQueue.dropPeeked}

def txStepPrefix (pid : PeerId) : MixedM Bool := do
  let (first, q) ← liftPrefix ((← getPeerMixed pid).txQueue.peek)
  modifyPeerKeysPrefix pid fun p => {p with txQueue := q}
  let go ← andPrefix (liftPrefix (branch .txPacket first.isSome)) do
    let some f := first | liftPrefix (invariant "unreachable")
    let some h := f.head? | liftPrefix (invariant "an empty ring item")
    liftPrefix (branch .txNotUncrypted ((← getTxSkbPrefix h).state != .uncrypted))
  if !go then return false
  let some item := first | liftPrefix (invariant "unreachable")
  let some headId := item.head? | liftPrefix (invariant "an empty ring item")
  let head ← getTxSkbPrefix headId
  txDropPeekedPrefix pid
  if ← liftPrefix (branch .txCrypted (head.state == .crypted)) then createDataDonePrefix pid item
  for id in item do freeTxSkbPrefix id
  keypairPutPrefix (some head.keypair) false
  peerPutMixed (some pid)
  return true

def txIterPrefix (pid : PeerId) (needResched : MixedM Bool) : MixedM IterResult :=
  workerIterPrefix .txWorker (some pid) (txStepPrefix pid)
    (do liftPrefix (branch .txNeedResched (← needResched)))

theorem txStepPrefix_erases (pid : PeerId) : ErasesPrefix (txStepPrefix pid) (txStep pid) := by
  unfold txStepPrefix txStep modifyPeerKeysPrefix txDropPeekedPrefix
  simp only [bind_assoc]
  repeat' first
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact getTxSkbPrefix_erases _
    | with_reducible exact createDataDonePrefix_erases _ _
    | with_reducible exact freeTxSkbPrefix_erases _
    | with_reducible exact keypairPutPrefix_erases _ _
    | with_reducible exact peerPutMixed_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply andPrefix_erases
    | with_reducible apply erasesPrefix_forIn
    | (with_reducible split)
  all_goals simp_all
  all_goals first
    | contradiction
    | exact erasesPrefix_foldlM _ _ _ _ (fun _ _ => freeTxSkbPrefix_erases _)
    | exact getTxSkbPrefix_erases _
    | exact createDataDonePrefix_erases _ _
    | exact freeTxSkbPrefix_erases _

theorem txStepPrefix_preserves_ambient (c : AmbientContracts I) (t : TxContracts I)
    (sc : SocketContracts I) (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (txStepPrefix pid) := by
  unfold txStepPrefix
  repeat' first
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | with_reducible exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (t.get (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c
        (fun _ => True) _ _ (fun _ => rfl))
    | with_reducible exact txDropPeekedPrefix_preserves c _
    | with_reducible exact createDataDonePrefix_preserves c t sc _ _
    | with_reducible exact t.free _
    | with_reducible exact t.put _ _
    | with_reducible exact c.peerPut _
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (prevQueuePeek_sameKernel _))
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply andPrefix_preserves c.safe
    | with_reducible apply PrefixPreserves.forIn _ _ _ c.safe
    | (with_reducible split)

theorem txIterPrefix_erases (pid : PeerId) (hr : ErasesPrefix needResched originalResched) :
    ErasesPrefix (txIterPrefix pid needResched) (txIter pid originalResched) := by
  apply workerIterPrefix_erases
  · exact txStepPrefix_erases pid
  · exact erasesPrefix_bind hr (fun _ => erasesPrefix_lift _)

theorem txIterPrefix_preserves_ambient (c : AmbientContracts I) (t : TxContracts I)
    (sc : SocketContracts I) (pid : PeerId)
    (hr : PrefixPreserves I LifetimeEvent.Safe needResched) :
    PrefixPreserves I LifetimeEvent.Safe (txIterPrefix pid needResched) := by
  apply workerIterPrefix_preserves _ _ c.safe (txStepPrefix_preserves_ambient c t sc pid)
  exact PrefixPreserves.bind hr (fun _ => AmbientContracts.drop (c.branch (fun _ => True) _ _))

theorem txIterPrefix_allocation (pid : PeerId)
    (hr : PrefixPreserves AllocationInv LifetimeEvent.Safe needResched) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (txIterPrefix pid needResched) :=
  txIterPrefix_preserves_ambient allocationAmbient allocationTx allocationSocket pid hr

/-- Five original completion helpers and one complete worker step. -/
inductive TxCall where
  | send (pid : PeerId) (bytes : List UInt8) (ds : Nat)
  | dataSent (pid : PeerId)
  | authenticatedSent (pid : PeerId)
  | fresh (pid : PeerId)
  | done (pid : PeerId) (item : List SkbId)
  | step (pid : PeerId)

namespace TxCall

def Result : TxCall → Type
  | .send .. | .step .. => Bool
  | _ => Unit

def original (call : TxCall) : M call.Result := match call with
  | .send pid bytes ds => sendSkbToPeer pid bytes ds
  | .dataSent pid => timersDataSent pid
  | .authenticatedSent pid => timersAnyAuthenticatedPacketSent pid
  | .fresh pid => keepKeyFresh pid
  | .done pid item => createDataDone pid item
  | .step pid => txStep pid

def observed (call : TxCall) : MixedM call.Result := match call with
  | .send pid bytes ds => sendSkbToPeerPrefix pid bytes ds
  | .dataSent pid => timersDataSentPrefix pid
  | .authenticatedSent pid => timersAnyAuthenticatedPacketSentPrefix pid
  | .fresh pid => keepKeyFreshPrefix pid
  | .done pid item => createDataDonePrefix pid item
  | .step pid => txStepPrefix pid

theorem erases (call : TxCall) : ErasesPrefix call.observed call.original := by
  cases call with
  | send pid bytes ds => exact sendSkbToPeerPrefix_erases pid bytes ds
  | dataSent pid => exact timersDataSentPrefix_erases pid
  | authenticatedSent pid => exact timersAnyAuthenticatedPacketSentPrefix_erases pid
  | fresh pid => exact keepKeyFreshPrefix_erases pid
  | done pid item => exact createDataDonePrefix_erases pid item
  | step pid => exact txStepPrefix_erases pid

theorem preserves_ambient (c : AmbientContracts I) (t : TxContracts I)
    (sc : SocketContracts I) (call : TxCall) :
    PrefixPreserves I LifetimeEvent.Safe call.observed := by
  cases call with
  | send pid bytes ds => exact AmbientContracts.drop (sendSkbToPeerPrefix_spec c sc (fun _ => True) pid bytes ds)
  | dataSent pid => exact AmbientContracts.drop (timersDataSentPrefix_spec c (fun _ => True) pid)
  | authenticatedSent pid => exact AmbientContracts.drop (timersAnyAuthenticatedPacketSentPrefix_spec c (fun _ => True) pid)
  | fresh pid =>
    exact keepKeyFreshPrefix_preserves c
      (fun pid => AmbientContracts.drop (t.device (fun _ => True) (.handshake pid))) pid
  | done pid item => exact createDataDonePrefix_preserves c t sc pid item
  | step pid => exact txStepPrefix_preserves_ambient c t sc pid

theorem allocation (call : TxCall) : PrefixPreserves AllocationInv LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient allocationTx allocationSocket

end TxCall
end Leanux.Proofs.WG.Lifetimes
