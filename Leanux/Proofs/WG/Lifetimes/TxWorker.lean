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
    ErasesStatePrefix (txDropPeekedPrefix pid)
      (do setPeer pid {(← getPeer pid) with txQueue := (← getPeer pid).txQueue.dropPeeked}) :=
  erasesStatePrefix_bind (getPeerMixed_erases _) (fun _ =>
    erasesStatePrefix_bind (getPeerMixed_erases _) (fun _ => setPeerMixed_erases _ _))

theorem txDropPeekedPrefix_preserves (c : AmbientContracts I) (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (txDropPeekedPrefix pid) := by
  apply AmbientContracts.drop (Q := fun _ _ => True)
  apply StatePrefixEnsures.bind (c.getPeer (fun _ => True) pid)
  intro p
  apply StatePrefixEnsures.bind (c.getPeer_frame (fun s => True ∧ s.1.slots pid = some p.internalId) pid)
  intro q
  exact c.setPeer (fun _ => True) pid {p with txQueue := q.txQueue.dropPeeked}

theorem txDropPeekedPrefix_preserves_product (c : ProductAmbientContracts I) (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (txDropPeekedPrefix pid)) := by
  unfold txDropPeekedPrefix
  simp only [liftWGObserver_bind]
  apply ProductAmbientContracts.drop (Q := fun _ _ => True)
  apply PrefixEnsures.bind (c.getPeer (fun _ => True) pid)
  intro p
  apply PrefixEnsures.bind (c.getPeer_frame (fun s => True ∧ s.1.slots pid = some p.internalId) pid)
  intro q
  exact c.setPeer (fun _ => True) pid {p with txQueue := q.txQueue.dropPeeked}

def txStepPrefix (pid : PeerId) : MixedM Bool := do
  let (first, q) ← liftWGPrefix ((← getPeerMixed pid).txQueue.peek)
  modifyPeerKeysPrefix pid fun p => {p with txQueue := q}
  let go ← andPrefix (liftWGPrefix (branch .txPacket first.isSome)) do
    let some f := first | liftWGPrefix (invariant "unreachable")
    let some h := f.head? | liftWGPrefix (invariant "an empty ring item")
    liftWGPrefix (branch .txNotUncrypted ((← getTxSkbPrefix h).state != .uncrypted))
  if !go then return false
  let some item := first | liftWGPrefix (invariant "unreachable")
  let some headId := item.head? | liftWGPrefix (invariant "an empty ring item")
  let head ← getTxSkbPrefix headId
  txDropPeekedPrefix pid
  if ← liftWGPrefix (branch .txCrypted (head.state == .crypted)) then createDataDonePrefix pid item
  for id in item do freeTxSkbPrefix id
  keypairPutPrefix (some head.keypair) false
  peerPutMixed (some pid)
  return true

def txIterPrefix (pid : PeerId) (needResched : PrefixM LifetimeEvent Bool) : PrefixM LifetimeEvent IterResult :=
  workerIterPrefix .txWorker (some pid) (liftWGObserver (txStepPrefix pid))
    (do liftPrefix (branch .txNeedResched (← needResched)))

theorem txStepPrefix_erases (pid : PeerId) : ErasesStatePrefix (txStepPrefix pid) (txStep pid) := by
  unfold txStepPrefix txStep modifyPeerKeysPrefix txDropPeekedPrefix andPrefix WG.andM
  simp only [bind_assoc]
  repeat' first
    | maintenance_erases_join
    | maintenance_erases_join_use
    | (maintenance_head getPeerMixed; exact getPeerMixed_erases _)
    | (maintenance_head setPeerMixed; exact setPeerMixed_erases _ _)
    | (maintenance_head getTxSkbPrefix; exact getTxSkbPrefix_erases _)
    | (maintenance_head createDataDonePrefix; exact createDataDonePrefix_erases _ _)
    | (maintenance_head freeTxSkbPrefix; exact freeTxSkbPrefix_erases _)
    | (maintenance_head keypairPutPrefix; exact keypairPutPrefix_erases _ _)
    | (maintenance_head peerPutMixed; exact peerPutMixed_erases _)
    | (maintenance_lift_head; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head ForIn.forIn; apply erasesStatePrefix_forIn)
    | maintenance_erases_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem txStepPrefix_preserves_ambient (c : AmbientContracts I) (t : TxContracts I)
    (sc : SocketContracts I) (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (txStepPrefix pid) := by
  change StatePrefixEnsures (fun h w _ => I h w) LifetimeEvent.Safe _ (fun _ h w _ => I h w)
  unfold txStepPrefix andPrefix
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | (maintenance_head getPeerMixed; exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    | (maintenance_head getTxSkbPrefix; exact AmbientContracts.drop (t.get (fun _ => True) _))
    | (maintenance_head modifyPeerKeysPrefix; exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) _ _ (fun _ => rfl)))
    | (maintenance_head txDropPeekedPrefix; exact txDropPeekedPrefix_preserves c _)
    | (maintenance_head createDataDonePrefix; exact createDataDonePrefix_preserves c t sc _ _)
    | (maintenance_head freeTxSkbPrefix; exact t.free _)
    | (maintenance_head keypairPutPrefix; exact t.put _ _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_lift_action_head PrevQueue.peek; exact AmbientContracts.drop (c.store (fun _ => True) _ (prevQueuePeek_sameWGStore _)))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (c.branch (fun _ => True) _ _))
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (c.invariant (fun _ => True) _))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head ForIn.forIn; apply StatePrefixEnsures.forInInvariant _ _ _ (fun _ h w _ => I h w) _ (fun _ h w _ hi => c.safe h w hi))
    | maintenance_spec_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem txStepPrefix_preserves_product (c : ProductAmbientContracts I) (t : ProductTxContracts I)
    (sc : ProductSocketContracts I) (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (txStepPrefix pid)) := by
  have ambient {α : Type} (a : AmbientM α) :
      PrefixEnsures I LifetimeEvent.Safe
        (liftWGObserver (liftWGPrefix (StateT.lift a))) (fun _ => I) := by
    rw [liftWGObserver_lift, liftWG_ambient]
    exact ProductAmbientContracts.drop (c.ambient (fun _ => True) a)
  change PrefixEnsures I LifetimeEvent.Safe _ (fun _ => I)
  unfold txStepPrefix andPrefix
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | (maintenance_head ForIn.forIn; rw [liftWGObserver_forIn])
    | maintenance_product_lift
    | (maintenance_head getPeerMixed; exact ProductAmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    | (maintenance_head getTxSkbPrefix; exact ProductAmbientContracts.drop (t.get (fun _ => True) _))
    | (maintenance_head modifyPeerKeysPrefix; exact ProductAmbientContracts.drop (modifyPeerKeysPrefix_spec_product c (fun _ => True) _ _ (fun _ => rfl)))
    | (maintenance_head txDropPeekedPrefix; exact txDropPeekedPrefix_preserves_product c _)
    | (maintenance_head createDataDonePrefix; exact createDataDonePrefix_preserves_product c t sc _ _)
    | (maintenance_head freeTxSkbPrefix; exact t.free _)
    | (maintenance_head keypairPutPrefix; exact t.put _ _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_lift_action_head PrevQueue.peek; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (prevQueuePeek_sameWGStore _)))
    | (maintenance_lift_action_head branch; exact ambient (AmbientM.branch _ _))
    | (maintenance_lift_action_head invariant; exact ambient (AmbientM.invariant _))
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head ForIn.forIn; apply PrefixEnsures.forInInvariant _ _ _ (fun _ => I) _ (fun _ => c.safe))
    | maintenance_product_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem txIterPrefix_erases (pid : PeerId) (hr : ErasesPrefix needResched originalResched) :
    ErasesPrefix (txIterPrefix pid needResched) (txIter pid originalResched) := by
  apply workerIterPrefix_erases
  · exact liftWGObserver_erases (txStepPrefix_erases pid)
  · exact erasesPrefix_bind hr (fun _ => erasesPrefix_lift _)

theorem txIterPrefix_preserves_ambient (c : ProductAmbientContracts I) (t : ProductTxContracts I)
    (sc : ProductSocketContracts I) (pid : PeerId)
    (hr : PrefixPreserves I LifetimeEvent.Safe needResched) :
    PrefixPreserves I LifetimeEvent.Safe (txIterPrefix pid needResched) := by
  apply workerIterPrefix_preserves _ _ c.safe (txStepPrefix_preserves_product c t sc pid)
  exact PrefixPreserves.bind hr (fun _ => ProductAmbientContracts.drop (c.branch (fun _ => True) _ _))

theorem txIterPrefix_allocation (pid : PeerId)
    (hr : PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe needResched) :
    PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe (txIterPrefix pid needResched) :=
  txIterPrefix_preserves_ambient (ProductAmbientContracts.ofNative allocationAmbient) (ProductTxContracts.ofNative allocationTx) ⟨fun P count => (allocationSocket.stats P count).liftWGObserver⟩ pid hr

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

def original (call : TxCall) : WG.M call.Result := match call with
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

theorem erases (call : TxCall) : ErasesStatePrefix call.observed call.original := by
  cases call with
  | send pid bytes ds => exact sendSkbToPeerPrefix_erases pid bytes ds
  | dataSent pid => exact timersDataSentPrefix_erases pid
  | authenticatedSent pid => exact timersAnyAuthenticatedPacketSentPrefix_erases pid
  | fresh pid => exact keepKeyFreshPrefix_erases pid
  | done pid item => exact createDataDonePrefix_erases pid item
  | step pid => exact txStepPrefix_erases pid

theorem preserves_ambient (c : AmbientContracts I) (t : TxContracts I)
    (sc : SocketContracts I) (call : TxCall) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe call.observed := by
  cases call with
  | send pid bytes ds => exact AmbientContracts.drop (sendSkbToPeerPrefix_spec c sc (fun _ => True) pid bytes ds)
  | dataSent pid => exact AmbientContracts.drop (timersDataSentPrefix_spec c (fun _ => True) pid)
  | authenticatedSent pid => exact AmbientContracts.drop (timersAnyAuthenticatedPacketSentPrefix_spec c (fun _ => True) pid)
  | fresh pid =>
    exact keepKeyFreshPrefix_preserves c
      (fun pid => AmbientContracts.drop (t.device (fun _ => True) (.handshake pid))) pid
  | done pid item => exact createDataDonePrefix_preserves c t sc pid item
  | step pid => exact txStepPrefix_preserves_ambient c t sc pid

theorem preserves_product (c : ProductAmbientContracts I) (t : ProductTxContracts I)
    (sc : ProductSocketContracts I) (call : TxCall) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) := by
  cases call with
  | send pid bytes ds => exact ProductAmbientContracts.drop (sendSkbToPeerPrefix_spec_product c sc (fun _ => True) pid bytes ds)
  | dataSent pid => exact ProductAmbientContracts.drop (timersDataSentPrefix_spec_product c (fun _ => True) pid)
  | authenticatedSent pid => exact ProductAmbientContracts.drop (timersAnyAuthenticatedPacketSentPrefix_spec_product c (fun _ => True) pid)
  | fresh pid =>
    exact keepKeyFreshPrefix_preserves_product c
      (fun pid => ProductAmbientContracts.drop (t.device (fun _ => True) (.handshake pid))) pid
  | done pid item => exact createDataDonePrefix_preserves_product c t sc pid item
  | step pid => exact txStepPrefix_preserves_product c t sc pid

theorem allocation (call : TxCall) : StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient allocationTx allocationSocket

end TxCall
end Leanux.Proofs.WG.Lifetimes
