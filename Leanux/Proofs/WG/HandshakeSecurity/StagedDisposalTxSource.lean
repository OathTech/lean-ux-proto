import Leanux.Proofs.WG.Queues.TxDisposition

/-! Native TX publication, admission failure and disposal expose the actual
peer-reference repayment. Existing lifetime accesses and disposition events
remain separate callbacks in their original source order. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.TxSource
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues

structure Ops (E : Type) where
  step : {α : Type} → WG.M α → PrefixM E α
  access : {α : Type} → MixedM α → PrefixM E α
  event : TxDisposition.Event → PrefixM E Unit
  enqueue : PeerId → List SkbId → PrefixM E Int
  release : Option PeerId → PrefixM E Unit

def native : Ops TxDisposition.Event where
  step := fun action => liftPrefix (liftWG action)
  access := TxDisposition.nativeAccess
  event := emitPrefix
  enqueue := TxDisposition.enqueue
  release := fun peer => TxDisposition.nativeAccess (peerPutMixed peer)

def publish (o : Ops E) (item : List SkbId) (state : PacketState) : PrefixM E Unit := do
  let some first := item.head? | o.step (invariant "an empty ring item")
  let pid ← o.access (peerDerefPrefix (.keypair (← o.access (getTxSkbPrefix first)).keypair))
  o.access (peerGetMixed pid)
  if !((← o.access (getPeerMixed pid)).txQueue.all.any (·.head? == some first)) then
    o.step (invariant "an item for the tx worker that is not on its peer's tx_queue")
  o.access (setTxSkbPrefix first fun p => {p with state})
  o.event (.published pid first state)
  _ ← o.access (cpumaskChooseOnlinePrefix pid)
  if !(← o.step getDev).txWorkQueue.contains pid || (← o.step (peekQueuedUnit .txWorker pid)) then
    o.step (recordQueued .txWorker pid)
    o.step (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue ++ [pid]})
  o.release (some pid)

def create (o : Ops E) (pid : PeerId) (item : List SkbId) : PrefixM E Unit := do
  let some first := item.head? | o.step (invariant "an empty ring item")
  let ret ← do
    if ← o.step (branch .createDataDead (← o.access (getPeerMixed pid)).isDead) then pure (-EINVAL)
    else
      let ret ← o.enqueue pid item
      if ← o.step (branch .createDataEpipe (ret == -WG.EPIPE)) then publish o item .dead
      pure ret
  if ← o.step (branch .createDataOk (ret == 0)) then return
  if ← o.step (branch .createDataOkEpipe (ret == -WG.EPIPE)) then return
  o.access (keypairPutPrefix (some (← o.access (getTxSkbPrefix first)).keypair) false)
  o.release (some pid)
  for id in item do o.access (freeTxSkbPrefix id)

def dispose (o : Ops E) (pid : PeerId) (item : List SkbId) (key : KeypairId) : PrefixM E Bool := do
  for id in item do o.access (freeTxSkbPrefix id)
  o.access (keypairPutPrefix (some key) false)
  o.release (some pid)
  return true

theorem publish_native (item : List SkbId) (state : PacketState) :
    publish native item state = TxDisposition.publish item state := rfl

theorem create_native (pid : PeerId) (item : List SkbId) :
    create native pid item = TxDisposition.create pid item := rfl

theorem dispose_native (pid : PeerId) (item : List SkbId) (key : KeypairId) :
    dispose native pid item key = TxDisposition.dispose pid item key := rfl

end Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.TxSource
