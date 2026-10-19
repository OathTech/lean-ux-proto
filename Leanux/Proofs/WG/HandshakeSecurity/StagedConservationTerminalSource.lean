import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalTxProjection
import Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffectsExecution

/-! Counterless postallocation drops retain their native branch and each
actual packet free. A socket success followed by physical disposal is not a
second terminal drop. The callbacks here expose the missing source distinction. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Terminal
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues AuthenticatedEffects

inductive Reason where
  | createRefused (pid : PeerId) (result : Int)
  | deadBatch (pid : PeerId) (head : DataPacket)

def createWith (o : StagedDisposal.TxSource.Ops E)
    (free : Reason → SkbId → PrefixM E Unit) (pid : PeerId) (item : List SkbId) : PrefixM E Unit := do
  let some first := item.head? | o.step (invariant "an empty ring item")
  let ret ← do
    if ← o.step (branch .createDataDead (← o.access (getPeerMixed pid)).isDead) then pure (-EINVAL)
    else
      let ret ← o.enqueue pid item
      if ← o.step (branch .createDataEpipe (ret == -WG.EPIPE)) then StagedDisposal.TxSource.publish o item .dead
      pure ret
  if ← o.step (branch .createDataOk (ret == 0)) then return
  if ← o.step (branch .createDataOkEpipe (ret == -WG.EPIPE)) then return
  o.access (keypairPutPrefix (some (← o.access (getTxSkbPrefix first)).keypair) false)
  o.release (some pid)
  for id in item do free (.createRefused pid ret) id

def disposeWith (o : StagedDisposal.TxSource.Ops E) (free : SkbId → PrefixM E Unit)
    (pid : PeerId) (item : List SkbId) (key : KeypairId) : PrefixM E Bool := do
  for id in item do free id
  o.access (keypairPutPrefix (some key) false)
  o.release (some pid)
  return true

theorem create_factor (o : StagedDisposal.TxSource.Ops E) (pid : PeerId) (item : List SkbId) :
    createWith o (fun _ id => o.access (freeTxSkbPrefix id)) pid item =
      StagedDisposal.TxSource.create o pid item := rfl

theorem dispose_factor (o : StagedDisposal.TxSource.Ops E)
    (pid : PeerId) (item : List SkbId) (key : KeypairId) :
    disposeWith o (fun id => o.access (freeTxSkbPrefix id)) pid item key =
      StagedDisposal.TxSource.dispose o pid item key := rfl

def bodyWith (o : CompletionEffects.Ops E)
    (complete : PeerId → List SkbId → PrefixM E Unit)
    (dead : PeerId → List SkbId → DataPacket → PrefixM E Bool)
    (pid : PeerId) (first : Option (List SkbId)) : PrefixM E Bool := do
  let go ← TxDisposition.andObs (o.step (branch .txPacket first.isSome)) do
    let some f := first | o.step (invariant "unreachable")
    let some h := f.head? | o.step (invariant "an empty ring item")
    o.step (branch .txNotUncrypted ((← o.packet h).state != .uncrypted))
  if !go then return false
  let some item := first | o.step (invariant "unreachable")
  let some headId := item.head? | o.step (invariant "an empty ring item")
  let head ← o.packet headId
  o.drop pid item
  if ← o.step (branch .txCrypted (head.state == .crypted)) then
    complete pid item
    o.dispose pid item head.keypair
  else dead pid item head

def stepWith (o : CompletionEffects.Ops E)
    (complete : PeerId → List SkbId → PrefixM E Unit)
    (dead : PeerId → List SkbId → DataPacket → PrefixM E Bool) (pid : PeerId) : PrefixM E Bool := do
  let (first,q) ← o.step ((← o.peer pid).txQueue.peek)
  o.modifyPeer pid fun p => {p with txQueue := q}
  bodyWith o complete dead pid first

theorem body_factor (o : CompletionEffects.Ops E)
    (complete : PeerId → List SkbId → PrefixM E Unit) (pid : PeerId) (first : Option (List SkbId)) :
    bodyWith o complete (fun pid item head => o.dispose pid item head.keypair) pid first =
      CompletionEffects.bodySourceWith o complete pid first := rfl

theorem step_factor (o : CompletionEffects.Ops E)
    (complete : PeerId → List SkbId → PrefixM E Unit) (pid : PeerId) :
    stepWith o complete (fun pid item head => o.dispose pid item head.keypair) pid =
      CompletionEffects.stepSourceWith o complete pid := by
  simp only [stepWith,CompletionEffects.stepSourceWith,body_factor]

end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Terminal
