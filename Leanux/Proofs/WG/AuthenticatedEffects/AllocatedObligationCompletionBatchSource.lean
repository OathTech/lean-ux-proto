import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationFirstTerminalSendSuffix
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCuts

/-! Exact caller factors expose the remaining send/free list. They retain
the original loop order, timer calls and reference repayments. These are
proof-tree source factors only; the common driver and mirror stay unchanged. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity HandshakeSecurity.StagedDisposal

def iteration (o : CompletionEffects.Ops E) (pid : PeerId) (id : SkbId) (dataSent : Bool) :
    PrefixM E Bool := do
  let packet ← captureObserved (o.packet id)
  _ ← o.step (branch .doneSkbIterate true)
  let isKeepalive := packet.value.bytes.length == MESSAGE_DATA_LEN_0
  let sent ← o.send pid id packet
  if ← TxDisposition.andObs (o.step (branch .doneSendOk sent))
      (o.step (branch .doneNotKeepalive !isKeepalive)) then return true
  return dataSent

def sendLoop (o : CompletionEffects.Ops E) (pid : PeerId) : List SkbId → Bool → PrefixM E Bool
  | [],dataSent => pure dataSent
  | id :: rest,dataSent => do
      let next ← iteration o pid id dataSent
      sendLoop o pid rest next

def finish (o : CompletionEffects.Ops E) (pid : PeerId) (dataSent : Bool) : PrefixM E Unit := do
  _ ← o.step (branch .doneSkbIterate false)
  if ← o.step (branch .doneDataSent dataSent) then o.dataSent pid
  o.fresh pid

def complete (o : CompletionEffects.Ops E) (pid : PeerId) (item : List SkbId) : PrefixM E Unit := do
  o.completion pid item
  o.traversal pid
  o.sent pid
  let dataSent ← sendLoop o pid item false
  finish o pid dataSent

private theorem sendLoop_forIn (o : CompletionEffects.Ops E) (pid : PeerId)
    (item : List SkbId) (dataSent : Bool) :
    sendLoop o pid item dataSent = forIn item dataSent (fun id state => do
      let next ← iteration o pid id state
      pure (.yield next)) := by
  induction item generalizing dataSent with
  | nil => rfl
  | cons id rest ih =>
    simp only [sendLoop,List.forIn_cons,bind_assoc,pure_bind]
    congr 1
    funext next
    exact ih next

theorem complete_factor (o : CompletionEffects.Ops E) (pid : PeerId) (item : List SkbId) :
    complete o pid item = CompletionEffects.completeWith o pid item := by
  simp only [complete,sendLoop_forIn,iteration,finish,CompletionEffects.completeWith,
    bind_assoc,TxDisposition.bind_ite,pure_bind]

def freeLoop (o : TxSource.Ops E) : List SkbId → PrefixM E Unit
  | [] => pure ()
  | id :: rest => do
      o.access (freeTxSkbPrefix id)
      freeLoop o rest

def release (o : TxSource.Ops E) (pid : PeerId) (key : KeypairId) : PrefixM E Bool := do
  o.access (keypairPutPrefix (some key) false)
  o.release (some pid)
  return true

def dispose (o : TxSource.Ops E) (pid : PeerId) (item : List SkbId) (key : KeypairId) : PrefixM E Bool := do
  freeLoop o item
  release o pid key

private theorem freeLoop_forIn (o : TxSource.Ops E) (item : List SkbId) :
    freeLoop o item = forIn item () (fun id _ => do
      o.access (freeTxSkbPrefix id)
      pure (.yield ())) := by
  induction item with
  | nil => rfl
  | cons id rest ih => simp only [freeLoop,List.forIn_cons,bind_assoc,pure_bind,ih]

theorem dispose_factor (o : TxSource.Ops E) (pid : PeerId) (item : List SkbId) (key : KeypairId) :
    dispose o pid item key = TxSource.dispose o pid item key := by
  simp only [dispose,freeLoop_forIn,release,TxSource.dispose]

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
