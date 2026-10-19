import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationAdmissionContracts

/-! The existing queue-write observation separates unpublished ownership
from peer-queue ownership before CPU/ring choices can stop. These factors
retain the original source and existing event vocabulary. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.QueueHandoff
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open HandshakeSecurity.StagedDisposal

def before (pid : PeerId) (items : List SkbId) : TxDisposition.Obs (Option Peer) := do
  let some first := items.head? | liftPrefix (liftWG (invariant "an empty ring item"))
  TxDisposition.nativeAccess (setTxSkbPrefix first fun p => {p with state := .uncrypted})
  let p ← TxDisposition.nativeAccess (getPeerMixed pid)
  if ← liftPrefix (liftWG (branch .enqueuePeerQueueFull (p.txQueue.count ≥ MAX_QUEUED_PACKETS))) then return none
  return some p

def install (pid : PeerId) (p : Peer) (items : List SkbId) : TxDisposition.Obs Unit := do
  TxDisposition.nativeAccess (setPeerMixed pid {p with txQueue := p.txQueue.enqueue items})
  emitPrefix (.queued pid items)

def after (items : List SkbId) : TxDisposition.Obs Int := do
  let d ← liftPrefix (liftWG getDev)
  let cpu ← liftPrefix (liftWG (cpumaskNextOnlineFrom d.encryptLastCpu))
  liftPrefix (liftWG (modifyDev fun d => {d with encryptLastCpu := cpu}))
  if ← liftPrefix (liftWG (branch .enqueueRingFull d.encryptQueue.full)) then return -WG.EPIPE
  liftPrefix (liftWG (queueDeviceWork .encryptWorker))
  liftPrefix (liftWG (modifyDev fun d => {d with encryptQueue := d.encryptQueue.produce items}))
  return 0

def offered (items : List SkbId) (ret : Int) : TxDisposition.Obs Int := do
  if ret = 0 then emitPrefix (.ring (.offered items true))
  else if ret = -WG.EPIPE then emitPrefix (.ring (.offered items false))
  return ret

theorem core_factor (pid : PeerId) (items : List SkbId) :
    TxDisposition.enqueueCore pid items = (do
      let some p ← before pid items | pure (-WG.ENOSPC)
      install pid p items
      after items) := by
  unfold TxDisposition.enqueueCore before install after
  cases head : items.head? <;>
    simp only [bind_assoc,TxDisposition.bind_ite,pure_bind]
  all_goals rfl

theorem enqueue_factor (pid : PeerId) (items : List SkbId) :
    TxDisposition.enqueue pid items = ((do
      let some p ← before pid items | pure (-WG.ENOSPC)
      install pid p items
      after items) >>= offered items) := by
  rw [TxDisposition.enqueue,core_factor]
  rfl

/-- The concrete final journal uses exactly the same focused source cuts. -/
theorem actual_factor (pid : PeerId) (items : List SkbId) :
    Admission.actualOps.enqueue pid items =
      focusPrefix CausalJournal.txEvent CausalJournal.txEvent? ((do
        let some p ← before pid items | pure (-WG.ENOSPC)
        install pid p items
        after items) >>= offered items) := by
  change focusPrefix _ _ (TxDisposition.enqueue pid items) = _
  rw [enqueue_factor]

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.QueueHandoff
