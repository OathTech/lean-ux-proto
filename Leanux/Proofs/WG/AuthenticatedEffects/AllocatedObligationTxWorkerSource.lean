import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationTxSelectedContext
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationDeadEntryContract

/-! The original worker readiness, selected-head read, queue removal and
crypted/DEAD branch are kept in source order. The crypted callback is exactly
the scoped send/free operation owned by the completion lane. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.TxWorker
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open HandshakeSecurity.StagedConservation

def ready (first : Option (List SkbId)) : PrefixM CausalJournal.Event Bool :=
  TxDisposition.andObs (CausalJournal.completionOps.step (branch .txPacket first.isSome)) do
    let some items := first | CausalJournal.completionOps.step (invariant "unreachable")
    let some id := items.head? | CausalJournal.completionOps.step (invariant "an empty ring item")
    CausalJournal.completionOps.step (branch .txNotUncrypted ((← CausalJournal.completionOps.packet id).state != .uncrypted))

def crypted (pid : PeerId) (items : List SkbId) (head : DataPacket) : PrefixM CausalJournal.Event Bool := do
  CompletionEffects.completeScoped CausalJournal.Event.scope CausalSources.Cause.completion CausalJournal.completionOps pid items
  CausalJournal.completionOps.dispose pid items head.keypair

def dispatch (pid : PeerId) (items : List SkbId) (head : DataPacket) : PrefixM CausalJournal.Event Bool := do
  if ← CausalJournal.completionOps.step (branch .txCrypted (head.state == .crypted)) then
    crypted pid items head
  else
    Terminal.deadObserved CausalJournal.txEvent CausalJournal.txEvent?
      CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items head

def afterRead (pid : PeerId) (items : List SkbId) (head : DataPacket) : PrefixM CausalJournal.Event Bool := do
  CausalJournal.completionOps.drop pid items
  if ← CausalJournal.completionOps.step (branch .txCrypted (head.state == .crypted)) then
    crypted pid items head
  else
    Terminal.deadObserved CausalJournal.txEvent CausalJournal.txEvent?
      CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items head

def body (pid : PeerId) (first : Option (List SkbId)) : PrefixM CausalJournal.Event Bool := do
  let go ← ready first
  if !go then return false
  let some items := first | CausalJournal.completionOps.step (invariant "unreachable")
  let some id := items.head? | CausalJournal.completionOps.step (invariant "an empty ring item")
  let head ← CausalJournal.completionOps.packet id
  afterRead pid items head

theorem afterRead_factor (pid : PeerId) (items : List SkbId) (head : DataPacket) :
    afterRead pid items head = (do
      CausalJournal.completionOps.drop pid items
      dispatch pid items head) := rfl

theorem transmit_factor (pid : PeerId) : CausalJournal.transmit pid = (do
    let first ← TxSelection.peek pid
    body pid first) := by
  rw [TxSelection.transmit_factor]
  simp only [body,ready,afterRead,crypted,Terminal.bodyWith]
  rfl

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.TxWorker
