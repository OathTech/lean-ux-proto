import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteTxWorker
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRepaymentPrefixes

/-! Fixed original worker prefixes. These execute the original peek,
readiness test, head read, dequeue and branch in their original order.
They are not arbitrary factorizations chosen to fit an accounted state. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation HandshakeSecurity.StagedConservation

structure Selected where
  items : List SkbId
  head : DataPacket
  crypted : Bool

def afterReadSelection (pid : PeerId) (items : List SkbId) (head : DataPacket) :
    PrefixM CausalJournal.Event Selected := do
  CausalJournal.completionOps.drop pid items
  let flag ← CausalJournal.completionOps.step (branch .txCrypted (head.state == .crypted))
  return ⟨items,head,flag⟩

def bodySelection (pid : PeerId) (first : Option (List SkbId)) :
    PrefixM CausalJournal.Event (Option Selected) := do
  let go ← TxWorker.ready first
  if !go then return none
  let some items := first | CausalJournal.completionOps.step (invariant "unreachable")
  let some id := items.head? | CausalJournal.completionOps.step (invariant "an empty ring item")
  let head ← CausalJournal.completionOps.packet id
  return some (← afterReadSelection pid items head)

def workerSelection (pid : PeerId) : PrefixM CausalJournal.Event (Option Selected) := do
  let first ← TxSelection.peek pid
  bodySelection pid first

def selectedCallback (pid : PeerId) : Option Selected → PrefixM CausalJournal.Event Bool
  | none => pure false
  | some picked => if picked.crypted then TxWorker.crypted pid picked.items picked.head else
      Terminal.deadObserved CausalJournal.txEvent CausalJournal.txEvent?
        CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid picked.items picked.head

theorem afterRead_selection_factor (pid : PeerId) (items : List SkbId) (head : DataPacket) :
    TxWorker.afterRead pid items head = (do
      let picked ← afterReadSelection pid items head
      selectedCallback pid (some picked)) := by
  simp only [TxWorker.afterRead,afterReadSelection,selectedCallback,bind_assoc,pure_bind]

theorem body_selection_factor (pid : PeerId) (first : Option (List SkbId)) :
    TxWorker.body pid first = (bodySelection pid first >>= selectedCallback pid) := by
  unfold TxWorker.body bodySelection
  simp only [bind_assoc]
  congr 1
  funext go
  cases go <;> simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,↓reduceIte,pure_bind,selectedCallback]
  cases first with
  | none => rfl
  | some items =>
    cases chosen : items.head? with
    | none => simp only [chosen]; rfl
    | some id =>
      simp only [chosen,bind_assoc]
      congr 1
      funext head
      simpa only [bind_assoc,pure_bind] using afterRead_selection_factor pid items head

/-- This is the actual worker split immediately after its original dequeue
and crypted/DEAD guard. The prefix itself chooses every saved state. -/
theorem worker_selection_factor (pid : PeerId) :
    CausalJournal.transmit pid = (workerSelection pid >>= selectedCallback pid) := by
  rw [TxWorker.transmit_factor]
  simp only [workerSelection,bind_assoc,body_selection_factor]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
