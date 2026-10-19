import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteCryptSources

/-! The TX activation's fixed original prefix and continuation. The copied
record guards remain inside the original crypt-ahead action. The worker
iteration has no state-changing begin operation; rescheduling follows only
an actual successful transmit that reports work. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxActivation
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity

abbrev entryPrefix (pid : PeerId) : PrefixM CausalJournal.Event Unit :=
  Driver.cryptAheadObserved CausalJournal.hooks pid

def continuation (more : Bool) : PrefixM CausalJournal.Event IterResult := do
  if !more then return .ended
  return if ← Driver.reschedObserved .txWorker .txNeedResched then .yielded else .continued

def tail (pid : PeerId) : PrefixM CausalJournal.Event IterResult :=
  CausalJournal.transmit pid >>= continuation

theorem tx_factor (pid : PeerId) :
    Driver.txIterObserved CausalJournal.hooks pid = tail pid := rfl

/-- The prefix uses the original crypt-ahead source, including its copied
record checks and possible encryption iteration. No ambient guard is dropped. -/
theorem iteration_factor (activation : Activation) (pid : PeerId)
    (worker : activation.worker = .txWorker) (peer : activation.pid = some pid) :
    Driver.iterationObserved CausalJournal.hooks activation =
      (do entryPrefix pid; tail pid) := by
  simp only [Driver.iterationObserved,worker,peer]
  rfl

theorem entry_checked (pid : PeerId) : CompleteProduct.Checked (entryPrefix pid) :=
  CompleteProduct.crypt_ahead CompleteProduct.encrypt_iteration pid

theorem continuation_checked (more : Bool) : CompleteProduct.Checked (continuation more) := by
  unfold continuation
  split
  · exact CompleteProduct.pure_checked _
  · exact CompleteProduct.bind_checked (CompleteProduct.resched .txWorker .txNeedResched)
      (fun _ => CompleteProduct.pure_checked _)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxActivation
