import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteCryptSources

/-! The actual encryption iteration selects its item before softirq work.
Its fixed entry prefix retains that value across softirq, then invokes the
original encryption callback and conditional reschedule continuation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity

def entryPrefix : PrefixM CausalJournal.Event (Option (List SkbId)) := do
  let item ← CausalJournal.hooks.poll
  Driver.softirqObserved CausalJournal.hooks
  pure item

def continuation (more : Bool) : PrefixM CausalJournal.Event IterResult := do
  if !more then return .ended
  return if ← Driver.reschedObserved .encryptWorker .encWorkerNeedResched then .yielded else .continued

def tail (item : Option (List SkbId)) : PrefixM CausalJournal.Event IterResult :=
  CausalJournal.hooks.encrypt item >>= continuation

theorem tail_factor (item : Option (List SkbId)) :
    Driver.encryptTailObserved CausalJournal.hooks item = tail item := rfl

theorem iteration_factor : Driver.encryptIterObserved CausalJournal.hooks = (entryPrefix >>= tail) := by
  simp only [Driver.encryptIterObserved,entryPrefix,tail_factor,bind_assoc,pure_bind]

theorem activation_factor (activation : Activation) (worker : activation.worker = .encryptWorker) :
    Driver.iterationObserved CausalJournal.hooks activation = (entryPrefix >>= tail) := by
  simp only [Driver.iterationObserved,worker]
  exact iteration_factor

theorem entry_checked : CompleteProduct.Checked entryPrefix :=
  CompleteProduct.bind_checked CompleteProduct.poll (fun item =>
    CompleteProduct.bind_checked CompleteProduct.softirq (fun _ => CompleteProduct.pure_checked item))

theorem continuation_checked (more : Bool) : CompleteProduct.Checked (continuation more) := by
  unfold continuation
  split
  · exact CompleteProduct.pure_checked _
  · exact CompleteProduct.bind_checked (CompleteProduct.resched .encryptWorker .encWorkerNeedResched)
      (fun _ => CompleteProduct.pure_checked _)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionEntry
