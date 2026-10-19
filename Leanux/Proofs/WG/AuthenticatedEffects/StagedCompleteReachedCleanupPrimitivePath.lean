import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCleanupPrimitivePending

/-! A primitive interior belongs to the next actual iteration in one ordered
loop path. Its deferred receipt and remaining loop have the same final
world, history and ledger as that path. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CleanupPrimitive
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation CreateDisposal HandshakeSecurity.StagedConservation

theorem next_iteration
    (path : DeadIntervals.Path reason pid debts locals items.length items w history ledger v last after)
    (n : Nat) (bound : n < items.length) :
    ∃ cutWorld cutHistory cutLedger skb remaining nextWorld nextHistory nextLedger,
      DeadIntervals.Path reason pid debts locals n items w history ledger cutWorld cutHistory cutLedger ∧
      items.drop n = skb :: remaining ∧
      DeadIntervals.Iteration reason pid debts locals skb remaining cutWorld cutHistory cutLedger
        nextWorld nextHistory nextLedger ∧
      DeadIntervals.Path reason pid debts locals remaining.length remaining nextWorld nextHistory nextLedger v last after := by
  obtain ⟨cutWorld,cutHistory,cutLedger,leading,trailing⟩ := path.split n (Nat.le_of_lt bound)
  cases dropped : items.drop n with
  | nil =>
    have length := congrArg List.length dropped
    simp only [List.length_drop,List.length_nil] at length
    omega
  | cons skb remaining =>
    have count : items.length - n = remaining.length + 1 := by
      have length := congrArg List.length dropped
      simpa only [List.length_drop,List.length_cons] using length
    rw [dropped,count] at trailing
    cases trailing with
    | cons first rest =>
      exact ⟨cutWorld,cutHistory,cutLedger,skb,remaining,_,_,_,leading,rfl,first,rest⟩

theorem iteration_interior
    (iteration : DeadIntervals.Iteration reason pid debts locals skb remaining w history ledger v last after)
    (phase : Phase) :
    runPrefix (readPrefix w skb) w history = (.ok ((),w),history ++ [readEvent w.wg skb]) ∧
      Accounted (history ++ [readEvent w.wg skb]) ledger debts
        (⟨.selected,pid,skb :: remaining⟩ :: locals) w.wg ∧
      Awaiting phase reason pid debts locals skb remaining w history ledger v after ∧
      runPrefix (atPhase phase w skb) w history = (.ok ((),v),current phase w skb history) ∧
      runPrefix (due phase reason skb w v) v (current phase w skb history) = (.ok ((),v),last) := by
  obtain ⟨ticket,position,ordinal,generation,value,accesses,pending,origin,cleanup,recorded,assigned,valid⟩ := iteration.settlement
  have native : (liftWG (freeTxSkb skb)).run w = .ok ((),v) := valid
  have sameLast : last = finished reason skb w v history :=
    congrArg Prod.snd (iteration.run.symm.trans (labelled_run reason skb w v history native))
  exact ⟨read_prefix_run skb w v history native,read_accounted skb iteration.entry,
    iteration_awaiting phase iteration,prefix_run phase skb w v history native,
    by simpa only [←sameLast] using due_run phase reason skb w v history⟩

/-- The pending receipt cannot fail or alter native state. After its exact
emission, the original remaining loop reaches the one shared completed run. -/
theorem iteration_continuation
    (iteration : DeadIntervals.Iteration reason pid debts locals skb remaining w history ledger v middle next)
    (tail : DeadIntervals.Path reason pid debts locals remaining.length remaining v middle next finalWorld last after)
    (phase : Phase) :
    runPrefix (do due phase reason skb w v; loop reason remaining)
      v (current phase w skb history) = (.ok ((),finalWorld),last) := by
  have emitted := (iteration_interior iteration phase).2.2.2.2
  rw [runPrefix_bind,emitted]
  simpa only [List.take_length] using tail.run

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CleanupPrimitive
