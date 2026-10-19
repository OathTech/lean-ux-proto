import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCleanupPrimitivePath

/-! Fixed worker prefixes reach the native mutation inside every DEAD free.
The proof-only snapshot reads the exact iteration entry without changing it.
The pending-emission carrier is retained until the original records appear. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation CreateDisposal HandshakeSecurity.StagedConservation
open CleanupPrimitive

def workerDeadPrimitivePrefix (pid : PeerId) (n : Nat) (phase : CleanupPrimitive.Phase) :
    PrefixM CausalJournal.Event Unit := do
  let selected ← workerSelection pid
  match selected with
  | none => pure ()
  | some picked =>
    if picked.crypted then pure ()
    else
      loop (.deadBatch pid picked.head) (picked.items.take n)
      let entry ← liftPrefix (get : Leanux.M World)
      let some skb := (picked.items.drop n).head? |
        liftPrefix (invariant "the requested DEAD iteration is outside its selected list")
      atPhase phase entry skb

theorem SelectionPath.dead_primitive_prefix_run
    (path : SelectionPath ledger locals pid w history ⟨items,head,false⟩ u middle)
    (leading : DeadIntervals.Path (.deadBatch pid head) pid [] locals n items u middle ledger
      cutWorld cutHistory cutLedger)
    (dropped : items.drop n = skb :: remaining)
    (iteration : DeadIntervals.Iteration (.deadBatch pid head) pid [] locals skb remaining
      cutWorld cutHistory cutLedger nextWorld nextHistory nextLedger)
    (phase : CleanupPrimitive.Phase) :
    runPrefix (workerDeadPrimitivePrefix pid n phase) w history =
      (.ok ((),nextWorld),current phase cutWorld skb cutHistory) := by
  rw [workerDeadPrimitivePrefix,runPrefix_bind,path.run]
  change runPrefix (loop (.deadBatch pid head) (items.take n) >>= fun _ => _) u middle = _
  rw [runPrefix_bind,leading.run]
  dsimp only
  rw [runPrefix_bind,runPrefix_lift]
  simp only [StateT.run_get, dropped, List.head?_cons]
  exact (iteration_interior iteration phase).2.2.2.1

/-- At every interior native erase, the selected obligation is represented
by its exact pending receipt and same successor ledger. The fixed source
prefix reaches the actual post-state; the total record suffix and remaining
loop reach the same completed run. No old-history Accounted is asserted there. -/
theorem SelectionPath.dead_primitive_intervals
    (path : SelectionPath ledger locals pid w history ⟨items,head,false⟩ u middle) :
    ∃ v last after,
      DeadIntervals.Path (.deadBatch pid head) pid [] locals items.length items u middle ledger v last after ∧
      Accounted last after [] locals v.wg ∧
      runPrefix (CausalJournal.transmit pid) w history = runPrefix (DeadEntry.repay pid head.keypair) v last ∧
      ∀ n, n < items.length → ∃ cutWorld cutHistory cutLedger skb remaining nextWorld nextHistory nextLedger,
        items.drop n = skb :: remaining ∧
        DeadIntervals.Path (.deadBatch pid head) pid [] locals n items u middle ledger cutWorld cutHistory cutLedger ∧
        DeadIntervals.Iteration (.deadBatch pid head) pid [] locals skb remaining
          cutWorld cutHistory cutLedger nextWorld nextHistory nextLedger ∧
        DeadIntervals.Path (.deadBatch pid head) pid [] locals remaining.length remaining
          nextWorld nextHistory nextLedger v last after ∧
        ∀ phase : CleanupPrimitive.Phase,
          Awaiting phase (.deadBatch pid head) pid [] locals skb remaining
            cutWorld cutHistory cutLedger nextWorld nextLedger ∧
          runPrefix (workerDeadPrimitivePrefix pid n phase) w history =
            (.ok ((),nextWorld),current phase cutWorld skb cutHistory) ∧
          runPrefix (do due phase (.deadBatch pid head) skb cutWorld nextWorld; loop (.deadBatch pid head) remaining)
            nextWorld (current phase cutWorld skb cutHistory) = (.ok ((),v),last) := by
  obtain ⟨v,last,after,full,accounted,continued,_⟩ := path.dead_cleanup_intervals
  refine ⟨v,last,after,full,accounted,continued,?_⟩
  intro n bound
  obtain ⟨cutWorld,cutHistory,cutLedger,skb,remaining,nextWorld,nextHistory,nextLedger,
    leading,dropped,iteration,tail⟩ := next_iteration full n bound
  refine ⟨cutWorld,cutHistory,cutLedger,skb,remaining,nextWorld,nextHistory,nextLedger,
    dropped,leading,iteration,tail,?_⟩
  intro phase
  exact ⟨iteration_awaiting phase iteration,path.dead_primitive_prefix_run leading dropped iteration phase,
    iteration_continuation iteration tail phase⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
