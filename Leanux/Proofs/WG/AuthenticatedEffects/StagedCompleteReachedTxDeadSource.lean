import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxSelectionPointFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDeadPrimitiveWorker

/-! Fixed DEAD-worker loop cuts and their original continuations. Point
constructors contain source runs, never an incoming ownership certificate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxDead
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CreateDisposal HandshakeSecurity.StagedConservation

theorem loop_append (reason : Terminal.Reason) (done rest : List SkbId) :
    loop reason (done ++ rest) = (do loop reason done; loop reason rest) := by
  induction done with
  | nil => simp [loop]
  | cons skb done ih => simp only [List.cons_append,loop_cons,ih,bind_assoc]

theorem selected_continuation
    (selected : runPrefix (workerSelection pid) w h=(.ok (some ⟨items,head,false⟩,u),middle)) :
    runPrefix (CausalJournal.transmit pid) w h=
      runPrefix (do loop (.deadBatch pid head) items; DeadEntry.repay pid head.keypair) u middle := by
  rw [worker_selection_factor,runPrefix_bind,selected]
  exact congrArg (fun action=>runPrefix action u middle) (DeadEntry.dead_factor pid items head)

theorem boundary_continuation
    (selected : runPrefix (workerSelection pid) w h=(.ok (some ⟨items,head,false⟩,u),middle))
    (leading : runPrefix (loop (.deadBatch pid head) (items.take n)) u middle=(.ok ((),v),last)) :
    runPrefix (CausalJournal.transmit pid) w h=
      runPrefix (do loop (.deadBatch pid head) (items.drop n); DeadEntry.repay pid head.keypair) v last := by
  rw [selected_continuation selected]
  have split : loop (.deadBatch pid head) items =
      (do loop (.deadBatch pid head) (items.take n); loop (.deadBatch pid head) (items.drop n)) :=
    (congrArg (loop (.deadBatch pid head)) (List.take_append_drop n items).symm).trans
      (loop_append (.deadBatch pid head) (items.take n) (items.drop n))
  rw [split,bind_assoc,runPrefix_bind,leading]

theorem primitive_continuation
    (selected : runPrefix (workerSelection pid) w h=(.ok (some ⟨items,head,false⟩,u),middle))
    (leading : runPrefix (loop (.deadBatch pid head) (items.take n)) u middle=(.ok ((),v),last))
    (dropped : items.drop n=skb::remaining)
    (native : (liftWG (freeTxSkb skb)).run v=.ok ((),q)) (phase : CleanupPrimitive.Phase) :
    runPrefix (CausalJournal.transmit pid) w h=
      runPrefix (do CleanupPrimitive.due phase (.deadBatch pid head) skb v q
                    loop (.deadBatch pid head) remaining
                    DeadEntry.repay pid head.keypair)
        q (CleanupPrimitive.current phase v skb last) := by
  rw [boundary_continuation selected leading,dropped,loop_cons,bind_assoc,runPrefix_bind,
    CleanupPrimitive.original_suffix phase (.deadBatch pid head) skb v q last native,
    CleanupPrimitive.due_run,runPrefix_bind,CleanupPrimitive.due_run]

inductive Point (pid : PeerId) (w : World) (h : List CausalJournal.Event) :
    World → List CausalJournal.Event → Prop where
  | boundary
      (selected : runPrefix (workerSelection pid) w h=(.ok (some ⟨items,head,false⟩,u),middle))
      (bound : n ≤ items.length)
      (leading : runPrefix (loop (.deadBatch pid head) (items.take n)) u middle=(.ok ((),v),last)) :
      Point pid w h v last
  | primitive
      (selected : runPrefix (workerSelection pid) w h=(.ok (some ⟨items,head,false⟩,u),middle))
      (leading : runPrefix (loop (.deadBatch pid head) (items.take n)) u middle=(.ok ((),v),last))
      (dropped : items.drop n=skb::remaining)
      (native : (liftWG (freeTxSkb skb)).run v=.ok ((),q)) (phase : CleanupPrimitive.Phase) :
      Point pid w h q (CleanupPrimitive.current phase v skb last)

theorem Point.remaining (point : Point pid w h u middle) :
    ∃remaining,runPrefix (CausalJournal.transmit pid) w h=runPrefix remaining u middle := by
  cases point with
  | boundary selected _ leading=>exact ⟨_,boundary_continuation selected leading⟩
  | primitive selected leading dropped native phase=>
    exact ⟨_,primitive_continuation selected leading dropped native phase⟩

noncomputable def remainder (point : Point pid w h u middle) : PrefixM CausalJournal.Event Bool :=
  Classical.choose point.remaining

theorem remainder_run (point : Point pid w h u middle) :
    runPrefix (CausalJournal.transmit pid) w h=runPrefix (remainder point) u middle :=
  Classical.choose_spec point.remaining

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxDead
