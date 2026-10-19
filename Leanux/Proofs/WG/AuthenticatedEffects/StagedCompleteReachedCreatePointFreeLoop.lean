import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePointFree

/-! The original ordered refusal loop, with the exact native erase and
pending receipt of each member. Each successor consumes its own fixed
ticket once, before the remaining original list is visited. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePoints
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CreateDisposal CompleteCarrier StagedTerminalComplete Staged.Obligations
open HandshakeSecurity.StagedConservation
set_option maxHeartbeats 600000

inductive FreeWalk (reason : Terminal.Reason) (pid : PeerId) (debts : List CleanupDebt)
    (locals : List TxLocalBatch) : List SkbId → World → List CausalJournal.Event → Ledger →
      World → List CausalJournal.Event → Ledger → Type where
  | nil (before : Accounted h ledger debts (⟨.unpublished,pid,[]⟩::locals) w.wg) :
      FreeWalk reason pid debts locals [] w h ledger w h ledger
  | cons (cut : FreeCut reason pid skb rest h ledger debts locals w)
      (remaining : FreeWalk reason pid debts locals rest cut.after
        (CleanupPrimitive.finished reason skb w cut.after h) cut.next v last final) :
      FreeWalk reason pid debts locals (skb::rest) w h ledger v last final

/-- This source walk is total from its real pending batch. The receipt list
is accumulated in the same order as the native for-loop. -/
theorem free_walk
    (before : Accounted history ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg)
    (pending : PendingBatch history ledger items) :
    ∃ v last final, Nonempty (FreeWalk reason pid debts locals items w history ledger v last final) := by
  induction items generalizing w history ledger with
  | nil=>exact ⟨w,history,ledger,⟨.nil before⟩⟩
  | cons skb rest ih=>
    obtain ⟨cut⟩:=free_cut reason before pending
    have unique : (skb::rest).Nodup := (List.nodup_append.mp before.entry.inventory.localUnique).1
    have absent:= (List.nodup_cons.mp unique).1
    have restPending : PendingBatch history ledger rest :=
      fun item member=>pending item (List.mem_cons_of_mem skb member)
    have nextPending : PendingBatch (CleanupPrimitive.finished reason skb w cut.after history) cut.next rest := by
      rw [cut.assigned]
      exact (restPending.settle_other before.entry.core.valid cut.pending cut.origin absent _).append _
    obtain ⟨v,last,final,⟨walk⟩⟩:=ih cut.accounted nextPending
    exact ⟨v,last,final,⟨.cons cut walk⟩⟩

theorem FreeWalk.run
    (walk : FreeWalk reason pid debts locals items w history ledger v last final) :
    runPrefix (loop reason items) w history=(.ok ((),v),last) := by
  induction walk with
  | nil=>rfl
  | cons cut remaining ih=>
    rw [loop_cons,runPrefix_bind,cut.original]
    exact ih

theorem FreeWalk.accounted
    (walk : FreeWalk reason pid debts locals items w history ledger v last final) :
    Accounted last final debts locals v.wg := by
  induction walk with
  | nil before=>exact ⟨empty_local .unpublished before.entry,before.complete⟩
  | cons cut remaining ih=>exact ih

theorem FreeWalk.step
    (walk : FreeWalk reason pid debts locals items w history ledger v last final) :
    Staged.Obligations.Step ledger final := by
  induction walk with
  | nil=>exact .refl _
  | cons cut remaining ih=>exact cut.step.trans ih

/-- A fixed original loop cursor retains the exact ordered cohort and saved
pre-erase world. No arbitrary split of an extensionally equal action is used. -/
inductive FreeCursor (reason : Terminal.Reason) (pid : PeerId) (debts : List CleanupDebt)
    (locals : List TxLocalBatch) : List SkbId → World → List CausalJournal.Event → Ledger →
      SkbId → List SkbId → World → List CausalJournal.Event → Ledger → Type where
  | here : FreeCursor reason pid debts locals (skb::rest) w h ledger skb rest w h ledger
  | later (cut : FreeCut reason pid head rest h ledger debts locals w)
      (cursor : FreeCursor reason pid debts locals rest cut.after
        (CleanupPrimitive.finished reason head w cut.after h) cut.next skb tail u middle active) :
      FreeCursor reason pid debts locals (head::rest) w h ledger skb tail u middle active

theorem FreeCursor.residual
    (cursor : FreeCursor reason pid debts locals items w history ledger skb rest u middle active) :
    runPrefix (loop reason items) w history=runPrefix (loop reason (skb::rest)) u middle := by
  induction cursor with
  | here=>rfl
  | later cut cursor ih=>rw [loop_cons,runPrefix_bind,cut.original]; exact ih

theorem FreeCursor.pending_receipt
    (cursor : FreeCursor reason pid debts locals items w history ledger skb rest u middle active)
    (cut : FreeCut reason pid skb rest middle active debts locals u) (phase : CleanupPrimitive.Phase) :
    runPrefix (loop reason items) w history=
      runPrefix (do CleanupPrimitive.due phase reason skb u cut.after; loop reason rest)
        cut.after (CleanupPrimitive.current phase u skb middle) := by
  rw [cursor.residual,loop_cons,runPrefix_bind,runPrefix_bind]
  rw [cut.pending_receipt phase |>.2.2.1]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePoints
