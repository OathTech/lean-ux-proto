import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCleanupPrimitiveRuns

/-! Between the native erase and the labelled event, this one obligation is
a fixed pending receipt. Accounted is asserted at the exact total emission's
history on the same native world, not at the shorter history where its old
allocated cell is already absent. No intervening operation can fail. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CleanupPrimitive
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation CreateDisposal HandshakeSecurity.StagedConservation

inductive Awaiting (phase : Phase) (reason : Terminal.Reason) (pid : PeerId)
    (debts : List CleanupDebt) (locals : List TxLocalBatch) (skb : SkbId) (remaining : List SkbId)
    (w : World) (history : List CausalJournal.Event) (ledger : Ledger) (v : World) (after : Ledger) : Prop where
  | pendingReceipt (ticket : Staged.Origins.Ticket) (position ordinal generation : Nat) (value : DataPacket)
      (initial : Accounted history ledger debts (⟨.selected,pid,skb :: remaining⟩ :: locals) w.wg)
      (pending : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger)
      (origin : Origin history position ordinal generation skb value)
      (native : (liftWG (freeTxSkb skb)).run w = .ok ((),v))
      (assigned : after = settle [ticket]
        (.disposed (history ++ [readEvent w.wg skb,releaseEvent w.wg skb]).length reason) ledger)
      (step : Staged.Obligations.Step ledger after)
      (terminal : (ticket,Status.terminal
        (.disposed (history ++ [readEvent w.wg skb,releaseEvent w.wg skb]).length reason)) ∈ after)
      (accounted : Accounted (finished reason skb w v history) after debts
        (⟨.selected,pid,remaining⟩ :: locals) v.wg)

/-- The original successful labelled iteration supplies its exact pending
receipt at both post-mutation phases. The assigned ledger is the same ledger
already retained by the iteration path, not a separately chosen successor. -/
theorem iteration_awaiting (phase : Phase)
    (cut : DeadIntervals.Iteration reason pid debts locals skb remaining w history ledger v last after) :
    Awaiting phase reason pid debts locals skb remaining w history ledger v after := by
  classical
  obtain ⟨ticket,position,ordinal,generation,value,accesses,pending,origin,cleanup,recorded,assigned,valid⟩ := cut.settlement
  have native : (liftWG (freeTxSkb skb)).run w = .ok ((),v) := valid
  have exactCleanup := cleanup_run skb w v history native
  have sameAccess : accesses = [readEvent w.wg skb,releaseEvent w.wg skb] :=
    List.append_cancel_left (congrArg Prod.snd (cleanup.symm.trans exactCleanup))
  have sameLast : last = finished reason skb w v history :=
    congrArg Prod.snd (cut.run.symm.trans (labelled_run reason skb w v history native))
  rw [sameAccess] at assigned
  have terminal : (ticket,Status.terminal
      (.disposed (history ++ [readEvent w.wg skb,releaseEvent w.wg skb]).length reason)) ∈ after := by
    rw [assigned,settle]
    exact List.mem_map.mpr ⟨(ticket,Status.pending (.allocated position ordinal)),pending,by simp⟩
  exact .pendingReceipt ticket position ordinal generation value cut.entry pending origin native assigned
    cut.result.1 terminal (sameLast ▸ cut.result.2.1)

/-- The disposition has happened in the native world. Its remaining records
are a fixed total suffix on that same world; only that exact completed
history carries ordinary Accounted while emission is outstanding. -/
theorem Awaiting.linearized
    (waiting : Awaiting phase reason pid debts locals skb remaining w history ledger v after) :
    runPrefix (atPhase phase w skb) w history = (.ok ((),v),current phase w skb history) ∧
      PacketMaterial.view v.wg skb = none ∧
      Staged.Obligations.Step ledger after ∧
      runPrefix (due phase reason skb w v) v (current phase w skb history) =
        (.ok ((),v),finished reason skb w v history) ∧
      Accounted (finished reason skb w v history) after debts (⟨.selected,pid,remaining⟩ :: locals) v.wg ∧
      runPrefix (free reason skb) w history =
        runPrefix (due phase reason skb w v) v (current phase w skb history) := by
  cases waiting with
  | pendingReceipt ticket position ordinal generation value initial pending origin native assigned step terminal accounted =>
    exact ⟨prefix_run phase skb w v history native,(FirstTerminal.cleanup_views skb w v native).2.1,
      step,due_run phase reason skb w v history,accounted,original_suffix phase reason skb w v history native⟩

/-- Retaining the old pending-cell claim at this native post-state would be
false. The explicit pending-receipt carrier is required until emission. -/
theorem Awaiting.not_old_accounted
    (waiting : Awaiting phase reason pid debts locals skb remaining w history ledger v after) :
    ¬ Accounted (current phase w skb history) ledger debts (⟨.selected,pid,skb :: remaining⟩ :: locals) v.wg := by
  cases waiting with
  | pendingReceipt ticket position ordinal generation value initial pending origin native assigned step terminal accounted =>
    intro old
    have original : Origin (current phase w skb history) position ordinal generation skb value := by
      cases phase with
      | mutated => exact origin.append [readEvent w.wg skb]
      | released => exact origin.append [readEvent w.wg skb,releaseEvent w.wg skb]
    have resident := ((old.entry.core.physical.resident ticket position ordinal pending).at_origin original).2
    rw [(FirstTerminal.cleanup_views skb w v native).2.1] at resident
    cases resident

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CleanupPrimitive
