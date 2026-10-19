import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePointContract

/-! Semantic phases of the same creation invocation. Each live phase retains
its actual world, successor ledger and ordered original cohort. An erased
cell awaiting its original receipt is separate from every live account. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePhase
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CreateDisposal CompleteCarrier StagedTerminalComplete Staged.Obligations
open HandshakeSecurity.StagedConservation CreatePoints
set_option maxHeartbeats 600000

inductive Live (rootLedger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) (items : List SkbId) : List CausalJournal.Event → WGWorld → Prop where
  | unpublished (current : Ledger) (steps : Staged.Obligations.Step rootLedger current)
      (pending : PendingBatch h current items)
      (account : Accounted h current debts (⟨.unpublished,pid,items⟩::locals) w) : Live rootLedger debts locals pid items h w
  | queued (current : Ledger) (steps : Staged.Obligations.Step rootLedger current)
      (pending : PendingBatch h current items)
      (account : Accounted h current debts locals w) : Live rootLedger debts locals pid items h w
  | cleanup (current : Ledger) (steps : Staged.Obligations.Step rootLedger current)
      (reason : Terminal.Reason) (done remaining : List SkbId) (ordered : items=done++remaining)
      (settled : AllDropped h current reason done) (pending : PendingBatch h current remaining)
      (account : Accounted h current debts (⟨.unpublished,pid,remaining⟩::locals) w) : Live rootLedger debts locals pid items h w
  | disposed (current : Ledger) (steps : Staged.Obligations.Step rootLedger current)
      (reason : Terminal.Reason) (settled : AllDropped h current reason items)
      (account : Accounted h current debts locals w) : Live rootLedger debts locals pid items h w

inductive Evidence (rootLedger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) (items : List SkbId) : List CausalJournal.Event → World → Prop where
  | live (account : Live rootLedger debts locals pid items h w.wg) : Evidence rootLedger debts locals pid items h w
  | awaiting (current : Ledger) (steps : Staged.Obligations.Step rootLedger current)
      (reason : Terminal.Reason) (done : List SkbId) (ordered : items=done++(skb::remaining))
      (settled : AllDropped h current reason done)
      (cut : FreeCut reason pid skb remaining h current debts locals w)
      (phase : CleanupPrimitive.Phase) :
      Evidence rootLedger debts locals pid items (CleanupPrimitive.current phase w skb h) cut.after

theorem entry_evidence (before : Accounted h ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg)
    (pending : PendingBatch h ledger items) : Evidence ledger debts locals pid items h w :=
  .live (.unpublished ledger (.refl _) pending before)

theorem Live.accounted (kept : Live rootLedger debts locals pid items h w) :
    ∃ current active, Staged.Obligations.Step rootLedger current ∧ Accounted h current debts active w := by
  cases kept with
  | unpublished current steps pending account=>exact ⟨current,_,steps,account⟩
  | queued current steps pending account=>exact ⟨current,_,steps,account⟩
  | cleanup current steps reason done remaining ordered settled pending account=>exact ⟨current,_,steps,account⟩
  | disposed current steps reason settled account=>exact ⟨current,_,steps,account⟩

theorem allDropped_append (settled : AllDropped h ledger reason items) (suffix : List CausalJournal.Event) :
    AllDropped (h++suffix) ledger reason items :=
  fun id member=>(settled id member).transport suffix (.refl _)

/-- A literal native view frame and independently quiet emitted suffix retain
all phase data. This is not a rule for counted release or packet erasure. -/
theorem Live.views (kept : Live rootLedger debts locals pid items h w)
    (suffix : List CausalJournal.Event)
    (births : ∀ event∈suffix,Staged.Obligations.birthPackets event=[])
    (terminals : ∀ event∈suffix,Quiet event)
    (view : StagedEntry.view v=StagedEntry.view w) : Live rootLedger debts locals pid items (h++suffix) v := by
  cases kept with
  | unpublished current steps pending account=>
    exact .unpublished current steps (pending.append suffix) ((account.append_quiet suffix births terminals).same_view view)
  | queued current steps pending account=>
    exact .queued current steps (pending.append suffix) ((account.append_quiet suffix births terminals).same_view view)
  | cleanup current steps reason done remaining ordered settled pending account=>
    exact .cleanup current steps reason done remaining ordered (allDropped_append settled suffix)
      (pending.append suffix) ((account.append_quiet suffix births terminals).same_view view)
  | disposed current steps reason settled account=>
    exact .disposed current steps reason (allDropped_append settled suffix)
      ((account.append_quiet suffix births terminals).same_view view)

theorem awaiting_not_old (cut : FreeCut reason pid skb remaining h current debts locals w)
    (phase : CleanupPrimitive.Phase) :
    ¬Accounted (CleanupPrimitive.current phase w skb h) current debts
      (⟨.unpublished,pid,skb::remaining⟩::locals) cut.after.wg := cut.not_old_accounted phase

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePhase
