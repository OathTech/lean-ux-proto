import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePhasePassive
import Leanux.Proofs.WG.AuthenticatedEffects.CausalCallbackQuietNative

/-! Actual nested peer repayment retains creation phases on the same counted
successor ledger. Its recorded disposal is accounted rather than declared
quiet; the primitive release interior remains a separately named child. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePhase
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CreateDisposal CompleteCarrier StagedTerminalComplete Staged.Obligations
open HandshakeSecurity.StagedDisposal CreatePoints
set_option maxHeartbeats 600000

theorem release_account (peer : Option PeerId)
    (before : Accounted h ledger debts active w.wg)
    (performed : runPrefix (Admission.actualOps.release peer) w h=(.ok ((),v),last)) :
    ∃ next suffix,Staged.Obligations.Step ledger next ∧ AllocatedFrame ledger next ∧
      last=h++suffix ∧ Accounted last next debts active v.wg := by
  have actual:=StagedTerminalComplete.Source.Nested.actual_cases peer before.entry before.complete
  rw [performed] at actual
  obtain ⟨value,g,a,cutHistory,next,cutRun,history,step,frame,settlement,entry,complete⟩:=actual
  obtain ⟨suffix,extended⟩:=(CausalJournal.CallbackQuiet.release (fun _=>none : CausalJournal.Event→Option Unit)
    (fun _=>rfl) (fun _=>rfl) peer).1 w h
  change (runPrefix (Admission.actualOps.release peer) w h).2=_ at extended
  rw [performed] at extended
  exact ⟨next,suffix,step,frame,extended,entry,complete⟩

theorem release_normal (peer : Option PeerId)
    (before : Live rootLedger debts locals pid items h w.wg)
    (performed : runPrefix (Admission.actualOps.release peer) w h=(.ok (value,v),last)) :
    Live rootLedger debts locals pid items last v.wg := by
  cases value
  cases before with
  | unpublished current steps pending account=>
    obtain ⟨next,suffix,step,frame,grown,after⟩:=release_account peer account performed
    exact .unpublished next (steps.trans step) (grown ▸ (pending.allocated_frame frame).append suffix) after
  | queued current steps pending account=>
    obtain ⟨next,suffix,step,frame,grown,after⟩:=release_account peer account performed
    exact .queued next (steps.trans step) (grown ▸ (pending.allocated_frame frame).append suffix) after
  | cleanup current steps reason done remaining ordered settled pending account=>
    obtain ⟨next,suffix,step,frame,grown,after⟩:=release_account peer account performed
    exact .cleanup next (steps.trans step) reason done remaining ordered
      (grown ▸ settled.transport suffix step) (grown ▸ (pending.allocated_frame frame).append suffix) after
  | disposed current steps reason settled account=>
    obtain ⟨next,suffix,step,frame,grown,after⟩:=release_account peer account performed
    exact .disposed next (steps.trans step) reason (grown ▸ settled.transport suffix step) after

theorem release_covers (peer : Option PeerId)
    (before : Live rootLedger debts locals pid items h w.wg) :
    Covers (fun h w=>Live rootLedger debts locals pid items h w.wg) (.child (.release peer)) w h :=
  covers_child (.release peer) before (fun _ _ _ run=>release_normal peer before run)

theorem published_covers (batch : List SkbId) (state : PacketState)
    (before : Live rootLedger debts locals pid items h w.wg) :
    Covers (fun h w=>Live rootLedger debts locals pid items h w.wg) (publishedShape batch state) w h := by
  have borrowed:=passive_covers (borrow_passive batch) before
  apply covers_bind borrowed
  intro pair v last run
  have marked:=passive_covers (mark_passive pair.2 pair.1 state) (borrowed.normal run)
  exact covers_bind marked (fun _ _ _ written=>covers_pure _ (marked.normal written))

theorem publish_covers (batch : List SkbId) (state : PacketState)
    (before : Live rootLedger debts locals pid items h w.wg) :
    Covers (fun h w=>Live rootLedger debts locals pid items h w.wg) (publishShape batch state) w h := by
  unfold publishShape
  apply covers_marked
  erw [covers_type_cast _ (published_prefix_factor batch state).symm]
  have published:=published_covers batch state before
  apply covers_bind published
  intro pair v last run
  have scheduled:=passive_covers (schedule_passive pair.2) (published.normal run)
  exact covers_bind scheduled (fun _ _ _ ready=>release_covers _ (scheduled.normal ready))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePhase
