import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePublicationFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePassive
import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteOriginalRelease
import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptQuietHistory

/-! The encryption publication repays its own native borrow. Its actual
original release receipt is nonfinal, including the prefix before any later
Stop; completeness is established at that cut, not from native erasure. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteEncrypt
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity AllocatedObligation CausalJournal
open Staged.Obligations StagedTerminalComplete HandshakeSecurity.StagedDisposal
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

/-- Exact native borrow and publication middle before the observed repayment. -/
theorem publication_factor (items : List SkbId) (state : PacketState) :
    HandshakeSecurity.StagedDisposal.Publication.observed Event.stagedDisposal stagedDisposal? items state =
      (do let (first,pid) ← liftWGPrefix (AllocatedObligation.Publication.borrowNative items)
          liftWGPrefix (TxDisposition.publicationMiddle pid first state)
          CausalJournal.peerRelease (some pid)) := by
  unfold HandshakeSecurity.StagedDisposal.Publication.observed
    HandshakeSecurity.StagedDisposal.Publication.withRelease AllocatedObligation.Publication.borrowNative
  cases items.head? with
  | none => rfl
  | some first =>
    simp only [Queued.lift_bind,Queued.lift_pure,Queued.lift_if,bind_assoc,pure_bind,
      TxDisposition.publicationMiddle,TxDisposition.bind_ite]
    rfl

theorem publication_run (items : List SkbId) (state : PacketState)
    (w : WGWorld) (a : Ambient) (history : List CausalJournal.Event) :
    runWGPrefix (HandshakeSecurity.StagedDisposal.Publication.observed
      Event.stagedDisposal stagedDisposal? items state) w a history =
    match ((AllocatedObligation.Publication.borrowNative items).run w).run a with
    | .error stop => (.error stop,history)
    | .ok (((first,pid),u),b) =>
      match ((TxDisposition.publicationMiddle pid first state).run u).run b with
      | .error stop => (.error stop,history)
      | .ok (((),v),c) => runWGPrefix (CausalJournal.peerRelease (some pid)) v c history := by
  rw [publication_factor]
  simp only [runWGPrefix,runStatePrefix_bind,liftWGPrefix,runStatePrefix_lift]
  cases acquired : ((AllocatedObligation.Publication.borrowNative items).run w).run a with
  | error stop => rfl
  | ok out =>
    obtain ⟨⟨⟨first,pid⟩,u⟩,b⟩ := out
    simp only []
    cases published : ((TxDisposition.publicationMiddle pid first state).run u).run b with
    | error stop => rfl
    | ok out => obtain ⟨⟨ignored,v⟩,c⟩ := out; cases ignored; rfl

/-- Every reached repayment is nonfinal by the earlier borrow on this same
native source path. A stopped borrow or middle has emitted no terminal. -/
theorem publication_complete (items : List SkbId) (state : PacketState)
    (w : WGWorld) (a : Ambient) (before : Complete history ledger) :
    Complete (runWGPrefix (HandshakeSecurity.StagedDisposal.Publication.observed
      Event.stagedDisposal stagedDisposal? items state) w a history).2 ledger := by
  rw [publication_run]
  cases acquired : ((AllocatedObligation.Publication.borrowNative items).run w).run a with
  | error stop => exact before
  | ok out =>
    obtain ⟨⟨⟨first,pid⟩,u⟩,b⟩ := out
    simp only []
    have funded := AllocatedObligation.Publication.borrow_funded items a b acquired
    cases published : ((TxDisposition.publicationMiddle pid first state).run u).run b with
    | error stop => exact before
    | ok out =>
      obtain ⟨⟨ignored,v⟩,c⟩ := out
      cases ignored
      have fundedAfter := AllocatedObligation.Publication.middle_funded pid first state funded b c published
      obtain ⟨g,d,cut⟩ := AllocatedObligation.Publication.release_cut_nonfinal pid fundedAfter c
      have actual := StagedAdmission.Front.put_run (some pid) v c history
      change runWGPrefix (CausalJournal.peerRelease (some pid)) v c history = _ at actual
      rw [cut] at actual
      simp only []
      rw [actual]
      exact before.append_quiet (suffix := [.stagedDisposal (.release (some pid) ⟨none,v,g,c,d⟩)])
        (by intro event member; cases List.mem_singleton.mp member; exact release_none_quiet rfl)

theorem publication_history (items : List SkbId) (state : PacketState) :
    Driver.StateHistorySafe (fun h => Complete h ledger)
      (HandshakeSecurity.StagedDisposal.Publication.observed Event.stagedDisposal stagedDisposal? items state) := by
  intro w a h before
  obtain ⟨suffix,extended⟩ := HandshakeSecurity.StagedDisposal.Publication.appends
    (Decoration.release Event.stagedDisposal stagedDisposal?)
    (fun _ => StateAppends.focus _ _ _) items state w a h
  have kept := publication_complete items state w a before
  refine ⟨suffix,extended,kept,?_⟩
  cases result : (runPrefix ((HandshakeSecurity.StagedDisposal.Publication.observed
    Event.stagedDisposal stagedDisposal? items state).run w) a h).1 with
  | error stop => trivial
  | ok out => exact kept

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteEncrypt
