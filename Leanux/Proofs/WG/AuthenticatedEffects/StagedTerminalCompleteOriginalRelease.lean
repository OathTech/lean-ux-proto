import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteReleaseSource

/-! The original release observer has the same counted settlement as the
nested observer, with no access-event prefix. A stopped timer/retirement
suffix keeps the paired ledger at the actual preceding receipt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalComplete.Source.Original
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity Staged.Obligations AllocatedObligation CausalJournal
open HandshakeSecurity.StagedDisposal

inductive Frontier (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (peer : Option PeerId) (w : WGWorld) (ambient : Ambient) (history : List CausalJournal.Event)
    (stop : Stop) (last : List CausalJournal.Event) : Prop where
  | cutStopped
      (entry : StagedEntry.Inv history ledger debts locals w)
      (complete : Complete history ledger)
      (failed : ((releaseCut peer).run w).run ambient = .error stop)
      (same : last = history)
  | finishStopped (pid : PeerId) (p : Peer) (g : WGWorld) (clock : Ambient) (afterLedger : Ledger)
      (performed : ((releaseCut peer).run w).run ambient = .ok ((some (pid,p),g),clock))
      (step : Staged.Obligations.Step ledger afterLedger) (frame : AllocatedFrame ledger afterLedger)
      (settlement : PeerRelease.Successor (some (pid,p)) w history.length ledger afterLedger)
      (entry : StagedEntry.Inv (history ++ [.stagedDisposal (.release peer ⟨some (pid,p),w,g,ambient,clock⟩)])
        afterLedger debts locals g)
      (complete : Complete (history ++ [.stagedDisposal (.release peer ⟨some (pid,p),w,g,ambient,clock⟩)]) afterLedger)
      (failed : ((releaseFinish pid p).run g).run clock = .error stop)
      (same : last = history ++ [.stagedDisposal (.release peer ⟨some (pid,p),w,g,ambient,clock⟩)])

def Returned (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (peer : Option PeerId) (w : WGWorld) (ambient : Ambient) (history : List CausalJournal.Event)
    (last : List CausalJournal.Event) (v : WGWorld) : Prop :=
  ∃ value g clock afterLedger,
    ((releaseCut peer).run w).run ambient = .ok ((value,g),clock) ∧
    last = history ++ [.stagedDisposal (.release peer ⟨value,w,g,ambient,clock⟩)] ∧
    Staged.Obligations.Step ledger afterLedger ∧ AllocatedFrame ledger afterLedger ∧
    PeerRelease.Successor value w history.length ledger afterLedger ∧
    StagedEntry.Inv last afterLedger debts locals v ∧ Complete last afterLedger

/-- Both directions of terminal accounting survive the actual original
release, with the same ledger retained even when its native finish stops. -/
theorem actual_cases (peer : Option PeerId) (ambient : Ambient)
    (before : StagedEntry.Inv history ledger debts locals w) (complete : Complete history ledger) :
    match (runWGPrefix (CausalJournal.peerRelease peer) w ambient history).1 with
    | .error stop => Frontier ledger debts locals peer w ambient history stop
        (runWGPrefix (CausalJournal.peerRelease peer) w ambient history).2
    | .ok (((),v),_) => Returned ledger debts locals peer w ambient history
        (runWGPrefix (CausalJournal.peerRelease peer) w ambient history).2 v := by
  have equation := StagedAdmission.Front.put_run peer w ambient history
  change runWGPrefix (CausalJournal.peerRelease peer) w ambient history = _ at equation
  rw [equation]
  cases native : ((releaseCut peer).run w).run ambient with
  | error stop => exact .cutStopped before complete native rfl
  | ok out =>
    obtain ⟨⟨value,g⟩,clock⟩ := out
    obtain ⟨afterLedger,step,frame,settlement,entry,finished⟩ :=
      original_native_entry peer before complete ambient clock native
    cases value with
    | none => exact ⟨none,g,clock,afterLedger,native,rfl,step,frame,settlement,entry,finished⟩
    | some pair =>
      obtain ⟨pid,p⟩ := pair
      simp only []
      cases suffix : ((releaseFinish pid p).run g).run clock with
      | error stop =>
        exact .finishStopped pid p g clock afterLedger native step frame settlement
          entry finished suffix rfl
      | ok out =>
        obtain ⟨⟨ignored,v⟩,lastClock⟩ := out
        cases ignored
        have final := (hoare_iff_run_ambient _ _ _).mp (StagedEntry.OriginalRelease.finish pid p)
          g clock () v lastClock entry suffix
        exact ⟨some (pid,p),g,clock,afterLedger,native,rfl,step,frame,settlement,final,finished⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalComplete.Source.Original
