import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCrypted

/-! Concrete source prefixes of disposal, chosen from three fixed call sites.
These are the original cleanup/key/recorded-peer-cut sequence, not existential
prefix programs related to the caller only by extensional equality. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation AllocatedObligation.CompletionBatch
open AllocatedObligation.CompletionBatch.Converse

def recordedPeerCut (peer : Option PeerId) : PrefixM CausalJournal.Event (Option (PeerId × Peer)) :=
  liftWGObserver (receiptWGObserved (PeerRelease.cut peer)
    (fun receipt => .stagedDisposal (.release peer receipt)))

theorem recordedPeerCut_run (peer : Option PeerId)
    (performed : runWGPrefix (PeerRelease.cut peer) w.wg w.ambient history =
      (.ok ((value,g),a),last)) :
    runPrefix (recordedPeerCut peer) w history =
      (.ok (value,{w with wg := g,ambient := a}),
        last ++ [PeerRelease.receipt peer value w.wg g w.ambient a]) := by
  rw [recordedPeerCut,liftWGObserver_run,runWGPrefix_receiptWGObserved,performed]
  rfl

inductive RepaymentStage where
  | key
  | peer
  | finish

def repaymentPrefix (pid : PeerId) (key : KeypairId) : RepaymentStage → PrefixM CausalJournal.Event Unit
  | .key => pure ()
  | .peer => keyRepayment key
  | .finish => do
      keyRepayment key
      _ ← recordedPeerCut (some pid)
      pure ()

theorem RepaymentStopped.prefix
    (stopped : RepaymentStopped context ledger key w history reason last saved) :
    ∃ stage, runPrefix (repaymentPrefix context.pid key stage) w history =
      (.ok ((),saved.world),saved.before) := by
  cases stopped with
  | keyStopped => exact ⟨.key,rfl⟩
  | peerStopped keyWorld keyHistory paid _ _ projection =>
    cases projection with
    | cutStopped => exact ⟨.peer,paid⟩
    | finishStopped value g a cutHistory after performed =>
      refine ⟨.finish,?_⟩
      change runPrefix (keyRepayment key >>= fun _ => _) w history = _
      rw [runPrefix_bind,paid]
      dsimp only
      rw [runPrefix_bind,recordedPeerCut_run (some context.pid) performed]
      rfl

def disposalPrefix (context : Context) (key : KeypairId) (stage : RepaymentStage) :
    PrefixM CausalJournal.Event Unit := do
  freeLoop cleanupOps context.items
  repaymentPrefix context.pid key stage

/-- The accounted stopped cut is an output of one of the fixed original
disposal prefixes, executed from precisely the supplied caller entry. -/
theorem DisposalInterval.reached_cut
    (interval : DisposalInterval context ledger debts key w history (.error reason) last) :
    ∃ stage, ∃ saved : Cut context,
      runPrefix (disposalPrefix context key stage) w history = (.ok ((),saved.world),saved.before) ∧
      Staged.Obligations.Step ledger saved.ledger ∧ saved.Valid reason last := by
  obtain ⟨freeWorld,freeHistory,saved,path,stopped,step,valid⟩ := interval.stopped
  obtain ⟨stage,prefixRun⟩ := stopped.prefix
  refine ⟨stage,saved,?_,step,valid⟩
  rw [disposalPrefix,runPrefix_bind,path.run]
  exact prefixRun

def cryptedDisposalPrefix (context : Context) (key : KeypairId) (stage : RepaymentStage) :
    PrefixM CausalJournal.Event Unit := do
  scopedCompletion context
  disposalPrefix context key stage

/-- Stops after completed sending have a cut reached by a fixed original
crypted-caller prefix. Stops inside sending retain their explicit unresolved
inner frontier instead of being promoted to this stronger conclusion. -/
theorem CryptedInterval.stopped_cut
    (interval : CryptedInterval context ledger key w history (.error reason) last) :
    (runPrefix (scopedCompletion context) w history = (.error reason,last) ∧
      Converse.SendingStopped context ledger [] reason last) ∨
    ∃ stage, ∃ saved : Cut context,
      runPrefix (cryptedDisposalPrefix context key stage) w history = (.ok ((),saved.world),saved.before) ∧
      Staged.Obligations.Step ledger saved.ledger ∧ saved.Valid reason last := by
  cases interval with
  | sendingStopped _ _ failed frontier => exact .inl ⟨failed,frontier⟩
  | disposing after debts cutWorld cutHistory completed trace _ _ _ interval =>
    obtain ⟨stage,saved,prefixRun,step,valid⟩ := interval.reached_cut
    refine .inr ⟨stage,saved,?_,trace.step.trans step,valid⟩
    rw [cryptedDisposalPrefix,runPrefix_bind,completed]
    exact prefixRun

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
