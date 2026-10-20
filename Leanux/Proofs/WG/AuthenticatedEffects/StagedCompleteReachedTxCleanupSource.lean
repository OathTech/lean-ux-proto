import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxDeadFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedOrdinaryCleanupWorker

/-! Actual crypted-worker completion and ordinary-free prefixes. The source
continuations require only their executed prefixes, independently of accounts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxCleanup
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch HandshakeSecurity.StagedConservation

def completion (pid : PeerId) (items : List SkbId) : PrefixM CausalJournal.Event Unit :=
  CompletionEffects.completeScoped CausalJournal.Event.scope CausalSources.Cause.completion
    CausalJournal.completionOps pid items

theorem selected_continuation
    (selected : runPrefix (workerSelection pid) w h=(.ok (some ⟨items,head,true⟩,u),middle))
    (completed : runPrefix (completion pid items) u middle=(.ok ((),v),last)) :
    runPrefix (CausalJournal.transmit pid) w h=
      runPrefix (do freeLoop cleanupOps items; CompletionBatch.release cleanupOps pid head.keypair) v last := by
  rw [worker_selection_factor,runPrefix_bind,selected]
  change runPrefix (TxWorker.crypted pid items head) u middle=_
  unfold completion at completed
  rw [TxWorker.crypted,runPrefix_bind,completed]
  change runPrefix (HandshakeSecurity.StagedDisposal.TxSource.dispose cleanupOps pid items head.keypair) v last=_
  rw [←dispose_factor]
  rfl

theorem boundary_continuation
    (selected : runPrefix (workerSelection pid) w h=(.ok (some ⟨items,head,true⟩,u),middle))
    (completed : runPrefix (completion pid items) u middle=(.ok ((),v),last))
    (shape : items=done++rest)
    (leading : runPrefix (freeLoop cleanupOps done) v last=(.ok ((),q),after)) :
    runPrefix (CausalJournal.transmit pid) w h=
      runPrefix (do freeLoop cleanupOps rest; CompletionBatch.release cleanupOps pid head.keypair) q after := by
  rw [selected_continuation selected completed,shape,OrdinaryCleanup.loop_append,bind_assoc,runPrefix_bind,leading]

theorem primitive_continuation
    (selected : runPrefix (workerSelection pid) w h=(.ok (some ⟨items,head,true⟩,u),middle))
    (completed : runPrefix (completion pid items) u middle=(.ok ((),v),last))
    (shape : items=done++skb::rest)
    (leading : runPrefix (freeLoop cleanupOps done) v last=(.ok ((),q),after))
    (native : (liftWG (freeTxSkb skb)).run q=.ok ((),r)) (phase : CleanupPrimitive.Phase) :
    runPrefix (CausalJournal.transmit pid) w h=
      runPrefix (do OrdinaryCleanup.due phase q skb
                    freeLoop cleanupOps rest
                    CompletionBatch.release cleanupOps pid head.keypair)
        r (CleanupPrimitive.current phase q skb after) := by
  rw [boundary_continuation selected completed shape leading]
  rw [freeLoop,bind_assoc]
  change runPrefix (do FirstTerminal.cleanupFree skb; freeLoop cleanupOps rest
                       CompletionBatch.release cleanupOps pid head.keypair) q after=_
  rw [runPrefix_bind,OrdinaryCleanup.original_suffix phase q r skb after native,
    OrdinaryCleanup.due_run,runPrefix_bind,OrdinaryCleanup.due_run]

inductive Point (pid : PeerId) (w : World) (h : List CausalJournal.Event) :
    World → List CausalJournal.Event → Prop where
  | boundary
      (selected : runPrefix (workerSelection pid) w h=(.ok (some ⟨items,head,true⟩,u),middle))
      (completed : runPrefix (completion pid items) u middle=(.ok ((),v),last))
      (shape : items=done++rest)
      (leading : runPrefix (freeLoop cleanupOps done) v last=(.ok ((),q),after)) : Point pid w h q after
  | primitive
      (selected : runPrefix (workerSelection pid) w h=(.ok (some ⟨items,head,true⟩,u),middle))
      (completed : runPrefix (completion pid items) u middle=(.ok ((),v),last))
      (shape : items=done++skb::rest)
      (leading : runPrefix (freeLoop cleanupOps done) v last=(.ok ((),q),after))
      (native : (liftWG (freeTxSkb skb)).run q=.ok ((),r)) (phase : CleanupPrimitive.Phase) :
      Point pid w h r (CleanupPrimitive.current phase q skb after)

theorem Point.remaining (point : Point pid w h u middle) :
    ∃remaining,runPrefix (CausalJournal.transmit pid) w h=runPrefix remaining u middle := by
  cases point with
  | boundary selected completed shape leading=>exact ⟨_,boundary_continuation selected completed shape leading⟩
  | primitive selected completed shape leading native phase=>
    exact ⟨_,primitive_continuation selected completed shape leading native phase⟩

noncomputable def remainder (point : Point pid w h u middle) : PrefixM CausalJournal.Event Bool :=
  Classical.choose point.remaining

theorem remainder_run (point : Point pid w h u middle) :
    runPrefix (CausalJournal.transmit pid) w h=runPrefix (remainder point) u middle :=
  Classical.choose_spec point.remaining

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxCleanup
