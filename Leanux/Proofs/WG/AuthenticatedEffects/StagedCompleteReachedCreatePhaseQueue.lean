import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePhasePassive

/-! The actual cached-peer installation consumes the unpublished alias at
its native write. The later access and queued records retain this same ledger;
the installation preconditions come from the preceding original before call. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePhase
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CreateDisposal CompleteCarrier StagedTerminalComplete Staged.Obligations
open HandshakeSecurity.StagedDisposal CreatePoints
set_option maxHeartbeats 600000

theorem queue_normal (steps : Staged.Obligations.Step rootLedger ledger)
    (pending : PendingBatch h ledger items)
    (device : w.wg.dev=some d) (resident : d.peers[pid]?=some peer)
    (before : Accounted h ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg)
    (performed : runPrefix (queueWrite pid peer items) w h=(.ok (value,v),last)) :
    Live rootLedger debts locals pid items last v.wg := by
  rw [queue_write_run device] at performed
  cases performed
  exact .queued ledger steps (pending.append _)
    (disposition_history (install_accounted pid peer items device resident before)
      [.access (.peer (.write pid peer.internalId))])

theorem install_covers (steps : Staged.Obligations.Step rootLedger ledger)
    (pending : PendingBatch h ledger items)
    (device : w.wg.dev=some d) (resident : d.peers[pid]?=some peer)
    (before : Accounted h ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg) :
    Covers (fun h w=>Live rootLedger debts locals pid items h w.wg) (installShape pid peer items) w h := by
  apply covers_marked
  apply covers_bind (covers_atom (.queue pid peer items) (.unpublished ledger steps pending before)
    (fun _ _ _ run=>queue_normal steps pending device resident before run))
  intro ignored v last written
  exact atom_covers (.event (.queued pid items)) trivial (queue_normal steps pending device resident before written)

theorem before_accounted
    (before : Accounted h ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg)
    (performed : runPrefix (queueBefore pid items) w h=(.ok (candidate,v),last)) :
    Accounted last ledger debts (⟨.unpublished,pid,items⟩::locals) v.wg ∧
      (∀ peer,candidate=some peer → ∃ d,v.wg.dev=some d ∧ d.peers[pid]?=some peer) ∧
      ∃ suffix,last=h++suffix := by
  have focused : runPrefix (QueueHandoff.focused (QueueHandoff.before pid items)) w h=
      (.ok (candidate,v),last) := by rw [before_factor]; exact performed
  obtain ⟨entry,resident⟩:=Queue.before_entry pid items before.entry focused
  have complete:=CompleteSource.focused_complete (QueueHandoff.before pid items) w before.complete
  rw [focused] at complete
  obtain ⟨suffix,grown,_⟩:=QueueHandoff.focused_quiet (QueueHandoff.before pid items) w h
  change (runPrefix (QueueHandoff.focused (QueueHandoff.before pid items)) w h).2=_ at grown
  rw [focused] at grown
  exact ⟨⟨entry,complete⟩,resident,suffix,grown⟩

theorem enqueue_covers (steps : Staged.Obligations.Step rootLedger ledger)
    (pending : PendingBatch h ledger items)
    (before : Accounted h ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg) :
    Covers (fun h w=>Live rootLedger debts locals pid items h w.wg) (enqueueShape pid items) w h := by
  unfold enqueueShape
  apply covers_marked
  erw [covers_type_cast _ (enqueue_factor pid items).symm]
  dsimp only [id]
  apply covers_bind
  · apply covers_bind (passive_covers (before_passive pid items) (.unpublished ledger steps pending before))
    intro candidate v last prepared
    obtain ⟨entry,resident,suffix,grown⟩:=before_accounted before prepared
    have remaining : PendingBatch last ledger items := grown ▸ pending.append suffix
    cases candidate with
    | none=>exact covers_pure _ (.unpublished ledger steps remaining entry)
    | some peer=>
      obtain ⟨d,device,atPeer⟩:=resident peer rfl
      have installed:=install_covers steps remaining device atPeer entry
      exact covers_bind installed (fun _ _ _ run=>passive_covers (after_passive items) (installed.normal run))
  · intro ret v last earlier
    have first : Covers (fun h w=>Live rootLedger debts locals pid items h w.wg)
        (Shape.bind (next:=fun candidate=>match candidate with
          | some peer=>do queueInstall pid peer items; queueAfter items
          | none=>pure (-WG.ENOSPC : Int))
          (beforeShape pid items) (fun candidate=>match candidate with
          | some peer=>Shape.bind (installShape pid peer items) (fun _=>afterShape items)
          | none=>Shape.pure (-WG.ENOSPC : Int))) w h := by
      apply covers_bind (passive_covers (before_passive pid items) (.unpublished ledger steps pending before))
      intro candidate v last prepared
      obtain ⟨entry,resident,suffix,grown⟩:=before_accounted before prepared
      have remaining : PendingBatch last ledger items := grown ▸ pending.append suffix
      cases candidate with
      | none=>exact covers_pure _ (.unpublished ledger steps remaining entry)
      | some peer=>
        obtain ⟨d,device,atPeer⟩:=resident peer rfl
        have installed:=install_covers steps remaining device atPeer entry
        exact covers_bind installed (fun _ _ _ run=>passive_covers (after_passive items) (installed.normal run))
    have same : (do let some peer ← queueBefore pid items | pure (-WG.ENOSPC)
                    queueInstall pid peer items
                    queueAfter items) =
        (queueBefore pid items >>= fun candidate=>match candidate with
          | some peer=>do queueInstall pid peer items; queueAfter items
          | none=>pure (-WG.ENOSPC : Int)) := by
      congr 1
      funext candidate
      cases candidate <;> rfl
    erw [same] at earlier
    exact passive_covers (offered_passive items ret) (first.normal earlier)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePhase
