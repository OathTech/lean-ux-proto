import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionFreshSource

/-! The actual lifetime-observed decision and installation prefixes retain
their native world and quiet history projection. The repayment callback is
identified with the existing exact nested-release observer, not erased away. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Fresh
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity
open HandshakeSecurity.StagedDisposal LifetimeEffects TransmitSecurity.Staged.Obligations

theorem prefix_appends : Ops.Appends prefixOps :=
  pinned_const _private.Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionTimers.«0».Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.timer_appends

macro "fresh_prefix_append" : tactic => `(tactic| first
  | with_reducible exact Ops.Appends.step prefix_appends _
  | with_reducible exact Ops.Appends.peer prefix_appends _
  | with_reducible exact Ops.Appends.keypair prefix_appends _
  | with_reducible exact Ops.Appends.modifyPeer prefix_appends _ _
  | with_reducible exact Ops.Appends.get prefix_appends _
  | exact StateAppends.pure _
  | apply StateAppends.bind
  | (maintenance_intro; try dsimp only)
  | maintenance_reduce
  | split)

theorem decision_appends (pid : PeerId) : StateAppends (decisionWith CausalJournal.completionLifetime pid) := by
  rw [decision_actual]
  unfold decisionWith
  repeat' fresh_prefix_append

theorem install_appends (pid : PeerId) : StateAppends (installWith CausalJournal.completionLifetime pid) := by
  rw [install_actual]
  unfold installWith
  repeat' fresh_prefix_append

theorem guard_appends (pid : PeerId) : StateAppends (guardWith CausalJournal.completionLifetime pid) := by
  rw [guard_actual]
  unfold guardWith
  simp only [andPrefix,orPrefix]
  repeat' fresh_prefix_append

theorem decision_original (pid : PeerId) : StateProjectsPrefix ledgerEvent? id
    (decisionWith CausalJournal.completionLifetime pid)
    (liftWGPrefix (StagedEntry.Queued.decisionPrefix pid)) := by
  rw [decision_actual,← decision_lifted]
  exact decision_projects ledgerEvent? prefix_projects pid

theorem install_original (pid : PeerId) : StateProjectsPrefix ledgerEvent? id
    (installWith CausalJournal.completionLifetime pid)
    (liftWGPrefix (StagedEntry.Queued.install pid)) := by
  rw [install_actual,← install_lifted]
  exact install_projects ledgerEvent? prefix_projects pid

theorem put_actual (peer : Option PeerId) :
    liftWGObserver (CausalJournal.completionLifetime.put peer) = Admission.actualOps.release peer := by
  have encode : LifetimeSource.peerEncode (CausalJournal.Event.old ∘ Journal.completionEvent) =
      TxSource.peerEncode CausalJournal.txEvent := rfl
  have decode : LifetimeSource.peerDecode CausalJournal.completion? =
      TxSource.peerDecode CausalJournal.txEvent? := by
    funext event
    cases event <;> try rfl
    rename_i old
    cases old <;> rfl
  change liftWGObserver (PeerSource.observed
    (PeerSource.Ops.focus _ _ PeerSource.peers) CausalJournal.Event.stagedDisposal peer) = _
  rw [encode,decode]
  rfl

theorem append_actual (pid : PeerId) :
    CausalJournal.completionLifetime.append pid = CausalJournal.effects.append pid := by
  have focus_lift {E F α : Type} (encode : E → F) (decode : F → Option E) (action : WG.M α) :
      focusStatePrefix encode decode (liftWGPrefix action) = liftWGPrefix action := by
    funext w a history
    change (((action.run w).run a),history ++
      ((history.filterMap decode).drop (history.filterMap decode).length).map encode) =
      (((action.run w).run a),history)
    simp only [List.drop_length,List.map_nil,List.append_nil]
  change CausalEffects.atCurrent CausalJournal.scope? (fun context =>
    receiptWGObserved (focusStatePrefix _ _ (liftWGPrefix
      (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})))
      (fun r => CausalJournal.Event.queued ⟨context,pid,r⟩)) = _
  rw [focus_lift]
  rfl

/-- A projected native prefix supplies both its exact native result and
the ledger-event frame, for normal as well as stopped execution. -/
theorem projected_parts {action : WGPrefix CausalJournal.Event α} {native : WG.M α}
    (projected : StateProjectsPrefix ledgerEvent? id action (liftWGPrefix native)) :
    ErasesStatePrefix action native ∧ StateHistoryFrame ledgerEvent? action := by
  constructor
  · intro w a history
    have same := congrArg Prod.fst (projected w a history)
    change ((native.run w).run a) = (runWGPrefix action w a history).1.map
      (fun ((x,v),b) => ((id x,v),b)) at same
    have mapped : (runWGPrefix action w a history).1.map
        (fun ((x,v),b) => ((id x,v),b)) = (runWGPrefix action w a history).1 := by
      cases result : (runWGPrefix action w a history).1 with
      | error reason => rfl
      | ok value => obtain ⟨⟨x,v⟩,b⟩ := value; rfl
    exact (same.trans mapped).symm
  · intro w a history
    exact (congrArg Prod.snd (projected w a history)).symm

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Fresh
