import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationQueueEntryFrames

/-! Exact native and history frames for the same canonical fixed ledger.
TX access/queue observations add no packet births. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.QueueHandoff
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations
set_option pp.structureInstances false

def Owned (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (h : List CausalJournal.Event) (w : World) : Prop :=
  Core h ledger debts w.wg ∧ TxCoverage locals w.wg ∧ TxInventory locals w.wg

theorem focused_quiet (action : TxDisposition.Obs α) (w : World) (history : List CausalJournal.Event) :
    ∃ suffix, (runPrefix (focusPrefix CausalJournal.txEvent CausalJournal.txEvent? action) w history).2 =
      history ++ suffix ∧ ∀ event ∈ suffix, birthPackets event = [] := by
  refine ⟨_,rfl,?_⟩
  intro event member
  obtain ⟨prior,_,rfl⟩ := List.mem_map.mp member
  rfl

theorem installed_queues (device : w.dev = some d) (found : d.peers[pid]? = some p) :
    Staged.stagedAt (replacePeer w d pid {p with txQueue := p.txQueue.enqueue items}) =
      Staged.stagedAt w := by
  funext other
  by_cases same : pid = other
  · subst other
    simp [Staged.stagedAt,replacePeer,device,found]
  · simp [Staged.stagedAt,replacePeer,device,Std.TreeMap.getElem?_insert,same]

/-- Successful original mark/read/full-guard returns its actual cached peer
and preserves the complete fixed ledger with unpublished ownership. -/
theorem before_entry (pid : PeerId) (items : List SkbId)
    (owned : Owned ledger debts (⟨.unpublished,pid,items⟩ :: locals) history w)
    (performed : runPrefix (focusPrefix CausalJournal.txEvent CausalJournal.txEvent? (before pid items)) w history =
      (.ok (candidate,v),last)) :
    Owned ledger debts (⟨.unpublished,pid,items⟩ :: locals) last v ∧
    ∀ p, candidate = some p → ∃ d, v.wg.dev = some d ∧ d.peers[pid]? = some p := by
  have full := (focusPrefix_erases _ _ (before_erases pid items) w history).symm.trans
    (congrArg Prod.fst performed)
  obtain ⟨suffix,extended,quiet⟩ := focused_quiet (before pid items) w history
  rw [performed] at extended
  change last = history ++ suffix at extended
  rw [liftWG_run] at full
  cases native : ((beforeNative pid items).run w.wg).run w.ambient with
  | error stop => simp [native,Except.map] at full
  | ok out =>
    obtain ⟨⟨result,g⟩,ambient⟩ := out
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at full
    obtain ⟨rfl,rfl⟩ := full
    have views := (ProjectedAction.iff_run_ambient _ _ _).mp
      (before_native_views pid items) w.wg w.ambient _ g ambient native
    obtain ⟨covered,unique,cached⟩ := before_native_entry owned.2.1 owned.2.2 _ _ native
    refine ⟨⟨?_,covered,unique⟩,cached⟩
    rw [extended]
    exact owned.1.quiet_views suffix quiet
      (congrArg (fun x => x.1.1) views) (congrArg Prod.snd views)
      (congrArg (fun x => x.1.2) views)

/-- The queue-write transfer preserves all staged and selected obligations;
only the physical owner of the already allocated batch changes. -/
theorem install_core (pid : PeerId) (p : Peer) (items : List SkbId)
    (device : w.wg.dev = some d) (found : d.peers[pid]? = some p)
    (owned : Owned ledger debts (⟨.unpublished,pid,items⟩ :: locals) history w) :
    ∃ v writes,
      runPrefix (focusPrefix CausalJournal.txEvent CausalJournal.txEvent? (install pid p items)) w history =
        (.ok ((),v),(history ++ writes) ++ [CausalJournal.txEvent (.queued pid items)]) ∧
      Owned ledger debts locals ((history ++ writes) ++ [CausalJournal.txEvent (.queued pid items)]) v := by
  obtain ⟨suffix,performed⟩ := install_total (history := history.filterMap CausalJournal.txEvent?) pid p items device
  have focused := focusPrefix_suffix CausalJournal.txEvent CausalJournal.txEvent?
    (install pid p items) w history _ (suffix ++ [.queued pid items])
    (by simpa only [List.append_assoc] using performed)
  simp only [List.map_append,List.map_cons,List.map_nil] at focused
  have material := installed_material (pid := pid) (p := {p with txQueue := p.txQueue.enqueue items}) device
  obtain ⟨covered,unique⟩ := installed_ownership device found owned.2.1 owned.2.2
  refine ⟨{w with wg := replacePeer w.wg d pid {p with txQueue := p.txQueue.enqueue items}},
    suffix.map CausalJournal.txEvent,?_,?_,covered,unique⟩
  · simpa only [List.append_assoc] using focused
  · have core := owned.1.quiet_views (v := replacePeer w.wg d pid {p with txQueue := p.txQueue.enqueue items}) (suffix.map CausalJournal.txEvent ++ [CausalJournal.txEvent (.queued pid items)])
      (by
        intro event member
        rcases List.mem_append.mp member with access | queued
        · obtain ⟨prior,_,rfl⟩ := List.mem_map.mp access; rfl
        · have same := List.mem_singleton.mp queued; subst event; rfl)
      (congrArg Prod.fst material) (installed_queues device found) (congrArg Prod.snd material)
    simpa only [List.append_assoc] using core

theorem after_entry (items : List SkbId) (owned : Owned ledger debts locals history w)
    (performed : runPrefix (focusPrefix CausalJournal.txEvent CausalJournal.txEvent? (after items)) w history =
      (.ok (ret,v),last)) : Owned ledger debts locals last v ∧ (ret = 0 ∨ ret = -WG.EPIPE) := by
  have full := (focusPrefix_erases _ _ (after_erases items) w history).symm.trans
    (congrArg Prod.fst performed)
  obtain ⟨suffix,extended,quiet⟩ := focused_quiet (after items) w history
  rw [performed] at extended
  change last = history ++ suffix at extended
  rw [liftWG_run] at full
  cases native : ((RxCredits.enqueueTailItem items).run w.wg).run w.ambient with
  | error stop => simp [native,Except.map] at full
  | ok out =>
    obtain ⟨⟨result,g⟩,ambient⟩ := out
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at full
    obtain ⟨rfl,rfl⟩ := full
    have views := (ProjectedAction.iff_run_ambient _ _ _).mp
      (after_native_views items) w.wg w.ambient _ g ambient native
    have owners := (ProjectedAction.iff_run_ambient _ _ _).mp
      (enqueue_tail_ownership items) w.wg w.ambient _ g ambient native
    refine ⟨⟨?_,owned.2.1.points owners,owned.2.2.points owners⟩,enqueue_tail_result items _ _ native⟩
    rw [extended]
    exact owned.1.quiet_views suffix quiet
      (congrArg (fun x => x.1.1) views) (congrArg Prod.snd views)
      (congrArg (fun x => x.1.2) views)

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.QueueHandoff
