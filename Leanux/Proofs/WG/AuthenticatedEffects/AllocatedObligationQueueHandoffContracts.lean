import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationQueueHandoffFrames

/-! A reached queue-write cut moves the exact batch out of the unpublished
local list. Its existing queued event and successful native ownership state
remain witnesses if subsequent ring/CPU work stops. No final state is
inferred from an exception, and whole-admission entry coverage stays separate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.QueueHandoff
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity RetirementSecurity
set_option pp.structureInstances false

theorem install_total (pid : PeerId) (p : Peer) (items : List SkbId)
    (device : w.wg.dev = some d) :
    ∃ suffix,
      runPrefix (install pid p items) w history =
        (.ok ((),{w with wg := replacePeer w.wg d pid {p with txQueue := p.txQueue.enqueue items}}),
          (history ++ suffix) ++ [.queued pid items]) := by
  let q := {p with txQueue := p.txQueue.enqueue items}
  let v := {w with wg := replacePeer w.wg d pid q}
  have native : (liftWG (setPeer pid q)).run w = .ok ((),v) := by
    simp [liftWG_run,setPeer,modifyDev,device,v,replacePeer,Except.map]
  have result := (TxDisposition.nativeAccess_erases (setPeerMixed_erases pid q) w history).trans native
  obtain ⟨suffix,extended⟩ := (Appends.focus TxDisposition.Event.access TxDisposition.accessEvent
    (liftWGObserver (setPeerMixed pid q))) w history
  have performed : runPrefix (TxDisposition.nativeAccess (setPeerMixed pid q)) w history =
      (.ok ((),v),history ++ suffix) := Prod.ext result extended
  refine ⟨suffix,?_⟩
  rw [install,runPrefix_bind,performed]
  rfl

/-- Exact focused source cut in the final journal, with ownership consumed
at the peer-queue write, before any ring choice or worker scheduling. -/
theorem actual_install (pid : PeerId) (p : Peer) (items : List SkbId)
    (device : w.wg.dev = some d) (found : d.peers[pid]? = some p)
    (physical : Physical history ledger debts w.wg)
    (coverage : TxCoverage (⟨.unpublished,pid,items⟩ :: locals) w.wg)
    (inventory : TxInventory (⟨.unpublished,pid,items⟩ :: locals) w.wg) :
    ∃ v suffix,
      runPrefix (focusPrefix CausalJournal.txEvent CausalJournal.txEvent? (install pid p items)) w history =
        (.ok ((),v),(history ++ suffix) ++ [CausalJournal.txEvent (.queued pid items)]) ∧
      Physical ((history ++ suffix) ++ [CausalJournal.txEvent (.queued pid items)]) ledger debts v.wg ∧
      TxCoverage locals v.wg ∧ TxInventory locals v.wg := by
  obtain ⟨suffix,performed⟩ := install_total (history := history.filterMap CausalJournal.txEvent?) pid p items device
  have focused := focusPrefix_suffix CausalJournal.txEvent CausalJournal.txEvent?
    (install pid p items) w history _ (suffix ++ [.queued pid items])
    (by simpa only [List.append_assoc] using performed)
  simp only [List.map_append,List.map_cons,List.map_nil] at focused
  have material := installed_material (pid := pid) (p := {p with txQueue := p.txQueue.enqueue items}) device
  have kept := (physical.views (v := replacePeer w.wg d pid {p with txQueue := p.txQueue.enqueue items}) (congrArg Prod.fst material) (congrArg Prod.snd material)).append
    (suffix.map CausalJournal.txEvent ++ [CausalJournal.txEvent (.queued pid items)])
  obtain ⟨covered,unique⟩ := installed_ownership device found coverage inventory
  refine ⟨{w with wg := replacePeer w.wg d pid {p with txQueue := p.txQueue.enqueue items}},
    suffix.map CausalJournal.txEvent,?_,?_,covered,unique⟩
  · simpa only [List.append_assoc] using focused
  · simpa only [List.append_assoc] using kept

/-- The same successful handoff and its actual history position survive an
arbitrary append-only continuation, including a Stop. The retained state is
the state at the cut, never a fabricated final state of the failed caller. -/
theorem actual_install_retained (pid : PeerId) (p : Peer) (items : List SkbId)
    (next : PrefixM CausalJournal.Event α) (appends : Appends next)
    (device : w.wg.dev = some d) (found : d.peers[pid]? = some p)
    (physical : Physical history ledger debts w.wg)
    (coverage : TxCoverage (⟨.unpublished,pid,items⟩ :: locals) w.wg)
    (inventory : TxInventory (⟨.unpublished,pid,items⟩ :: locals) w.wg) :
    ∃ v writes suffix,
      runPrefix (focusPrefix CausalJournal.txEvent CausalJournal.txEvent? (install pid p items)) w history =
        (.ok ((),v),(history ++ writes) ++ [CausalJournal.txEvent (.queued pid items)]) ∧
      (runPrefix (do
        focusPrefix CausalJournal.txEvent CausalJournal.txEvent? (install pid p items)
        next) w history).2 =
        ((history ++ writes) ++ [CausalJournal.txEvent (.queued pid items)]) ++ suffix ∧
      Physical ((history ++ writes) ++ [CausalJournal.txEvent (.queued pid items)]) ledger debts v.wg ∧
      TxCoverage locals v.wg ∧ TxInventory locals v.wg := by
  obtain ⟨v,writes,performed,kept,covered,unique⟩ :=
    actual_install pid p items device found physical coverage inventory
  obtain ⟨suffix,extended⟩ := appends v ((history ++ writes) ++ [CausalJournal.txEvent (.queued pid items)])
  refine ⟨v,writes,suffix,performed,?_,kept,covered,unique⟩
  rw [runPrefix_bind,performed]
  exact extended

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.QueueHandoff
