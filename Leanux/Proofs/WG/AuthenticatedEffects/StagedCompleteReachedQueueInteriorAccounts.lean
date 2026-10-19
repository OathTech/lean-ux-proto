import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedQueueInteriorObserved

/-! At the silent dequeue setter the actual selected batch is already owned
by its worker local. Existing access and removal events preserve both halves
of the same ledger; none of these observations creates a terminal charge. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.QueueInterior
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompleteCarrier StagedTerminalComplete

theorem access_accounted (before : Accounted history ledger debts locals w)
    (events : List LifetimeEvent) :
    Accounted (history++events.map queueAccessEvent) ledger debts locals w := by
  apply before.append_quiet
  · intro event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    rfl
  · intro event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    intro position
    rfl

theorem removal_accounted (before : Accounted history ledger debts locals w) (pid : PeerId) (items : List SkbId) :
    Accounted (history++[removedEvent pid items]) ledger debts locals w := by
  apply before.append_quiet
  · intro event member
    simp only [List.mem_singleton] at member
    subst event
    rfl
  · intro event member
    simp only [List.mem_singleton] at member
    subst event
    intro position
    rfl

/-- The account is over the actual post-setter world and exact original read
history. Selection is a native ownership transfer, with no terminal charge. -/
theorem drop_pending (before : Accounted history ledger [] locals w.wg)
    (device : w.wg.dev=some d) (resident : d.peers[pid]?=some p)
    (cached : p.txQueue.peeked=some items) :
    let after := replacePeer w.wg d pid {p with txQueue:=p.txQueue.dropPeeked}
    let readHistory := history++[readEvent pid p,readEvent pid p]
    runPrefix (dropMutation pid) w history=(.ok ((p,p),{w with wg:=after}),readHistory) ∧
      Accounted readHistory ledger [] (⟨.selected,pid,items⟩::locals) after ∧
      CreateDisposal.PendingBatch readHistory ledger items ∧
      p.txQueue.all=items::p.txQueue.dropPeeked.all ∧
      runPrefix (CausalJournal.completionOps.drop pid items) w history=
        runPrefix (dropDue pid items (p,p)) {w with wg:=after} readHistory := by
  have readAccount := access_accounted before [.peer (.read pid p.internalId),.peer (.read pid p.internalId)]
  obtain ⟨selected,pending,shape⟩ := drop_accounted w.ambient readAccount device resident cached
  exact ⟨drop_mutation device resident,selected,pending,shape,drop_original_suffix device resident⟩

/-- The setter's write event and removal receipt retain the already-transferred
selected batch and its complete fixed ledger. Neither settles a packet. -/
theorem drop_recorded {w : World} (before : Accounted history ledger [] locals w.wg)
    (device : w.wg.dev=some d) (resident : d.peers[pid]?=some p)
    (cached : p.txQueue.peeked=some items) :
    let after := replacePeer w.wg d pid {p with txQueue:=p.txQueue.dropPeeked}
    let reads := history++[readEvent pid p,readEvent pid p]
    Accounted (reads++[writeEvent pid p]) ledger [] (⟨.selected,pid,items⟩::locals) after ∧
      Accounted (reads++[writeEvent pid p,removedEvent pid items]) ledger []
        (⟨.selected,pid,items⟩::locals) after := by
  have pending := (drop_pending before device resident cached).2.1
  have written := access_accounted pending [.peer (.write pid p.internalId)]
  refine ⟨written,?_⟩
  simpa only [writeEvent,queueAccessEvent,List.map_cons,List.map_nil,List.append_assoc,List.cons_append,List.nil_append] using removal_accounted written pid items

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.QueueInterior
