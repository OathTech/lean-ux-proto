import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntrySourceContracts
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationNativeDisposalCarrier
import Leanux.Proofs.WG.RetirementSecurity.HolderTimerKeys

/-! Actual counted purge removes the matching staged obligations once while
retaining allocated cells, cleanup debts and their existing terminal evidence. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Purge
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins RetirementSecurity AllocatedObligation Staged.Obligations CausalJournal

theorem receipt (pid : PeerId) (r : WGRunWitness Unit)
    (native : r.Valid (purgeStagedPackets pid)) (before : Inv history ledger debts locals r.before) :
    ∃ (part : HandshakeSecurity.StagedDisposal.Partition pid r.before r.after) (generation : Nat),
      part.removed = part.packets.length ∧ Packets.epoch r.before = some generation ∧
      let chosen := (pendingAt (.staged generation pid part.stamp) ledger).take part.removed
      let after := settle chosen (.counted history.length .purge) ledger
      Staged.Obligations.Step ledger after ∧ AllocatedFrame ledger after ∧
      Inv (history ++ [.stagedDisposal (.purge pid r)]) after debts locals r.after ∧
      chosen.length = part.removed ∧
      (∀ ticket ∈ chosen, (ticket,Status.terminal (.counted history.length .purge)) ∈ after) ∧
      (∃ count, Staged.dropped r.before = some count ∧ Staged.dropped r.after = some (count+chosen.length)) := by
  obtain ⟨part,generation,whole,epoch,step,core,length,terminal,charged⟩ := core_purge pid r native before.core
  have aligned := before.core.queues generation pid part.stamp
  rw [partition_before part epoch] at aligned
  have frame := settle_allocated_frame before.core.valid
    (fun ticket (member : ticket ∈ (pendingAt (.staged generation pid part.stamp) ledger).take part.removed) =>
      List.mem_of_mem_take member) (by intro _ _; simp) (.counted history.length .purge)
  have justified := (StagedProvenance.settle_at before.core.valid before.justified
    (fun ticket (member : ticket ∈ (pendingAt (.staged generation pid part.stamp) ledger).take part.removed) =>
      List.mem_of_mem_take member)
    (fun _ member => StagedProvenance.At.purge pid r native part whole generation epoch _ aligned
      (List.mem_of_mem_take member))).2
  have geometry := (ProjectedAction.iff_run_ambient _ _ _).mp (purge_packet_geometry pid)
    r.before r.ambientBefore r.value r.after r.ambientAfter native
  have snapshot : Packets.snapshot r.after = Packets.snapshot r.before := congrArg Prod.fst geometry
  have points := (ProjectedAction.iff_run_ambient _ _ _).mp (HolderTimerKeys.purge_points pid)
    r.before r.ambientBefore r.value r.after r.ambientAfter native
  refine ⟨part,generation,whole,epoch,step,frame,?_,length,terminal,charged⟩
  exact ⟨core,justified,(before.allocationLinks.frame frame).append _,before.noSelected.settled _ _,
    by simpa only [Packets.Inv,snapshot] using before.packets,
    before.coverage.points points,before.inventory.points points⟩

theorem run (pid : PeerId) (w : WGWorld) (a : Ambient) (h : List Event) :
    runWGPrefix (CausalJournal.stagedPurge pid) w a h =
      match ((purgeStagedPackets pid).run w).run a with
      | .error stop => (.error stop,h)
      | .ok (((),v),b) => (.ok (((),v),b),h ++ [.stagedDisposal (.purge pid ⟨(),w,v,a,b⟩)]) := by
  change runPrefix (focusPrefix Event.stagedDisposal stagedDisposal?
    ((HandshakeSecurity.StagedDisposal.purgeObserved pid).run w)) a h = _
  have source := runWGPrefix_receiptWGObserved (liftWGPrefix (purgeStagedPackets pid))
    (HandshakeSecurity.StagedDisposal.Event.purge pid) w a (h.filterMap stagedDisposal?)
  rw [runWGPrefix_lift] at source
  cases native : ((purgeStagedPackets pid).run w).run a with
  | error stop =>
    rw [native] at source
    have localRun : runPrefix ((HandshakeSecurity.StagedDisposal.purgeObserved pid).run w)
        a (h.filterMap stagedDisposal?) = (.error stop,h.filterMap stagedDisposal? ++ []) := by
      simpa only [HandshakeSecurity.StagedDisposal.purgeObserved,List.append_nil,runWGPrefix,runStatePrefix] using source
    simpa only [List.map_nil,List.append_nil] using
      focusPrefix_suffix Event.stagedDisposal stagedDisposal? _ a h _ [] localRun
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    cases value
    rw [native] at source
    exact focusPrefix_suffix Event.stagedDisposal stagedDisposal? _ a h _ [_] source

/-- Actual purge supplies its precise counted terminal receipt, or retains
the incoming entry on native failure with no fabricated disposal event. -/
theorem checked (pid : PeerId) (Safe : List Event → Prop)
    (entrySafe : ∀ ledger h w, Inv h ledger debts locals w → Safe h) :
    StatePrefixPreserves (Source.Carrier debts locals) Safe (CausalJournal.stagedPurge pid) := by
  intro w a h before
  obtain ⟨ledger,entry⟩ := before
  have equation := run pid w a h
  change runPrefix ((CausalJournal.stagedPurge pid).run w) a h = _ at equation
  rw [equation]
  cases native : ((purgeStagedPackets pid).run w).run a with
  | error stop => exact ⟨[],by simp,entrySafe _ _ _ entry,True.intro⟩
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    cases value
    obtain ⟨part,generation,_,_,_,_,kept,_,_,_⟩ := receipt pid ⟨(),w,v,a,b⟩ native entry
    exact ⟨[.stagedDisposal (.purge pid ⟨(),w,v,a,b⟩)],rfl,entrySafe _ _ _ kept,_,kept⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Purge
