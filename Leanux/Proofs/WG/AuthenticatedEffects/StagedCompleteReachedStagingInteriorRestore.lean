import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingInteriorTake

/-! Both restore reads are from the same actual native world. The single
prepend write preserves original occurrence order and the drop counter;
selected tickets transfer back only at its existing completed receipt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingInterior
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open TransmitSecurity Staged.Obligations Staged.Origins CausalJournal CompleteCarrier
open HandshakeSecurity.StagedConservation
set_option maxHeartbeats 600000

theorem restore_native (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    ((Restore.nativeRestore pid packets).run w).run a=
      .ok (((),queueWorld pid p (packets++p.staged) d w),a) := by
  rw [restore_factor,MaterialOrigin.bind_ok_ambient]
  exact ⟨(p,p),w,a,restore_read device resident,restore_write device⟩

theorem restore_read_stopped (failed : ((getPeer pid).run w).run a=.error stop) :
    ((Restore.nativeRestore pid packets).run w).run a=.error stop := by
  unfold Restore.nativeRestore
  simp only [StateT.run_bind,failed]
  rfl

inductive RestoreCase (pid : PeerId) (packets : List Packet) (w : WGWorld) (a : Ambient) :
    Except Stop ((Unit × WGWorld) × Ambient) → Prop where
  | readStopped (failed : ((getPeer pid).run w).run a=.error stop) : RestoreCase pid packets w a (.error stop)
  | restored (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
      RestoreCase pid packets w a (.ok (((),queueWorld pid p (packets++p.staged) d w),a))

theorem RestoreCase.literal (path : RestoreCase pid packets w a result) :
    ((Restore.nativeRestore pid packets).run w).run a=result := by
  cases path with
  | readStopped failed => exact restore_read_stopped failed
  | restored device resident => exact restore_native device resident

theorem restore_cases (pid : PeerId) (packets : List Packet) (w : WGWorld) (a : Ambient) :
    RestoreCase pid packets w a (((Restore.nativeRestore pid packets).run w).run a) := by
  cases read : ((getPeer pid).run w).run a with
  | error stop => rw [restore_read_stopped read]; exact .readStopped read
  | ok out =>
    obtain ⟨⟨p,v⟩,b⟩:=out
    obtain ⟨rfl,rfl,d,device,resident⟩:=Origins.getPeer_return pid w v p a b read
    rw [restore_native device resident]
    exact .restored device resident

theorem restore_recorded (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    runWGPrefix (CausalJournal.stagedRestore pid packets) w a h=
      (.ok (((),queueWorld pid p (packets++p.staged) d w),a),
        h++[.stagedRestored ⟨pid,packets,⟨(),w,queueWorld pid p (packets++p.staged) d w,a,a⟩⟩]) :=
  Restore.observed_completed Event.stagedRestored pid packets w _ a a h (restore_native device resident)

theorem restore_stopped (failed : ((getPeer pid).run w).run a=.error stop) :
    runWGPrefix (CausalJournal.stagedRestore pid packets) w a h=(.error stop,h) := by
  change runWGPrefix (receiptWGObserved (liftWGPrefix (Restore.nativeRestore pid packets))
    (fun run=>Event.stagedRestored ⟨pid,packets,run⟩)) w a h=_
  rw [runWGPrefix_receiptWGObserved,runWGPrefix_lift,restore_read_stopped failed]

/-- Every restored input occurrence retains its original ordinal before
any pre-existing resident packets; duplicate packet values do not merge. -/
theorem restore_position (ordinal : Nat) (position : packets[ordinal]?=some packet) :
    (stagedPackets d.ifindex pid p.internalId
      (queueWorld pid p (packets++p.staged) d w))[ordinal]?=some packet := by
  apply queue_position ordinal
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp position).choose]
  exact position

/-- Before the restore receipt, these are still the original selected
obligations. The actual write restores precisely their ordered plaintexts,
without charging the counter or asserting an unchanged idle carrier. -/
theorem restore_pending
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a)
    (device : w.dev=some d) (resident : d.peers[pid]?=some current) :
    ((Restore.nativeRestore pid peer.staged).run w).run a=
      .ok (((),queueWorld pid current (peer.staged++current.staged) d w),a) ∧
    Aligned (Born h generation pid peer.internalId) (pendingAt (.selected position) ledger) peer.staged ∧
    Staged.stagedAt (queueWorld pid current (peer.staged++current.staged) d w) pid=
      some (peer.internalId,peer.staged) ∧
    Staged.dropped (queueWorld pid current (peer.staged++current.staged) d w)=Staged.dropped w := by
  have shape : (current.internalId,current.staged)=(peer.internalId,([] : List Packet)) := by
    simpa [Staged.stagedAt,device,resident] using before.vacant.2
  have stamp : current.internalId=peer.internalId := congrArg Prod.fst shape
  have empty : current.staged=[] := congrArg Prod.snd shape
  refine ⟨restore_native device resident,before.aligned,?_,(queue_geometry device).2.1⟩
  simpa only [stamp,empty,List.append_nil] using
    (queue_geometry (pid:=pid) (p:=current) (packets:=peer.staged++current.staged) device).1

/-- This literal restore cut recovers the same selected cohort and all old
terminal dispositions. The counter remains exactly the entry counter. -/
theorem restore_accounted
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a)
    (device : w.dev=some d) (resident : d.peers[pid]?=some current) :
    let v := queueWorld pid current (peer.staged++current.staged) d w
    let r : Restore.Receipt := ⟨pid,peer.staged,⟨(),w,v,a,a⟩⟩
    let next := HeldFrontier.restoredLedger ledger generation pid peer position
    Accounted (h++[.stagedRestored r]) next debts locals v ∧
      pendingAt (.selected position) next=[] ∧
      pendingAt (.staged generation pid peer.internalId) next=pendingAt (.selected position) ledger ∧
      Staged.dropped v=Staged.dropped w := by
  let r : Restore.Receipt := ⟨pid,peer.staged,⟨(),w,queueWorld pid current (peer.staged++current.staged) d w,a,a⟩⟩
  have native : r.Valid:=restore_native device resident
  have active : StagedEntry.Active h ledger debts locals position w :=
    ⟨before.core,before.justified,before.links,before.only,before.native.1,before.native.2.1,before.native.2.2⟩
  obtain ⟨_,entry,empty,located,_⟩:=Restoration.restored r native active before.vacant.1 before.vacant.2 before.aligned
  have complete := (before.complete.transferred (.selected position) (.staged generation pid peer.internalId)).append_quiet
    (suffix:=[Event.stagedRestored r]) (fun _ member=>by cases List.mem_singleton.mp member; intro pos; rfl)
  exact ⟨⟨entry,complete⟩,empty,located,(queue_geometry device).2.1⟩

/-- The actual selected caller supplies the resident destination itself;
no successful restore, live key or extra empty-queue premise is assumed. -/
theorem restore_ready_total
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a) :
    ∃ d current, w.dev=some d ∧ d.peers[pid]?=some current ∧
      let v := queueWorld pid current (peer.staged++current.staged) d w
      let r : Restore.Receipt := ⟨pid,peer.staged,⟨(),w,v,a,a⟩⟩
      runWGPrefix (CausalJournal.stagedRestore pid peer.staged) w a h=(.ok (((),v),a),h++[.stagedRestored r]) ∧
      Accounted (h++[.stagedRestored r]) (HeldFrontier.restoredLedger ledger generation pid peer position) debts locals v := by
  have vacant := before.vacant.2
  cases device : w.dev with
  | none => simp [Staged.stagedAt,device] at vacant
  | some d =>
    cases resident : d.peers[pid]? with
    | none => simp [Staged.stagedAt,device,resident] at vacant
    | some current =>
      exact ⟨d,current,rfl,resident,restore_recorded device resident,
        (restore_accounted before device resident).1⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingInterior
