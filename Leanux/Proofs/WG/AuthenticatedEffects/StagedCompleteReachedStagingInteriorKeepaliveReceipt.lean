import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingInteriorKeepalive

/-! The singleton keepalive birth belongs to its actual preparation event,
not a true result alone. Before that event the inserted packet is an explicit
pending birth; after it the exact fresh ticket is admitted on the same ledger. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingInterior
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open TransmitSecurity Staged.Obligations Staged.Origins CausalJournal CompleteCarrier
open HandshakeSecurity.StagedConservation RetirementSecurity
set_option maxHeartbeats 600000

def keepaliveEvent (pid : PeerId) (ready : Bool) (w v : WGWorld) (a b : Ambient) : Event :=
  .keepalivePrepared pid ⟨ready,w,v,a,b⟩

theorem keepalive_recorded
    (native : ((OccurrenceHandshake.keepalivePrepare pid).run w).run a=.ok ((ready,v),b)) :
    runWGPrefix (CausalJournal.keepalivePrepare pid) w a h=
      (.ok ((ready,v),b),h++[keepaliveEvent pid ready w v a b]) := by
  unfold CausalJournal.keepalivePrepare
  rw [runWGPrefix_receiptWGObserved,runWGPrefix_lift,native]
  rfl

theorem keepalive_stopped
    (native : ((OccurrenceHandshake.keepalivePrepare pid).run w).run a=.error stop) :
    runWGPrefix (CausalJournal.keepalivePrepare pid) w a h=(.error stop,h) := by
  unfold CausalJournal.keepalivePrepare
  rw [runWGPrefix_receiptWGObserved,runWGPrefix_lift,native]

theorem empty_list {packets : List α} (empty : packets.isEmpty=true) : packets=[] := by
  cases packets <;> simp_all

/-- The actual insertion has occurred but the birth event has not. Existing
canonical tickets remain the entry domain; the new singleton is pending its
own invocation position, and no disposal counter has changed. -/
theorem keepalive_pending (before : Accounted h ledger debts locals w)
    (device : w.dev=some d) (resident : d.peers[pid]?=some p) (empty : p.staged.isEmpty=true)
    (allocation : keepaliveAllocation.run (clock a .keepaliveStagedEmpty true)=.ok (false,b)) :
    ((keepaliveAllocated pid).run w).run a=.ok (((p,some false),w),b) ∧
    ((OccurrenceHandshake.keepalivePrepare pid).run w).run a=
      .ok ((true,queueWorld pid p (p.staged++[{mtu:=d.mtu}]) d w),b) ∧
    pendingAt (.staged d.ifindex pid p.internalId) ledger=[] ∧
    Staged.stagedAt (queueWorld pid p (p.staged++[{mtu:=d.mtu}]) d w) pid=
      some (p.internalId,[{mtu:=d.mtu}]) ∧
    Staged.dropped (queueWorld pid p (p.staged++[{mtu:=d.mtu}]) d w)=Staged.dropped w := by
  have emptyPackets := empty_list empty
  have aligned := before.entry.core.queues d.ifindex pid p.internalId
  have size := aligned_length aligned
  have noTickets : pendingAt (.staged d.ifindex pid p.internalId) ledger=[] := by
    apply List.eq_nil_of_length_eq_zero
    simpa [stagedPackets,Packets.epoch,Staged.stagedAt,device,resident,emptyPackets] using size
  refine ⟨keepalive_allocated device resident empty allocation,keepalive_inserted device resident empty allocation,
    noTickets,?_,(queue_geometry device).2.1⟩
  calc
    _=some (p.internalId,p.staged++[({mtu:=d.mtu} : WG.Packet)]) := (queue_geometry device).1
    _=_ := by rw [emptyPackets]; rfl

/-- This birth names the actual original invocation event and ordinal zero. -/
theorem keepalive_birth (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (empty : p.staged.isEmpty=true)
    (allocation : keepaliveAllocation.run (clock a .keepaliveStagedEmpty true)=.ok (false,b)) :
    let v := queueWorld pid p (p.staged++[{mtu:=d.mtu}]) d w
    let event := keepaliveEvent pid true w v a b
    birthPackets event=[{}] ∧
      Born (h++[event]) d.ifindex pid p.internalId ⟨h.length,0⟩ {mtu:=d.mtu} := by
  have emptyPackets := empty_list empty
  let r : WGRunWitness Bool := ⟨true,w,queueWorld pid p (p.staged++[{mtu:=d.mtu}]) d w,a,b⟩
  have native : r.Valid (OccurrenceHandshake.keepalivePrepare pid):=keepalive_inserted device resident empty allocation
  constructor
  · simp [birthPackets,keepaliveEvent,Staged.stagedAt,device,resident,emptyPackets]
  · exact .keepalive r h [] d.mtu rfl native rfl
      (by simp [r,queueWorld,Packets.epoch])
      (by simp [r,Staged.stagedAt,device,resident,emptyPackets])
      (by simp [r,queueWorld,Staged.stagedAt,emptyPackets])
      (by simp [r,device])

/-- The canonical domain uses the exact invocation position and ordinal;
the separate Born relation above retains the actual MTU and plaintext. -/
theorem keepalive_tickets (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (empty : p.staged.isEmpty=true)
    (allocation : keepaliveAllocation.run (clock a .keepaliveStagedEmpty true)=.ok (false,b)) :
    let v := queueWorld pid p (p.staged++[{mtu:=d.mtu}]) d w
    births (h++[keepaliveEvent pid true w v a b])=births h++[⟨h.length,0⟩] := by
  dsimp only
  rw [births_emit,(keepalive_birth (h:=h) device resident empty allocation).1]
  rfl

/-- The successor is the precise singleton admission at this invocation,
with all prior terminals retained and no synthetic disposal charge. -/
theorem keepalive_accounted (before : Accounted h ledger debts locals w)
    (device : w.dev=some d) (resident : d.peers[pid]?=some p) (empty : p.staged.isEmpty=true)
    (allocation : keepaliveAllocation.run (clock a .keepaliveStagedEmpty true)=.ok (false,b)) :
    let v := queueWorld pid p (p.staged++[{mtu:=d.mtu}]) d w
    let event := keepaliveEvent pid true w v a b
    Accounted (h++[event])
      (StagedAdmission.appendBirths ledger h.length (.staged d.ifindex pid p.internalId) [{mtu:=d.mtu}]) debts locals v := by
  let r : WGRunWitness Bool := ⟨true,w,queueWorld pid p (p.staged++[{mtu:=d.mtu}]) d w,a,b⟩
  have native : r.Valid (OccurrenceHandshake.keepalivePrepare pid):=keepalive_inserted device resident empty allocation
  obtain ⟨after,entry,change,_⟩:=StagedEntry.keepalive_receipt pid r native before.entry
  have complete:=CompleteKeepalive.changed change before.complete
  cases change with
  | unchanged noBirth _ =>
    have born := (keepalive_birth (h:=h) device resident empty allocation).1
    change birthPackets (keepaliveEvent pid true w _ a b)=[] at noBirth
    rw [born] at noBirth
    cases noBirth
  | admitted generation stamp mtu _ epoch vacant mtuRead =>
    have gen : generation=d.ifindex := by simpa [r,Packets.epoch,device] using epoch.symm
    have allocationId : stamp=p.internalId := by
      have shape : (p.internalId,p.staged)=(stamp,([] : List Packet)) := by
        simpa [r,Staged.stagedAt,device,resident] using vacant
      exact (congrArg Prod.fst shape).symm
    have actualMtu : mtu=d.mtu := by simpa [r,device] using mtuRead.symm
    subst generation
    subst stamp
    subst mtu
    exact ⟨entry,complete⟩

/-- Reusing a nonempty queue creates neither a birth nor a disposal. The
actual true return still has its own completed invocation receipt. -/
theorem keepalive_existing_accounted (before : Accounted h ledger debts locals w)
    (device : w.dev=some d) (resident : d.peers[pid]?=some p) (nonempty : p.staged.isEmpty=false) :
    let b := clock a .keepaliveStagedEmpty false
    Accounted (h++[keepaliveEvent pid true w w a b]) ledger debts locals w ∧
      runWGPrefix (CausalJournal.keepalivePrepare pid) w a h=
        (.ok ((true,w),b),h++[keepaliveEvent pid true w w a b]) := by
  have noBirth : birthPackets (keepaliveEvent pid true w w a (clock a .keepaliveStagedEmpty false))=[] := by
    cases packets : p.staged with
    | nil => simp [packets] at nonempty
    | cons packet rest => simp [birthPackets,keepaliveEvent,Staged.stagedAt,device,resident,packets]
  refine ⟨before.append_quiet _ ?_ ?_,keepalive_recorded (keepalive_nonempty device resident nonempty)⟩
  · intro event member
    cases List.mem_singleton.mp member
    exact noBirth
  · intro event member
    cases List.mem_singleton.mp member
    intro position
    rfl

/-- Allocation refusal is a completed false invocation with no new ticket
or counter disposition; it is distinct from a stopped hidden-choice child. -/
theorem keepalive_refused_accounted (before : Accounted h ledger debts locals w)
    (device : w.dev=some d) (resident : d.peers[pid]?=some p) (empty : p.staged.isEmpty=true)
    (allocation : keepaliveAllocation.run (clock a .keepaliveStagedEmpty true)=.ok (true,b)) :
    Accounted (h++[keepaliveEvent pid false w w a b]) ledger debts locals w ∧
      runWGPrefix (CausalJournal.keepalivePrepare pid) w a h=
        (.ok ((false,w),b),h++[keepaliveEvent pid false w w a b]) := by
  refine ⟨before.append_quiet _ ?_ ?_,keepalive_recorded (keepalive_refused device resident empty allocation)⟩
  · intro event member
    cases List.mem_singleton.mp member
    rfl
  · intro event member
    cases List.mem_singleton.mp member
    intro position
    rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingInterior
