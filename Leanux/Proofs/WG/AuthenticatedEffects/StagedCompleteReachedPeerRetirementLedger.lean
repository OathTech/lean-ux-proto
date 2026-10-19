import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerRetirementPurge

/-! At silent erasure the old ledger is an entry obligation, not an assertion
that the erased queue still exists. Its ordered cohort remains fixed until
the actual counted receipt assigns the terminal positions. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open TransmitSecurity Staged.Obligations CausalJournal CompleteCarrier Staged.Origins
open HandshakeSecurity.StagedConservation HandshakeSecurity.StagedDisposal
set_option maxHeartbeats 600000

def cohort (ledger : Ledger) (pid : PeerId) (p : Peer) (d : Device) : List Staged.Origins.Ticket :=
  pendingAt (.staged d.ifindex pid p.internalId) ledger

theorem cohort_aligned (before : Accounted h ledger debts locals w)
    (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    Aligned (Staged.Origins.Born h d.ifindex pid p.internalId) (cohort ledger pid p d) p.staged := by
  have same := before.entry.core.queues d.ifindex pid p.internalId
  simpa [cohort,stagedPackets,Packets.epoch,Staged.stagedAt,device,resident] using same

theorem cohort_pending (member : ticket ∈ cohort ledger pid p d) :
    (ticket,Status.pending (.staged d.ifindex pid p.internalId)) ∈ ledger :=
  mem_pendingAt.mp member

/-- Even a subsequently failed refcount test has this actual decremented
prefix. Its original ordered queue and charge remain present at the cut. -/
theorem decrement_cohort (before : Accounted h ledger debts locals w)
    (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    ((decrementTo (some pid)).run w).run a=
      .ok ((some (pid,p),decremented pid p d w),entryClock a) ∧
    Aligned (Staged.Origins.Born h d.ifindex pid p.internalId) (cohort ledger pid p d) p.staged ∧
    Staged.stagedAt (decremented pid p d w) pid=Staged.stagedAt w pid ∧
    Staged.dropped (decremented pid p d w)=Staged.dropped w :=
  ⟨decrement_prefix device resident,cohort_aligned before device resident,
    (decrement_geometry device resident).1,(decrement_geometry device resident).2.1⟩

/-- The unhash prefix precedes the actual queue guard on both branches.
No counted queue erasure is inferred if that guard subsequently stops. -/
theorem unlink_cohort (before : Accounted h ledger debts locals w)
    (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (tested : (testAmbient p.refcount).run (entryClock a)=.ok (true,b)) :
    ((unlinkTo (some pid)).run w).run a=
      .ok ((some (pid,p),indexWorld pid p d w),indexClock pid d b) ∧
    Aligned (Staged.Origins.Born h d.ifindex pid p.internalId) (cohort ledger pid p d) p.staged ∧
    Staged.stagedAt (indexWorld pid p d w) pid=Staged.stagedAt w pid ∧
    Staged.dropped (indexWorld pid p d w)=Staged.dropped w := by
  have unchanged := unlink_geometry (pid:=pid) (w:=decremented pid p d w) (d:=decDevice pid p d) rfl
  refine ⟨unlink_prefix device resident tested,cohort_aligned before device resident,?_,?_⟩
  · exact (congrFun unchanged.1 pid).trans (decrement_geometry device resident).1
  · exact unchanged.2.trans (decrement_geometry device resident).2.1

/-- A native final erasure has happened, but its receipt has not. The
original ordered tickets and debts are still entry facts; no unchanged
Accounted assertion is made about this erased native world. -/
theorem release_pending (before : Accounted h ledger debts locals w)
    (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (tested : (testAmbient p.refcount).run (entryClock a)=.ok (true,b))
    (quiet : queued p=false) :
    ((releaseCut (some pid)).run w).run a=
      .ok ((some (pid,p),finalWorld pid p d w),indexClock pid d b) ∧
    Aligned (Staged.Origins.Born h d.ifindex pid p.internalId) (cohort ledger pid p d) p.staged ∧
    Staged.stagedAt (finalWorld pid p d w) pid=none ∧
    Staged.dropped (finalWorld pid p d w)=some (d.txDropped+(cohort ledger pid p d).length) := by
  have aligned := cohort_aligned before device resident
  refine ⟨erase_prefix device resident tested quiet,aligned,?_,?_⟩
  · exact (erase_geometry (pid:=pid) (p:=p) (d:=indexDevice pid p d) (w:=indexWorld pid p d w)).1
  · have size := aligned_length aligned
    simpa [finalWorld,indexDevice,decDevice,size] using
      (erase_geometry (pid:=pid) (p:=p) (d:=indexDevice pid p d) (w:=indexWorld pid p d w)).2

/-- Purge charges before clearing: the same cohort is counted at the first
write while its packet queue is still present, then becomes receipt-pending
at the second write. Both worlds are literal runs from the same entry. -/
theorem purge_pending (before : Accounted h ledger debts locals w)
    (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    ((purgeChargeTo pid).run w).run a=.ok ((p,charged p d w),a) ∧
    ((purgeStagedPackets pid).run w).run a=.ok (((),cleared pid p d w),a) ∧
    Aligned (Staged.Origins.Born h d.ifindex pid p.internalId) (cohort ledger pid p d) p.staged ∧
    Staged.stagedAt (charged p d w)=Staged.stagedAt w ∧
    Staged.dropped (charged p d w)=some (d.txDropped+(cohort ledger pid p d).length) ∧
    Staged.stagedAt (cleared pid p d w) pid=some (p.internalId,[]) ∧
    Staged.dropped (cleared pid p d w)=some (d.txDropped+(cohort ledger pid p d).length) := by
  have aligned := cohort_aligned before device resident
  have size := aligned_length aligned
  refine ⟨purge_charge_prefix device resident,purge_clear_prefix device resident,aligned,
    (charge_geometry (p:=p) device).1,?_,clear_geometry.1,?_⟩
  · simpa only [size] using (charge_geometry (p:=p) device).2
  · simpa only [size] using (clear_geometry (pid:=pid) (p:=p) (d:=d) (w:=w)).2

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement
