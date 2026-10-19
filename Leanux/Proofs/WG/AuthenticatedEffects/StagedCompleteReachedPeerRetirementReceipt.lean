import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerRetirementLedger

/-! The original observer emits the receipt for the same literal native cut.
Its counted successor restores the full carrier before releaseFinish; an
error in that remaining child retains the receipt and its exact position. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open TransmitSecurity Staged.Obligations CausalJournal CompleteCarrier
open HandshakeSecurity.StagedDisposal
set_option maxHeartbeats 600000

def releaseEvent (peer : Option PeerId) (value : Cached) (w v : WGWorld) (a b : Ambient) : CausalJournal.Event :=
  .stagedDisposal (.release peer ⟨value,w,v,a,b⟩)

def purgeEvent (pid : PeerId) (w v : WGWorld) (a b : Ambient) : CausalJournal.Event :=
  .stagedDisposal (.purge pid ⟨(),w,v,a,b⟩)

/-- This equation leaves the actual native finish visible, including Stop. -/
theorem release_recorded
    (native : ((releaseCut peer).run w).run a=.ok ((some (pid,p),v),b)) :
    runWGPrefix (CausalJournal.peerRelease peer) w a h=
      (((releaseFinish pid p).run v).run b,h++[releaseEvent peer (some (pid,p)) w v a b]) := by
  have source := StagedAdmission.Front.put_run peer w a h
  change runWGPrefix (CausalJournal.peerRelease peer) w a h=_ at source
  rw [source,native]
  rfl

theorem release_none_recorded
    (native : ((releaseCut peer).run w).run a=.ok ((none,v),b)) :
    runWGPrefix (CausalJournal.peerRelease peer) w a h=
      (.ok (((),v),b),h++[releaseEvent peer none w v a b]) := by
  have source := StagedAdmission.Front.put_run peer w a h
  change runWGPrefix (CausalJournal.peerRelease peer) w a h=_ at source
  rw [source,native]
  rfl

theorem release_stopped
    (native : ((releaseCut peer).run w).run a=.error stop) :
    runWGPrefix (CausalJournal.peerRelease peer) w a h=(.error stop,h) := by
  have source := StagedAdmission.Front.put_run peer w a h
  change runWGPrefix (CausalJournal.peerRelease peer) w a h=_ at source
  rw [source,native]

/-- Settlement is derived from this exact native erasure, at this exact
receipt position. Every old terminal and allocated obligation is retained. -/
theorem release_accounted (before : Accounted h ledger debts locals w)
    (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (tested : (testAmbient p.refcount).run (entryClock a)=.ok (true,b))
    (quiet : queued p=false) :
    let next := settle (cohort ledger pid p d) (.counted h.length .finalRelease) ledger
    let history := h++[releaseEvent (some pid) (some (pid,p)) w (finalWorld pid p d w) a (indexClock pid d b)]
    Accounted history next debts locals (finalWorld pid p d w) ∧
      Staged.Obligations.Step ledger next ∧ AllocatedFrame ledger next := by
  obtain ⟨after,step,frame,successor,entry,complete⟩ :=
    StagedTerminalComplete.Source.original_native_entry (some pid) before.entry before.complete a _
      (erase_prefix device resident tested quiet)
  obtain ⟨generation,epoch,equal⟩ := successor
  have generation_eq : generation=d.ifindex := by
    simpa [Packets.epoch,device] using epoch.symm
  subst generation
  subst after
  exact ⟨⟨entry,complete⟩,step,frame⟩

theorem purge_recorded (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    runWGPrefix (CausalJournal.stagedPurge pid) w a h=
      (.ok (((),cleared pid p d w),a),h++[purgeEvent pid w (cleared pid p d w) a a]) := by
  rw [StagedEntry.Purge.run,purge_clear_prefix device resident]
  rfl

/-- The exact completed purge has one actual receipt and a paired successor;
the native Partition fixes its original queue and counted prefix. -/
theorem purge_accounted (before : Accounted h ledger debts locals w)
    (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    ∃ (part : Partition pid w (cleared pid p d w)) (generation : Nat),
      part.removed=part.packets.length ∧ Packets.epoch w=some generation ∧
      let chosen := (pendingAt (.staged generation pid part.stamp) ledger).take part.removed
      let next := settle chosen (.counted h.length .purge) ledger
      Accounted (h++[purgeEvent pid w (cleared pid p d w) a a]) next debts locals (cleared pid p d w) ∧
      Staged.Obligations.Step ledger next ∧ AllocatedFrame ledger next ∧ chosen.length=part.removed := by
  obtain ⟨part,generation,whole,epoch,step,frame,entry,complete,count⟩ :=
    StagedTerminalComplete.Source.purge_receipt pid ⟨(),w,cleared pid p d w,a,a⟩
      (purge_clear_prefix device resident) before.entry before.complete
  exact ⟨part,generation,whole,epoch,⟨entry,complete⟩,step,frame,count⟩

/-- The purge successor is precisely the original ordered cohort, not an
existentially selected equal-length list of tickets. -/
theorem purge_cohort_accounted (before : Accounted h ledger debts locals w)
    (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    let next := settle (cohort ledger pid p d) (.counted h.length .purge) ledger
    Accounted (h++[purgeEvent pid w (cleared pid p d w) a a]) next debts locals (cleared pid p d w) ∧
      Staged.Obligations.Step ledger next ∧ AllocatedFrame ledger next := by
  obtain ⟨part,generation,whole,epoch,accounted,step,frame,_⟩ := purge_accounted before device resident (a:=a)
  have shape : (p.internalId,p.staged)=(part.stamp,part.packets) := by
    simpa [Staged.stagedAt,device,resident] using part.before
  have stamp : part.stamp=p.internalId := (congrArg Prod.fst shape).symm
  have packets : part.packets=p.staged := (congrArg Prod.snd shape).symm
  have generation_eq : generation=d.ifindex := by
    simpa [Packets.epoch,device] using epoch.symm
  have size := HandshakeSecurity.StagedConservation.aligned_length (cohort_aligned before device resident)
  have chosen : (pendingAt (.staged generation pid part.stamp) ledger).take part.removed=cohort ledger pid p d := by
    rw [generation_eq,stamp,whole,packets,←size]
    exact List.take_length
  simpa only [chosen] using And.intro accounted (And.intro step frame)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement
