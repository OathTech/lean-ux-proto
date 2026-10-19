import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePhaseCoverage

/-! Semantic phases at the actual silent state-mark and queue-install writes.
These expand their canonical atom boundaries using the original fixed native
prefix and pending observer suffix, without moving an endpoint account back. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePhase
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CreateDisposal CompleteCarrier StagedTerminalComplete Staged.Obligations
open HandshakeSecurity.StagedDisposal CreatePoints
set_option maxHeartbeats 600000

theorem marked_phase {id : SkbId} (device : w.wg.dev=some d) (resident : d.txSkbs[id]?=some packet)
    (before : Live rootLedger debts locals pid items h w.wg) :
    Live rootLedger debts locals pid items (markedHistory w id h) (markedWorld w d id packet state).wg ∧
      runPrefix (markPrefix w id state) w h=
        (.ok ((),markedWorld w d id packet state),markedHistory w id h) ∧
      runPrefix (Admission.actualOps.access (setTxSkbPrefix id fun p=>{p with state})) w h=
        runPrefix (markDue w id) (markedWorld w d id packet state) (markedHistory w id h) := by
  have kept : Live rootLedger debts locals pid items (markedHistory w id h) (markedWorld w d id packet state).wg := by
    apply before.transport [accessEvent (.packet (.read (.inl id) (packetStamp w.wg id)))]
    intro current active account
    exact (mark_cut device resident account).1
  obtain ⟨current,active,steps,account⟩:=before.accounted
  exact ⟨kept,(mark_cut device resident account).2.2,(mark_cut device resident account).2.1⟩

theorem installed_phase (device : w.wg.dev=some d) (resident : d.peers[pid]?=some peer)
    (steps : Staged.Obligations.Step rootLedger ledger) (pending : PendingBatch h ledger items)
    (before : Accounted h ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg) :
    let cut:={w with wg:=replacePeer w.wg d pid {peer with txQueue:=peer.txQueue.enqueue items}}
    Live rootLedger debts locals pid items h cut.wg ∧
      runPrefix (queuePrefix pid peer items) w h=(.ok ((),cut),h) ∧
      runPrefix (queueInstall pid peer items) w h=runPrefix (queueDue pid peer items) cut h := by
  obtain ⟨account,run,residual⟩:=queue_cut device resident before
  exact ⟨.queued ledger steps pending account,run,residual⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePhase
