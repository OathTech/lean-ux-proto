import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalProvenanceFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionCoreCheckpoint

/-! Native counted cuts supply provenance for the exact incoming staged
ticket prefix. Receipt entry and queue alignment are the same native state;
neither an unrelated receipt nor payload membership substitutes for that cut. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedProvenance
open Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open CausalJournal

theorem overflow (pid : PeerId) (r : WGRunWitness Unit) (native : r.Valid (xmitTrim pid))
    (part : HandshakeSecurity.StagedDisposal.Partition pid r.before r.after)
    (epoch : Packets.epoch r.before = some generation)
    (queues : QueueInv history ledger r.before) (valid : Valid domain ledger)
    (before : Justified history ledger) :
    let chosen := (pendingAt (.staged generation pid part.stamp) ledger).take part.removed
    let outcome := Staged.Obligations.Terminal.counted history.length .overflow
    Staged.Obligations.Step ledger (settle chosen outcome ledger) ∧
      Justified (history ++ [.stagedDisposal (.overflow pid r)]) (settle chosen outcome ledger) := by
  have aligned := queues generation pid part.stamp
  rw [partition_before part epoch] at aligned
  exact settle_at valid before (fun _ member => List.mem_of_mem_take member)
    (fun _ member => .overflow pid r native part generation epoch _ aligned member)

theorem purge (pid : PeerId) (r : WGRunWitness Unit) (native : r.Valid (purgeStagedPackets pid))
    (part : HandshakeSecurity.StagedDisposal.Partition pid r.before r.after)
    (whole : part.removed = part.packets.length) (epoch : Packets.epoch r.before = some generation)
    (queues : QueueInv history ledger r.before) (valid : Valid domain ledger)
    (before : Justified history ledger) :
    let chosen := pendingAt (.staged generation pid part.stamp) ledger
    let outcome := Staged.Obligations.Terminal.counted history.length .purge
    Staged.Obligations.Step ledger (settle chosen outcome ledger) ∧
      Justified (history ++ [.stagedDisposal (.purge pid r)]) (settle chosen outcome ledger) := by
  have aligned := queues generation pid part.stamp
  rw [partition_before part epoch] at aligned
  exact settle_at valid before (fun _ member => member)
    (fun _ member => .purge pid r native part whole generation epoch _ aligned member)

theorem released (peer : Option PeerId) (r : WGRunWitness (Option (PeerId × Peer)))
    (native : r.Valid (HandshakeSecurity.StagedDisposal.releaseCut peer))
    (result : r.value = some (pid,p)) (epoch : Packets.epoch r.before = some generation)
    (queues : QueueInv history ledger r.before) (valid : Valid domain ledger)
    (before : Justified history ledger) :
    let chosen := pendingAt (.staged generation pid p.internalId) ledger
    let outcome := Staged.Obligations.Terminal.counted history.length .finalRelease
    Staged.Obligations.Step ledger (settle chosen outcome ledger) ∧
      Justified (history ++ [.stagedDisposal (.release peer r)]) (settle chosen outcome ledger) := by
  obtain ⟨device,_,deviceBefore,resident,_,_,_,_,_⟩ :=
    HandshakeSecurity.StagedDisposal.release_exact peer r native pid p result
  have staged : Staged.stagedAt r.before pid = some (p.internalId,p.staged) := by
    simp only [Staged.stagedAt,deviceBefore,Option.bind_some,resident,Option.map_some]
  have aligned := queues generation pid p.internalId
  simp only [stagedPackets,epoch,staged,ite_true,eq_self] at aligned
  exact settle_at valid before (fun _ member => member)
    (fun _ member => .released peer r native pid p result generation epoch _ aligned member)

theorem checkpoint (cut : StagedAdmission.Front.Checkpoint entry history ledger snapshot)
    (before : Justified entry.history entry.ledger) : Justified history ledger := by
  cases cut with
  | initial => exact before
  | nonfinal => exact before.append _
  | released peer r run pid p value generation epoch queues =>
    exact (released peer r run value epoch queues entry.valid before).2
  | trimmed pid r run part generation epoch queues =>
    exact (overflow pid r run part epoch queues entry.valid before).2

theorem normal (result : StagedAdmission.Front.Normal entry input r history ledger)
    (before : Justified entry.history entry.ledger) :
    Justified (history ++ [StagedAdmission.Front.routedEvent input r]) ledger := by
  obtain ⟨prior,snapshot,cut,after⟩ := result.2.2.2.2
  have checked := checkpoint cut before
  cases selected : r.value with
  | error code =>
    rw [selected] at after
    rw [after.1]
    exact checked.append _
  | ok pid =>
    rw [selected] at after
    obtain ⟨w,a,generation,stamp,_,_,rfl⟩ := after
    exact (checked.admitted _ _ _).append _

theorem AllocationLinks.frame (before : AllocationLinks history ledger)
    (frame : AllocatedFrame ledger after) : AllocationLinks history after :=
  fun ticket batch ordinal member => before ticket batch ordinal ((frame.pending _ _ _).mp member)

theorem checkpoint_links (cut : StagedAdmission.Front.Checkpoint entry history ledger snapshot)
    (before : AllocationLinks entry.history entry.ledger) : AllocationLinks history ledger := by
  obtain ⟨suffix,append⟩ := cut.extends
  rw [append]
  exact (before.frame cut.allocated_frame).append suffix

theorem normal_links (result : StagedAdmission.Front.Normal entry input r history ledger)
    (before : AllocationLinks entry.history entry.ledger) :
    AllocationLinks (history ++ [StagedAdmission.Front.routedEvent input r]) ledger := by
  obtain ⟨prior,snapshot,cut,_⟩ := result.2.2.2.2
  obtain ⟨suffix,append⟩ := cut.extends
  rw [append,List.append_assoc]
  exact (before.frame result.allocated_frame).append _

end Leanux.Proofs.WG.AuthenticatedEffects.StagedProvenance
