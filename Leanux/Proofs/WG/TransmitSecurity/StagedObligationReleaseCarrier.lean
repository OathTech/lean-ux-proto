import Leanux.Proofs.WG.TransmitSecurity.StagedObligationDisposalMaterialFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionFrontFrames

/-! Actual final-reference release settles its staged queue at the existing
receipt, before timer checks or retirement can stop. Nonfinal release retains
the same canonical ledger and all physical allocation/cleanup claims. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Staged.Origins
open AuthenticatedEffects CausalJournal

theorem core_release_none (peer : Option PeerId)
    (r : WGRunWitness (Option (PeerId × Peer)))
    (native : r.Valid (HandshakeSecurity.StagedDisposal.releaseCut peer))
    (value : r.value = none) (before : Core history ledger debts r.before) :
    Core (history ++ [.stagedDisposal (.release peer r)]) ledger debts r.after := by
  obtain ⟨epoch,queues⟩ := StagedAdmission.Front.Native.release_none peer r native value
  have cells := (ProjectedAction.iff_run_ambient _ _ _).mp (release_packet_material peer)
    r.before r.ambientBefore r.value r.after r.ambientAfter native
  apply before.quiet_views _ ?_ epoch queues cells
  intro event member
  have same : event = .stagedDisposal (.release peer r) := by simpa using member
  subst event
  rfl

/-- The final native release charges each removed staged ticket once, retains
all first terminal outcomes, and preserves every allocated cleanup debt. -/
theorem core_release_final (peer : Option PeerId)
    (r : WGRunWitness (Option (PeerId × Peer)))
    (native : r.Valid (HandshakeSecurity.StagedDisposal.releaseCut peer))
    (value : r.value = some (pid,p)) (before : Core history ledger debts r.before) :
    ∃ generation, Packets.epoch r.before = some generation ∧
      let selected := pendingAt (.staged generation pid p.internalId) ledger
      let after := settle selected (.counted history.length .finalRelease) ledger
      Step ledger after ∧ Core (history ++ [.stagedDisposal (.release peer r)]) after debts r.after ∧
        (∀ ticket ∈ selected, (ticket,Status.terminal (.counted history.length .finalRelease)) ∈ after) ∧
        (∃ count, dropped r.before = some count ∧ dropped r.after = some (count+selected.length)) := by
  obtain ⟨d,_,device,_,_,_,_,sameEpoch,_⟩ :=
    HandshakeSecurity.StagedDisposal.release_exact peer r native pid p value
  have epoch : Packets.epoch r.before = some d.ifindex := by simp [Packets.epoch,device]
  have cells := (ProjectedAction.iff_run_ambient _ _ _).mp (release_packet_material peer)
    r.before r.ambientBefore r.value r.after r.ambientAfter native
  obtain ⟨step,valid,queues,terminals,charged⟩ :=
    release_step peer r native value before.valid before.queues epoch history.length
  have chosen : ∀ ticket ∈ pendingAt (.staged d.ifindex pid p.internalId) ledger,
      ticket ∈ pendingAt (.staged d.ifindex pid p.internalId) ledger := fun _ member => member
  have frame := settle_allocated_frame before.valid chosen (by intro _ _; simp)
    (.counted history.length .finalRelease)
  refine ⟨d.ifindex,epoch,step,⟨?_,queues.append_history _,(before.selected.settled _ _).append _,
    ((before.physical.ledger_frame frame).views sameEpoch cells).append _⟩,terminals,charged⟩
  rw [births_quiet _ rfl]
  exact valid

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
