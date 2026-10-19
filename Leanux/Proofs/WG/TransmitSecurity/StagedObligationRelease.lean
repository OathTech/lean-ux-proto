import Leanux.Proofs.WG.TransmitSecurity.StagedObligationCounted
import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationReleaseTickets

/-! Final peer release settles the existing queue's entire fixed ticket list
before native timer checks or retirement can stop. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Leanux.Proofs.Logged Staged.Origins
open AuthenticatedEffects.CausalJournal

theorem release_step (peer : Option PeerId)
    (r : WGRunWitness (Option (PeerId × Peer)))
    (run : r.Valid (HandshakeSecurity.StagedDisposal.releaseCut peer))
    (released : r.value = some (pid,p))
    (valid : Valid births ledger) (before : QueueInv history ledger r.before)
    (epoch : Packets.epoch r.before = some generation) (position : Nat) :
    let selected := pendingAt (.staged generation pid p.internalId) ledger
    let after := settle selected (.counted position .finalRelease) ledger
    Step ledger after ∧ Valid births after ∧ QueueInv history after r.after ∧
      (∀ ticket ∈ selected, (ticket,Status.terminal (.counted position .finalRelease)) ∈ after) ∧
      (∃ count, dropped r.before = some count ∧ dropped r.after = some (count+selected.length)) := by
  dsimp only
  let location := Pending.staged generation pid p.internalId
  let selected := pendingAt location ledger
  let after := settle selected (.counted position .finalRelease) ledger
  have unique : (keys ledger).Nodup := valid.1.symm ▸ valid.2
  have selectedPending : ∀ ticket ∈ selected, ticket ∈ pendingAt location ledger := by
    intro ticket member
    exact member
  have step : Step ledger after := settle_pending unique selectedPending
  obtain ⟨device,_,deviceBefore,resident,_,absent,_,sameEpoch,others⟩ :=
    HandshakeSecurity.StagedDisposal.release_exact peer r run pid p released
  have stagedBefore : stagedAt r.before pid = some (p.internalId,p.staged) := by
    simp only [stagedAt,deviceBefore,Option.bind_some,resident,Option.map_some]
  have aligned : Aligned (Born history generation pid p.internalId) selected p.staged := by
    have related := before generation pid p.internalId
    simpa only [stagedPackets,epoch,stagedBefore,ite_true,Option.some.injEq,eq_self] using related
  have native := HandshakeSecurity.StagedConservation.native_release peer r run pid p released
    selected (Born history generation pid p.internalId) aligned
  refine ⟨step,step.valid valid,?_,?_,native.2.2.2.1⟩
  · intro otherGeneration otherPid stamp
    by_cases same : Pending.staged otherGeneration otherPid stamp = location
    · obtain ⟨rfl,rfl,rfl⟩ := Pending.staged.inj same
      have empty : pendingAt location after = [] := by
        rw [pendingAt_settle]
        apply List.filter_eq_nil_iff.mpr
        intro ticket member
        simp only [selected,location] at member ⊢
        simp [member]
      change Aligned _ (pendingAt location after) _
      rw [empty]
      have nativeEmpty : stagedPackets otherGeneration otherPid p.internalId r.after = [] := by
        simp [stagedPackets,absent]
      rw [nativeEmpty]
      exact .nil
    · rw [erased_other epoch sameEpoch stagedBefore absent others same,
        settle_other_location unique selectedPending same]
      exact before otherGeneration otherPid stamp
  · intro ticket member
    apply List.mem_map.mpr
    refine ⟨(ticket,Status.pending location),mem_pendingAt.mp member,?_⟩
    simp only [ite_eq_left member]

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
