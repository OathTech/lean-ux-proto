import Leanux.Proofs.WG.HandshakeSecurity.StagingSelectionSource

namespace Leanux.Proofs.WG.HandshakeSecurity.StagingSelection
open Leanux Leanux.WG Leanux.Proofs.Logged

/-- A successful native borrow returns only the requested slot. -/
theorem keypairGet_selected (kp : Option KeypairId) (id : KeypairId)
    (w v : WGWorld) (a b : Ambient)
    (run : ((keypairGet kp).run w).run a = .ok ((some id, v), b)) :
    kp = some id := by
  cases kp with
  | none => simp [keypairGet, branch, AmbientM.branch] at run
  | some requested =>
    cases device : w.dev with
    | none =>
      simp [keypairGet, getKeypair, getDev, device, branch, AmbientM.branch,
        invariant, AmbientM.invariant] at run
      cases run
    | some d =>
      cases key : d.keypairs[requested]? with
      | none =>
        simp [keypairGet, getKeypair, getDev, device, key, branch, AmbientM.branch,
          invariant, AmbientM.invariant] at run
        cases run
      | some k =>
        simp only [keypairGet, getKeypair, getDev, setKeypair, modifyDev,
          branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, refcountIncNotZero,
          unsupported, invariant, AmbientM.unsupported, AmbientM.invariant,
          StateT.run_bind] at run
        simp [device, key] at run
        split at run <;> simp_all
        all_goals try split at run <;> simp_all
        all_goals try split at run <;> simp_all
        all_goals try split at run <;> simp_all
        all_goals change (Except.error _ : Except Stop _) = _ at run
        all_goals cases run

theorem peerRead_resident (pid : PeerId) (r : WGRunWitness Peer)
    (valid : r.Valid (getPeer pid)) :
    ∃ d, r.before.dev = some d ∧ d.peers[pid]? = some r.value := by
  cases device : r.before.dev with
  | none =>
    simp [WGRunWitness.Valid, getPeer, getDev, device, invariant, AmbientM.invariant] at valid
    cases valid
  | some d =>
    cases peer : d.peers[pid]? with
    | none =>
      simp [WGRunWitness.Valid, getPeer, getDev, device, peer, invariant, AmbientM.invariant] at valid
      cases valid
    | some p =>
      simp [WGRunWitness.Valid, getPeer, getDev, device, peer] at valid
      exact ⟨d, rfl, valid.1.1 ▸ peer⟩

theorem receipt_selected (r : Receipt) (valid : r.Valid) :
    r.peerRead.value.keypairCurrent = some r.admission.slot := by
  apply keypairGet_selected _ _ r.loanRead.before r.loanRead.after
    r.loanRead.ambientBefore r.loanRead.ambientAfter
  have run := valid.2.1
  change ((keypairGet r.peerRead.value.keypairCurrent).run r.loanRead.before).run
    r.loanRead.ambientBefore = .ok ((r.loanRead.value, r.loanRead.after), r.loanRead.ambientAfter) at run
  rwa [valid.2.2.1] at run

theorem receipt_resident (r : Receipt) (valid : r.Valid) :
    (∃ d, r.peerRead.before.dev = some d ∧
      d.peers[r.admission.peer]? = some r.peerRead.value) ∧
    (∃ d, r.admission.keyRead.before.dev = some d ∧
      d.keypairs[r.admission.slot]? = some r.admission.keyRead.value) := by
  refine ⟨peerRead_resident _ _ valid.1, ?_⟩
  exact (KeyTimes.getKeypair_return r.admission.slot r.admission.keyRead.before
    r.admission.keyRead.after r.admission.keyRead.value r.admission.keyRead.ambientBefore
    r.admission.keyRead.ambientAfter valid.2.2.2.1).2.2

end Leanux.Proofs.WG.HandshakeSecurity.StagingSelection
