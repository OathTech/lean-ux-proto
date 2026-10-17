import Leanux.Proofs.WG.Config.StagedLeaves

set_option pp.structureInstances false
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def invalidStagedDevice (d : Device) (pid : PeerId) (p : Peer) (now : Int64) : Device :=
  fallbackDevice (keyReferenceRoundTrip (clearedStaged d pid p) p.keypairCurrent)
    pid { p with staged := [] } p.staged now

theorem staged_invalid (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p)
    (invalid : ∀ id k, p.keypairCurrent = some id → d.keypairs[id]? = some k → k.sending.isValid = false) :
    Ensures (sendStagedPackets pid) (fun w => w.k.wg = some d)
      (fun _ w => if p.staged = [] then w.k.wg = some d
        else ∃ now, w.k.wg = some (invalidStagedDevice d pid p now)) := by
  by_cases empty : p.staged = []
  · intro w ret v hd hr
    obtain ⟨u, result, he, hv⟩ := staged_empty pid d p resident empty w hd
    rw [hr] at he
    cases he
    simpa [empty] using hv
  · simp only [empty, ite_eq_right, not_false_eq_true]
    cases current : p.keypairCurrent with
    | none =>
      refine staged_compose pid d p resident empty none (clearedStaged d pid p) _ ?_ ?_
      · intro w ret v hd hr
        rw [current] at hr
        obtain ⟨u, result, he, hu, hv⟩ := keypairGet_none (clearedStaged d pid p) w hd
        rw [hr] at he
        cases he
        exact ⟨hu, hv⟩
      · simpa [invalidStagedDevice, current, keyReferenceRoundTrip] using
          stagedAfterGet_none pid p.staged (clearedStaged d pid p) { p with staged := [] }
            (by simp [clearedStaged, withPeer])
    | some id =>
      cases keyResident : d.keypairs[id]? with
      | none =>
        refine staged_compose pid d p resident empty none (clearedStaged d pid p) _ ?_ ?_
        · intro w ret v hd hr
          rw [current] at hr
          exact False.elim (keypairGet_missing id (clearedStaged d pid p) keyResident w ret v hd hr)
        · intro w ret v hd hr
          obtain ⟨now, hv⟩ := stagedAfterGet_none pid p.staged (clearedStaged d pid p)
            { p with staged := [] } (by simp [clearedStaged, withPeer]) w ret v hd hr
          exact ⟨now, by simpa [invalidStagedDevice, current, keyReferenceRoundTrip, clearedStaged, withPeer, keyResident] using hv⟩
      | some k =>
        have hg := keypairGet_present id (clearedStaged d pid p) k keyResident
        by_cases zero : k.refcount = 0
        · refine staged_compose pid d p resident empty none (clearedStaged d pid p) _ ?_ ?_
          · simpa [current, zero] using hg
          · simpa [invalidStagedDevice, current, keyReferenceRoundTrip, clearedStaged, withPeer, keyResident, zero] using
              stagedAfterGet_none pid p.staged (clearedStaged d pid p) { p with staged := [] }
                (by simp [clearedStaged, withPeer])
        · let acquired := withKeypair (clearedStaged d pid p) id { k with refcount := k.refcount + 1 }
          refine staged_compose pid d p resident empty (some id) acquired _ ?_ ?_
          · simpa [current, zero, acquired] using hg
          · have hs := stagedAfterGet_invalid pid p.staged id acquired { p with staged := [] }
              { k with refcount := k.refcount + 1 }
              (by simp [acquired, withKeypair, clearedStaged, withPeer])
              (by simp [acquired, withKeypair]) (invalid id k current keyResident) (by simp; omega)
            simpa [invalidStagedDevice, current, keyReferenceRoundTrip, acquired, clearedStaged, withPeer, keyResident, zero] using hs

end Leanux.Proofs.WG.Config
