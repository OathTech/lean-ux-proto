import Leanux.Proofs.WG.Noise.ClearWorkerFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.ClearWorker
open Leanux Leanux.WG Leanux.Proofs.Framing

/-- Exact normal tag effect of the whole worker, including the final put. -/
theorem queuedClear_effect (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (queuedExpiredZeroKeyMaterial pid) (fun g => g.dev = some d)
      (fun _ g => 0 < p.refcount ∧ ∀ target, responseTagMap g.dev target =
        if pid = target then
          if p.refcount = 1 then none else some HANDSHAKE_ZEROED
        else responseTagMap (some d) target) := by
  let zeroed := Config.zeroedHandshake p
  let zeroDevice := Config.expiryZeroDevice d pid p
  let cleared : Peer := {zeroed with
    keypairNext := none, keypairPrevious := none, keypairCurrent := none}
  have zeroResident : zeroDevice.peers[pid]? = some zeroed := by
    simp [zeroDevice,zeroed,Config.expiryZeroDevice,Config.withPeer]
  have clear : Ensures (handshakeClear pid) (fun g => g.dev = some d)
      (fun _ g => g.dev = some zeroDevice) := by
    simpa only [Config.expiryReadPrefix,requireNotPending,pure_bind] using
      Config.expiryReadPrefix_exact pid d p resident
  have keys : Ensures (keypairsClear pid) (fun g => g.dev = some zeroDevice)
      (fun _ g => ∃ out, g.dev = some out ∧
        responseTagMap (some out) = responseTagMap (some zeroDevice) ∧
        out.peers[pid]? = some cleared) := by
    intro g ambient result final after device run
    obtain ⟨out,output,steps⟩ := keypairsClear_effect pid zeroDevice zeroed zeroResident
      g ambient result final after device run
    have peer := keypairsClear_peer pid zeroed g ambient result final after
      (by simp [peerAt,device,zeroResident]) run
    exact ⟨out,output,clearRun_tagMap steps,by simpa [peerAt,output,cleared] using peer⟩
  unfold queuedExpiredZeroKeyMaterial
  refine ensures_bind _ _ clear ?_
  intro u
  refine ensures_bind _ _ keys ?_
  intro v g ambient result final after pre run
  obtain ⟨out,device,tags,residentOut⟩ := pre
  have effect := peerPut_spec_clearTagMap_variant pid out cleared residentOut
    g ambient result final after device run
  refine ⟨effect.1, ?_⟩
  intro target
  rw [effect.2 target]
  by_cases same : pid = target
  · simp [same,cleared,zeroed,Config.zeroedHandshake,HANDSHAKE_ZEROED]
  · simp only [same,ite_false]
    rw [tags]
    simp [zeroDevice,Config.expiryZeroDevice,Config.withPeer,responseTagMap,
      Std.TreeMap.getElem?_insert,same]

end Leanux.Proofs.WG.Noise.ClearWorker
