import Leanux.Proofs.WG.Config.Model
import Leanux.Proofs.WG.Config.PeerScalars

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem clearEndpointSource_exact (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (clearPeerEndpointSrc pid) (fun w => w.dev = some d)
      (fun _ w => ∃ d' reset, w.dev = some d' ∧
        d' = { d with peers := d'.peers } ∧
        d'.peers[pid]? = some (clearedSource p reset) ∧
        ∀ q, q ≠ pid → d'.peers[q]? = d.peers[q]?) := by
  intro g ambient result final after device run
  have hiddenLift : (hiddenJiffies .dstCacheResetTs : WG.M UInt64) =
      StateT.lift (AmbientM.hiddenJiffies .dstCacheResetTs) := rfl
  cases mode : ambient.armRecords && g.dstCacheRecords with
  | false =>
    have disabled : ambient.armRecords = false ∨ g.dstCacheRecords = false := by
      cases arm : ambient.armRecords with
      | false => exact Or.inl rfl
      | true => exact Or.inr (by simpa [arm] using mode)
    simp [clearPeerEndpointSrc, dstCacheResetNow, dstCacheReset, getPeer, getDev,
      setPeer, modifyDev, getAmbient, device, resident, disabled] at run
    rcases run with ⟨rfl, rfl⟩
    refine ⟨_, p.dstCache.resetTs, rfl, rfl, ?_, ?_⟩
    · simp [clearedSource]
    · intro q different
      simp [Std.TreeMap.getElem?_insert, Ne.symm different]
  | true =>
    have modes : ambient.armRecords = true ∧ g.dstCacheRecords = true := by simpa using mode
    cases draw : (AmbientM.hiddenJiffies .dstCacheResetTs).run ambient with
    | error stop =>
      simp [clearPeerEndpointSrc, dstCacheResetNow, dstCacheReset, getPeer, getDev,
        setPeer, modifyDev, getAmbient, device, resident, modes.1, modes.2, hiddenLift, draw] at run
      cases run
    | ok output =>
      obtain ⟨reset, next⟩ := output
      simp [clearPeerEndpointSrc, dstCacheResetNow, dstCacheReset, getPeer, getDev,
        setPeer, modifyDev, getAmbient, device, resident, modes.1, modes.2, hiddenLift, draw] at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨_, reset, rfl, rfl, ?_, ?_⟩
      · simp [clearedSource]
      · intro q different
        simp [Std.TreeMap.getElem?_insert, Ne.symm different]

end Leanux.Proofs.WG.Config
