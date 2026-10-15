import Leanux.Proofs.WG.Index.ResponseFrames
import Leanux.Proofs.WG.Index.SendSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Combine the existing numeric and owner/bound contracts over the same original run. -/
theorem createResponse_tables (pid : PeerId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ createResponse pid
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  cases hd : w.k.wg with
  | none =>
    have stop : (getPeer pid).run w = .error (.invariant "no WireGuard device in this trace's fixture") := by
      simp [getPeer, getDev, getK, invariant, hd, StateT.run_bind]
      rfl
    change ((getPeer pid).run w >>= _) = _ at run
    rw [stop] at run
    cases run
  | some d =>
    have safe := pre d hd
    obtain ⟨di, hi, indices⟩ := (ensures_iff _ _ _).mpr (createResponse_indices_spec pid)
      w result final ⟨d, hd, safe.1⟩ run
    obtain ⟨doo, ho, owners, bounded⟩ := (ensures_iff _ _ _).mpr (createResponse_owners_spec pid)
      w result final ⟨d, hd, safe.2.1, safe.2.2⟩ run
    intro df hf
    rw [hf] at hi ho
    cases hi
    cases ho
    exact ⟨indices, owners, bounded⟩

/-- Combine the existing numeric and owner/bound contracts over the same original run. -/
theorem beginSession_tables (pid : PeerId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ beginSession pid
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  cases hd : w.k.wg with
  | none =>
    have stop : (getPeer pid).run w = .error (.invariant "no WireGuard device in this trace's fixture") := by
      simp [getPeer, getDev, getK, invariant, hd, StateT.run_bind]
      rfl
    change ((getPeer pid).run w >>= _) = _ at run
    rw [stop] at run
    cases run
  | some d =>
    have safe := pre d hd
    obtain ⟨di, hi, indices⟩ := (ensures_iff _ _ _).mpr (beginSession_indices_spec pid)
      w result final ⟨d, hd, safe.1⟩ run
    obtain ⟨doo, ho, owners, bounded⟩ := (ensures_iff _ _ _).mpr (beginSession_owners_spec pid)
      w result final ⟨d, hd, safe.2.1, safe.2.2⟩ run
    intro df hf
    rw [hf] at hi ho
    cases hi
    cases ho
    exact ⟨indices, owners, bounded⟩

/-- Compose response creation, session installation and the original send/timer suffix. -/
theorem sendHandshakeResponse_tables (pid : PeerId) : Ensures (sendHandshakeResponse pid)
    (fun w => TablesSafeKernel w.k) (fun _ w => TablesSafeKernel w.k) := by
  have hc := createResponse_tables pid
  have hb := beginSession_tables pid
  have hm := addMacToPacket_tables pid
  have hsession := timersSessionDerived_tables pid
  have ht := traversal_tables pid
  have hd := delKeepalive_tables pid
  have hs := sendBufferToPeer_tables pid
  have hh := hiddenClock64_kernel_spec TablesSafeKernel
  have hp := setPeer_tables
  rw [ensures_iff]
  mvcgen [sendHandshakeResponse, getPeer, getDev, getK, branch, invariant,
    hc, hb, hm, hsession, ht, hd, hs, hh, hp]

end Leanux.Proofs.WG.Index
