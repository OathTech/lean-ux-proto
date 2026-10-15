import Leanux.Proofs.WG.Index.SendFrames
import Leanux.Proofs.WG.Index.OwnerCreation
import Leanux.Proofs.WG.Index.PeerRelease

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem createInitiation_tables (pid : PeerId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ createInitiation pid
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  cases hd : w.k.wg with
  | none =>
    have stop : getDev.run w = .error (.invariant "no WireGuard device in this trace's fixture") := by
      simp [getDev, getK, invariant, hd, StateT.run_bind]
      rfl
    change (getDev.run w >>= _) = _ at run
    rw [stop] at run
    cases run
  | some d =>
    have safe := pre d hd
    obtain ⟨di, hi, indices⟩ := (ensures_iff _ _ _).mpr (createInitiation_indices_spec pid)
      w result final ⟨d, hd, safe.1⟩ run
    obtain ⟨doo, ho, owners, bounded⟩ := (ensures_iff _ _ _).mpr (createInitiation_owners_spec pid)
      w result final ⟨d, hd, safe.2.1, safe.2.2⟩ run
    intro df hf
    rw [hf] at hi ho
    cases hi
    cases ho
    exact ⟨indices, owners, bounded⟩

theorem sendHandshakeInitiation_tables (pid : PeerId) : Ensures (sendHandshakeInitiation pid)
    (fun w => TablesSafeKernel w.k) (fun _ w => TablesSafeKernel w.k) := by
  have hc := createInitiation_tables pid
  have hm := addMacToPacket_tables pid
  have ht := traversal_tables pid
  have hd := delKeepalive_tables pid
  have hs := sendBufferToPeer_tables pid
  have hf := timersHandshakeInitiated_tables pid
  have hh := hiddenClock64_kernel_spec TablesSafeKernel
  have hp := setPeer_tables
  rw [ensures_iff]
  mvcgen [sendHandshakeInitiation, branchExpired, birthdateTest, getPeer, getDev, getK,
    branch, branchCmp, invariant, hc, hm, ht, hd, hs, hf, hh, hp]

theorem indexRemove_tables (owner : IndexOwner) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ indexRemove owner
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  cases hd : w.k.wg with
  | none =>
    have stop : getDev.run w = .error (.invariant "no WireGuard device in this trace's fixture") := by
      simp [getDev, getK, invariant, hd, StateT.run_bind]
      rfl
    change (getDev.run w >>= _) = _ at run
    rw [stop] at run
    cases run
  | some d =>
    obtain ⟨r, after, execution, device⟩ := indexRemove_exact owner d w hd
    rw [run] at execution
    cases execution
    intro df present
    rw [device] at present
    cases present
    have safe := pre d hd
    refine ⟨remove_indices owner _ safe.1, remove_owners owner _ safe.2.1, ?_⟩
    intro e member id own
    exact safe.2.2 e (List.mem_filter.mp member).1 id own

/-- A normal final release may remove the peer; no retained-reference premise is needed. -/
theorem peerPut_tables (peer : Option PeerId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ peerPut peer
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hp := setPeer_tables
  have hr := indexRemove_tables
  have hc := refcountDecAndTest_kernel_variant TablesSafeKernel
  mvcgen [peerPut, requireNotPending, getPeer, getDev, getK,
    branch, invariant, modifyDev, modifyK, retirePeerUnits, hp, hr, hc]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [TablesSafeKernel, DeviceTablesSafe, KeypairOwnersBounded]
  all_goals grind

theorem handshakeSendWorker_tables (pid : PeerId) : Ensures (handshakeSendWorker pid)
    (fun w => TablesSafeKernel w.k) (fun _ w => TablesSafeKernel w.k) := by
  have hs := (ensures_iff _ _ _).mp (sendHandshakeInitiation_tables pid)
  have hp := peerPut_tables
  rw [ensures_iff]
  mvcgen [handshakeSendWorker, hs, hp]

end Leanux.Proofs.WG.Index
