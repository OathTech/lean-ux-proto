import Leanux.Proofs.WG.Index.ReceiveFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem delTimer_tables (pid : PeerId) (timer : PeerTimer) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ delTimer pid timer
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  unfold delTimer
  refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ ?_
  · intro g ambient p final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG)
      g ambient p final after pre run).1
  · intro p
    exact (ensures_iff _ _ _).mpr (setPeer_tables pid _)

theorem clearPeerEndpointSrc_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ clearPeerEndpointSrc pid
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  have read : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient p final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG)
      g ambient p final after pre run).1
  apply (ensures_iff _ _ _).mp
  unfold clearPeerEndpointSrc dstCacheResetNow
  refine ensures_bind _ _ read ?_
  intro p
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (setPeer_tables pid _)) ?_
  intro _
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (dstCacheReset_tables pid)) ?_
  intro _
  refine ensures_bind _ _ read ?_
  intro p
  exact (ensures_iff _ _ _).mpr (setPeer_tables pid _)

theorem purgeStagedPackets_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ purgeStagedPackets pid
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  unfold purgeStagedPackets
  refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ ?_
  · intro g ambient p final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG)
      g ambient p final after pre run).1
  · intro p
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ ?_
    · intro g ambient result final after pre run
      cases run
      exact tablesSafe_of_cursor g _ (by simp only [Option.map_map]; rfl) pre
    · intro _
      exact (ensures_iff _ _ _).mpr (setPeer_tables pid _)

end Leanux.Proofs.WG.Index
