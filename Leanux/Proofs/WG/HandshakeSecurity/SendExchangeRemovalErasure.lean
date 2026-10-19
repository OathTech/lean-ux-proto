import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeRemovalSource
import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeErasure

/-! Native result and Stop erasure through direct configuration drains. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.SendExchange
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

variable (sg : {α : Type} → WG.M α → WGPrefix E α)
  (hs : ∀ {α} (a : WG.M α), ErasesStatePrefix (sg a) a)
  (dg : Option PeerId → WGPrefix E Unit)
  (hd : ∀ peer, ErasesStatePrefix (dg peer) (drainHandshakeSendWq peer))

include hs hd in
theorem timersStop_erases (pid : PeerId) :
    ErasesStatePrefix (timersStopWith sg dg pid) (timersStop pid) := by
  unfold timersStopWith timersStop
  repeat' first | exact hs _ | exact hd _ | work_root_erasure_step

include hs hd in
theorem afterDead_erases (pid : PeerId) :
    ErasesStatePrefix (afterDeadWith sg dg pid) (peerRemoveAfterDead pid) := by
  unfold afterDeadWith peerRemoveAfterDead
  repeat' first
    | exact hs _
    | exact hd _
    | exact timersStop_erases sg hs dg hd _
    | work_root_erasure_step

include hs hd in
theorem remove_erases (peer : Option PeerId) :
    ErasesStatePrefix (removeWith sg dg peer) (peerRemove peer) := by
  rw [← remove_factor]
  unfold removeWith Configuration.peerRemoveWith
  repeat' first
    | exact hs _
    | exact afterDead_erases sg hs dg hd _
    | work_root_erasure_step
  all_goals simp_all only [Option.some.injEq]
  all_goals first | exact afterDead_erases sg hs dg hd _ | exact False.elim (by solve_by_elim)

include hs hd in
theorem removeAll_erases :
    ErasesStatePrefix (removeAllWith sg dg) peerRemoveAll := by
  rw [← removeAll_factor]
  unfold removeAllWith Configuration.peerRemoveAllWith
  repeat' first
    | exact hs _
    | exact afterDead_erases sg hs dg hd _
    | work_root_erasure_step

end Leanux.Proofs.WG.HandshakeSecurity.SendExchange
