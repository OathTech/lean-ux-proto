import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedIterationReadSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProduct

/-! Read-only iteration cuts preserve both the packet account and its native
allocation companion. A projection frame alone would not establish the latter. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Iteration.Reads
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

theorem packet_world (point : SkbAccess.Point (SkbStore.getTx skb) w a v b) : v=w := by
  cases point with
  | read point => exact point.world
  | component device performed => rfl
  | returned performed => exact (Packets.getTxSkb_current _ _ _ _ _ _ performed).1

theorem peer_carrier {w : World}
    (point : ReadAccess.Point (ReadAccess.peerShape pid) w.wg w.ambient v b)
    (before : CompleteProduct.Carrier h w) :
    CompleteProduct.Carrier h {w with wg:=v,ambient:=b} := by
  rw [point.world]
  exact before

theorem packet_carrier {w : World}
    (point : SkbAccess.Point (SkbStore.getTx skb) w.wg w.ambient v b)
    (before : CompleteProduct.Carrier h w) :
    CompleteProduct.Carrier h {w with wg:=v,ambient:=b} := by
  rw [packet_world point]
  exact before

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Iteration.Reads
