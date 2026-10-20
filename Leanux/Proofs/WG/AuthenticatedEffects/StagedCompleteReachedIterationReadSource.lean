import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedReadAccessFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSkbAccessFrames

/-! Worker read points retain the literal getter and packet adapter suffix.
The read-only shape excludes WG mutation by its constructors. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Iteration.Reads
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

noncomputable def peerRemainder {w : World}
    (h : List Event) (point : ReadAccess.Point (ReadAccess.peerShape pid) w.wg w.ambient v b) :
    PrefixM Event Peer := Classical.choose (point.observed_remaining h)

theorem peerRemainder_run {w : World}
    (h : List Event) (point : ReadAccess.Point (ReadAccess.peerShape pid) w.wg w.ambient v b) :
    runPrefix (liftPrefix (liftWG (getPeer pid))) w h =
      runPrefix (peerRemainder h point) {w with wg:=v,ambient:=b} h := by
  rw [←liftWGObserver_lift]
  exact Classical.choose_spec (point.observed_remaining h)

noncomputable def packetRemainder {w : World}
    (h : List Event) (point : SkbAccess.Point (SkbStore.getTx skb) w.wg w.ambient v b) :
    PrefixM Event DataPacket := Classical.choose (point.observed_remaining h)

theorem packetRemainder_run {w : World}
    (h : List Event) (point : SkbAccess.Point (SkbStore.getTx skb) w.wg w.ambient v b) :
    runPrefix (liftPrefix (liftWG (getTxSkb skb))) w h =
      runPrefix (packetRemainder h point) {w with wg:=v,ambient:=b} h := by
  rw [←liftWGObserver_lift]
  exact Classical.choose_spec (point.observed_remaining h)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Iteration.Reads
