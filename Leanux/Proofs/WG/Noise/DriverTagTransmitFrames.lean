import Leanux.Proofs.WG.Index.TransmitRuleSource
import Leanux.Proofs.WG.Noise.DriverTagSilentFrames
import Leanux.Proofs.WG.Noise.DriverTagPeerConfigurationFrames
import Leanux.Proofs.WG.Queues.RxStackFrames
import Leanux.Proofs.WG.Queues.RxBorrow

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.DriverTags.Transmit
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Std.Do

/-- Tag counterpart of CurrentSlots.lookupDst_view, projected directly from
the existing exact acquisition effect rather than a new lookup traversal. -/
theorem lookupDst_tag_frame (family addr : Nat) :
    SameView tagView (lookupDst family addr) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupDst_spec family addr (wgStoreView g))
    g ambient result final after rfl run
  change responseTagMap (wgStoreView final).dev = responseTagMap (wgStoreView g).dev
  cases result with
  | none =>
    change wgStoreView final = wgStoreView g at borrowed
    rw [borrowed]
  | some pid =>
    obtain ⟨d,p,device,resident,_,effect⟩ := borrowed
    rw [effect,device]
    exact tagMap_write d pid p _ resident rfl

/-- Tag counterpart of CurrentSlots.trim_preserves. The actual read remains
paired with its conditional staged-queue write; no saved arbitrary peer is framed. -/
theorem xmitTrim_tag_variant (pid : PeerId) :
    SameView tagView (xmitTrim pid) := by
  apply Index.TransmitCore.xmitTrim_view tagView pid
  intro w d p device resident
  funext target
  simpa only [tagView,device,responseTagMap,Option.bind_some] using
    congrFun (tagMap_write d pid p {p with staged:=p.staged.drop 1} resident rfl) target
/-- Tag counterpart of CurrentSlots.splice_preserves. The repeated original
read is reduced using its existing exact read/read source equation. -/
theorem xmitSplice_tag_variant (pid : PeerId) (packets : List Packet) :
    SameView tagView (xmitSplice pid packets) := by
  unfold xmitSplice
  rw [getPeer_twice]
  exact modifyPeer_frame pid (fun p => {p with staged := p.staged ++ packets}) (fun _ => rfl)

end Leanux.Proofs.WG.Noise.DriverTags.Transmit
