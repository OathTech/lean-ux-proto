import Leanux.Proofs.WG.Noise.DriverTagPeerConfigurationFrames
import Leanux.Proofs.WG.Noise.DriverTagProductSource
import Leanux.Proofs.WG.Config.DumpInvariantSource
import Leanux.Proofs.WG.Queues.RxPollComposition

set_option autoImplicit false

/-! Frames: specialize the existing dump invariant contract to raw tag
retention. Peer releases may delete a cursor peer; no residency assumption
or replacement serializer is introduced. -/
namespace Leanux.Proofs.WG.Noise.DriverTags.Dump
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Std.Do

theorem contracts (entry : TagMap) :
    Config.DumpInvariant.Contracts (fun g => TagsRetained entry (tagView g)) where
  stable := by
    intro g final same prior
    have tags : tagView final = tagView g :=
      congrArg (fun s : WGStoreView => responseTagMap s.dev) same
    change TagsRetained entry (tagView final)
    rw [tags]
    exact prior
  acquire pid := (peerGet_frame pid).wp (TagsRetained entry)
  release pid := Configuration.put_preserves pid entry

end Leanux.Proofs.WG.Noise.DriverTags.Dump
