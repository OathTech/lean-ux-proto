import Leanux.Proofs.WG.Index.TransmitRuleSource
import Leanux.Proofs.WG.Noise.DriverTagTransmitFrames

set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.DriverTags.Transmit
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Std.Do

/-! Source: instantiate the existing literal transmit factor. Negative errno
returns and the final peer release remain original; the result only retains
the tags of surviving peers. -/
theorem native (entry : TagMap) (family addr : Nat)
    (packets : List Packet) (mtu : Nat) :
    Preserves (Silent.Retained entry) (wgXmit family addr packets mtu) :=
  Index.TransmitCore.wgXmit_preserves_source (Silent.Retained entry) family addr packets mtu
    (fun _ same=>(store_frame same).wp (TagsRetained entry))
    ((lookupDst_tag_frame family addr).wp (TagsRetained entry))
    (fun pid=>(xmitTrim_tag_variant pid).wp (TagsRetained entry))
    (fun pid xs=>(xmitSplice_tag_variant pid xs).wp (TagsRetained entry))
    (fun pid=>Configuration.staged_preserves pid entry) (Silent.peerPut entry)
    ((modifyDev_frame (fun d : Device=>{d with txErrors:=d.txErrors+1})
      (fun _=>rfl)).wp (TagsRetained entry))
theorem retained (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (g : WGWorld) (ambient : Ambient) (value : Int) (final : WGWorld) (after : Ambient)
    (run : ((wgXmit family addr packets mtu).run g).run ambient =
      .ok ((value,final),after)) :
    TagsRetained (tagView g) (tagView final) :=
  (hoare_iff_run_ambient _ _ _).mp (native (tagView g) family addr packets mtu)
    g ambient value final after (TagsRetained.refl _) run

end Leanux.Proofs.WG.Noise.DriverTags.Transmit
