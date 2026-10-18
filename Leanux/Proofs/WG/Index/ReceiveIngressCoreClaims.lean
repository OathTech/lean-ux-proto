import Leanux.Proofs.WG.Index.ReceiveIngressCoreSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.Framing

theorem packetReceive_index (msg : List UInt8) (src : SkbSource) :
    Campaign2.Ensures (packetReceive msg src) View.IndexCore (fun _=>View.IndexCore) :=
  (Noise.ensures_iff _ _ _).mpr (ReceiveIngressCore.packet_core msg src)

theorem wgReceive_index (msg : List UInt8) (src : SkbSource) :
    Campaign2.Ensures (wgReceive msg src) View.IndexCore (fun _=>View.IndexCore) :=
  (Noise.ensures_iff _ _ _).mpr (ReceiveIngressCore.receive_core msg src)

end Leanux.Proofs.WG.Index
