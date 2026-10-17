import Leanux.Proofs.WG.Config.MixedPageScanModel
import Leanux.Proofs.WG.Config.MixedPeerCoalesceModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- The exact fixed part emitted by a fresh or resumed peer occurrence. -/
def mixedPeerFixed (p : Peer) (ctx : DumpCtx) : List (String × Json) :=
  if ctx.nextAllowedip.isNone then peerFixedAttrs p
  else [("public_key",toJson (hexKey p.remoteStatic))]

/-- A virtual complete suffix in the exact serializer attribute shape. Only
its first row may be a continuation; all later rows start fresh. -/
def mixedRowsParts (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (ctx : DumpCtx) : List MixedPeerRow → List PeerDumpAttrs
  | [] => []
  | (pid,ids)::rows =>
      coalesceAipPart (hexKey (peers pid).remoteStatic) (mixedPeerFixed (peers pid) ctx)
        (dumpNodeJsons nodes ids) false ::
      rows.map (fun row => coalesceAipPart (hexKey (peers row.1).remoteStatic)
        (peerFixedAttrs (peers row.1)) (dumpNodeJsons nodes row.2) false)

end Leanux.Proofs.WG.Config
