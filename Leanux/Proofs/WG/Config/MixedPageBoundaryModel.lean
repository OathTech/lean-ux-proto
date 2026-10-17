import Leanux.Proofs.WG.Config.MixedPageScanModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

def mixedPageRoom (d : Device) (ctx : DumpCtx) : Nat :=
  if ctx.nextPeer.isNone then NLMSG_GOODSIZE-devicePrefixSpace d else NLMSG_GOODSIZE-24

/-- A static space domain, with no successful callback or receive premise. -/
def MixedPageReady (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (rows : List MixedPeerRow) (ctx : DumpCtx) : Prop :=
  rows = [] ∨ 84 ≤ mixedPageRoom d ctx ∧
    ∀ pid ids tail, rows = (pid,ids)::tail →
      mixedPeerHeadFits nodes (peers pid) ctx {room := mixedPageRoom d ctx} ids


end Leanux.Proofs.WG.Config
