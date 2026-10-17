import Leanux.Proofs.WG.Config.MixedPageBoundaryClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Canonical finite callback plan, indexed only by static room and first-head
conditions. Recursion follows exact unconsumed occurrences, never forced fuel. -/
def mixedPages (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (rows : List MixedPeerRow) (ctx : DumpCtx) (ready : MixedPageReady d peers nodes rows ctx) :
    List MixedPeerScan :=
  let result := mixedPeerScan d peers nodes rows ctx ctx.nextPeer {room := mixedPageRoom d ctx} #[]
  if finished : result.remaining = [] then [result]
  else result :: mixedPages d peers nodes result.remaining
    {result.native.1 with nextPeer := result.native.2.1}
    (mixedPageReady_next d peers nodes rows ctx ready finished)
termination_by mixedPageMeasure rows ctx
decreasing_by
  exact mixedPageReady_progress d peers nodes rows ctx ready finished


end Leanux.Proofs.WG.Config
