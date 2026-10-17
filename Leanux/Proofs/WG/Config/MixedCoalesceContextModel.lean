import Leanux.Proofs.WG.Config.MixedPageContentModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Data-only content invariant for the actual inner coalescer. A fresh head
follows a complete accumulator; a resumed head continues its canonical last
record. The target is fixed serialized content, not an execution premise. -/
def MixedCoalesceState (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (rows : List MixedPeerRow) (ctx : DumpCtx) (acc target : Array PeerDumpAttrs) : Prop :=
  match ctx.nextAllowedip with
  | none => (acc = #[] ∨ acc.back!.split = false) ∧
      target = acc ++ (mixedRowsParts peers nodes ctx rows).toArray
  | some _ => ∃ (pid : PeerId) (ids : List NodeId) (rest : List MixedPeerRow)
      (before : Array Json) (fixed : List (String × Json)) (done : Array PeerDumpAttrs),
      rows = (pid,ids)::rest ∧ ids ≠ [] ∧
      (∀ item ∈ fixed, item.1 ≠ "allowed_ips") ∧
      acc = done.push (coalesceAipPart (hexKey (peers pid).remoteStatic) fixed before true) ∧
      target = done.push (coalesceAipPart (hexKey (peers pid).remoteStatic) fixed
        (before ++ dumpNodeJsons nodes ids) false) ++
        (mixedRowsParts peers nodes {ctx with nextAllowedip := none} rest).toArray

end Leanux.Proofs.WG.Config
