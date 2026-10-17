import Leanux.Proofs.WG.Config.MixedPeerSerializerModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

abbrev MixedPeerRow := PeerId × List NodeId
abbrev MixedPeerNative := DumpCtx × Option PeerId × NlSkb × Bool × Array PeerDumpAttrs

/-- The native loop value and the exact unconsumed occurrence suffix. -/
structure MixedPeerScan where
  native : MixedPeerNative
  remaining : List MixedPeerRow

/-- Two units per peer occurrence cover the resumed-to-fresh phase reset. -/
def mixedRowsWeight : List MixedPeerRow → Nat
  | [] => 0
  | row :: rows => 2 + row.2.length + mixedRowsWeight rows

def mixedPageMeasure (rows : List MixedPeerRow) (ctx : DumpCtx) : Nat :=
  mixedRowsWeight rows + if ctx.nextAllowedip.isNone then 1 else 0

/-- Only used on the actual split branch, where prefix and nest reservations fit. -/
def mixedPeerRemaining (nodes : NodeId → AipNode) (p : Peer) (ctx : DumpCtx)
    (skb : NlSkb) (ids : List NodeId) : List NodeId :=
  let cost := if ctx.nextAllowedip.isNone then peerFixedSpace p else 40
  (weightedPrefix nodes (skb.room-cost-4) ids).2

/-- A fresh nonempty peer needs its nest but need not emit a node. A resumed
nonempty peer must emit its first node. Empty lists need only the actual prefix. -/
def mixedPeerHeadFits (nodes : NodeId → AipNode) (p : Peer) (ctx : DumpCtx)
    (skb : NlSkb) (ids : List NodeId) : Prop :=
  let cost := if ctx.nextAllowedip.isNone then peerFixedSpace p else 40
  match ids with
  | [] => cost ≤ skb.room
  | first :: _ => cost + 4 ≤ skb.room ∧
      (ctx.nextAllowedip.isNone = true ∨ dumpNodeSpace (nodes first) ≤ skb.room-cost-4)

/-- Literal complete/split/cancel control of the native peer forIn. The old
held cursor remains in ctx; only nextCursor changes after a complete peer. -/
def mixedPeerScan (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode) :
    List MixedPeerRow → DumpCtx → Option PeerId → NlSkb → Array PeerDumpAttrs → MixedPeerScan
  | [], ctx, cursor, skb, prior => ⟨(ctx,cursor,skb,true,prior),[]⟩
  | (pid,ids) :: rows, ctx, cursor, skb, prior =>
    let result := weightedPeerResult d nodes (peers pid) ctx skb ids
    match result.2.2 with
    | .complete attrs => mixedPeerScan d peers nodes rows result.2.1 (some pid) result.1 (prior.push attrs)
    | .split attrs => ⟨(result.2.1,cursor,result.1,false,prior.push attrs),
        (pid,mixedPeerRemaining nodes (peers pid) ctx skb ids)::rows⟩
    | .cancelled => ⟨(result.2.1,cursor,result.1,false,prior),(pid,ids)::rows⟩


end Leanux.Proofs.WG.Config
