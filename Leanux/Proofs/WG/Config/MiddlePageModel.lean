import Leanux.Proofs.WG.Config.TwoPageCallbackModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- Extensional held-reference invariant over the actual current Device.
Raw TreeMap representation is retained; only peer lookups are compared. -/
def CursorHeld (base current : Device) (cursor : Option PeerId) : Prop :=
  {current with peers := base.peers} = base ∧
  ∀ id, current.peers[id]? = (base.peers[id]?).map (fun p =>
    if cursor = some id then {p with refcount := p.refcount+1} else p)

/-- The actual ordered cursor handoff, including the two TreeMap updates. -/
def cursorHandoff (d : Device) (old next : Option PeerId) : Device :=
  cursorReleased (cursorAcquired d next) old

/-- Exact maximal completed prefix with an already-held previous cursor. -/
theorem fixedPeersRun_resumed_split (peers : PeerId → Peer) (front : List PeerId)
    (next bad : PeerId) (tail : List PeerId) (ctx : DumpCtx) (old : Option PeerId) (skb : NlSkb)
    (fresh : ctx.nextAllowedip = none) (sequence : ctx.allowedipsSeq = 0)
    (fits : multiPeerSpace peers (front ++ [next]) ≤ skb.room)
    (short : skb.room-multiPeerSpace peers (front ++ [next]) < peerFixedSpace (peers bad)) :
    fixedPeersRun peers ((front ++ [next]) ++ bad :: tail) ctx old skb #[] =
      (ctx,some next,{skb with room := skb.room-multiPeerSpace peers (front ++ [next])},false,
        (multiPeerParts peers (front ++ [next])).toArray) := by
  rw [TwoPage.fixedPeersRun_prefix peers (front ++ [next]) (bad::tail) ctx fresh sequence old skb #[] fits]
  have notFit : ¬peerFixedSpace (peers bad) ≤ skb.room-multiPeerSpace peers (front ++ [next]) := by omega
  simp [fixedPeersRun,notFit]

end Leanux.Proofs.WG.Config
