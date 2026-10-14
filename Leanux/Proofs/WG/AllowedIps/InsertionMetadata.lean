import Leanux.Proofs.WG.AllowedIps.InsertionCases

/-! Exact peer-map effects of the existing insertion endpoints. Fresh allocation
only appends; exact replacement first filters every resident peer list. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux
set_option pp.structureInstances false

/-- The source's peer update, including the raw fresh/replacement distinction. -/
def insertionPeer (allocations id pid q : Nat) (p : WG.Peer) : WG.Peer :=
  let base := if allocations = 0 then unlist id p else p
  if q = pid then {base with allowedipsList := base.allowedipsList ++ [id]} else base

def InsertionPeers (d out : WG.Device) (allocations id pid : Nat) : Prop :=
  ∀ q : Nat, out.peers[q]? = (d.peers[q]?).map (insertionPeer allocations id pid q)

def InsertionFrame (d out : WG.Device) : Prop :=
  out = {d with
    nodes := out.nodes
    peers := out.peers
    peerAllowedips := out.peerAllowedips
    nextNode := out.nextNode}

theorem fresh_peer_map (d : WG.Device) (pid id allocations : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (ha : allocations ≠ 0) (q : Nat) :
    (d.peers.insert pid {p with allowedipsList := p.allowedipsList ++ [id]})[q]? =
      (d.peers[q]?).map (insertionPeer allocations id pid q) := by
  by_cases hq : q = pid
  · subst q
    simp [insertionPeer, hp, ha]
  · cases he : d.peers[q]? <;> simp [insertionPeer, ha, hq, Std.TreeMap.getElem?_insert, Ne.symm hq, he]

theorem emptyInstalled_peers (d : WG.Device) (v4 : Bool) (addr cidr pid : Nat)
    (p : WG.Peer) (hp : d.peers[pid]? = some p) :
    InsertionPeers d (emptyInstalled d v4 addr cidr pid p) 1 d.nextNode pid := by
  intro q
  exact fresh_peer_map d pid d.nextNode 1 p hp (by decide) q

theorem gapInstalledAt_peers (d : WG.Device) (v4 : Bool) (base : WG.Slot)
    (n : NodeData) (side : Nat) (sibling : Tree) (addr cidr pid : Nat)
    (p : WG.Peer) (hp : d.peers[pid]? = some p) :
    InsertionPeers d (gapInstalledAt d v4 base n side sibling addr cidr pid p) 1 d.nextNode pid := by
  intro q
  exact fresh_peer_map d pid d.nextNode 1 p hp (by decide) q

theorem exactInstalled_peers (d : WG.Device) (id : Nat) (old : WG.AipNode)
    (pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p) :
    InsertionPeers d (exactInstalled d id old pid p) 0 id pid := by
  intro q
  by_cases hq : q = pid
  · subst q
    simpa [insertionPeer, hp, unlist] using exactInstalled_peer d id old pid p
  · rw [exactInstalled_other_peer d id old pid p q (Ne.symm hq)]
    cases d.peers[q]? <;> simp [insertionPeer, hq]

theorem graftInstalled_peers (d : WG.Device) (v4 : Bool) (id : Nat) (old : WG.AipNode)
    (addr cidr pid allocations : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (ha : allocations ≠ 0) :
    InsertionPeers d (graftInstalled d v4 id old addr cidr pid p) allocations d.nextNode pid := by
  intro q
  unfold graftInstalled
  dsimp only
  split <;> exact fresh_peer_map d pid d.nextNode allocations p hp ha q

theorem graftChildInstalled_peers (d : WG.Device) (v4 : Bool) (parent : Nat) (pn : WG.AipNode)
    (id : Nat) (old : WG.AipNode) (addr cidr pid allocations : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (ha : allocations ≠ 0) :
    InsertionPeers d (graftChildInstalled d v4 parent pn id old addr cidr pid p) allocations d.nextNode pid := by
  intro q
  unfold graftChildInstalled
  dsimp only
  split <;> exact fresh_peer_map d pid d.nextNode allocations p hp ha q

theorem emptyInstalled_frame (d : WG.Device) (v4 : Bool) (addr cidr pid : Nat) (p : WG.Peer) :
    InsertionFrame d (emptyInstalled d v4 addr cidr pid p) := by
  cases v4 <;> rfl

theorem gapInstalledAt_frame (d : WG.Device) (v4 : Bool) (base : WG.Slot)
    (n : NodeData) (side : Nat) (sibling : Tree) (addr cidr pid : Nat) (p : WG.Peer) :
    InsertionFrame d (gapInstalledAt d v4 base n side sibling addr cidr pid p) := rfl

theorem exactInstalled_frame (d : WG.Device) (id : Nat) (old : WG.AipNode) (pid : Nat) (p : WG.Peer) :
    InsertionFrame d (exactInstalled d id old pid p) := rfl

theorem graftInstalled_frame (d : WG.Device) (v4 : Bool) (id : Nat) (old : WG.AipNode)
    (addr cidr pid : Nat) (p : WG.Peer) :
    InsertionFrame d (graftInstalled d v4 id old addr cidr pid p) := by
  unfold graftInstalled
  dsimp only
  split <;> cases v4 <;> simp only [InsertionFrame, graftOne, graftTwo, connectedRoot, rootWrite, connectedChild, graftListed, allocated]

theorem graftChildInstalled_frame (d : WG.Device) (v4 : Bool) (parent : Nat) (pn : WG.AipNode)
    (id : Nat) (old : WG.AipNode) (addr cidr pid : Nat) (p : WG.Peer) :
    InsertionFrame d (graftChildInstalled d v4 parent pn id old addr cidr pid p) := by
  unfold graftChildInstalled
  dsimp only
  split <;> simp only [InsertionFrame, graftOneChild, graftTwoChild, connectedChild, graftListed, allocated]

end Leanux.Proofs.WG.AllowedIps
