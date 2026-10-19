import Leanux.Proofs.WG.RetirementSecurity.TxWorkNapi

/-! Actual allowed-IP lookup and nullable peer acquisition retain suspended
actors. The original finite trie traversal and both refusal branches remain. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem aip_lift {action : AipM α} (frame : Keeps action) : Keeps (liftAip action) := by
  unfold liftAip
  apply bind device
  intro d
  apply bind (ambient (frame {trie:=d.peerAllowedips,nodes:=d.nodes,nextNode:=d.nextNode}))
  rintro ⟨value,table⟩
  exact bind (modify_device _) (fun _=>pure value)

theorem aip_node (id : NodeId) : Keeps (getNode id) := by
  suspension_source [getNode] using [invariant]

theorem aip_find (root : Option NodeId) (bits key : Nat) : Keeps (findNode root bits key) := by
  suspension_source [findNode,prefixMatches,commonBits,choose,AipNode.bitAt] using [aip_node,branch,invariant]

theorem aip_node_call (id : NodeId) : Keeps (monadLift (getNode id) : WG.M AipNode) := aip_lift (aip_node id)

theorem aip_find_call (root : Option NodeId) (bits key : Nat) :
    Keeps (monadLift (findNode root bits key) : WG.M (Option NodeId)) := aip_lift (aip_find root bits key)

theorem endian (bits : Nat) : Keeps (swapEndian bits) := by
  suspension_source [swapEndian] using [branch]

theorem peer_get_maybe (pid : Option PeerId) : Keeps (peerGetMaybeZero pid) := by
  suspension_source [peerGetMaybeZero,requireNotPending,refcountIncNotZero]
    using [branch,compare,invariant,unsupported,peer,set_peer]

theorem allowed_lookup (root : Option NodeId) (bits key : Nat) : Keeps (lookup root bits key) := by
  suspension_source [lookup] using [endian,aip_find_call,aip_node_call,peer_get_maybe,branch,invariant,unsupported]

theorem lookup_dst (family addr : Nat) : Keeps (lookupDst family addr) := by
  suspension_source [lookupDst] using [device,branch,allowed_lookup]

theorem lookup_src (protocol : Nat) (bytes : List UInt8) : Keeps (lookupSrc protocol bytes) := by
  suspension_source [lookupSrc] using [device,branch,allowed_lookup]

theorem lookup_repay (protocol : Nat) (bytes : List UInt8) : Keeps (RxBorrow.source protocol bytes) := by
  unfold RxBorrow.source RxBorrow.repayLookup
  simp only [monadLift_self]
  suspension_source [] using [lookup_src,peer_put]

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension
