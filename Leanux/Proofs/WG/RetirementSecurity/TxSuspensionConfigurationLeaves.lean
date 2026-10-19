import Leanux.Proofs.WG.RetirementSecurity.TxWorkDeviceConfiguration

/-! Configuration's concrete trie and peer-allocation paths retain suspended
actors. Ambient allocation/clock records are handled at their native sites;
there is no generic frame for arbitrary Ambient code. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem aip_slot_get (slot : Slot) : Keeps (slotGet slot) := by
  suspension_source [slotGet,AipNode.bitAt] using [aip_node,invariant]

theorem aip_slot_get_call (slot : Slot) : Keeps (monadLift (slotGet slot) : WG.M (Option NodeId)) :=
  aip_lift (aip_slot_get slot)

theorem aip_alloc (site : AllocSite) (node : AipNode) : Keeps (allocNode site node) := by
  suspension_source [allocNode] using [allocation]

theorem aip_alloc_call (site : AllocSite) (node : AipNode) :
    Keeps (monadLift (allocNode site node) : WG.M (Option NodeId)) := aip_lift (aip_alloc site node)

theorem aip_connect (slot : Slot) (id : NodeId) : Keeps (connectNode slot id) := by
  suspension_source [connectNode] using [aip_node,aip_set_node,aip_slot]

theorem aip_connect_call (slot : Slot) (id : NodeId) :
    Keeps (monadLift (connectNode slot id) : WG.M Unit) := aip_lift (aip_connect slot id)

theorem aip_choose_connect (parent node : NodeId) : Keeps (chooseAndConnectNode parent node) := by
  suspension_source [chooseAndConnectNode,choose] using [aip_node,invariant,aip_connect]

theorem aip_choose_connect_call (parent node : NodeId) :
    Keeps (monadLift (chooseAndConnectNode parent node) : WG.M Unit) := aip_lift (aip_choose_connect parent node)

theorem aip_placement (root : Option NodeId) (key cidr bits : Nat) : Keeps (nodePlacement root key cidr bits) := by
  suspension_source [nodePlacement,prefixMatches,commonBits,choose,AipNode.bitAt] using
    [aip_node,branch,compare,invariant]

theorem aip_placement_call (root : Option NodeId) (key cidr bits : Nat) :
    Keeps (monadLift (nodePlacement root key cidr bits) : WG.M (Option NodeId × Bool)) :=
  aip_lift (aip_placement root key cidr bits)

theorem aip_list_add (pid : PeerId) (node : NodeId) : Keeps (listAddTail pid node) := by
  suspension_source [listAddTail] using [peer,set_peer]

theorem aip_add (root : Slot) (bits key cidr : Nat) (owner : Option PeerId) : Keeps (add root bits key cidr owner) := by
  suspension_source [add,choose,commonBits,AipNode.bitAt] using
    [branch,compare,invariant,aip_slot_get_call,aip_alloc_call,aip_list_add,aip_connect_call,
      aip_placement_call,aip_node_call,aip_set_node_call,aip_list_delete,aip_choose_connect_call,aip_free_node_call]

theorem aip_insert (family addr cidr : Nat) (pid : PeerId) : Keeps (WG.insert family addr cidr pid) := by
  suspension_source [WG.insert] using [modify_device,aip_add]

theorem aip_set (pid : PeerId) (ip : AllowedIpAttrs) : Keeps (setAllowedip pid ip) := by
  suspension_source [setAllowedip,WG.andM,WG.orM] using [branch,aip_insert,endian]

theorem precompute (pid : PeerId) : Keeps (precomputeStaticStatic pid) := by
  suspension_source [precomputeStaticStatic,requireNotPending] using [device,peer,set_peer,branch]

theorem handshake_init (pid : PeerId) (psk : Option Key) : Keeps (handshakeInit pid psk) := by
  suspension_source [handshakeInit] using [owner_set,branch,peer,set_peer,precompute]

theorem peer_create (key : Key) (psk : Option Key) : Keeps (peerCreate key psk) := by
  suspension_source [peerCreate] using
    [device,branch,compare,allocation,modify_device,set_peer,cache_reset,handshake_init,reset]

theorem set_port (port : Nat) : Keeps (setPort port) := by
  suspension_source [setPort] using [device,branch,modify_device,clear_endpoint,socket_init]

theorem expire_keys (pid : PeerId) : Keeps (expireCurrentPeerKeypairs pid) := by
  suspension_source [expireCurrentPeerKeypairs,requireNotPending] using
    [handshake_clear,reset,peer,key,set_key,branch,invariant]

theorem static_identity (key : Key) : Keeps (setStaticIdentityPrivateKey key) := by
  suspension_source [setStaticIdentityPrivateKey,requireNotPending] using [device,public_key,modify_device]

theorem cookie_precompute : Keeps cookiePrecomputeDeviceKeys := by
  suspension_source [cookiePrecomputeDeviceKeys] using [device,modify_device,branch]

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension
