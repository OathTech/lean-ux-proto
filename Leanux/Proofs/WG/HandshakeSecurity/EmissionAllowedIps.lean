import Leanux.Proofs.WG.TransmitSecurity.EmissionDumpFrames

/-! The allowed-IP mutation leaves preserve the actual pending datagram
buffer. Trie and peer-list updates are framed directly, without using the
WGStore projection, which does not contain sent datagrams. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.EmissionAllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open AuthenticatedEffects TransmitSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem trie_spec (P : List SentDatagram → Prop) {α : Type} (body : AipM α) :
    Preserves (fun w => P w.sent) (monadLift body : WG.M α) :=
  hoare_liftAip body _ (fun _ _ _ hi _ => hi)

theorem list_add (pid : PeerId) (id : NodeId) : SameView WGWorld.sent (listAddTail pid id) := by
  sent_frame [listAddTail] using [getPeer_sent_spec,setPeer_sent_spec]

theorem list_add_spec (P : List SentDatagram → Prop) (pid : PeerId) (id : NodeId) :
    Preserves (fun w => P w.sent) (listAddTail pid id) := (list_add pid id).wp P

theorem list_delete (id : NodeId) : SameView WGWorld.sent (listDel id) := by
  sent_frame [listDel] using [setPeer_sent_spec,EmissionDump.list_spec]

theorem list_delete_spec (P : List SentDatagram → Prop) (id : NodeId) :
    Preserves (fun w => P w.sent) (listDel id) := (list_delete id).wp P

theorem add_node (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    SameView WGWorld.sent (add root bits key cidr peer) := by
  sent_frame [add,choose,commonBits,AipNode.bitAt] using [list_add_spec,list_delete_spec]
  all_goals
    cookie_source_lift AipM
    apply hoare_liftAip
    intro w d store hi device
    exact hi

theorem add_node_spec (P : List SentDatagram → Prop) (root : Slot) (bits key cidr : Nat)
    (peer : Option PeerId) : Preserves (fun w => P w.sent) (add root bits key cidr peer) :=
  (add_node root bits key cidr peer).wp P

theorem insert_prefix (family addr cidr : Nat) (pid : PeerId) :
    SameView WGWorld.sent (insert family addr cidr pid) := by
  sent_frame [WG.insert] using [add_node_spec]

theorem insert_prefix_spec (P : List SentDatagram → Prop) (family addr cidr : Nat) (pid : PeerId) :
    Preserves (fun w => P w.sent) (insert family addr cidr pid) := (insert_prefix family addr cidr pid).wp P

theorem allowedip (pid : PeerId) (ip : AllowedIpAttrs) :
    SameView WGWorld.sent (setAllowedip pid ip) := by
  sent_frame [setAllowedip] using [insert_prefix_spec]

theorem remove_peer (pid : PeerId) : SameView WGWorld.sent (removeByPeer pid) := by
  sent_frame [removeByPeer,AipNode.bitAt] using [getPeer_sent_spec,list_delete_spec,EmissionDump.list_spec]
  all_goals
    cookie_source_lift AipM
    apply hoare_liftAip
    intro w d store hi device
    exact hi

theorem remove_peer_spec (P : List SentDatagram → Prop) (pid : PeerId) :
    Preserves (fun w => P w.sent) (removeByPeer pid) := (remove_peer pid).wp P

theorem root_lists (root : NodeId) : SameView WGWorld.sent (rootRemovePeerLists root) := by
  sent_frame [rootRemovePeerLists] using
    [getPeer_sent_spec,list_delete_spec,EmissionDump.list_spec,EmissionDump.range_spec]
  all_goals
    cookie_source_lift AipM
    apply hoare_liftAip
    intro w d store hi device
    exact hi

theorem root_lists_spec (P : List SentDatagram → Prop) (root : NodeId) :
    Preserves (fun w => P w.sent) (rootRemovePeerLists root) := (root_lists root).wp P

theorem free : SameView WGWorld.sent WG.free := by
  sent_frame [WG.free] using [root_lists_spec,EmissionDump.list_spec]
  all_goals
    cookie_source_lift AipM
    apply hoare_liftAip
    intro w d store hi device
    exact hi

end Leanux.Proofs.WG.HandshakeSecurity.EmissionAllowedIps
