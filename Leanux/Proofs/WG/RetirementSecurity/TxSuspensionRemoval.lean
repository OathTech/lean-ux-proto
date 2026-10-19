import Leanux.Proofs.WG.RetirementSecurity.TxActorDeferred

/-! Allowed-IP cleanup and peer removal retain actual suspended activations.
The original drain selects only handshake send/clear workers; it cannot silently
consume an outstanding TX activation. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem aip_set_node (id : NodeId) (n : AipNode) : Keeps (setNode id n) := by
  suspension_source [setNode] using []

theorem aip_free_node (id : NodeId) : Keeps (freeNode id) := by
  suspension_source [freeNode] using [aip_node]

theorem aip_slot (slot : Slot) (id : Option NodeId) : Keeps (slotSet slot id) := by
  suspension_source [slotSet] using [aip_node,aip_set_node,invariant]

theorem aip_set_node_call (id : NodeId) (n : AipNode) :
    Keeps (monadLift (setNode id n) : WG.M Unit) := aip_lift (aip_set_node id n)

theorem aip_free_node_call (id : NodeId) :
    Keeps (monadLift (freeNode id) : WG.M Unit) := aip_lift (aip_free_node id)

theorem aip_slot_call (slot : Slot) (id : Option NodeId) :
    Keeps (monadLift (slotSet slot id) : WG.M Unit) := aip_lift (aip_slot slot id)

theorem aip_list_delete (id : NodeId) : Keeps (listDel id) := by
  suspension_source [listDel] using [device,set_peer]

theorem aip_remove (pid : PeerId) : Keeps (removeByPeer pid) := by
  suspension_source [removeByPeer,AipNode.bitAt] using
    [peer,modify_device,branch,invariant,aip_list_delete,aip_node_call,
      aip_set_node_call,aip_slot_call,aip_free_node_call]

theorem aip_subtree (id : NodeId) : Keeps (subtree id) := by
  suspension_source [subtree] using [aip_node,invariant]

theorem aip_subtree_call (id : NodeId) :
    Keeps (monadLift (subtree id) : WG.M (List NodeId)) := aip_lift (aip_subtree id)

theorem aip_root_remove (id : NodeId) : Keeps (rootRemovePeerLists id) := by
  suspension_source [rootRemovePeerLists] using
    [device,branch,invariant,aip_node_call,peer,aip_list_delete]

theorem aip_free : Keeps WG.free := by
  suspension_source [WG.free] using
    [device,modify_device,branch,aip_root_remove,aip_subtree_call,aip_free_node_call]

theorem drain_handshake (upTo : Option PeerId) : Keeps (drainHandshakeSendWq upTo) := by
  have peek (worker : Worker) : Keeps (peekUnit worker : WG.M (Option Nat)) :=
    ambient (TxActorFrames.peek_unit worker)
  have resolve (worker : Worker) (unit : Nat) (queue : List Nat) :
      Keeps (resolveUnit worker unit queue : WG.M PeerId) := ambient (TxActorFrames.resolve worker unit queue)
  have read : Keeps (getAmbient : WG.M Ambient) := by
    apply ambient
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w result v run
    cases run
    rfl
  suspension_source [drainHandshakeSendWq] using
    [device,peek,resolve,read,flushed_send,flushed_clear,invariant]

theorem timers_stop (pid : PeerId) : Keeps (timersStop pid) := by
  suspension_source [timersStop] using [delete,device,drain_handshake]

theorem remove_after_dead (pid : PeerId) : Keeps (peerRemoveAfterDead pid) := by
  suspension_source [peerRemoveAfterDead] using
    [branch,peer,unsupported,key_clear,timers_stop,device,drain_handshake,
      invariant,modify_device,peer_put]

theorem make_dead (pid : PeerId) : Keeps (peerMakeDead pid) := by
  suspension_source [peerMakeDead] using
    [branch,peer,set_peer,device,modify_device,aip_remove]

theorem peer_remove (pid : Option PeerId) : Keeps (peerRemove pid) := by
  suspension_source [peerRemove] using [branch,invariant,make_dead,remove_after_dead]

theorem peer_remove_all : Keeps peerRemoveAll := by
  suspension_source [peerRemoveAll] using [aip_free,device,branch,make_dead,remove_after_dead]

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension
