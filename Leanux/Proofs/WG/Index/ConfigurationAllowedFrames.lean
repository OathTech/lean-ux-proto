import Leanux.Proofs.WG.Index.ConfigurationIndexFrames
import Leanux.Proofs.WG.Index.AllowedFrameSource
import Leanux.Proofs.WG.Noise.PendingAllowedInsertionFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ConfigurationIndex
open Leanux Leanux.WG Noise Queues Leanux.Proofs.Framing Lifetimes Std.Do
theorem aip_fields {α : Type} (a : AipM α) : SameView fields (liftAip a) := by
  intro initial
  apply hoare_liftAip
  intro w d store hi hd
  simpa only [fields,deviceFields,senderDeviceCell,hd,Option.map_some] using hi

theorem node_fields {α : Type} {action : WG.M α} (same : SameNode action) :
    SameView fields action := by
  apply same.of_factor (fun s : WGStoreView => s.dev.map deviceFields)
  intro w
  simp only [nodeView,nodeDevice,wgStoreView,fields,Option.map_map,Function.comp_def]
  rfl

def clearFields (s : WGStoreView × (PeerId → Option Peer)) :=
  s.1.dev.map fun d => (d.nextKeypairId,d.indexTable,d.ifindex,
    (fun kid : KeypairId=>d.keypairs[kid]?),fun pid : PeerId=>(s.2 pid).map senderPeerCell)

theorem clearFields_eq (w : WGWorld) : clearFields (AllowedIps.clearListView w)=fields w := by
  cases device:w.dev <;>
    simp only [clearFields,AllowedIps.clearListView,wgStoreView,fields,device,
      Option.map_none,Option.map_some,Option.bind_some,Option.map_map,Function.comp_def]
  rfl

theorem listDel_fields (id : NodeId) : SameView fields (listDel id) :=
  (AllowedIps.listDel_clearListView id).of_factor clearFields fields (fun w=>(clearFields_eq w).symm)

theorem listAddTail_fields (pid : PeerId) (id : NodeId) : SameView fields (listAddTail pid id) :=
  modifyPeer_fields pid (fun p=>{p with allowedipsList:=p.allowedipsList++[id]}) (fun _=>rfl)

theorem allowedSequence_fields : SameView fields
    (modifyDev fun d=>{d with peerAllowedips:={d.peerAllowedips with seq:=d.peerAllowedips.seq+1}}) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases run
  cases hd:w.dev <;> simp [fields,hd,deviceFields,senderDeviceCell]

theorem allowedContracts : Config.AllowedFrame.Contracts fields where
  aip := aip_fields
  deleteList := listDel_fields
  appendList := listAddTail_fields
  sequence := allowedSequence_fields
  removeNode := fun id=>node_fields (removeNodeBody_sameNode id)

theorem setAllowedip_fields (pid : PeerId) (ip : AllowedIpAttrs) :
    SameView fields (setAllowedip pid ip) :=
  Config.AllowedFrame.allowed allowedContracts pid ip

theorem removeByPeer_fields (pid : PeerId) : SameView fields (removeByPeer pid) :=
  Config.AllowedFrame.remove allowedContracts pid

end Leanux.Proofs.WG.Index.ConfigurationIndex
