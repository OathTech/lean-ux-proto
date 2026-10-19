import Leanux.Proofs.WG.Config.PeerScalarRetentionClaims
import Leanux.Proofs.WG.Index.AllowedFrameSource
import Leanux.Proofs.WG.Index.ConfigurationAllowedFrames
import Leanux.Proofs.WG.Config.ScalarFinishModel

/-! Scalar projections of existing allowed-IP source contracts. The same original insertion/removal walkers are instantiated once; the complete peer cell excludes only fields these operations modify. -/

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.ScalarAllowed
open Leanux Leanux.WG Noise Std.Do
open Queues Queues.RxCredits Leanux.Proofs.Framing Lifetimes
open PeerScalarRetention ScalarFinish

theorem aip_frame {α : Type} (action : AipM α) : SameView view (liftAip action) := by
  intro initial
  apply hoare_liftAip
  intro g d store pre hd
  rw [←pre]
  simp only [view,hd]
  rfl

theorem node_frame {α : Type} {action : WG.M α} (same : SameNode action) :
    SameView view action := by
  apply same.of_factor (fun s : WGStoreView => peerValues s.dev)
  intro g
  cases hd:g.dev <;>
    simp only [view,nodeView,wgStoreView,hd,Option.map_none,Option.map_some] <;> rfl

def clearedValues (s : WGStoreView × (PeerId → Option Peer)) : Map :=
  fun pid=>(s.2 pid).map cell

theorem clear_values (g : WGWorld) :
    clearedValues (AllowedIps.clearListView g)=view g := by
  funext pid
  cases hd:g.dev with
  | none =>
    simp only [clearedValues,AllowedIps.clearListView,view,peerValues,hd,Option.bind_none,
      Option.map_none]
  | some d =>
    simp only [clearedValues,AllowedIps.clearListView,view,peerValues,hd,Option.bind_some,
      Option.map_map,Function.comp_def]
    rfl

theorem delete_frame (id : NodeId) : SameView view (listDel id) :=
  (AllowedIps.listDel_clearListView id).of_factor clearedValues view
    (fun g=>(clear_values g).symm)

theorem append_frame (pid : PeerId) (id : NodeId) :
    SameView view (listAddTail pid id) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a result final b run
  unfold listAddTail at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,read,write⟩ := run
  obtain ⟨rfl,rfl,d,device,resident⟩ := getPeer_normal pid g u p a c read
  cases write
  funext other
  by_cases eq:other=pid
  · subst other
    simp only [view,peerValues,device,Option.bind_some,Std.TreeMap.getElem?_insert_self,
      resident,Option.map_some,cell]
  · simp [view,peerValues,device,Std.TreeMap.getElem?_insert,Ne.symm eq]

theorem sequence_frame : SameView view
    (modifyDev fun d=>{d with peerAllowedips:={d.peerAllowedips with seq:=d.peerAllowedips.seq+1}}) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a result final b run
  cases run
  cases hd:g.dev <;>
    simp only [view,hd,Option.map_none,Option.map_some] <;> rfl

theorem contracts : AllowedFrame.Contracts view where
  aip := aip_frame
  deleteList := delete_frame
  appendList := append_frame
  sequence := sequence_frame
  removeNode := fun id=>node_frame (removeNodeBody_sameNode id)

theorem allowed_frame (pid : PeerId) (ip : AllowedIpAttrs) : SameView view (setAllowedip pid ip) :=
  AllowedFrame.allowed contracts pid ip

theorem remove_frame (pid : PeerId) : SameView view (removeByPeer pid) :=
  AllowedFrame.remove contracts pid

end Leanux.Proofs.WG.Config.ScalarAllowed
