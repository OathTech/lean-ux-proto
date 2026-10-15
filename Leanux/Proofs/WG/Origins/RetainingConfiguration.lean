import Leanux.Proofs.WG.Origins.RetainingLifecycle
import Leanux.Proofs.Framing.WGAllowedIpsInsert
import Leanux.Proofs.WG.Configuration.AllowedIpSource
import Leanux.Proofs.WG.Configuration.DeviceSource

/-! Original configuration preserves receiving material on every normal return,
including negative errno after partial updates. Erasure and invalidation are
permitted. This is not peer-identity preservation or a returned-World claim on Stop. -/
namespace Leanux.Proofs.WG.Origins.Retaining
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.Configuration Leanux.Proofs.WG.Queues Leanux.Proofs.WG.Lifetimes Std.Do
set_option pp.structureInstances false

theorem nodeAllocation_material (ha : SameNodeAllocation a) : SameView view a := by
  apply ha.of_factor (fun k : Kernel => k.wg.map materialState) view
  intro w
  simp [view,nodeAllocationView,nodeAllocationKernel,nodeAllocationDevice,nodeDevice,
    materialState,Option.map_map,Function.comp_def]

theorem listAddTail_material (pid : PeerId) (id : NodeId) : SameView view (listAddTail pid id) := by
  apply SameView.of_wp
  intro s
  have hg := material_getPeer (fun t=>t=s) pid
  have hs := material_setPeer (fun t=>t=s) pid
  mvcgen [listAddTail,hg,hs]

theorem add_material (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    SameView view (add root bits key cidr peer) := by
  apply SameView.of_wp
  intro s
  have hg := fun id => (kernel (Framing.getNode_sameKernel id)).wp (fun t=>t=s)
  have hs := fun id n => (node_material (setNode_sameNodeKernel id n)).wp (fun t=>t=s)
  have hr := fun slot => (kernel (slotGet_sameKernel slot)).wp (fun t=>t=s)
  have ha := fun site n => (nodeAllocation_material (allocNode_sameNodeAllocation site n)).wp (fun t=>t=s)
  have hl := fun pid id => (listAddTail_material pid id).wp (fun t=>t=s)
  have hd := fun id => (listDel_material id).wp (fun t=>t=s)
  have hf := fun id => (node_material (freeNode_sameNodeKernel id)).wp (fun t=>t=s)
  have hp := fun tr k c b => (kernel (nodePlacement_sameKernel tr k c b)).wp (fun t=>t=s)
  have hc := fun slot id => (node_material (connectNode_sameNodeKernel slot id)).wp (fun t=>t=s)
  have hcc := fun p n => (node_material (chooseAndConnectNode_sameNodeKernel p n)).wp (fun t=>t=s)
  have hb := fun n i => (kernel (aipBitAt_sameKernel n i)).wp (fun t=>t=s)
  have hchoose := fun n k => (kernel (choose_sameKernel n k)).wp (fun t=>t=s)
  have hcommon := fun n k b => (kernel (commonBits_sameKernel n k b)).wp (fun t=>t=s)
  mvcgen [add,hg,hs,hr,ha,hl,hd,hf,hp,hc,hcc,hb,hchoose,hcommon,branch,branchCmp,invariant]

theorem insert_material (family addr cidr : Nat) (pid : PeerId) : SameView view (insert family addr cidr pid) := by
  apply SameView.of_wp
  intro s
  have hm := (modifyDev_material (fun d=>{d with peerAllowedips:={d.peerAllowedips with seq:=d.peerAllowedips.seq+1}}) (fun _=>rfl)).wp (fun t=>t=s)
  have ha := fun root bits => (add_material root bits addr cidr (some pid)).wp (fun t=>t=s)
  mvcgen [WG.insert,hm,ha]

theorem setAllowedip_material (pid : PeerId) (ip : AllowedIpAttrs) : SameView view (setAllowedip pid ip) := by
  apply SameView.of_wp
  intro s
  have hi := fun family addr cidr => (insert_material family addr cidr pid).wp (fun t=>t=s)
  mvcgen [setAllowedip,hi,WG.andM,WG.orM,branch]

theorem precomputeStaticStatic_material (pid : PeerId) : SameView view (precomputeStaticStatic pid) := by
  apply SameView.of_wp
  intro s
  have hg := material_getPeer (fun t=>t=s) pid
  have hs := material_setPeer (fun t=>t=s) pid
  mvcgen [precomputeStaticStatic,requireNotPending,hg,hs,getDev,getK,branch,invariant]

theorem handshakeInit_material (pid : PeerId) (psk : Option Key) : SameView view (handshakeInit pid psk) := by
  apply SameView.of_wp
  intro s
  have hg := material_getPeer (fun t=>t=s) pid
  have hs := material_setPeer (fun t=>t=s) pid
  have hp := (precomputeStaticStatic_material pid).wp (fun t=>t=s)
  mvcgen [handshakeInit,IndexOwner.setPeerWord,hg,hs,hp,branch]

theorem peerCreate_material (key : Key) (psk : Option Key) : SameView view (peerCreate key psk) := by
  apply SameView.of_wp
  intro s
  have hs := material_setPeer (fun t=>t=s)
  have hh := fun pid => (handshakeInit_material pid psk).wp (fun t=>t=s)
  have hd := fun pid => (dstCacheReset_material pid).wp (fun t=>t=s)
  have hr := fun pid => (resetLastSentHandshake_material pid).wp (fun t=>t=s)
  have ha := (kernel (hiddenAlloc_sameKernel .kmemCacheZallocPeer)).wp (fun t=>t=s)
  mvcgen [peerCreate,hs,hh,hd,hr,ha,getDev,getK,modifyDev,modifyK,branch,branchCmp,invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [view,Option.map_map,Function.comp_def]

theorem peerTailFinish_material (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    RetainsCall (peerTailFinishSource a peer pid ret) := by
  apply ProjectedAction.of_wp
  intro s
  have hg := material_getPeer (RetainsView s) pid
  have hs := material_setPeer (RetainsView s) pid
  have hp := (peerPut_material peer).wp (RetainsView s)
  have hk := (sendKeepalive_material pid).wp s
  have ht := (sendStagedPackets_material pid).wp s
  mvcgen [peerTailFinishSource,hg,hs,hp,hk,ht,WG.andM,getDev,getK,branch,invariant]
  all_goals try exact (fun _ h=>h)
  all_goals subst s
  all_goals exact RetainsView.refl _

theorem peerConfigTail_material (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    RetainsCall (peerConfigTailSource a peer pid) := by
  rw [peerConfigTailSource_factor]
  apply ProjectedAction.of_wp
  intro s
  have hp := (peerPut_material peer).wp (RetainsView s)
  have hi := fun ip => (setAllowedip_material pid ip).wp (RetainsView s)
  have hn := fun ret => (peerTailFinish_material a peer pid ret).wp s
  have hl (α β : Type) := list_view_spec view (α:=α) (β:=β) (RetainsView s)
  mvcgen [-Std.Do.Spec.forIn_list,-Std.Do.Spec.forIn'_list,hl,peerAllowedIpsSource,hp,hi,hn,branch]
  all_goals try exact ((⇓? _ w=>⌜RetainsView s (view w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try assumption
  all_goals try exact id
  all_goals subst s
  all_goals exact RetainsView.refl _

theorem peerConfigUpdate_material (a : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    RetainsCall (peerConfigUpdateSource a peer flags psk pid) := by
  apply ProjectedAction.of_wp
  intro s
  have hg := material_getPeer (RetainsView s) pid
  have hs := material_setPeer (RetainsView s) pid
  have hp := (peerPut_material peer).wp (RetainsView s)
  have hr := (peerRemove_material peer).wp s
  have he := fun e => (setPeerEndpoint_material pid e).wp (RetainsView s)
  have ha := (removeByPeer_material pid).wp (RetainsView s)
  have ht := (peerConfigTail_material a peer pid).wp s
  mvcgen [peerConfigUpdateSource,hg,hs,hp,hr,he,ha,ht,WG.andM,branch,invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try assumption
  all_goals try exact id
  all_goals subst s
  all_goals exact RetainsView.refl _

theorem setPeerCmd_material (a : PeerAttrs) : RetainsCall (setPeerCmd a) := by
  rw [←setPeerCmd_source]
  apply ProjectedAction.of_wp
  intro s
  have hp := fun peer => (peerPut_material peer).wp (RetainsView s)
  have hl := fun key => (pubkeyLookup_material key).wp (RetainsView s)
  have hc := fun key psk => (peerCreate_material key psk).wp (RetainsView s)
  have hg := fun pid => (peerGet_material pid).wp (RetainsView s)
  have hu := fun peer flags psk pid => (peerConfigUpdate_material a peer flags psk pid).wp s
  mvcgen [setPeerCmdSource,hp,hl,hc,hg,hu,WG.andM,branch,getDev,getK,invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try assumption
  all_goals try exact id
  all_goals subst s
  all_goals exact RetainsView.refl _

theorem devicePeers_material (a : DeviceAttrs) : RetainsCall (devicePeersSource a) := by
  apply ProjectedAction.of_wp
  intro s
  have hp := fun p => (setPeerCmd_material p).wp s
  have hl (α β : Type) := list_view_spec view (α:=α) (β:=β) (RetainsView s)
  mvcgen [-Std.Do.Spec.forIn_list,-Std.Do.Spec.forIn'_list,hl,devicePeersSource,hp,branch]
  all_goals try exact ((⇓? _ w=>⌜RetainsView s (view w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try assumption
  all_goals try exact id
  all_goals subst s
  all_goals exact RetainsView.refl _

theorem deviceKey_material (a : DeviceAttrs) : RetainsCall (deviceKeySource a) := by
  apply ProjectedAction.of_wp
  intro s
  have hg := fun key => (kernel (Framing.generatePublic_sameKernel key)).wp (RetainsView s)
  have hl := fun key => (pubkeyLookup_material key).wp (RetainsView s)
  have hp := fun peer => (peerPut_material peer).wp (RetainsView s)
  have hr := fun peer => (peerRemove_material peer).wp s
  have hs := fun key => (configuration_material _ (setStaticIdentityPrivateKey_sameConfiguration key)).wp (RetainsView s)
  have hc := (configuration_material _ cookiePrecomputeDeviceKeys_sameConfiguration).wp (RetainsView s)
  have hpre := fun pid => (precomputeStaticStatic_material pid).wp (RetainsView s)
  have he := fun pid => (expireCurrentPeerKeypairs_material pid).wp s
  have ht := fun pid => (sendStagedPackets_material pid).wp s
  have hn := (devicePeers_material a).wp s
  have hlist (α β : Type) := list_view_spec view (α:=α) (β:=β) (RetainsView s)
  mvcgen [-Std.Do.Spec.forIn_list,-Std.Do.Spec.forIn'_list,hlist,deviceKeySource,hg,hl,hp,hr,hs,hc,hpre,he,ht,hn,WG.andM,getDev,getK,branch,invariant]
  all_goals try exact ((⇓? _ w=>⌜RetainsView s (view w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try assumption
  all_goals try exact id
  all_goals subst s
  all_goals exact RetainsView.refl _

theorem deviceUpdate_material (a : DeviceAttrs) (flags : UInt32) : RetainsCall (deviceUpdateSource a flags) := by
  apply ProjectedAction.of_wp
  intro s
  have hgen := (modifyDev_material (fun d=>{d with deviceUpdateGen:=d.deviceUpdateGen+1}) (fun _=>rfl)).wp (RetainsView s)
  have hmark := fun n => (modifyDev_material (fun d=>{d with fwmark:=n}) (fun _=>rfl)).wp (RetainsView s)
  have he := fun pid => (clearPeerEndpointSrc_material pid).wp (RetainsView s)
  have hp := fun port => (setPort_material port).wp (RetainsView s)
  have hr := peerRemoveAll_material.wp s
  have hn := (deviceKey_material a).wp s
  have hl (α β : Type) := list_view_spec view (α:=α) (β:=β) (RetainsView s)
  mvcgen [-Std.Do.Spec.forIn_list,-Std.Do.Spec.forIn'_list,hl,deviceUpdateSource,hgen,hmark,he,hp,hr,hn,getDev,getK,branch,invariant]
  all_goals try exact ((⇓? _ w=>⌜RetainsView s (view w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try assumption
  all_goals try exact id
  all_goals subst s
  all_goals exact RetainsView.refl _

theorem wgSetDevice_material (a : DeviceAttrs) : RetainsCall (wgSetDevice a) := by
  rw [←wgSetDevice_source]
  apply ProjectedAction.of_wp
  intro s
  have hl := (kernel (lookupInterface_sameKernel a.device)).wp (RetainsView s)
  have hu := fun flags => (deviceUpdate_material a flags).wp s
  mvcgen [wgSetDeviceSource,hl,hu,WG.orM,getDev,getK,branch,invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try assumption
  all_goals try exact id
  all_goals subst s
  all_goals exact RetainsView.refl _

end Leanux.Proofs.WG.Origins.Retaining
