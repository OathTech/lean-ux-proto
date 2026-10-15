import Leanux.Proofs.WG.AllowedIps.RoutingRetains
import Leanux.Proofs.WG.Queues.RxTxFrames

/-! Concrete routing frames for the original staged-send helpers. Packet,
key and queue effects remain unrestricted; peer release may delete a resident.
The existing source factors and matcher environment are shared with RX frames. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes
open Leanux.Proofs.WG.Queues Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem RetainsRoutingCall.wp (h : RetainsRoutingCall a) (s : Option RoutingState) :
    ⦃fun w => ⌜RetainsRouting s (routingView w)⌝⦄ a
    ⦃⇓? _ w => ⌜RetainsRouting s (routingView w)⌝⦄ :=
  ProjectedAction.wp h (RetainsRouting s) (fun _ _ hr hs => hs.trans hr)

theorem requireNotPending_routing (pid : PeerId) (why : String) :
    SameView routingView (requireNotPending pid why) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s) pid
  mvcgen [requireNotPending, hg, unsupported]

theorem getPeer_routing (pid : PeerId) : SameView routingView (getPeer pid) := by
  apply SameView.of_wp
  intro s
  mvcgen [getPeer, getDev, getK, invariant]

theorem getKeypair_routing (id : KeypairId) : SameView routingView (getKeypair id) := by
  apply SameView.of_wp
  intro s
  mvcgen [getKeypair, getDev, getK, invariant]

theorem ownerDeref_routing (owner : IndexOwner) : SameView routingView owner.peerDeref :=
  routing_kernel _ (indexOwner_peerDeref_sameKernel owner)

theorem ownerWord_routing (owner : IndexOwner) : SameView routingView owner.peerWord :=
  routing_kernel _ (indexOwner_peerWord_sameKernel owner)

theorem setKeypair_routing (id : KeypairId) (k : Keypair) : SameView routingView (setKeypair id k) :=
  modifyDev_routing _ (fun _ => rfl)

theorem getTxSkb_routing (id : SkbId) : SameView routingView (getTxSkb id) := by
  apply SameView.of_wp
  intro s
  mvcgen [getTxSkb, getDev, getK, invariant]

theorem setTxSkb_routing (id : SkbId) (f : DataPacket → DataPacket) :
    SameView routingView (setTxSkb id f) := by
  apply SameView.of_wp
  intro s
  have hg := (getTxSkb_routing id).wp (fun t => t = s)
  have hm := fun p => (modifyDev_routing (fun d => {d with txSkbs := d.txSkbs.insert id (f p)})
    (fun _ => rfl)).wp (fun t => t = s)
  mvcgen [setTxSkb, hg, hm]

theorem newTxSkb_routing (p : DataPacket) : SameView routingView (newTxSkb p) := by
  apply SameView.of_wp
  intro s
  mvcgen [newTxSkb, getDev, getK, modifyDev, modifyK, invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [routingView, routingState]

theorem freeTxSkb_routing (id : SkbId) : SameView routingView (freeTxSkb id) := by
  apply SameView.of_wp
  intro s
  have hg := (getTxSkb_routing id).wp (fun t => t = s)
  have hm := (modifyDev_routing (fun d => {d with txSkbs := d.txSkbs.erase id}) (fun _ => rfl)).wp (fun t => t = s)
  mvcgen [freeTxSkb, hg, hm]

theorem peerGet_routing (pid : PeerId) : SameView routingView (peerGet pid) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have hn := (requireNotPending_routing pid "taking a reference").wp (fun t => t = s)
  mvcgen [peerGet, requireNotPending, hg, hs, refcountInc, branch, branchCmp, unsupported]
  all_goals simp_all

theorem keypairGet_routing (kp : Option KeypairId) : SameView routingView (keypairGet kp) := by
  apply SameView.of_wp
  intro s
  have hg := fun id => (getKeypair_routing id).wp (fun t => t = s)
  have hs := fun id k => (setKeypair_routing id k).wp (fun t => t = s)
  mvcgen [keypairGet, hg, hs, refcountIncNotZero, branch, branchCmp, unsupported]

theorem keypairPut_routing (kp : Option KeypairId) (now : Bool) : SameView routingView (keypairPut kp now) := by
  apply SameView.of_wp
  intro s
  simp only [keypairPut, indexRemove_eq, indexUnhash]
  have hd := fun o k => sameKernel_wp _ (indexOwner_peerDeref_sameKernel o) (fun v => v = k)
  mvcgen [hd,getKeypair, getDev, getK, setKeypair, modifyDev, modifyK,
    branch, branchCmp, refcountDecAndTest, unsupported, invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [routingView, routingState]
  all_goals subst_vars
  all_goals simp_all [routingView, routingState]

theorem sendQueuedHandshakeInitiation_routing (pid : PeerId) (retry : Bool) :
    RetainsRoutingCall (sendQueuedHandshakeInitiation pid retry) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hg := routing_getPeer P pid
  have hs := fun p => routing_setPeer P pid p
  have hn := (requireNotPending_routing pid "queueing a handshake").wp P
  have hc := fun date => (routing_kernel _ (branchExpired_sameKernel .queuedNotExpired date REKEY_TIMEOUT (!·))).wp P
  have hget := (peerGet_routing pid).wp P
  have hput := (peerPut_retainsRouting (some pid)).wp s
  have hrec := (routing_kernel _ (recordQueued_sameKernel .sendWorker pid)).wp P
  have hqueue := (modifyDev_routing (fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})
    (fun _ => rfl)).wp P
  mvcgen [sendQueuedHandshakeInitiation, hg, hs, hn, hc, hget, hput, hrec, hqueue, branch]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold routingView at *; simp_all [routingState])
  all_goals try assumption
  all_goals subst s
  all_goals try exact RetainsRouting.refl _

theorem txDevice_routing (u : TxDeviceUpdate) : SameView routingView (modifyDev u.apply) :=
  modifyDev_routing _ (fun d => by cases u <;> rfl)

theorem cpumaskChooseOnline_routing (pid : PeerId) : SameView routingView (cpumaskChooseOnline pid) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  mvcgen [cpumaskChooseOnline, hg, hs, branch]
  all_goals try exact ((⇓? _ w => ⌜routingView w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try (unfold routingView at *; simp_all [routingState, Option.bind_map, Function.comp_def])
  all_goals trivial

theorem enqueuePerDeviceAndPeer_routing (pid : PeerId) (item : List SkbId) :
    SameView routingView (enqueuePerDeviceAndPeer pid item) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have hp := fun id f => (setTxSkb_routing id f).wp (fun t => t = s)
  have hc := fun last => (routing_kernel _ (cpumaskNextOnlineFrom_sameKernel last)).wp (fun t => t = s)
  have hw := (routing_kernel _ (queueDeviceWork_sameKernel .encryptWorker)).wp (fun t => t = s)
  have hd := fun u => (txDevice_routing u).wp (fun t => t = s)
  have hcpu := fun cpu => hd (.cpu cpu)
  have hring := hd (.ring item)
  mvcgen [enqueuePerDeviceAndPeer, hg, hs, hp, hc, hw, hcpu, hring, getDev, getK, modifyDev, modifyK, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold routingView at *; simp_all [routingState, Option.bind_map, Function.comp_def]
  all_goals assumption

theorem enqueuePerPeerTx_routing (item : List SkbId) (state : PacketState) :
    RetainsRoutingCall (enqueuePerPeerTx item state) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have htx := fun id => (getTxSkb_routing id).wp P
  have hk := fun id => (getKeypair_routing id).wp P
  have hg := fun pid => (getPeer_routing pid).wp P
  have hget := fun pid => (peerGet_routing pid).wp P
  have hput := fun pid => (peerPut_retainsRouting pid).wp s
  have hset := fun id f => (setTxSkb_routing id f).wp P
  have hcpu := fun pid => (cpumaskChooseOnline_routing pid).wp P
  have hpeek := fun pid => (routing_kernel _ (peekQueuedUnit_sameKernel .txWorker pid)).wp P
  have hrec := fun pid => (routing_kernel _ (recordQueued_sameKernel .txWorker pid)).wp P
  have hdev := fun pid => (txDevice_routing (.work pid)).wp P
  have hw := fun o => (ownerDeref_routing o).wp P
  mvcgen [hw, enqueuePerPeerTx, htx, hk, hg, hget, hput, hset, hcpu, hpeek, hrec, hdev,
    getDev, getK, modifyDev, modifyK, branch, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold routingView at *; simp_all [routingState, Option.bind_map, Function.comp_def])
  all_goals try assumption
  all_goals subst s
  all_goals try exact RetainsRouting.refl _

theorem createData_routing (pid : PeerId) (item : List SkbId) : RetainsRoutingCall (createData pid item) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hg := (getPeer_routing pid).wp P
  have ht := fun id => (getTxSkb_routing id).wp P
  have hd := (enqueuePerDeviceAndPeer_routing pid item).wp P
  have hp := (enqueuePerPeerTx_routing item .dead).wp s
  have hk := fun id => (keypairPut_routing id false).wp P
  have hr := (peerPut_retainsRouting (some pid)).wp s
  have hf := fun id => (freeTxSkb_routing id).wp P
  mvcgen [createData, hg, ht, hd, hp, hk, hr, hf, branch, invariant]
  all_goals try exact ((⇓? _ w => ⌜P (routingView w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold routingView at *; simp_all [routingState, Option.bind_map, Function.comp_def])
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | trivial

theorem stagedOutNokey_routing (pid : PeerId) (packets : List Packet)
    (keypair : Option KeypairId) (invalid : Bool) :
    RetainsRoutingCall (stagedOutNokey pid packets keypair invalid) := by
  cases invalid <;> cases keypair <;> apply ProjectedAction.of_wp <;> intro s
  all_goals
    let P := RetainsRouting s
    have hg := routing_getPeer P pid
    have hs := fun p => routing_setPeer P pid p
    have hk := fun id => (getKeypair_routing id).wp P
    have hset := fun id k => (setKeypair_routing id k).wp P
    have hp := fun kp => (keypairPut_routing kp false).wp P
    have hq := (sendQueuedHandshakeInitiation_routing pid false).wp s
    have hl (α β : Type) := list_view_spec routingView (α := α) (β := β) P
    simp only [stagedOutNokey, getPeer_twice, Bool.false_eq_true, ↓reduceIte]
    mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
      hg, hs, hk, hset, hp, hq, branch, invariant]
  all_goals try exact ((⇓? _ w => ⌜RetainsRouting s (routingView w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try (unfold routingView at *; simp_all [routingState, Option.bind_map, Function.comp_def])
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | trivial

theorem newTxSkbs_routing (packets : List DataPacket) : SameView routingView (packets.mapM newTxSkb) := by
  induction packets with
  | nil => exact SameView.pure _ _
  | cons p ps ih =>
    simp only [List.mapM_cons]
    exact SameView.bind (newTxSkb_routing p) (fun _ => SameView.bind ih (fun _ => SameView.pure _ _))

theorem sendStagedPackets_routing (pid : PeerId) : RetainsRoutingCall (sendStagedPackets pid) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hg := routing_getPeer P pid
  have hs := fun p => routing_setPeer P pid p
  have hk := fun id => (getKeypair_routing id).wp P
  have hset := fun id k => (setKeypair_routing id k).wp P
  have hget := fun kp => (keypairGet_routing kp).wp P
  have hp := fun pid => (peerGet_routing pid).wp P
  have hout := fun packets kp invalid => (stagedOutNokey_routing pid packets kp invalid).wp s
  have hput := fun kp => (keypairPut_routing kp false).wp P
  have hqueue := (sendQueuedHandshakeInitiation_routing pid false).wp s
  have ht := fun date => (routing_kernel _ (branchExpired_sameKernel .stagedBirthdateExpired date REJECT_AFTER_TIME)).wp P
  have he := fun pkt => (routing_kernel _ (ipTunnelEcnEncap_sameKernel pkt)).wp P
  have hn := fun packets => (newTxSkbs_routing packets).wp P
  have hc := fun item => (createData_routing pid item).wp s
  have hl (α β : Type) := list_view_spec routingView (α := α) (β := β) P
  simp only [sendStagedPackets, getPeer_twice]
  have hw := fun o => (routing_kernel _ (indexOwner_peerDeref_sameKernel o)).wp P
  mvcgen [hw,-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl, hg, hs, hk, hset, hget, hp, hout, hput, hqueue, ht, he, hn, hc, branch, branchCmp, invariant]
  all_goals try exact ((⇓? _ w => ⌜P (routingView w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold routingView at *; simp_all [routingState, Option.bind_map, Function.comp_def])
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | trivial


theorem sendKeepalive_routing (pid : PeerId) : RetainsRoutingCall (sendKeepalive pid) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hg := routing_getPeer P pid
  have hs := fun p => routing_setPeer P pid p
  have ha (p : Peer) := sameKernel_wp (hiddenAlloc .keepaliveSkb) (hiddenAlloc_sameKernel .keepaliveSkb)
    (fun k => P (k.wg.map routingState) ∧
      (k.wg.bind fun d => (d.peers[pid]?).map (·.allowedipsList)) = some p.allowedipsList)
  have ht := (sendStagedPackets_routing pid).wp s
  mvcgen [sendKeepalive, hg, hs, ha, ht, getDev, getK, branch, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold routingView at *; simp_all [routingState])
  all_goals try assumption
  all_goals try assumption
  all_goals subst s
  all_goals try exact RetainsRouting.refl _

end Leanux.Proofs.WG.AllowedIps
