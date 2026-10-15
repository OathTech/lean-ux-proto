import Leanux.Proofs.WG.Origins.RetainingTraffic
import Leanux.Proofs.Framing.WGSocketLifecycle
import Leanux.Proofs.Framing.WGAllowedIps
import Leanux.Proofs.WG.Lifetimes.TimerCallbacks

/-! Actual clear, timer, removal and guarded device lifecycle contracts for
receiving material. Retention permits erasure and invalidation, and only speaks
about normal returns. Session installation is handled by the separate receipts. -/
namespace Leanux.Proofs.WG.Origins.Retaining
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.Lifetimes Leanux.Proofs.WG.Queues Std.Do
set_option pp.structureInstances false

theorem handshakeZero_material (pid : PeerId) : SameView view (handshakeZero pid) := handshakeZero_view pid

theorem keypairsClear_material (pid : PeerId) : RetainsCall (keypairsClear pid) := by
  apply ProjectedAction.of_wp
  intro s
  have hg := (getPeer_view pid).wp (RetainsView s)
  have hs := modifyPeer_spec (RetainsView s) pid
  have hk := fun kp => (keypairPut_material kp true).wp s
  mvcgen [keypairsClear,hg,hs,hk]
  all_goals subst s
  all_goals exact RetainsView.refl _

theorem handshakeClear_material (pid : PeerId) : SameView view (handshakeClear pid) :=
  (ownerDeref_material (.handshake pid)).bind (fun _ =>
    (indexRemove_material (.handshake pid)).bind (fun _ => handshakeZero_material pid))

theorem handshakeSendWorker_material (pid : PeerId) : RetainsCall (handshakeSendWorker pid) := by
  apply ProjectedAction.of_wp
  intro s
  have hi := (sendHandshakeInitiation_material pid).wp (RetainsView s)
  have hp := (peerPut_material (some pid)).wp (RetainsView s)
  mvcgen [handshakeSendWorker, hi, hp]
  all_goals subst s
  all_goals exact RetainsView.refl _

theorem queuedExpiredZeroKeyMaterial_material (pid : PeerId) : RetainsCall (queuedExpiredZeroKeyMaterial pid) := by
  apply ProjectedAction.of_wp
  intro s
  have hh := (handshakeClear_material pid).wp (RetainsView s)
  have hk := (keypairsClear_material pid).wp s
  have hp := (peerPut_material (some pid)).wp (RetainsView s)
  mvcgen [queuedExpiredZeroKeyMaterial, hh, hk, hp]
  all_goals subst s
  all_goals exact RetainsView.refl _
theorem runFlushedSendWork_material (pid : PeerId) : RetainsCall (runFlushedSendWork pid) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have hg := material_getPeer P pid
  have hs := fun p => material_setPeer P pid p
  have hm := (modifyDev_material (fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid}) (fun _ => rfl)).wp P
  have hh := fun site => (kernel (hidden_sameKernel site)).wp P
  have hw := (handshakeSendWorker_material pid).wp s
  mvcgen [runFlushedSendWork, hg, hs, hm, hh, hw, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all
  all_goals try exact id
  all_goals try trivial
  all_goals subst s
  all_goals exact RetainsView.refl _

theorem runFlushedClearWork_material (pid : PeerId) : RetainsCall (runFlushedClearWork pid) := by
  apply ProjectedAction.of_wp
  intro s
  have hm := (modifyDev_material (fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid}) (fun _ => rfl)).wp (RetainsView s)
  have hh := fun site => (kernel (hidden_sameKernel site)).wp (RetainsView s)
  have hw := (queuedExpiredZeroKeyMaterial_material pid).wp s
  mvcgen [runFlushedClearWork, hm, hh, hw]
  all_goals try exact id
  all_goals try trivial
  all_goals subst s
  all_goals exact RetainsView.refl _

theorem drainHandshakeSendWq_material (upTo : Option PeerId) : RetainsCall (drainHandshakeSendWq upTo) := by
  apply ProjectedAction.of_wp
  intro s
  have hs := fun pid => (runFlushedSendWork_material pid).wp s
  have hc := fun pid => (runFlushedClearWork_material pid).wp s
  have hp := fun worker => (kernel (Framing.peekUnit_sameKernel worker)).wp (RetainsView s)
  have hr := fun worker unit queue => (kernel (Framing.resolveUnit_sameKernel worker unit queue)).wp (RetainsView s)
  mvcgen [drainHandshakeSendWq, hs, hc, hp, hr, getDev, getK, invariant]
  all_goals try exact ((⇓? _ w => ⌜RetainsView s (view w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all
  all_goals try assumption
  all_goals try exact id
  all_goals try trivial
  all_goals subst s
  all_goals exact RetainsView.refl _

theorem timersStop_material (pid : PeerId) : RetainsCall (timersStop pid) := by
  apply ProjectedAction.of_wp
  intro s
  have hd := fun t => (delTimer_material pid t).wp (RetainsView s)
  have hw := (drainHandshakeSendWq_material (some pid)).wp s
  mvcgen [timersStop, hd, hw, getDev, getK, invariant]
  all_goals try exact ((⇓? _ w => ⌜RetainsView s (view w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try assumption
  all_goals try exact id
  all_goals try trivial
  all_goals subst s
  all_goals exact RetainsView.refl _

theorem peerRemoveAfterDead_material (pid : PeerId) : RetainsCall (peerRemoveAfterDead pid) := by
  apply ProjectedAction.of_wp
  intro s
  have hg := (getPeer_material pid).wp (RetainsView s)
  have hk := (keypairsClear_material pid).wp s
  have ht := (timersStop_material pid).wp s
  have hw := (drainHandshakeSendWq_material none).wp s
  have hm := (modifyDev_material (fun d => {d with numPeers := d.numPeers - 1}) (fun _ => rfl)).wp (RetainsView s)
  have hp := (peerPut_material (some pid)).wp (RetainsView s)
  mvcgen [peerRemoveAfterDead, hg, hk, ht, hw, hm, hp, getDev, getK, branch, unsupported, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try assumption
  all_goals try exact id
  all_goals try trivial
  all_goals subst s
  all_goals exact RetainsView.refl _
theorem resetLastSentHandshake_material (pid : PeerId) : SameView view (resetLastSentHandshake pid) := by
  apply SameView.of_wp
  intro s
  have hg := material_getPeer (fun t => t = s)
  have hs := material_setPeer (fun t => t = s)
  have ht := (kernel (hiddenClock64_sameKernel .resetLastSent)).wp (fun t => t = s)
  mvcgen [resetLastSentHandshake, hg, hs, ht]
  all_goals simp_all

theorem configuration_material (a : M α) (ha : SameConfiguration a) : SameView view a := by
  apply ha.of_factor (fun k : Kernel => k.wg.map materialState) view
  intro w
  simp [view, configurationView, configurationKernel, configurationDevice,
    materialState, Option.map_map, Function.comp_def]

theorem socketControl_material (a : M α) (ha : SameSocketKernel a) : SameView view a := by
  apply ha.of_factor (fun k : Kernel => k.wg.map materialState) view
  intro w
  simp [view, socketKernelView, socketKernel, socketDevice,
    materialState, Option.map_map, Function.comp_def]

theorem dstCacheResetNow_material (pid : PeerId) : SameView view (dstCacheResetNow pid) := by
  apply (dstCacheReset_material pid).bind
  intro _
  exact modifyPeer_material pid (fun p => {p with dstCache := {p.dstCache with slot := none}})

theorem clearPeerEndpointSrc_material (pid : PeerId) : SameView view (clearPeerEndpointSrc pid) := by
  apply SameView.of_wp
  intro s
  have hg := material_getPeer (fun t => t = s) pid
  have hs := fun p => material_setPeer (fun t => t = s) pid p
  have hr := (dstCacheResetNow_material pid).wp (fun t => t = s)
  mvcgen [clearPeerEndpointSrc, hg, hs, hr]
  all_goals simp_all

theorem setPort_material (port : Nat) : SameView view (setPort port) := by
  apply SameView.of_wp
  intro s
  have hc := fun pid => (clearPeerEndpointSrc_material pid).wp (fun t => t = s)
  have hs := (socketControl_material _ (socketInit_sameSocketKernel port)).wp (fun t => t = s)
  have hm := (modifyDev_material (fun d => {d with incomingPort := port}) (fun _ => rfl)).wp (fun t => t = s)
  have hl (α β : Type) := list_view_spec view (α := α) (β := β) (fun t => t = s)
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl, setPort, hc, hs, hm, getDev, getK, branch, invariant]

theorem expireCurrentPeerKeypairs_material (pid : PeerId) :
    RetainsCall (expireCurrentPeerKeypairs pid) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have hh := (handshakeClear_material pid).wp P
  have hr := (resetLastSentHandshake_material pid).wp P
  have hp := (getPeer_view pid).wp P
  have hg := fun kp => getKeypair_spec P kp
  have hs := fun kp => setKeypair_spec P (fun _ _ hr hi => hi.trans hr) kp
  mvcgen [expireCurrentPeerKeypairs,requireNotPending,hh,hr,hp,hg,hs,branch,invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [KeyLe,MaterialOrigin.material,WordLe]
  all_goals try subst s
  all_goals first | exact RetainsView.refl _ | assumption

theorem purgeStagedPackets_material (pid : PeerId) : SameView view (purgeStagedPackets pid) := by
  apply SameView.of_wp
  intro s
  have hg := material_getPeer (fun t => t = s) pid
  have hs := fun p => material_setPeer (fun t => t = s) pid p
  mvcgen [purgeStagedPackets, hg, hs, modifyDev, modifyK]
  all_goals dsimp +zetaDelta only at *
  all_goals try simp_all [view, materialState, Option.map_map, Option.bind_map, Function.comp_def]
  all_goals exact And.left (by assumption)

theorem wgStop_material : RetainsCall wgStop := by
  apply ProjectedAction.of_wp
  intro s
  have hn := fun pid => (requireNotPending_material pid "wg_stop while a handshake is queued").wp (RetainsView s)
  have hp := fun pid => (purgeStagedPackets_material pid).wp (RetainsView s)
  have ht := fun pid => (timersStop_material pid).wp s
  have hh := fun pid => (handshakeClear_material pid).wp (RetainsView s)
  have hk := fun pid => (keypairsClear_material pid).wp s
  have hr := fun pid => (resetLastSentHandshake_material pid).wp (RetainsView s)
  have hm := (modifyDev_material (fun d => {d with handshakeQueueLen := 0}) (fun _ => rfl)).wp (RetainsView s)
  have hs := (socketControl_material _ (socketReinit_sameSocketKernel none none)).wp (RetainsView s)
  mvcgen [wgStop, hn, hp, ht, hh, hk, hr, hm, hs, getDev, getK, branch, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜RetainsView s (view w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try assumption
  all_goals try exact id
  all_goals try trivial
  all_goals subst s
  all_goals exact RetainsView.refl _

theorem wgDown_material : RetainsCall wgDown := by
  apply ProjectedAction.of_wp
  intro s
  have hm := (modifyDev_material (fun d => {d with running := false}) (fun _ => rfl)).wp (RetainsView s)
  have hs := wgStop_material.wp s
  mvcgen [wgDown, hm, hs]
  all_goals subst s
  all_goals exact RetainsView.refl _

theorem expiredRetransmitHandshake_material (pid : PeerId) :
    RetainsCall (expiredRetransmitHandshake pid) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have hg := material_getPeer P pid
  have hs := fun p => material_setPeer P pid p
  have hd := (delTimer_material pid .sendKeepalive).wp P
  have hp := (purgeStagedPackets_material pid).wp P
  have hm := (modPeerTimer_material .timerJiffiesRetransmitZeroKey pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS).wp P
  have he := (clearPeerEndpointSrc_material pid).wp P
  have hq := (sendQueuedHandshakeInitiation_material pid true).wp s
  have hx (α : Type) := discard_view_spec view (α := α) P
  mvcgen [expiredRetransmitHandshake, hg, hs, hd, hp, hm, he, hq, hx, branch, branchCmp]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [view, materialState]
  all_goals try subst s
  all_goals first | exact RetainsView.refl _ | assumption

theorem expiredSendKeepalive_material (pid : PeerId) :
    RetainsCall (expiredSendKeepalive pid) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have hg := material_getPeer P pid
  have hs := fun p => material_setPeer P pid p
  have hk := (sendKeepalive_material pid).wp s
  have hm := (modPeerTimer_material .timerJiffiesExpiredKeepalive pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS).wp P
  have hx (α : Type) := discard_view_spec view (α := α) P
  mvcgen [expiredSendKeepalive, hg, hs, hk, hm, hx, branch]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [view, materialState]
  all_goals try subst s
  all_goals first | exact RetainsView.refl _ | assumption

theorem expiredNewHandshake_material (pid : PeerId) :
    RetainsCall (expiredNewHandshake pid) := by
  apply ProjectedAction.of_wp
  intro s
  have he := (clearPeerEndpointSrc_material pid).wp (RetainsView s)
  have hq := (sendQueuedHandshakeInitiation_material pid false).wp s
  mvcgen [expiredNewHandshake, he, hq]
  subst s
  exact RetainsView.refl _

theorem expiredZeroKeyMaterial_material (pid : PeerId) :
    RetainsCall (expiredZeroKeyMaterial pid) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have hg := (getPeer_material pid).wp P
  have hget := (peerGet_material pid).wp P
  have hput := (peerPut_material (some pid)).wp (RetainsView s)
  have hrec := (kernel (recordQueued_sameKernel .clearPeerWorker pid)).wp P
  have hm := (modifyDev_material (fun d => {d with clearWorkQueue := d.clearWorkQueue ++ [pid]}) (fun _ => rfl)).wp P
  mvcgen [expiredZeroKeyMaterial, hg, hget, hput, hrec, hm, getDev, getK, branch, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold view at *; simp_all)
  all_goals try subst s
  all_goals first | exact RetainsView.refl _ | assumption

theorem expiredSendPersistentKeepalive_material (pid : PeerId) :
    RetainsCall (expiredSendPersistentKeepalive pid) := by
  apply ProjectedAction.of_wp
  intro s
  have hg := (getPeer_material pid).wp (RetainsView s)
  have hk := (sendKeepalive_material pid).wp s
  mvcgen [expiredSendPersistentKeepalive, hg, hk, branch]
  all_goals subst s
  all_goals exact RetainsView.refl _

theorem timerCallback_material (pid : PeerId) (timer : PeerTimer) :
    RetainsCall (timerCallback pid timer) := by
  cases timer with
  | retransmitHandshake => exact expiredRetransmitHandshake_material pid
  | sendKeepalive => exact expiredSendKeepalive_material pid
  | newHandshake => exact expiredNewHandshake_material pid
  | zeroKeyMaterial => exact expiredZeroKeyMaterial_material pid
  | persistentKeepalive => exact expiredSendPersistentKeepalive_material pid

theorem wgOpen_material : RetainsCall wgOpen := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have hs := fun port => (socketControl_material _ (socketInit_sameSocketKernel port)).wp P
  have hsend := fun pid => (sendStagedPackets_material pid).wp s
  have hk := fun pid => (sendKeepalive_material pid).wp s
  have hg := fun pid => (getPeer_material pid).wp P
  have hl (α β : Type) := list_view_spec view (α := α) (β := β) P
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    wgOpen, hs, hsend, hk, hg, getDev, getK, branch, invariant]
  all_goals try exact ((⇓? _ w => ⌜P (view w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold view at *; simp_all)
  all_goals try subst s
  all_goals first | exact RetainsView.refl _ | assumption

theorem wgUp_material : RetainsCall wgUp := by
  apply ProjectedAction.of_wp
  intro s
  have hm := fun running => (modifyDev_material (fun d => {d with running}) (fun _ => rfl)).wp (RetainsView s)
  have ho := wgOpen_material.wp s
  mvcgen [wgUp, hm, ho]
  all_goals subst s
  all_goals exact RetainsView.refl _

theorem netnsPreExit_material : SameView view netnsPreExit := by
  apply SameView.of_wp
  intro s
  have hs := (socketControl_material _ (socketReinit_sameSocketKernel none none)).wp (fun t => t = s)
  have he := fun pid => (clearPeerEndpointSrc_material pid).wp (fun t => t = s)
  have hm := (modifyDev_material (fun d => {d with carrier := false, creatingNet := false}) (fun _ => rfl)).wp (fun t => t = s)
  have hl (α β : Type) := list_view_spec view (α := α) (β := β) (fun t => t = s)
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    netnsPreExit, hs, he, hm, getDev, getK, branch, invariant]


theorem node_material (ha : SameNodeKernel a) : SameView view a := by
  apply ha.of_factor (fun k : Kernel => k.wg.map materialState) view
  intro w
  simp [view,nodeKernelView,nodeKernel,nodeDevice,materialState,Option.map_map,Function.comp_def]

theorem listDel_material (id : NodeId) : SameView view (listDel id) := by
  apply SameView.of_wp
  intro s
  have hs := fun pid p => (setPeer_view pid p).wp (fun t => t = s)
  have hl (α β : Type) := list_view_spec view (α := α) (β := β) (fun t => t = s)
  mvcgen [-Std.Do.Spec.forIn_list,-Std.Do.Spec.forIn'_list,hl,listDel,hs,getDev,getK,invariant]

theorem rootRemovePeerLists_material (root : NodeId) : SameView view (rootRemovePeerLists root) := by
  apply SameView.of_wp
  intro s
  have hn := fun id => (kernel (Framing.getNode_sameKernel id)).wp (fun t => t = s)
  have hp := fun pid => (getPeer_view pid).wp (fun t => t = s)
  have hd := fun id => (listDel_material id).wp (fun t => t = s)
  have hl (α β : Type) := list_view_spec view (α := α) (β := β) (fun t => t = s)
  mvcgen [-Std.Do.Spec.forIn_list,-Std.Do.Spec.forIn'_list,hl,
    rootRemovePeerLists,hn,hp,hd,getDev,getK,branch,invariant]
  all_goals try exact ((⇓? _ w => ⌜view w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [view]
  all_goals trivial

theorem allowedipsFree_material : SameView view WG.free := by
  apply SameView.of_wp
  intro s
  have hr := fun id => (rootRemovePeerLists_material id).wp (fun t => t = s)
  have ht := fun id => (kernel (subtree_sameKernel id)).wp (fun t => t = s)
  have hf := fun id => (node_material (freeNode_sameNodeKernel id)).wp (fun t => t = s)
  have hm := fun roots => (modifyDev_material (fun d => {d with peerAllowedips := roots}) (fun _ => rfl)).wp (fun t => t = s)
  have hl (α β : Type) := list_view_spec view (α := α) (β := β) (fun t => t = s)
  mvcgen [-Std.Do.Spec.forIn_list,-Std.Do.Spec.forIn'_list,hl,WG.free,hr,ht,hf,hm,getDev,getK,branch,invariant]

theorem removeByPeer_material (pid : PeerId) : SameView view (removeByPeer pid) := by
  rw [← AllowedIps.removeByPeerWithStep_eq]
  apply SameView.of_wp
  intro s
  have hg := (getPeer_view pid).wp (fun t => t = s)
  have hlst := fun id => (listDel_material id).wp (fun t => t = s)
  have hn := fun id => (node_material (removeNodeBody_sameNodeKernel id)).wp (fun t => t = s)
  have hm := (modifyDev_material (fun d => {d with peerAllowedips := {d.peerAllowedips with seq := d.peerAllowedips.seq + 1}}) (fun _ => rfl)).wp (fun t => t = s)
  have hl (α β : Type) := list_view_spec view (α := α) (β := β) (fun t => t = s)
  mvcgen [-Std.Do.Spec.forIn_list,-Std.Do.Spec.forIn'_list,hl,
    AllowedIps.removeByPeerWithStep,AllowedIps.removeStep,hg,hlst,hn,hm,branch]

theorem peerMakeDead_material (pid : PeerId) : SameView view (peerMakeDead pid) := by
  apply SameView.of_wp
  intro s
  have hg := (getPeer_view pid).wp (fun t => t = s)
  have hs := fun p => (setPeer_view pid p).wp (fun t => t = s)
  have hr := (removeByPeer_material pid).wp (fun t => t = s)
  mvcgen [peerMakeDead,hg,hs,hr,modifyDev,modifyK]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [view,Option.map_map,Function.comp_def]

theorem peerRemove_material (peer : Option PeerId) : RetainsCall (peerRemove peer) := by
  apply ProjectedAction.of_wp
  intro s
  have hd := fun pid => (peerMakeDead_material pid).wp (RetainsView s)
  have hr := fun pid => (peerRemoveAfterDead_material pid).wp s
  mvcgen [peerRemove,hd,hr,branch,invariant]
  all_goals subst s
  all_goals exact RetainsView.refl _

theorem peerRemoveAll_material : RetainsCall peerRemoveAll := by
  apply ProjectedAction.of_wp
  intro s
  have hf := allowedipsFree_material.wp (RetainsView s)
  have hd := fun pid => (peerMakeDead_material pid).wp (RetainsView s)
  have hr := fun pid => (peerRemoveAfterDead_material pid).wp s
  have hl (α β : Type) := list_view_spec view (α := α) (β := β) (RetainsView s)
  mvcgen [-Std.Do.Spec.forIn_list,-Std.Do.Spec.forIn'_list,hl,peerRemoveAll,hf,hd,hr,getDev,getK,branch,invariant]
  all_goals subst s
  all_goals exact RetainsView.refl _

theorem materialView_link (w : World) :
    (linkView w).wg.map materialState = view w := by
  simp [linkView,linkKernel,linkDevice,WGKernelView.ofKernel,view,materialState,Option.map_map,Function.comp_def]

theorem wgCreate_material : RetainsCall wgCreate := by
  intro w result v hr
  have hc := (hoare_iff_triple _ _ _).mpr (wgCreate_endpoint (linkView w)) w result v rfl hr
  rcases hc with he | ⟨hn,he⟩
  · have hv := congrArg (fun s : WGKernelView => s.wg.map materialState) he
    rw [materialView_link,materialView_link] at hv
    rw [hv]
    exact RetainsView.refl _
  · have hv := congrArg (fun s : WGKernelView => s.wg.map materialState) he
    rw [materialView_link] at hv
    intro epoch keys heq id k hk valid
    rw [hv] at heq
    simp [registeredLink,setupLink,linkDevice,materialState] at heq
    obtain ⟨rfl,rfl⟩ := heq
    simp at hk

theorem ratelimiter_material (ha : SameRatelimiterKernel a) : SameView view a :=
  ha.of_factor (fun k : Kernel => k.wg.map materialState) view (fun _ => rfl)

/-- Actual teardown may fail before the drop; on a normal return its device is
absent, which vacuously retains every surviving valid receiving key. -/
theorem wgDestruct_material : RetainsCall wgDestruct := by
  apply ProjectedAction.of_wp
  intro s
  have hs := (socketControl_material _ (socketReinit_sameSocketKernel none none)).wp (RetainsView s)
  have hp := peerRemoveAll_material.wp s
  have hm := (kernel mayHaveSlept_sameKernel).wp (RetainsView s)
  have hr := (ratelimiter_material ratelimiterUninit_sameRatelimiterKernel).wp (RetainsView s)
  have ht := (kernel retireDeviceUnits_sameKernel).wp (RetainsView s)
  mvcgen [wgDestruct,hs,hp,hm,hr,ht,getDev,getK,modifyDev,modifyK,unsupported,invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals try simp_all [view,Option.map_map,Function.comp_def,retains_absent]
  all_goals try subst s
  all_goals first | exact RetainsView.refl _ | assumption

theorem wgDelete_material : RetainsCall wgDelete := by
  apply ProjectedAction.of_wp
  intro s
  have hd := wgDown_material.wp s
  have ht := wgDestruct_material.wp s
  have hc := (kernel (skipCut_sameKernel allocCuts)).wp (RetainsView s)
  have hm := (kernel mayHaveSlept_sameKernel).wp (RetainsView s)
  mvcgen [wgDelete,hd,ht,hc,hm,getDev,getK,invariant]
  all_goals subst s
  all_goals exact RetainsView.refl _

end Leanux.Proofs.WG.Origins.Retaining
