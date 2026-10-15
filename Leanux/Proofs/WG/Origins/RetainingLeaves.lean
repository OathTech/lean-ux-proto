import Leanux.Proofs.WG.Origins.IndexMaterial
import Leanux.Proofs.WG.Queues.RxRingHandshake
import Leanux.Proofs.Framing.WGCookie
import Leanux.Proofs.Framing.WGConfiguration
import Leanux.Proofs.Framing.WGDeviceLifecycle

/-! Concrete normal-return frames for the complete receiving-material view.
Peer and packet writes retain that view; key writes use actual resident records.
These contracts neither establish initial support nor retain erased objects. -/
namespace Leanux.Proofs.WG.Origins.Retaining
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.Lifetimes Leanux.Proofs.WG.Queues Std.Do
set_option pp.structureInstances false

abbrev RetainsCall (a : M α) := ProjectedAction view RetainsView a

theorem RetainsCall.wp (h : RetainsCall a) (s : View) :
    ⦃fun w => ⌜RetainsView s (view w)⌝⦄ a
    ⦃⇓? _ w => ⌜RetainsView s (view w)⌝⦄ :=
  ProjectedAction.wp h (RetainsView s) (fun _ _ hr hs => hs.trans hr)

theorem of_view (h : SameView view a) : RetainsCall a :=
  fun _ _ _ hr => retains_of_sameView h hr

theorem RetainsCall.of_same (h : SameView view a) : RetainsCall a := of_view h

/-- Supplied session support is transported on a normal return; no returned
World or state-retention statement is attached to a Stop. -/
theorem RetainsCall.support (ha : RetainsCall a) (hi : Inv history w)
    (hr : a.run w = .ok (result,v)) : Inv history v :=
  hi.retain (ha w result v hr)

def materialState (d : Device) : Nat × (KeypairId → Option Keypair) :=
  (d.ifindex, fun id => d.keypairs[id]?)

theorem material_getPeer (P : View → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (view w)⌝⦄ getPeer pid ⦃⇓? _ w => ⌜P (view w)⌝⦄ := (getPeer_view pid).wp P

theorem material_setPeer (P : View → Prop) (pid : PeerId) (p : Peer) :
    ⦃fun w => ⌜P (view w)⌝⦄ setPeer pid p ⦃⇓? _ w => ⌜P (view w)⌝⦄ := (setPeer_view pid p).wp P

theorem modifyDev_material (f : Device → Device)
    (hf : ∀ d, ((f d).ifindex,(f d).keypairs) = (d.ifindex,d.keypairs)) :
    SameView view (modifyDev f) := by
  apply SameView.of_wp
  intro s
  exact modifyDev_spec (fun t => t = s) f (fun d => congrArg Prod.fst (hf d))
    (fun d => congrArg Prod.snd (hf d))

theorem getPeer_material (pid : PeerId) : SameView view (getPeer pid) := getPeer_view pid

theorem getKeypair_material (id : KeypairId) : SameView view (getKeypair id) :=
by
  apply SameView.of_wp
  intro s
  mvcgen [getKeypair,getDev,getK,invariant]

theorem requireNotPending_material (pid : PeerId) (why : String) :
    SameView view (requireNotPending pid why) := by intro w x v h; cases h; rfl

theorem ownerDeref_material (o : IndexOwner) : SameView view o.peerDeref := kernel (indexOwner_peerDeref_sameKernel o)

theorem ownerWord_material (o : IndexOwner) : SameView view o.peerWord := kernel (indexOwner_peerWord_sameKernel o)

theorem indexRemove_material (o : IndexOwner) : SameView view (indexRemove o) := index (indexRemove_sameIndexKernel o)

theorem peerGet_material (pid : PeerId) : SameView view (peerGet pid) := by
  apply SameView.of_wp
  intro s
  have hg := material_getPeer (fun t => t = s) pid
  have hs := material_setPeer (fun t => t = s) pid
  mvcgen [peerGet,requireNotPending,hg,hs,refcountInc,branch,branchCmp,unsupported]

theorem peerPut_material (pid : Option PeerId) : SameView view (peerPut pid) := by
  apply SameView.of_wp
  intro s
  have hg := material_getPeer (fun t => t = s)
  have hs := material_setPeer (fun t => t = s)
  have hi := fun o => (indexRemove_material o).wp (fun t => t = s)
  mvcgen [peerPut,requireNotPending,hg,hs,hi,refcountDecAndTest,retirePeerUnits,
    getDev,getK,modifyDev,modifyK,branch,branchCmp,unsupported,invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [view,Function.comp_def]

theorem keypairGet_material (kp : Option KeypairId) : RetainsCall (keypairGet kp) := by
  intro w x v hr
  exact (hoare_iff_triple _ _ _).mpr
    (keypairGet_spec (RetainsView (view w)) (fun _ _ hr hi => hi.trans hr) kp)
    w x v (RetainsView.refl _) hr

theorem keypairPut_material (kp : Option KeypairId) (now : Bool) : RetainsCall (keypairPut kp now) := by
  intro w x v hr
  exact (hoare_iff_triple _ _ _).mpr
    (keypairPut_spec (RetainsView (view w)) (fun _ _ hr hi => hi.trans hr) kp now)
    w x v (RetainsView.refl _) hr

theorem keypairCreate_material (word : Option PeerId) : RetainsCall (keypairCreate word) :=
  fun w x v hr => create_retains word w v x hr

theorem pubkeyLookup_material (key : Key) : SameView view (pubkeyLookup key) := by
  have spec (initial : Kernel) : ⦃fun w => ⌜w.k = initial⌝⦄ pubkeyLookup key
      ⦃⇓? result w => ⌜PeerBorrow.Borrowed initial result w.k⌝⦄ := by
    have ha := fun peer => PeerBorrow.acquire_spec peer initial
    mvcgen [pubkeyLookup,ha,getDev,getK,branch,invariant]
    all_goals simp_all
  intro w result v hr
  have hb := (hoare_iff_triple _ _ _).mpr (spec w.k) w result v rfl hr
  cases result with
  | none => change v.k = w.k at hb; simp [view,hb]
  | some pid => obtain ⟨d,p,hd,_,_,hk⟩ := hb; simp [view,hk,hd]

theorem dstCacheReset_material (pid : PeerId) : SameView view (dstCacheReset pid) := by
  apply SameView.of_wp
  intro s
  have hg := material_getPeer (fun t => t = s) pid
  have hs := material_setPeer (fun t => t = s) pid
  have hc := (kernel (hiddenJiffies_sameKernel .dstCacheResetTs)).wp (fun t => t = s)
  mvcgen [dstCacheReset,hg,hs,hc]

theorem dstCacheGet_material (pid : PeerId) (gen : Nat) : SameView view (dstCacheGet pid gen) := by
  apply SameView.of_wp
  intro s
  have hp := material_getPeer (fun t => t = s) pid
  have hs := fun p => material_setPeer (fun t => t = s) pid p
  have ht := fun site => (kernel (hiddenJiffies_sameKernel site)).wp (fun t => t = s)
  mvcgen [dstCacheGet, hp, hs, ht, branch, branchCmp]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [view, materialState]
  all_goals try assumption

theorem dstCacheSet_material (pid : PeerId) (src gen dev : Nat) : SameView view (dstCacheSet pid src gen dev) := by
  apply SameView.of_wp
  intro s
  have hp := material_getPeer (fun t => t = s) pid
  have hs := fun p => material_setPeer (fun t => t = s) pid p
  have ht := fun site => (kernel (hiddenJiffies_sameKernel site)).wp (fun t => t = s)
  mvcgen [dstCacheSet, hp, hs, ht, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [view, materialState]
  all_goals try assumption

theorem tunnelXmit_material (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    SameView view ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx) := by
  rw [tunnelXmitSource_eq]
  apply SameView.of_wp
  intro s
  have hl := fun sites force => (kernel (Leanux.Proofs.WG.Queues.loopbackSend_kernel sites force)).wp (fun t => t = s)
  have hc := fun sites => (kernel (skipCut_sameKernel sites)).wp (fun t => t = s)
  have hp := fun fam => (kernel (socketPort_sameKernel fam)).wp (fun t => t = s)
  mvcgen [tunnelXmitSource, hl, hc, hp, modifyDev, modifyK, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [view, materialState, Option.map_map, Function.comp_def]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [view, materialState]
  all_goals try assumption

theorem send4ClearSrc_material cache : SameView view (send4ClearSrcSource cache) := by
  apply SameView.of_wp
  intro s
  have hp := fun pid => material_getPeer (fun t => t = s) pid
  have hs := fun pid p => material_setPeer (fun t => t = s) pid p
  mvcgen [send4ClearSrcSource, hp, hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [view, materialState]
  all_goals try assumption

theorem send4Finish_material e bytes ds exactRx route : SameView view (send4FinishSource e bytes ds exactRx route) := by
  apply SameView.of_wp
  intro s
  have ht := fun r => (tunnelXmit_material e bytes ds r exactRx).wp (fun t => t = s)
  mvcgen [send4FinishSource, ht, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [view, materialState]
  all_goals try assumption

theorem send4RouteDone_material e cache bytes ds exactRx gen fallback rt :
    SameView view (send4RouteDoneSource e cache bytes ds exactRx gen fallback rt) := by
  apply SameView.of_wp
  intro s
  have hs := fun pid src gen dev => (dstCacheSet_material pid src gen dev).wp (fun t => t = s)
  have hf := fun r => (send4Finish_material e bytes ds exactRx r).wp (fun t => t = s)
  mvcgen [send4RouteDoneSource, hs, hf, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [view, materialState]
  all_goals try assumption

theorem send4Retry_material e cache bytes ds exactRx gen fallback srcIf rt :
    SameView view (send4RetrySource e cache bytes ds exactRx gen fallback srcIf rt) := by
  apply SameView.of_wp
  intro s
  have hc := (send4ClearSrc_material cache).wp (fun t => t = s)
  have hr := fun pid => (dstCacheReset_material pid).wp (fun t => t = s)
  have hl := fun fam src dst => (kernel (routeLookup_sameKernel fam src dst)).wp (fun t => t = s)
  have hd := fun rt => (send4RouteDone_material e cache bytes ds exactRx gen fallback rt).wp (fun t => t = s)
  mvcgen [send4RetrySource, hc, hr, hl, hd, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [view, materialState]
  all_goals try assumption

theorem send4Miss_material e cache bytes ds exactRx gen fallback saddr srcIf :
    SameView view (send4MissSource e cache bytes ds exactRx gen fallback saddr srcIf) := by
  apply SameView.of_wp
  intro s
  have hc := (send4ClearSrc_material cache).wp (fun t => t = s)
  have hr := fun pid => (dstCacheReset_material pid).wp (fun t => t = s)
  have hl := fun fam src dst => (kernel (routeLookup_sameKernel fam src dst)).wp (fun t => t = s)
  have hn := fun srcIf rt => (send4Retry_material e cache bytes ds exactRx gen fallback srcIf rt).wp (fun t => t = s)
  mvcgen [send4MissSource, hc, hr, hl, hn, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [view, materialState]
  all_goals try assumption

theorem send4AfterCache_material e cache bytes ds exactRx gen saddr srcIf route :
    SameView view (send4AfterCacheSource e cache bytes ds exactRx gen saddr srcIf route) := by
  apply SameView.of_wp
  intro s
  have hm := (send4Miss_material e cache bytes ds exactRx gen route saddr srcIf).wp (fun t => t = s)
  have hf := (send4Finish_material e bytes ds exactRx route).wp (fun t => t = s)
  mvcgen [send4AfterCacheSource, hm, hf, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [view, materialState]
  all_goals try assumption

theorem send4_material e cache bytes ds exactRx : SameView view (send4 e cache bytes ds exactRx) := by
  rw [← send4Source_eq]
  apply SameView.of_wp
  intro s
  have hg := fun pid gen => (dstCacheGet_material pid gen).wp (fun t => t = s)
  have ha := fun gen src srcIf route => (send4AfterCache_material e cache bytes ds exactRx gen src srcIf route).wp (fun t => t = s)
  mvcgen [send4Source, hg, ha, getDev, getK, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [view, materialState]
  all_goals try assumption

theorem send6_material e cache bytes ds exactRx : SameView view (send6 e cache bytes ds exactRx) := by
  apply SameView.of_wp
  intro s
  have hg := fun pid gen => (dstCacheGet_material pid gen).wp (fun t => t = s)
  have hp := fun pid => material_getPeer (fun t => t = s) pid
  have hs := fun pid p => material_setPeer (fun t => t = s) pid p
  have hr := fun pid => (dstCacheReset_material pid).wp (fun t => t = s)
  have hl := fun fam src dst => (kernel (routeLookup_sameKernel fam src dst)).wp (fun t => t = s)
  have hc := fun pid src gen dev => (dstCacheSet_material pid src gen dev).wp (fun t => t = s)
  have ht := fun r => (tunnelXmit_material e bytes ds r exactRx).wp (fun t => t = s)
  mvcgen [send6, hg, hp, hs, hr, hl, hc, ht, getDev, getK, branch, invariant]

  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [view, materialState]
  all_goals try assumption
theorem modifyPeer_material (pid : PeerId) (f : Peer → Peer)
    :
    SameView view (do let p ← getPeer pid; setPeer pid (f p)) := by
  apply SameView.of_wp
  intro s
  have hg := material_getPeer (fun t => t = s) pid
  have hs := fun p => material_setPeer (fun t => t = s) pid p
  mvcgen [hg, hs]
  all_goals simp_all

theorem setPeerEndpoint_material (pid : PeerId) (e : Endpoint) : SameView view (setPeerEndpoint pid e) := by
  apply SameView.of_wp
  intro s
  have hg := material_getPeer (fun t => t = s) pid
  have hs := fun p => material_setPeer (fun t => t = s) pid p
  have hn := (requireNotPending_material pid "changing the endpoint").wp (fun t => t = s)
  have he := fun old => (kernel (endpointEq_sameKernel e old)).wp (fun t => t = s)
  have hc := (dstCacheReset_material pid).wp (fun t => t = s)
  mvcgen [setPeerEndpoint, hg, hs, hn, he, hc, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [view, materialState]
  all_goals try assumption

theorem armTimer_material (pid : PeerId) (timer : PeerTimer) (delay : Nat) (jc : Option UInt64 := none) :
    SameView view (armTimer pid timer delay jc) := by
  rw [armTimer_source pid timer delay jc]
  apply SameView.bind (kernel (timerArmExpiry_sameKernel pid timer delay jc))
  intro expiry
  exact modifyPeer_material pid (fun p => p.setTimer timer (some expiry))

theorem delTimer_material (pid : PeerId) (timer : PeerTimer) : SameView view (delTimer pid timer) :=
  modifyPeer_material pid (fun p => p.setTimer timer none)

theorem modPeerTimerGuard_material (pid : PeerId) : SameView view (modPeerTimerGuard pid) := by
  apply SameView.of_wp
  intro s
  have hg := (getPeer_material pid).wp (fun t => t = s)
  mvcgen [modPeerTimerGuard, getDev, getK, hg, WG.andM, branch, invariant]

theorem modPeerTimer_material (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    SameView view (modPeerTimer site pid timer delay) := by
  apply SameView.of_wp
  intro s
  have hg := (modPeerTimerGuard_material pid).wp (fun t => t = s)
  have ha := fun jc => (armTimer_material pid timer delay jc).wp (fun t => t = s)
  have hc := (kernel (callerJiffies_sameKernel site)).wp (fun t => t = s)
  mvcgen [modPeerTimer, hg, ha, hc]

theorem timersTraversal_material (pid : PeerId) : SameView view (timersTraversal pid) := by
  apply SameView.of_wp
  intro s
  have hg := (getPeer_material pid).wp (fun t => t = s)
  have ht := fun delay => (modPeerTimer_material .timerJiffiesTraversal pid .persistentKeepalive delay).wp (fun t => t = s)
  have hd := fun delay => discard_view_spec view (fun t => t = s) _ (ht delay)
  mvcgen [timersTraversal, hg, ht, hd, branchCmp]


theorem timersAnyAuthenticatedPacketSent_material (pid : PeerId) :
    SameView view (timersAnyAuthenticatedPacketSent pid) := delTimer_material pid .sendKeepalive

theorem timersHandshakeInitiated_material (pid : PeerId) :
    SameView view (timersHandshakeInitiated pid) := by
  apply SameView.of_wp
  intro s
  have hc := (kernel (callerJiffies_sameKernel .timerJiffiesHandshakeInitiated)).wp (fun t => t = s)
  have hj := (kernel (jitterBelowRekeyTimeout_sameKernel .retransmitJitter)).wp (fun t => t = s)
  have hg := (modPeerTimerGuard_material pid).wp (fun t => t = s)
  have ha := fun n jc => (armTimer_material pid .retransmitHandshake n jc).wp (fun t => t = s)
  mvcgen [timersHandshakeInitiated, hc, hj, hg, ha]

theorem indexInsert_material (owner : IndexOwner) :
    SameView view (indexInsert owner) := by
  apply (indexInsert_sameIndexKernel owner).of_factor
    (fun k : Kernel => k.wg.map materialState) view
  intro w
  simp [view, indexKernelView, indexKernel, materialState, Option.map_map, Function.comp_def]
  try rfl

theorem createInitiation_material (pid : PeerId) : SameView view (createInitiation pid) := by
  apply SameView.of_wp
  intro s
  have hg := fun pid => material_getPeer (fun t => t = s) pid
  have hs := fun pid p => material_setPeer (fun t => t = s) pid p
  have hh := fun site => (kernel (hidden_sameKernel site)).wp (fun t => t = s)
  have hp := fun k => (kernel (generatePublic_sameKernel k)).wp (fun t => t = s)
  have he := fun b e ck h => (kernel (messageEphemeral_sameKernel b e ck h)).wp (fun t => t = s)
  have hd := fun b ck p q => (kernel (mixDh_sameKernel b ck p q)).wp (fun t => t = s)
  have hpre := fun ck p => (kernel (mixPrecomputedDh_sameKernel ck p)).wp (fun t => t = s)
  have hi := (indexInsert_material (.handshake pid)).wp (fun t => t = s)
  unfold createInitiation
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  have hw := (ownerDeref_material (.handshake pid)).wp (fun t => t = s)
  mvcgen [hw, hg, hs, hh, hp, he, hd, hpre, hi, getDev, getK, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [view, materialState]
  all_goals try assumption

theorem addMacToPacket_material (pid : PeerId) (msg : List UInt8) :
    SameView view (addMacToPacket pid msg) := by
  apply SameView.of_wp
  intro s
  have hg := material_getPeer (fun t => t = s) pid
  have hs := fun p => material_setPeer (fun t => t = s) pid p
  have he := fun d b n f => (kernel (branchExpired_sameKernel d b n f)).wp (fun t => t = s)
  mvcgen [addMacToPacket, hg, hs, he, branch, WG.andM]
  all_goals simp_all

theorem sendBufferToPeer_material (pid : PeerId) (bytes : List UInt8) :
    SameView view (sendBufferToPeer pid bytes) := by
  apply SameView.of_wp
  intro s
  have hg := material_getPeer (fun t => t = s) pid
  have hs := fun p => material_setPeer (fun t => t = s) pid p
  have ha := fun site => (kernel (hiddenAlloc_sameKernel site)).wp (fun t => t = s)
  have h4 := fun e => (send4_material e (some pid) bytes HANDSHAKE_DSCP true).wp (fun t => t = s)
  have h6 := fun e => (send6_material e (some pid) bytes HANDSHAKE_DSCP true).wp (fun t => t = s)
  mvcgen [sendBufferToPeer, hg, hs, ha, h4, h6, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [view, materialState]
  all_goals try assumption

theorem sendHandshakeInitiation_material (pid : PeerId) : SameView view (sendHandshakeInitiation pid) := by
  apply SameView.of_wp
  intro s
  have hg := material_getPeer (fun t => t = s) pid
  have hs := fun p => material_setPeer (fun t => t = s) pid p
  have he := fun date => (kernel (branchExpired_sameKernel .initRateLimited date REKEY_TIMEOUT (!·))).wp (fun t => t = s)
  have hc := fun site => (kernel (hiddenClock64_sameKernel site)).wp (fun t => t = s)
  have hi := (createInitiation_material pid).wp (fun t => t = s)
  have hm := fun msg => (addMacToPacket_material pid msg).wp (fun t => t = s)
  have ht := (timersTraversal_material pid).wp (fun t => t = s)
  have ha := (timersAnyAuthenticatedPacketSent_material pid).wp (fun t => t = s)
  have hb := fun msg => (sendBufferToPeer_material pid msg).wp (fun t => t = s)
  have hj := (timersHandshakeInitiated_material pid).wp (fun t => t = s)
  mvcgen [sendHandshakeInitiation, hg, hs, he, hc, hi, hm, ht, ha, hb, hj, branch, invariant]
  all_goals try simp_all

theorem createResponse_material (pid : PeerId) : SameView view (createResponse pid) := by
  apply SameView.of_wp
  intro s
  have hg := material_getPeer (fun t => t = s) pid
  have hs := fun p => material_setPeer (fun t => t = s) pid p
  have hh := fun site => (kernel (hidden_sameKernel site)).wp (fun t => t = s)
  have hp := fun k => (kernel (generatePublic_sameKernel k)).wp (fun t => t = s)
  have he := fun b e ck h => (kernel (messageEphemeral_sameKernel b e ck h)).wp (fun t => t = s)
  have hd := fun b ck p q => (kernel (mixDh_sameKernel b ck p q)).wp (fun t => t = s)
  have hk := fun b c ck d => (kernel (Framing.kdf_sameKernel b c ck d)).wp (fun t => t = s)
  have ho := fun xs i => (kernel (Framing.kdfOut_sameKernel xs i)).wp (fun t => t = s)
  have hi := (indexInsert_material (.handshake pid)).wp (fun t => t = s)
  unfold createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  have hw := (ownerDeref_material (.handshake pid)).wp (fun t => t = s)
  mvcgen [hw, hg, hs, hh, hp, he, hd, hk, ho, hi, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [view, materialState]

theorem timersSessionDerived_material (pid : PeerId) : SameView view (timersSessionDerived pid) := by
  apply SameView.of_wp
  intro s
  have hm := fun site timer delay => (modPeerTimer_material site pid timer delay).wp (fun t => t = s)
  have hd (α : Type) := discard_view_spec view (α := α) (fun t => t = s)
  mvcgen [timersSessionDerived, hm, hd]

theorem cookie_material (a : M α) (ha : SameCookieKernel a) : SameView view a := by
  apply ha.of_factor (fun k : Kernel => k.wg.map materialState) view
  intro w
  simp [cookieKernelView, cookieKernel, cookieDevice, view,
    Option.map_map, Function.comp_def]
  rfl

theorem consumeInitiation_material (msg : List UInt8) : RetainsCall (consumeInitiation msg) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have hg := fun pid => material_getPeer P pid
  have hs := fun pid p => material_setPeer P pid p
  have hu := fun peer => (peerPut_material peer).wp P
  have hc := fun site => (kernel (hiddenClock64_sameKernel site)).wp P
  have he := fun b e ck h => (kernel (messageEphemeral_sameKernel b e ck h)).wp P
  have hd := fun b ck p q => (kernel (mixDh_sameKernel b ck p q)).wp P
  have hp := fun ck p => (kernel (mixPrecomputedDh_sameKernel ck p)).wp P
  have hdec := fun a k h => (kernel (messageDecrypt_sameKernel a k h)).wp P
  have hl := fun k => (pubkeyLookup_material k).wp P
  have hb := fun d b => (kernel (sameKernel_branch d b)).wp P
  have hbc := fun d b x y => (kernel (branchCmp_sameKernel d b x y)).wp P
  mvcgen [hb, hbc, consumeInitiation, hg, hs, hu, hc, he, hd, hp, hdec, hl,
    getDev, getK, WG.orM, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [view, materialState]
  all_goals try subst s
  all_goals first | exact RetainsView.refl _ | assumption

theorem consumeResponse_material (msg : List UInt8) : RetainsCall (consumeResponse msg) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have hg := fun pid => material_getPeer P pid
  have hs := fun pid p => material_setPeer P pid p
  have hu := fun peer => (peerPut_material peer).wp P
  have hl := fun ks i => (indexLookup_retains ks i).wp (RetainsView s) (fun _ _ hr hi => hi.trans hr)
  have he := fun b e ck h => (kernel (messageEphemeral_sameKernel b e ck h)).wp P
  have hd := fun b ck p q => (kernel (mixDh_sameKernel b ck p q)).wp P
  have hdec := fun a k h => (kernel (messageDecrypt_sameKernel a k h)).wp P
  have hk := fun b c ck d => (kernel (Framing.kdf_sameKernel b c ck d)).wp P
  have ho := fun xs i => (kernel (Framing.kdfOut_sameKernel xs i)).wp P
  mvcgen [consumeResponse, hg, hs, hu, hl, he, hd, hdec, hk, ho,
    getDev, getK, branch, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [view, materialState]
  all_goals try subst s
  all_goals first | exact RetainsView.refl _ | assumption

theorem cookieMessageConsume_material (msg : List UInt8) :
    RetainsCall (cookieMessageConsume msg) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have hl := (indexLookup_retains [.handshake, .keypair] (u32le msg 4)).wp (RetainsView s) (fun _ _ hr hi => hi.trans hr)
  have hg := fun pid => material_getPeer P pid
  have hs := fun pid p => material_setPeer P pid p
  have hu := fun peer => (peerPut_material peer).wp P
  have hc := (kernel (hiddenClock64_sameKernel .cookieBirthdate)).wp P
  mvcgen [cookieMessageConsume, hl, hg, hs, hu, hc, branch, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [view, materialState]
  all_goals try subst s
  all_goals first | exact RetainsView.refl _ | assumption

end Leanux.Proofs.WG.Origins.Retaining
