import Leanux.Proofs.WG.Keypairs.OrdinaryRules
import Leanux.Proofs.WG.Keypairs.SnapshotRules
import Leanux.Proofs.WG.Keypairs.Frames.WGTransitions
import Leanux.Proofs.Framing.WGCookie

namespace Leanux.Proofs.WG.Keypairs.WGMore
open Leanux Leanux.WG Std.Do Leanux.Proofs.WG.Keypairs Leanux.Proofs.WG.Keypairs.KernelFrames Leanux.Proofs.WG.Keypairs.WGFrames Leanux.Proofs.WG.Keypairs.WGTransitions
open Lean

set_option pp.structureInstances false
set_option maxHeartbeats 800000

/-- Legacy receive snapshots are a projection of the canonical cookie frame. -/
theorem sameSnapshot_of_sameCookieKernel (h : Framing.SameCookieKernel a) : SameSnapshot a := by
  intro w x v hr
  have hf := congrArg (fun k => snapshot {w with k}) (h w x v hr)
  simpa [snapshot, Framing.cookieKernelView, Framing.cookieKernel,
    Framing.cookieDevice, Option.bind_map, Function.comp_def] using hf

/-! The dump helpers contain many mutable-local joins. Proving each shared
continuation once avoids expanding its control flow at every incoming edge. -/
namespace DumpComposition
open Lean Meta Elab Tactic

theorem map_sameSnapshot (f : α → β) {a : M α} (ha : SameSnapshot a) :
    SameSnapshot (f <$> a) := by
  simpa only [map_eq_pure_bind] using snapshot_bind ha (fun x => snapshot_pure (f x))

theorem discard_sameSnapshot {a : M α} (ha : SameSnapshot a) : SameSnapshot (discard a) := by
  unfold Functor.discard
  exact map_sameSnapshot _ ha

theorem forIn_sameSnapshot (xs : List α) (b : β) (f : α → β → M (ForInStep β))
    (hf : ∀ a b, SameSnapshot (f a b)) : SameSnapshot (forIn xs b f) := by
  induction xs generalizing b with
  | nil => simpa only [List.forIn_nil] using snapshot_pure b
  | cons a xs ih =>
    rw [List.forIn_cons]
    apply snapshot_bind (hf a b)
    intro step
    cases step with
    | done b => exact snapshot_pure b
    | yield b => exact ih b

theorem andM_sameSnapshot (a b : M Bool) (ha : SameSnapshot a) (hb : SameSnapshot b) :
    SameSnapshot (Leanux.WG.andM a b) := by
  unfold Leanux.WG.andM
  apply snapshot_bind ha
  intro result
  cases result
  · exact snapshot_pure false
  · exact hb

theorem orM_sameSnapshot (a b : M Bool) (ha : SameSnapshot a) (hb : SameSnapshot b) :
    SameSnapshot (Leanux.WG.orM a b) := by
  unfold Leanux.WG.orM
  apply snapshot_bind ha
  intro result
  cases result
  · exact hb
  · exact snapshot_pure true

private def snapshotHeadBZ : Nat → Expr → Expr
  | 0, e => e
  | n+1, e =>
    let e := e.consumeMData
    match e with
    | .letE _ _ v b _ => snapshotHeadBZ n (b.instantiate1 v)
    | _ =>
      match e.getAppFn.consumeMData with
      | .letE _ _ v b _ => snapshotHeadBZ n (mkAppN (b.instantiate1 v) e.getAppArgs)
      | .lam .. =>
        let e' := e.headBeta
        if Expr.equal e e' then e else snapshotHeadBZ n e'
      | _ => e

elab "dump_snapshot_head_reduce" : tactic => withMainContext do
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isAppOf ``SameSnapshot do throwError "not SameSnapshot"
  let .app f a := t | throwError "missing action"
  let a' := snapshotHeadBZ 64 a
  if Expr.equal a a' then throwError "head unchanged"
  replaceMainGoal [← g.replaceTargetDefEq (.app f a')]

elab "dump_snapshot_head_match" : tactic => withMainContext do
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isAppOf ``SameSnapshot do throwError "not SameSnapshot"
  let a := t.getAppArgs.back! |>.consumeMData
  let some _ ← Lean.Meta.matchMatcherApp? a | throwError "not a top matcher"
  replaceMainGoal (← Lean.Meta.Split.splitMatch g a)

elab "dump_snapshot_join_let" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``SameSnapshot do throwError "not SameSnapshot"
  let action := target.getAppArgs.back! |>.consumeMData
  let .letE name ty value body _ := action | throwError "not a let"
  unless name.toString.startsWith "__do_jp" do throwError "not a join continuation"
  let property ← forallTelescope ty fun args _ => do
    let result ← mkAppM ``SameSnapshot #[mkAppN value args]
    mkForallFVars args result
  let valueProof ← mkFreshExprSyntheticOpaqueMVar property
  let (continuation, next) ← withLocalDeclD name ty fun f => do
    let contract ← forallTelescope ty fun args _ => do
      let result ← mkAppM ``SameSnapshot #[mkAppN f args]
      mkForallFVars args result
    withLocalDeclD `dump_snapshot_join contract fun hf => do
      let bodyProp ← mkAppM ``SameSnapshot #[body.instantiate1 f]
      let next ← mkFreshExprSyntheticOpaqueMVar bodyProp
      let proof ← mkLambdaFVars #[f, hf] next
      pure (proof, next.mvarId!)
  goal.assign (mkApp2 continuation value valueProof)
  replaceMainGoal [valueProof.mvarId!, next]

elab "dump_snapshot_join_use" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``SameSnapshot do throwError "not SameSnapshot"
  let action := target.getAppArgs.back! |>.consumeMData |>.headBeta
  unless action.getAppFn.isFVar do throwError "not a local continuation"
  for decl in ← getLCtx do
    if decl.userName == `dump_snapshot_join then
      let proof := mkAppN decl.toExpr action.getAppArgs
      try
        if ← withReducible (isDefEq (← inferType proof) target) then
          goal.assign proof
          replaceMainGoal []
          return
      catch _ => pure ()
  throwError "no continuation contract"

macro "dump_snapshot_step" : tactic => `(tactic|
  first
    | contradiction
    | intro_forall
    | with_reducible assumption
    | dump_snapshot_join_let
    | dump_snapshot_join_use
    | (snapshot_head Pure.pure; exact snapshot_pure _)
    | (snapshot_head Bind.bind; refine snapshot_bind ?_ ?_)
    | (snapshot_head ite; refine snapshot_ite _ ?_ ?_)
    | (snapshot_head Leanux.WG.andM; refine andM_sameSnapshot _ _ ?_ ?_)
    | (snapshot_head Leanux.WG.orM; refine orM_sameSnapshot _ _ ?_ ?_)
    | (snapshot_head Functor.discard; refine discard_sameSnapshot ?_)
    | (snapshot_head Functor.map; refine map_sameSnapshot _ ?_)
    | (snapshot_head ForIn.forIn; with_reducible refine forIn_sameSnapshot _ _ _ ?_)
    | dump_snapshot_head_reduce
    | dump_snapshot_head_match)

end DumpComposition
open DumpComposition

theorem lookup_sameSnapshot (root : Option NodeId) (bits key : Nat) :
    SameSnapshot (Leanux.WG.lookup root bits key) := by
  frame_same [Leanux.WG.lookup] using [swapEndian_spec, findNode_spec, peerGetMaybeZero_spec, getNode_spec]

theorem lookup_spec (P : Snapshot → Prop) (root : Option NodeId) (bits key : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.lookup root bits key
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (lookup_sameSnapshot root bits key).wp P

theorem enqueuePerPeerRx_sameSnapshot (irq : M Unit) (hi : SameSnapshot irq)
    (pkt : SkbId) (state : PacketState) : SameSnapshot (enqueuePerPeerRx irq pkt state) := by
  have irq_spec := hi.wp
  frame_same [Leanux.WG.enqueuePerPeerRx] using [irq_spec, getKeypair_live_spec,
    getPeer_spec, setPeer_spec, peerGet_spec, peerPut_spec, getRxSkb_spec, setRxSkb_spec]

theorem enqueuePerPeerRx_pure_spec (P : Snapshot → Prop) (pkt : SkbId) (state : PacketState) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ enqueuePerPeerRx (pure ()) pkt state
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := by
  apply (enqueuePerPeerRx_sameSnapshot (pure ()) ?_ pkt state).wp P
  intro w x w' hr
  cases hr
  rfl

theorem calculateSkbPadding_sameSnapshot (len mtu : Nat) : SameSnapshot (Leanux.WG.calculateSkbPadding len mtu) := by
  frame_same [Leanux.WG.calculateSkbPadding] using []

theorem calculateSkbPadding_spec (P : Snapshot → Prop) (len mtu : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.calculateSkbPadding len mtu
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (calculateSkbPadding_sameSnapshot len mtu).wp P

theorem cookieMessageConsume_sameSnapshot (msg : List UInt8) : SameSnapshot (Leanux.WG.cookieMessageConsume msg) := by
  frame_same [Leanux.WG.cookieMessageConsume] using [getPeer_spec, hiddenClock64_spec, indexLookup_spec, peerPut_spec, setPeer_spec]

theorem cookieMessageConsume_spec (P : Snapshot → Prop) (msg : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.cookieMessageConsume msg
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (cookieMessageConsume_sameSnapshot msg).wp P

theorem cpumaskNextOnline_sameSnapshot  : SameSnapshot (Leanux.WG.cpumaskNextOnline ) := by
  frame_same [Leanux.WG.cpumaskNextOnline] using [getDev_spec]

theorem cpumaskNextOnline_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.cpumaskNextOnline
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (cpumaskNextOnline_sameSnapshot ).wp P

theorem decryptPacket_sameSnapshot (pkt : RxPacket) : SameSnapshot (Leanux.WG.decryptPacket pkt) := by
  exact Leanux.Proofs.WG.Keypairs.decryptPacket_sameSnapshot pkt

theorem decryptPacket_spec (P : Snapshot → Prop) (pkt : RxPacket) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.decryptPacket pkt
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (decryptPacket_sameSnapshot pkt).wp P

theorem dishonest_sameSnapshot (why : Dishonest) : SameSnapshot (Leanux.WG.dishonest why) := by
  cases why <;> frame_same [Leanux.WG.dishonest] using []

theorem dishonest_spec (P : Snapshot → Prop) (why : Dishonest) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.dishonest why
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (dishonest_sameSnapshot why).wp P

theorem enqueuePerDeviceAndPeerRx_sameSnapshot (pkt : SkbId) : SameSnapshot (Leanux.WG.enqueuePerDeviceAndPeerRx pkt) := by
  frame_same [Leanux.WG.enqueuePerDeviceAndPeerRx] using [cpumaskNextOnlineFrom_spec, getDev_spec, getPeer_spec, queueDeviceWork_spec, setPeer_spec, getRxSkb_spec, setRxSkb_spec]

theorem enqueuePerDeviceAndPeerRx_spec (P : Snapshot → Prop) (pkt : SkbId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.enqueuePerDeviceAndPeerRx pkt
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (enqueuePerDeviceAndPeerRx_sameSnapshot pkt).wp P

theorem expiredNewHandshake_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.expiredNewHandshake pid) := by
  frame_same [Leanux.WG.expiredNewHandshake] using [clearPeerEndpointSrc_spec, sendQueuedHandshakeInitiation_spec]

theorem expiredNewHandshake_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.expiredNewHandshake pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (expiredNewHandshake_sameSnapshot pid).wp P

theorem expiredRetransmitHandshake_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.expiredRetransmitHandshake pid) := by
  frame_same [Leanux.WG.expiredRetransmitHandshake] using [clearPeerEndpointSrc_spec, delTimer_spec, getPeer_spec, modPeerTimer_spec, purgeStagedPackets_spec, sendQueuedHandshakeInitiation_spec, setPeer_spec]

theorem expiredRetransmitHandshake_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.expiredRetransmitHandshake pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (expiredRetransmitHandshake_sameSnapshot pid).wp P

theorem expiredSendKeepalive_ordinary (pid : PeerId) : OrdinaryAction (Leanux.WG.expiredSendKeepalive pid) := by
  frame_ordinary [Leanux.WG.expiredSendKeepalive] using [getPeer_spec, modPeerTimer_spec, setPeer_spec] ordinary [sendKeepalive_spec]

theorem expiredSendKeepalive_spec (P : Snapshot → Prop) (hp : Stable P) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.expiredSendKeepalive pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (expiredSendKeepalive_ordinary pid).wp P hp

theorem expiredSendPersistentKeepalive_ordinary (pid : PeerId) : OrdinaryAction (Leanux.WG.expiredSendPersistentKeepalive pid) := by
  frame_ordinary [Leanux.WG.expiredSendPersistentKeepalive] using [getPeer_spec] ordinary [sendKeepalive_spec]

theorem expiredSendPersistentKeepalive_spec (P : Snapshot → Prop) (hp : Stable P) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.expiredSendPersistentKeepalive pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (expiredSendPersistentKeepalive_ordinary pid).wp P hp

theorem expiredZeroKeyMaterial_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.expiredZeroKeyMaterial pid) := by
  frame_same [Leanux.WG.expiredZeroKeyMaterial] using [getDev_spec, getPeer_spec, peerGet_spec, peerPut_spec, recordQueued_spec]

theorem expiredZeroKeyMaterial_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.expiredZeroKeyMaterial pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (expiredZeroKeyMaterial_sameSnapshot pid).wp P

theorem getAllowedips_sameSnapshot (skb : NlSkb) (family masked cidr : Nat) :
    SameSnapshot (Leanux.WG.getAllowedips skb family masked cidr) := by
  frame_same [Leanux.WG.getAllowedips] using []

theorem getAllowedips_spec (P : Snapshot → Prop) (skb : NlSkb) (family masked cidr : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.getAllowedips skb family masked cidr
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getAllowedips_sameSnapshot skb family masked cidr).wp P

theorem ip6EcnSetCe_sameSnapshot (bytes : List UInt8) : SameSnapshot (Leanux.WG.ip6EcnSetCe bytes) := by
  frame_same [Leanux.WG.ip6EcnSetCe] using []

theorem ip6EcnSetCe_spec (P : Snapshot → Prop) (bytes : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.ip6EcnSetCe bytes
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (ip6EcnSetCe_sameSnapshot bytes).wp P

theorem ip6EcnSetEct1_sameSnapshot (bytes : List UInt8) : SameSnapshot (Leanux.WG.ip6EcnSetEct1 bytes) := by
  frame_same [Leanux.WG.ip6EcnSetEct1] using []

theorem ip6EcnSetEct1_spec (P : Snapshot → Prop) (bytes : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.ip6EcnSetEct1 bytes
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (ip6EcnSetEct1_sameSnapshot bytes).wp P

theorem ipEcnSetCe_sameSnapshot (bytes : List UInt8) : SameSnapshot (Leanux.WG.ipEcnSetCe bytes) := by
  frame_same [Leanux.WG.ipEcnSetCe] using []

theorem ipEcnSetCe_spec (P : Snapshot → Prop) (bytes : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.ipEcnSetCe bytes
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (ipEcnSetCe_sameSnapshot bytes).wp P

theorem ipEcnSetEct1_sameSnapshot (bytes : List UInt8) : SameSnapshot (Leanux.WG.ipEcnSetEct1 bytes) := by
  frame_same [Leanux.WG.ipEcnSetEct1] using []

theorem ipEcnSetEct1_spec (P : Snapshot → Prop) (bytes : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.ipEcnSetEct1 bytes
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (ipEcnSetEct1_sameSnapshot bytes).wp P

theorem keepKeyFresh_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.keepKeyFresh pid) := by
  frame_same [Leanux.WG.keepKeyFresh] using [branchExpired_spec, getKeypair_live_spec, getPeer_spec, sendQueuedHandshakeInitiation_spec]

theorem keepKeyFresh_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.keepKeyFresh pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (keepKeyFresh_sameSnapshot pid).wp P

theorem keepKeyFreshRx_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.keepKeyFreshRx pid) := by
  frame_same [Leanux.WG.keepKeyFreshRx] using [branchExpired_spec, getKeypair_live_spec, getPeer_spec, sendQueuedHandshakeInitiation_spec, setPeer_spec]

theorem keepKeyFreshRx_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.keepKeyFreshRx pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (keepKeyFreshRx_sameSnapshot pid).wp P

theorem lookupSrc_sameSnapshot (protocol : Nat) (bytes : List UInt8) : SameSnapshot (Leanux.WG.lookupSrc protocol bytes) := by
  frame_same [Leanux.WG.lookupSrc] using [getDev_spec, lookup_spec]

theorem lookupSrc_spec (P : Snapshot → Prop) (protocol : Nat) (bytes : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.lookupSrc protocol bytes
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (lookupSrc_sameSnapshot protocol bytes).wp P

theorem makeCookie_sameSnapshot (src : SkbSource) : SameSnapshot (Leanux.WG.makeCookie src) := by
  exact sameSnapshot_of_sameCookieKernel (Framing.makeCookie_sameCookieKernel src)

theorem makeCookie_spec (P : Snapshot → Prop) (src : SkbSource) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.makeCookie src
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (makeCookie_sameSnapshot src).wp P

theorem netDevices_sameSnapshot  : SameSnapshot (Leanux.WG.netDevices ) := by
  frame_same [Leanux.WG.netDevices] using []

theorem netDevices_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.netDevices
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (netDevices_sameSnapshot ).wp P

theorem ratelimiterAllow_sameSnapshot (src : SkbSource) : SameSnapshot (Leanux.WG.ratelimiterAllow src) := by
  exact sameSnapshot_of_sameCookieKernel (Framing.ratelimiterAllow_sameCookieKernel src)

theorem ratelimiterAllow_spec (P : Snapshot → Prop) (src : SkbSource) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.ratelimiterAllow src
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (ratelimiterAllow_sameSnapshot src).wp P

theorem runFlushedClearWork_ordinary (pid : PeerId) : OrdinaryAction (Leanux.WG.runFlushedClearWork pid) := by
  frame_ordinary [Leanux.WG.runFlushedClearWork] using [hidden_snapshot_spec] ordinary [queuedExpiredZeroKeyMaterial_spec]

theorem runFlushedClearWork_spec (P : Snapshot → Prop) (hp : Stable P) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.runFlushedClearWork pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (runFlushedClearWork_ordinary pid).wp P hp

theorem runFlushedSendWork_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.runFlushedSendWork pid) := by
  frame_same [Leanux.WG.runFlushedSendWork] using [getPeer_spec, handshakeSendWorker_spec, hidden_snapshot_spec, setPeer_spec]

theorem runFlushedSendWork_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.runFlushedSendWork pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (runFlushedSendWork_sameSnapshot pid).wp P

theorem sendBufferAsReplyToSkb_sameSnapshot (src : SkbSource) (buffer : List UInt8) : SameSnapshot (Leanux.WG.sendBufferAsReplyToSkb src buffer) := by
  frame_same [Leanux.WG.sendBufferAsReplyToSkb] using [endpointFromSkb_spec, hiddenAlloc_snapshot_spec, send4_spec, send6_spec]

theorem sendBufferAsReplyToSkb_spec (P : Snapshot → Prop) (src : SkbSource) (buffer : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.sendBufferAsReplyToSkb src buffer
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sendBufferAsReplyToSkb_sameSnapshot src buffer).wp P

theorem sendSkbToPeer_sameSnapshot (pid : PeerId) (bytes : List UInt8) (ds : Nat) : SameSnapshot (Leanux.WG.sendSkbToPeer pid bytes ds) := by
  frame_same [Leanux.WG.sendSkbToPeer] using [getPeer_spec, send4_spec, send6_spec, setPeer_spec]

theorem sendSkbToPeer_spec (P : Snapshot → Prop) (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.sendSkbToPeer pid bytes ds
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sendSkbToPeer_sameSnapshot pid bytes ds).wp P

theorem setAllowedip_sameSnapshot (pid : PeerId) (ip : AllowedIpAttrs) : SameSnapshot (Leanux.WG.setAllowedip pid ip) := by
  frame_same [Leanux.WG.setAllowedip] using [insert_spec]

theorem setAllowedip_spec (P : Snapshot → Prop) (pid : PeerId) (ip : AllowedIpAttrs) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.setAllowedip pid ip
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setAllowedip_sameSnapshot pid ip).wp P

theorem setPort_sameSnapshot (port : Nat) : SameSnapshot (Leanux.WG.setPort port) := by
  frame_same [Leanux.WG.setPort] using [clearPeerEndpointSrc_spec, getDev_spec, socketInit_spec]

theorem setPort_spec (P : Snapshot → Prop) (port : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.setPort port
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setPort_sameSnapshot port).wp P

theorem updateRxStats_sameSnapshot (pid : PeerId) (len : Nat) : SameSnapshot (Leanux.WG.updateRxStats pid len) := by
  frame_same [Leanux.WG.updateRxStats] using [getPeer_spec, setPeer_spec]

theorem updateRxStats_spec (P : Snapshot → Prop) (pid : PeerId) (len : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.updateRxStats pid len
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (updateRxStats_sameSnapshot pid len).wp P

theorem validateHeaderLen_sameSnapshot (msg : List UInt8) : SameSnapshot (Leanux.WG.validateHeaderLen msg) := by
  frame_same [Leanux.WG.validateHeaderLen] using []

theorem validateHeaderLen_spec (P : Snapshot → Prop) (msg : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.validateHeaderLen msg
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (validateHeaderLen_sameSnapshot msg).wp P

theorem consumeData_ordinary (msg : List UInt8) (src : SkbSource) (ds : Nat) : OrdinaryAction (Leanux.WG.consumeData msg src ds) := by
  frame_ordinary [Leanux.WG.consumeData] using [freeRxSkb_spec, enqueuePerDeviceAndPeerRx_spec, enqueuePerPeerRx_pure_spec, getPeer_spec, indexLookup_spec, keypairGetCurrent_spec, keypairGet_snapshot_spec, peerPut_spec, newRxSkb_spec] ordinary [keypairPut_ordinary_spec]

theorem consumeData_spec (P : Snapshot → Prop) (hp : Stable P) (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.consumeData msg src ds
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (consumeData_ordinary msg src ds).wp P hp

theorem cookieMessageCreate_sameSnapshot (index : Nat) (src : SkbSource) (mac1 : List UInt8) : SameSnapshot (Leanux.WG.cookieMessageCreate index src mac1) := by
  exact sameSnapshot_of_sameCookieKernel (Framing.cookieMessageCreate_sameCookieKernel index src mac1)

theorem cookieMessageCreate_spec (P : Snapshot → Prop) (index : Nat) (src : SkbSource) (mac1 : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.cookieMessageCreate index src mac1
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (cookieMessageCreate_sameSnapshot index src mac1).wp P

theorem cookieValidatePacket_sameSnapshot (msg : List UInt8) (src : SkbSource) (checkCookie : Bool) : SameSnapshot (Leanux.WG.cookieValidatePacket msg src checkCookie) := by
  exact sameSnapshot_of_sameCookieKernel (Framing.cookieValidatePacket_sameCookieKernel msg src checkCookie)

theorem cookieValidatePacket_spec (P : Snapshot → Prop) (msg : List UInt8) (src : SkbSource) (checkCookie : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.cookieValidatePacket msg src checkCookie
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (cookieValidatePacket_sameSnapshot msg src checkCookie).wp P

theorem createDataDone_sameSnapshot (pid : PeerId) (item : List SkbId) : SameSnapshot (Leanux.WG.createDataDone pid item) := by
  frame_same [Leanux.WG.createDataDone] using [keepKeyFresh_spec, sendSkbToPeer_spec, timersAnyAuthenticatedPacketSent_spec, timersDataSent_spec, timersTraversal_spec, getTxSkb_spec]

theorem createDataDone_spec (P : Snapshot → Prop) (pid : PeerId) (item : List SkbId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.createDataDone pid item
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (createDataDone_sameSnapshot pid item).wp P

theorem drainHandshakeSendWq_ordinary (upTo : Option PeerId) : OrdinaryAction (Leanux.WG.drainHandshakeSendWq upTo) := by
  frame_ordinary [Leanux.WG.drainHandshakeSendWq] using [getDev_spec, peekUnit_spec, resolveUnit_spec, runFlushedSendWork_spec] ordinary [runFlushedClearWork_spec]

theorem drainHandshakeSendWq_spec (P : Snapshot → Prop) (hp : Stable P) (upTo : Option PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.drainHandshakeSendWq upTo
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (drainHandshakeSendWq_ordinary upTo).wp P hp

theorem getPeerDump_sameSnapshot (pid : PeerId) (ctx : DumpCtx) (skb : NlSkb) :
    SameSnapshot (Leanux.WG.getPeerDump pid ctx skb) := by
  unfold Leanux.WG.getPeerDump
  repeat' first
    | (snapshot_head Leanux.WG.getPeer; with_reducible exact @getPeer_sameSnapshot _)
    | (snapshot_head Leanux.WG.getDev; with_reducible exact @getDev_sameSnapshot)
    | (snapshot_head Leanux.WG.getNode; with_reducible exact @getNode_sameSnapshot _)
    | (snapshot_head Leanux.WG.readNode; with_reducible exact @readNode_sameSnapshot _)
    | (snapshot_head Leanux.WG.getAllowedips; with_reducible exact @getAllowedips_sameSnapshot _ _ _ _)
    | (snapshot_head Leanux.branch; with_reducible exact @branch_sameSnapshot _ _)
    | (snapshot_head Leanux.invariant; with_reducible exact @invariant_sameSnapshot _ _)
    | dump_snapshot_step

theorem getPeerDump_spec (P : Snapshot → Prop) (pid : PeerId) (ctx : DumpCtx) (skb : NlSkb) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.getPeerDump pid ctx skb
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getPeerDump_sameSnapshot pid ctx skb).wp P

theorem inetEcnSet_sameSnapshot (ce : Bool) (protocol : Nat) (bytes : List UInt8) : SameSnapshot (Leanux.WG.inetEcnSet ce protocol bytes) := by
  frame_same [Leanux.WG.inetEcnSet] using [ip6EcnSetCe_spec, ip6EcnSetEct1_spec, ipEcnSetCe_spec, ipEcnSetEct1_spec]

theorem inetEcnSet_spec (P : Snapshot → Prop) (ce : Bool) (protocol : Nat) (bytes : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.inetEcnSet ce protocol bytes
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (inetEcnSet_sameSnapshot ce protocol bytes).wp P

theorem lookupInterface_sameSnapshot (ref : DeviceRef) : SameSnapshot (Leanux.WG.lookupInterface ref) := by
  frame_same [Leanux.WG.lookupInterface] using [netDevices_spec]

theorem lookupInterface_spec (P : Snapshot → Prop) (ref : DeviceRef) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.lookupInterface ref
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (lookupInterface_sameSnapshot ref).wp P

theorem prepareSkbHeader_sameSnapshot (msg : List UInt8) : SameSnapshot (Leanux.WG.prepareSkbHeader msg) := by
  frame_same [Leanux.WG.prepareSkbHeader] using [validateHeaderLen_spec]

theorem prepareSkbHeader_spec (P : Snapshot → Prop) (msg : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.prepareSkbHeader msg
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (prepareSkbHeader_sameSnapshot msg).wp P

theorem inetEcnDecapsulate_sameSnapshot (protocol outer : Nat) (bytes : List UInt8) : SameSnapshot (Leanux.WG.inetEcnDecapsulate protocol outer bytes) := by
  frame_same [Leanux.WG.inetEcnDecapsulate] using [inetEcnSet_spec]

theorem inetEcnDecapsulate_spec (P : Snapshot → Prop) (protocol outer : Nat) (bytes : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.inetEcnDecapsulate protocol outer bytes
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (inetEcnDecapsulate_sameSnapshot protocol outer bytes).wp P

theorem packetReceive_ordinary (msg : List UInt8) (src : SkbSource) : OrdinaryAction (Leanux.WG.packetReceive msg src) := by
  frame_ordinary [Leanux.WG.packetReceive] using [cpumaskNextOnline_spec, getDev_spec, ipTunnelGetDsfield_spec, prepareSkbHeader_spec, queueDeviceWork_spec] ordinary [consumeData_spec]

theorem packetReceive_spec (P : Snapshot → Prop) (hp : Stable P) (msg : List UInt8) (src : SkbSource) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.packetReceive msg src
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (packetReceive_ordinary msg src).wp P hp

theorem sendHandshakeCookie_sameSnapshot (msg : List UInt8) (src : SkbSource) : SameSnapshot (Leanux.WG.sendHandshakeCookie msg src) := by
  frame_same [Leanux.WG.sendHandshakeCookie] using [cookieMessageCreate_spec, sendBufferAsReplyToSkb_spec]

theorem sendHandshakeCookie_spec (P : Snapshot → Prop) (msg : List UInt8) (src : SkbSource) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.sendHandshakeCookie msg src
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sendHandshakeCookie_sameSnapshot msg src).wp P

theorem timersStop_ordinary (pid : PeerId) : OrdinaryAction (Leanux.WG.timersStop pid) := by
  frame_ordinary [Leanux.WG.timersStop] using [delTimer_spec, getDev_spec] ordinary [drainHandshakeSendWq_spec]

theorem timersStop_spec (P : Snapshot → Prop) (hp : Stable P) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.timersStop pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (timersStop_ordinary pid).wp P hp

theorem wgGetDeviceDone_sameSnapshot (ctx : DumpCtx) : SameSnapshot (WG.wgGetDeviceDone ctx) := by
  frame_same [WG.wgGetDeviceDone] using [peerPut_spec]

theorem wgGetDeviceDone_spec (P : Snapshot → Prop) (ctx : DumpCtx) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ WG.wgGetDeviceDone ctx
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wgGetDeviceDone_sameSnapshot ctx).wp P

theorem wgGetDeviceDump_sameSnapshot (ctx : DumpCtx) (prevSeq : Nat) (skb : NlSkb) :
    SameSnapshot (WG.wgGetDeviceDump ctx prevSeq skb) := by
  unfold Leanux.WG.wgGetDeviceDump
  repeat' first
    | (snapshot_head Leanux.WG.getDev; with_reducible exact @getDev_sameSnapshot)
    | (snapshot_head Leanux.WG.getPeer; with_reducible exact @getPeer_sameSnapshot _)
    | (snapshot_head Leanux.WG.getPeerDump; with_reducible exact @getPeerDump_sameSnapshot _ _ _)
    | (snapshot_head Leanux.WG.requireNotPending; with_reducible exact @requireNotPending_sameSnapshot _ _)
    | (snapshot_head Leanux.WG.peerGet; with_reducible exact @peerGet_sameSnapshot _)
    | (snapshot_head Leanux.WG.peerPut; with_reducible exact @peerPut_sameSnapshot _)
    | (snapshot_head Leanux.branch; with_reducible exact @branch_sameSnapshot _ _)
    | (snapshot_head Leanux.invariant; with_reducible exact @invariant_sameSnapshot _ _)
    | (snapshot_head Leanux.unsupported; with_reducible exact @unsupported_sameSnapshot _ _)
    | dump_snapshot_step

theorem wgGetDeviceDump_spec (P : Snapshot → Prop) (ctx : DumpCtx) (prevSeq : Nat) (skb : NlSkb) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ WG.wgGetDeviceDump ctx prevSeq skb
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wgGetDeviceDump_sameSnapshot ctx prevSeq skb).wp P

theorem getNlSock_sameSnapshot (fd : Nat) : SameSnapshot (WG.getNlSock fd) := by
  frame_same [WG.getNlSock] using []

theorem getNlSock_spec (P : Snapshot → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ WG.getNlSock fd
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getNlSock_sameSnapshot fd).wp P

theorem setNlSock_sameSnapshot (fd : Nat) (sock : NlSock) : SameSnapshot (WG.setNlSock fd sock) := by
  unfold WG.setNlSock
  apply snapshot_modifyK
  intro k
  split <;> exact ⟨rfl, rfl⟩

theorem setNlSock_spec (P : Snapshot → Prop) (fd : Nat) (sock : NlSock) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ WG.setNlSock fd sock
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setNlSock_sameSnapshot fd sock).wp P

theorem netlinkDump_sameSnapshot (fd : Nat) : SameSnapshot (WG.netlinkDump fd) := by
  frame_same [WG.netlinkDump] using [getNlSock_spec, setNlSock_spec,
    wgGetDeviceDump_spec, wgGetDeviceDone_spec]

theorem netlinkDump_spec (P : Snapshot → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ WG.netlinkDump fd
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (netlinkDump_sameSnapshot fd).wp P

theorem netlinkDumpStart_sameSnapshot (fd : Nat) (ref : DeviceRef) :
    SameSnapshot (WG.netlinkDumpStart fd ref) := by
  frame_same [WG.netlinkDumpStart] using [getNlSock_spec, setNlSock_spec,
    lookupInterface_spec, netlinkDump_spec]

theorem netlinkDumpStart_spec (P : Snapshot → Prop) (fd : Nat) (ref : DeviceRef) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ WG.netlinkDumpStart fd ref
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (netlinkDumpStart_sameSnapshot fd ref).wp P

theorem netlinkRecvmsg_sameSnapshot (fd : Nat) : SameSnapshot (WG.netlinkRecvmsg fd) := by
  frame_same [WG.netlinkRecvmsg] using [getNlSock_spec, setNlSock_spec, netlinkDump_spec]

theorem netlinkRecvmsg_spec (P : Snapshot → Prop) (fd : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ WG.netlinkRecvmsg fd
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (netlinkRecvmsg_sameSnapshot fd).wp P

theorem coalesce_sameSnapshot (messages : List NlMessage) : SameSnapshot (WG.coalesce messages) := by
  frame_same [WG.coalesce] using []

theorem coalesce_spec (P : Snapshot → Prop) (messages : List NlMessage) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ WG.coalesce messages
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (coalesce_sameSnapshot messages).wp P

theorem wgGetDevice_sameSnapshot (ref : DeviceRef) : SameSnapshot (Leanux.WG.wgGetDevice ref) := by
  frame_same [Leanux.WG.wgGetDevice] using [netlinkDumpStart_spec, netlinkRecvmsg_spec, coalesce_spec]

theorem wgGetDevice_spec (P : Snapshot → Prop) (ref : DeviceRef) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.wgGetDevice ref
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wgGetDevice_sameSnapshot ref).wp P

theorem consumeDataDone_ordinary (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) : OrdinaryAction (Leanux.WG.consumeDataDone pid pkt endpoint) := by
  frame_ordinary [Leanux.WG.consumeDataDone] using [dishonest_spec, inetEcnDecapsulate_spec, keepKeyFreshRx_spec, lookupSrc_spec, peerPut_spec, setPeerEndpoint_spec, timersAnyAuthenticatedPacketReceived_spec, timersDataReceived_spec, timersHandshakeComplete_spec, timersTraversal_spec, updateRxStats_spec] ordinary [receivedWithKeypair_spec, sendStagedPackets_spec]

theorem consumeDataDone_spec (P : Snapshot → Prop) (hp : Stable P) (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.consumeDataDone pid pkt endpoint
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (consumeDataDone_ordinary pid pkt endpoint).wp P hp

theorem peerRemoveAfterDead_ordinary (pid : PeerId) : OrdinaryAction (Leanux.WG.peerRemoveAfterDead pid) := by
  frame_ordinary [Leanux.WG.peerRemoveAfterDead] using [getDev_spec, getPeer_spec, peerPut_spec] ordinary [drainHandshakeSendWq_spec, keypairsClear_spec, timersStop_spec]

theorem peerRemoveAfterDead_spec (P : Snapshot → Prop) (hp : Stable P) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.peerRemoveAfterDead pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (peerRemoveAfterDead_ordinary pid).wp P hp

theorem receiveHandshakePacket_ordinary (msg : List UInt8) (src : SkbSource) : OrdinaryAction (Leanux.WG.receiveHandshakePacket msg src) := by
  unfold Leanux.WG.receiveHandshakePacket
  repeat' first
    | intro_forall
    | (ordinary_head Leanux.WG.beginSession; with_reducible exact @beginSession_ordinary _)
    | (ordinary_head Leanux.WG.sendHandshakeResponse; with_reducible exact @sendHandshakeResponse_ordinary _)
    | (ordinary_head Leanux.WG.sendKeepalive; with_reducible exact @sendKeepalive_ordinary _)
    | (ordinary_head Leanux.WG.consumeInitiation; refine SameSnapshot.ordinary ?_; with_reducible exact @consumeInitiation_sameSnapshot _)
    | (ordinary_head Leanux.WG.consumeResponse; refine SameSnapshot.ordinary ?_; with_reducible exact @consumeResponse_sameSnapshot _)
    | (ordinary_head Leanux.WG.cookieMessageConsume; refine SameSnapshot.ordinary ?_; with_reducible exact @cookieMessageConsume_sameSnapshot _)
    | (ordinary_head Leanux.WG.cookieValidatePacket; refine SameSnapshot.ordinary ?_; with_reducible exact @cookieValidatePacket_sameSnapshot _ _ _)
    | (ordinary_head Leanux.WG.getDev; refine SameSnapshot.ordinary ?_; with_reducible exact @getDev_sameSnapshot)
    | (ordinary_head Leanux.WG.getPeer; refine SameSnapshot.ordinary ?_; with_reducible exact @getPeer_sameSnapshot _)
    | (ordinary_head Leanux.hiddenClock64; exact (hiddenClock64_sameSnapshot _).ordinary)
    | (ordinary_head Leanux.WG.birthdateTest; exact (birthdateTest_sameSnapshot _ _).ordinary)
    | (ordinary_head Leanux.WG.branchExpired; exact (branchExpired_sameSnapshot _ _ _ _).ordinary)
    | (ordinary_head Leanux.hiddenClock; refine SameSnapshot.ordinary ?_; with_reducible exact @hiddenClock_sameSnapshot _)
    | (ordinary_head Leanux.WG.birthdateHasExpired; exact (birthdateHasExpired_sameSnapshot _ _).ordinary)
    | (ordinary_head Leanux.WG.peerPut; refine SameSnapshot.ordinary ?_; with_reducible exact @peerPut_sameSnapshot _)
    | (ordinary_head Leanux.WG.sendHandshakeCookie; refine SameSnapshot.ordinary ?_; with_reducible exact @sendHandshakeCookie_sameSnapshot _ _)
    | (ordinary_head Leanux.WG.setPeerEndpointFromSkb; refine SameSnapshot.ordinary ?_; with_reducible exact @setPeerEndpointFromSkb_sameSnapshot _ _)
    | (ordinary_head Leanux.WG.setPeer; refine SameSnapshot.ordinary ?_; with_reducible exact @setPeer_sameSnapshot _ _)
    | (ordinary_head Leanux.WG.timersAnyAuthenticatedPacketReceived; refine SameSnapshot.ordinary ?_; with_reducible exact @timersAnyAuthenticatedPacketReceived_sameSnapshot _)
    | (ordinary_head Leanux.WG.timersHandshakeComplete; refine SameSnapshot.ordinary ?_; with_reducible exact @timersHandshakeComplete_sameSnapshot _ _)
    | (ordinary_head Leanux.WG.timersSessionDerived; refine SameSnapshot.ordinary ?_; with_reducible exact @timersSessionDerived_sameSnapshot _)
    | (ordinary_head Leanux.WG.timersTraversal; refine SameSnapshot.ordinary ?_; with_reducible exact @timersTraversal_sameSnapshot _)
    | (ordinary_head Leanux.branch; refine SameSnapshot.ordinary ?_; with_reducible exact @branch_sameSnapshot _ _)
    | (ordinary_head Leanux.branchCmp; refine SameSnapshot.ordinary ?_; with_reducible exact @branchCmp_sameSnapshot _ _ _ _)
    | (ordinary_head Leanux.branchCmpExcluded; refine SameSnapshot.ordinary ?_; with_reducible exact @branchCmpExcluded_sameSnapshot _ _ _)
    | (ordinary_head Leanux.invariant; refine SameSnapshot.ordinary ?_; with_reducible exact @invariant_sameSnapshot _ _)
    | (ordinary_head Leanux.unsupported; refine SameSnapshot.ordinary ?_; with_reducible exact @unsupported_sameSnapshot _ _)
    | ordinary_step

theorem receiveHandshakePacket_spec (P : Snapshot → Prop) (hp : Stable P) (msg : List UInt8) (src : SkbSource) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.receiveHandshakePacket msg src
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (receiveHandshakePacket_ordinary msg src).wp P hp

theorem wgReceive_ordinary (msg : List UInt8) (src : SkbSource) : OrdinaryAction (Leanux.WG.wgReceive msg src) := by
  frame_ordinary [Leanux.WG.wgReceive] using [] ordinary [packetReceive_spec]

theorem wgReceive_spec (P : Snapshot → Prop) (hp : Stable P) (msg : List UInt8) (src : SkbSource) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.wgReceive msg src
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wgReceive_ordinary msg src).wp P hp

theorem peerRemove_ordinary (peer : Option PeerId) : OrdinaryAction (Leanux.WG.peerRemove peer) := by
  frame_ordinary [Leanux.WG.peerRemove] using [peerMakeDead_spec] ordinary [peerRemoveAfterDead_spec]

theorem peerRemove_spec (P : Snapshot → Prop) (hp : Stable P) (peer : Option PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.peerRemove peer
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (peerRemove_ordinary peer).wp P hp

theorem peerRemoveAll_ordinary  : OrdinaryAction (Leanux.WG.peerRemoveAll ) := by
  frame_ordinary [Leanux.WG.peerRemoveAll] using [free_spec, getDev_spec, peerMakeDead_spec] ordinary [peerRemoveAfterDead_spec]

theorem peerRemoveAll_spec (P : Snapshot → Prop) (hp : Stable P)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.peerRemoveAll
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (peerRemoveAll_ordinary ).wp P hp

end Leanux.Proofs.WG.Keypairs.WGMore
