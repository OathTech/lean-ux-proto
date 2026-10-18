import Leanux.Proofs.Framing.WGReceiveHeaders
import Leanux.Proofs.WG.Keypairs.Frames.WGBase

namespace Leanux.Proofs.WG.Keypairs.WGTransitions
open Leanux Leanux.WG Std.Do Leanux.Proofs.WG.Keypairs Leanux.Proofs.WG.Keypairs.WGFrames

set_option pp.structureInstances false
set_option maxHeartbeats 800000

open Lean Meta Elab Tactic

/-- Apply a checked native frame or ordinary relation at its actual action head. -/
elab "transition_fact " n:ident : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``OrdinaryAction || target.isAppOf ``Lifetimes.ProjectedAction do
    throwError "not an ordinary action"
  let action := target.getAppArgs.back! |>.consumeMData |>.headBeta
  let proof ← Lean.Elab.Term.elabTerm n none
  let proofType ← Lean.instantiateMVars (← Lean.Meta.inferType proof)
  let (args, _, conclusion) ← Lean.Meta.forallMetaTelescope proofType
  let conclusion ← Lean.instantiateMVars conclusion
  unless conclusion.isAppOf ``SameSnapshot || conclusion.isAppOf ``Framing.SameView ||
      conclusion.isAppOf ``OrdinaryAction || conclusion.isAppOf ``Lifetimes.ProjectedAction do
    throwError "not a native frame or ordinary relation"
  let framed := conclusion.getAppArgs.back! |>.consumeMData |>.headBeta
  let sameHead := match action.getAppFn, framed.getAppFn with
    | .const a _, .const b _ => a == b
    | a, b => a == b
  unless sameHead do throwError "different source action for {n}: {action.getAppFn} versus {framed.getAppFn}"
  let framedArgs := framed.getAppArgs
  let actualArgs := action.getAppArgs
  unless framedArgs.size == actualArgs.size do throwError "different source arity"
  for (lhs, rhs) in framedArgs.zip actualArgs do
    unless ← Lean.Meta.withReducible (Lean.Meta.isDefEq lhs rhs) do
      throwError "different source argument for {n}: {lhs} versus {rhs}"
  let proof := Lean.mkAppN proof args
  let proof ← if conclusion.isAppOf ``SameSnapshot || conclusion.isAppOf ``Framing.SameView then
    Lean.Meta.mkAppM ``SameView.ordinary #[proof]
    else pure proof
  goal.assign proof
  let mut pending := []
  for arg in args do
    if arg.isMVar then
      let id := arg.mvarId!
      unless ← id.isAssigned do pending := pending ++ [id]
  Lean.Elab.Tactic.replaceMainGoal pending

macro "transition_ordinary" "[" fs:ident,* "]" "using" "[" facts:ident,* "]" : tactic => do
  let mut use ← `(tactic| fail "no named ordinary frame")
  for fact in facts.getElems.reverse do
    use ← `(tactic| first | transition_fact $fact | ($use:tactic))
  let mut component ← `(tactic| fail "not a component head")
  for name in #[``Leanux.branch,``Leanux.branchCmp,``Leanux.invariant,``Leanux.unsupported,
      ``Leanux.hidden,``Leanux.hiddenAlloc,``Leanux.hiddenClock64,``Leanux.skipCut,``Leanux.getAmbient,
      ``Leanux.modifyAmbient,``Leanux.WG.orM,``Leanux.WG.andM,
      ``Leanux.WG.getTxSkb,``Leanux.WG.setTxSkb,``Leanux.WG.freeTxSkb,
      ``Leanux.WG.newRxSkb,``Leanux.WG.getRxSkb,``Leanux.WG.setRxSkb,``Leanux.WG.freeRxSkb,
      ``Leanux.WG.liftSkb,
      ``MonadLiftT.monadLift,``MonadLift.monadLift,``Leanux.WG.modifyDev,
      ``get,``modify,``throw,``MonadExceptOf.throw,``liftM].reverse do
    let n := Lean.mkCIdent name
    component ← `(tactic| first
      | (ordinary_head $n; apply SameView.ordinary; snapshot_source [] using [])
      | ($component:tactic))
  let expand ← if fs.getElems.isEmpty then `(tactic| skip) else `(tactic| unfold $fs:ident*)
  `(tactic|
    ($expand:tactic
     repeat' first
       | ordinary_join_let
       | ordinary_join_use
       | ($use:tactic)
       | ($component:tactic)
       | contradiction
       | keypairs_intro_forall
       | (ordinary_head Pure.pure; exact ordinary_pure _)
       | (ordinary_head Bind.bind; refine ordinary_bind ?_ ?_)
       | (ordinary_head ite; refine ordinary_ite _ ?_ ?_)
       | (ordinary_head ForIn.forIn; first | apply ordinary_forIn | apply ordinary_range)
       | (ordinary_head StateT.map; apply ordinary_map)
       | (ordinary_head Functor.discard; apply ordinary_discard)
       | ordinary_head_reduce
       | ordinary_head_match))


theorem Packet_protocol_sameSnapshot (pkt : Packet) : SameSnapshot (Leanux.WG.Packet.protocol pkt) := by
  snapshot_source [Leanux.WG.Packet.protocol] using []

theorem Packet_protocol_spec (P : Snapshot → Prop) (pkt : Packet) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.Packet.protocol pkt
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (Packet_protocol_sameSnapshot pkt).wp P

theorem addMacToPacket_sameSnapshot (pid : PeerId) (msg : List UInt8) : SameSnapshot (Leanux.WG.addMacToPacket pid msg) := by
  snapshot_source [Leanux.WG.addMacToPacket] using [branchExpired_sameSnapshot, getPeer_sameSnapshot, setPeer_sameSnapshot]

theorem addMacToPacket_spec (P : Snapshot → Prop) (pid : PeerId) (msg : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.addMacToPacket pid msg
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (addMacToPacket_sameSnapshot pid msg).wp P

theorem cpumaskChooseOnline_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.cpumaskChooseOnline pid) := by
  snapshot_source [Leanux.WG.cpumaskChooseOnline] using [getPeer_sameSnapshot, setPeer_sameSnapshot]

theorem cpumaskChooseOnline_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.cpumaskChooseOnline pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (cpumaskChooseOnline_sameSnapshot pid).wp P

theorem cpumaskNextOnlineFrom_sameSnapshot (lastCpu : Int) : SameSnapshot (Leanux.WG.cpumaskNextOnlineFrom lastCpu) := by
  snapshot_source [Leanux.WG.cpumaskNextOnlineFrom] using []

theorem cpumaskNextOnlineFrom_spec (P : Snapshot → Prop) (lastCpu : Int) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.cpumaskNextOnlineFrom lastCpu
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (cpumaskNextOnlineFrom_sameSnapshot lastCpu).wp P

theorem endpointFromSkb_sameSnapshot (src : SkbSource) : SameSnapshot (Leanux.WG.endpointFromSkb src) := by
  snapshot_source [Leanux.WG.endpointFromSkb] using []

theorem endpointFromSkb_spec (P : Snapshot → Prop) (src : SkbSource) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.endpointFromSkb src
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (endpointFromSkb_sameSnapshot src).wp P

theorem expireCurrentPeerKeypairs_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.expireCurrentPeerKeypairs pid) := by
  let invalidate (kp : KeypairId) : WG.M Unit := do
    let k ← getKeypair kp
    setKeypair kp {k with sending := {k.sending with isValid := false}}
  have hi (kp : KeypairId) : SameSnapshot (invalidate kp) := by
    apply sameSnapshot_of_wp
    intro initial
    unfold invalidate
    refine Std.Do.Triple.bind _ _ (getKeypair_live_spec (fun s => s = initial) kp) ?_
    intro key
    exact setKeypair_live_spec (fun s => s = initial) kp
      {key with sending := {key.sending with isValid := false}}
  change SameSnapshot (do
    requireNotPending pid "clearing the handshake"
    handshakeClear pid
    resetLastSentHandshake pid
    let p ← getPeer pid
    if ← branch .expireNextKeypair p.keypairNext.isSome then
      let some kp := p.keypairNext | invariant "unreachable"
      invalidate kp
    if ← branch .expireCurrentKeypair p.keypairCurrent.isSome then
      let some kp := p.keypairCurrent | invariant "unreachable"
      invalidate kp)
  snapshot_source [handshakeClear] using [ownerPeerDeref_sameSnapshot,
    ownerPeerWord_sameSnapshot, getPeer_sameSnapshot, handshakeZero_sameSnapshot,
    requireNotPending_sameSnapshot, resetLastSentHandshake_sameSnapshot]
  all_goals exact hi _

theorem expireCurrentPeerKeypairs_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.expireCurrentPeerKeypairs pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (expireCurrentPeerKeypairs_sameSnapshot pid).wp P

theorem handshakeClear_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.handshakeClear pid) := by
  snapshot_source [Leanux.WG.handshakeClear] using [ownerPeerDeref_sameSnapshot, ownerPeerWord_sameSnapshot, handshakeZero_sameSnapshot]

theorem handshakeClear_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.handshakeClear pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (handshakeClear_sameSnapshot pid).wp P

theorem ipTunnelGetDsfield_sameSnapshot (protocol : Nat) (hdr : List UInt8) : SameSnapshot (Leanux.WG.ipTunnelGetDsfield protocol hdr) := by
  exact (Framing.ipTunnelGetDsfield_sameWGWorld protocol hdr).factor snapshot

theorem ipTunnelGetDsfield_spec (P : Snapshot → Prop) (protocol : Nat) (hdr : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.ipTunnelGetDsfield protocol hdr
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (ipTunnelGetDsfield_sameSnapshot protocol hdr).wp P

theorem jitterBelowRekeyTimeout_sameSnapshot (site : HiddenSite) : SameSnapshot (Leanux.WG.jitterBelowRekeyTimeout site) :=
  (Framing.jitterBelowRekeyTimeout_sameWGWorld site).factor snapshot

theorem jitterBelowRekeyTimeout_spec (P : Snapshot → Prop) (site : HiddenSite) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.jitterBelowRekeyTimeout site
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (jitterBelowRekeyTimeout_sameSnapshot site).wp P

theorem kdf_sameSnapshot (second third : Bool) (chainingKey data : List UInt8) : SameSnapshot (Leanux.WG.kdf second third chainingKey data) :=
  (Framing.kdf_sameWGWorld second third chainingKey data).factor snapshot

theorem kdf_spec (P : Snapshot → Prop) (second third : Bool) (chainingKey data : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.kdf second third chainingKey data
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (kdf_sameSnapshot second third chainingKey data).wp P

theorem kdfOut_sameSnapshot (outs : List (List UInt8)) (i : Nat) : SameSnapshot (Leanux.WG.kdfOut outs i) :=
  (Framing.kdfOut_sameWGWorld outs i).factor snapshot

theorem kdfOut_spec (P : Snapshot → Prop) (outs : List (List UInt8)) (i : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.kdfOut outs i
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (kdfOut_sameSnapshot outs i).wp P

theorem keypairGetNull_sameSnapshot  : SameSnapshot (Leanux.WG.keypairGetNull ) := by
  snapshot_source [Leanux.WG.keypairGetNull] using []

theorem keypairGetNull_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.keypairGetNull
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (keypairGetNull_sameSnapshot ).wp P

theorem messageDecrypt_sameSnapshot (sealed key hash : List UInt8) : SameSnapshot (Leanux.WG.messageDecrypt sealed key hash) :=
  (Framing.messageDecrypt_sameWGWorld sealed key hash).factor snapshot

theorem messageDecrypt_spec (P : Snapshot → Prop) (sealed key hash : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.messageDecrypt sealed key hash
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (messageDecrypt_sameSnapshot sealed key hash).wp P

theorem modPeerTimerGuard_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.modPeerTimerGuard pid) := by
  snapshot_source [Leanux.WG.modPeerTimerGuard] using [getDev_sameSnapshot, getPeer_sameSnapshot]

theorem modPeerTimerGuard_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.modPeerTimerGuard pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (modPeerTimerGuard_sameSnapshot pid).wp P

theorem purgeStagedPackets_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.purgeStagedPackets pid) := by
  snapshot_source [Leanux.WG.purgeStagedPackets] using [getPeer_sameSnapshot, setPeer_sameSnapshot]

theorem purgeStagedPackets_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.purgeStagedPackets pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (purgeStagedPackets_sameSnapshot pid).wp P

theorem sendBufferToPeer_sameSnapshot (pid : PeerId) (bytes : List UInt8) : SameSnapshot (Leanux.WG.sendBufferToPeer pid bytes) := by
  snapshot_source [Leanux.WG.sendBufferToPeer] using [getPeer_sameSnapshot, send4_sameSnapshot, send6_sameSnapshot, setPeer_sameSnapshot]

theorem sendBufferToPeer_spec (P : Snapshot → Prop) (pid : PeerId) (bytes : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.sendBufferToPeer pid bytes
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sendBufferToPeer_sameSnapshot pid bytes).wp P

theorem sendQueuedHandshakeInitiation_sameSnapshot (pid : PeerId) (isRetry : Bool) : SameSnapshot (Leanux.WG.sendQueuedHandshakeInitiation pid isRetry) := by
  snapshot_source [Leanux.WG.sendQueuedHandshakeInitiation, Leanux.peekQueuedUnit, Leanux.recordQueued] using [branchExpired_sameSnapshot, getPeer_sameSnapshot, peerGet_sameSnapshot, peerPut_sameSnapshot, requireNotPending_sameSnapshot, setPeer_sameSnapshot]

theorem sendQueuedHandshakeInitiation_spec (P : Snapshot → Prop) (pid : PeerId) (isRetry : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.sendQueuedHandshakeInitiation pid isRetry
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sendQueuedHandshakeInitiation_sameSnapshot pid isRetry).wp P

theorem timersAnyAuthenticatedPacketReceived_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.timersAnyAuthenticatedPacketReceived pid) := by
  snapshot_source [Leanux.WG.timersAnyAuthenticatedPacketReceived] using [delTimer_sameSnapshot]

theorem timersAnyAuthenticatedPacketReceived_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.timersAnyAuthenticatedPacketReceived pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (timersAnyAuthenticatedPacketReceived_sameSnapshot pid).wp P

theorem timersAnyAuthenticatedPacketSent_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.timersAnyAuthenticatedPacketSent pid) := by
  snapshot_source [Leanux.WG.timersAnyAuthenticatedPacketSent] using [delTimer_sameSnapshot]

theorem timersAnyAuthenticatedPacketSent_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.timersAnyAuthenticatedPacketSent pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (timersAnyAuthenticatedPacketSent_sameSnapshot pid).wp P

theorem timersHandshakeComplete_sameSnapshot (pid : PeerId) (site : HiddenSite := .walltimeLastHandshake) : SameSnapshot (Leanux.WG.timersHandshakeComplete pid site) := by
  snapshot_source [Leanux.WG.timersHandshakeComplete] using [delTimer_sameSnapshot, getPeer_sameSnapshot, setPeer_sameSnapshot]

theorem timersHandshakeComplete_spec (P : Snapshot → Prop) (pid : PeerId) (site : HiddenSite := .walltimeLastHandshake) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.timersHandshakeComplete pid site
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (timersHandshakeComplete_sameSnapshot pid site).wp P

theorem setChain_sameSnapshot (pid : PeerId) (ck hash : List UInt8) : SameSnapshot ((pinned_const _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain) pid ck hash) := by
  snapshot_source [_private.Leanux.WG.Handshake.«0».Leanux.WG.setChain] using [getPeer_sameSnapshot, setPeer_sameSnapshot]

theorem setChain_spec (P : Snapshot → Prop) (pid : PeerId) (ck hash : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (pinned_const _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain) pid ck hash
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setChain_sameSnapshot pid ck hash).wp P

theorem modifyPeer_sameSnapshot (pid : PeerId) (f : Peer → Peer) : SameSnapshot ((pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid f) := by
  snapshot_source [_private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer] using [getPeer_sameSnapshot, setPeer_sameSnapshot]

theorem modifyPeer_spec (P : Snapshot → Prop) (pid : PeerId) (f : Peer → Peer) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (modifyPeer_sameSnapshot pid f).wp P

theorem addNewKeypair_ordinary (pid : PeerId) (newKeypair : KeypairId) : OrdinaryAction (Leanux.WG.addNewKeypair pid newKeypair) := by
  transition_ordinary [Leanux.WG.addNewKeypair] using [getKeypair_sameSnapshot, getPeer_sameSnapshot, modifyPeer_sameSnapshot, keypairPut_ordinary]

theorem addNewKeypair_spec (P : Snapshot → Prop) (hp : Stable P) (pid : PeerId) (newKeypair : KeypairId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.addNewKeypair pid newKeypair
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (addNewKeypair_ordinary pid newKeypair).wp P hp

theorem deriveKeys_sameSnapshot (kp : KeypairId) (initiator : Bool) (chainingKey : List UInt8) : SameSnapshot (Leanux.WG.deriveKeys kp initiator chainingKey) := by
  exact Leanux.Proofs.WG.Keypairs.deriveKeys_sameSnapshot kp initiator chainingKey

theorem deriveKeys_spec (P : Snapshot → Prop) (kp : KeypairId) (initiator : Bool) (chainingKey : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.deriveKeys kp initiator chainingKey
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (deriveKeys_sameSnapshot kp initiator chainingKey).wp P

theorem enqueuePerDeviceAndPeer_sameSnapshot (pid : PeerId) (item : List SkbId) : SameSnapshot (Leanux.WG.enqueuePerDeviceAndPeer pid item) := by
  snapshot_source [Leanux.WG.enqueuePerDeviceAndPeer, Leanux.queueDeviceWork] using [cpumaskNextOnlineFrom_sameSnapshot, getDev_sameSnapshot, getPeer_sameSnapshot, setPeer_sameSnapshot]

theorem enqueuePerDeviceAndPeer_spec (P : Snapshot → Prop) (pid : PeerId) (item : List SkbId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.enqueuePerDeviceAndPeer pid item
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (enqueuePerDeviceAndPeer_sameSnapshot pid item).wp P

theorem enqueuePerPeerTx_sameSnapshot (item : List SkbId) (state : PacketState) : SameSnapshot (Leanux.WG.enqueuePerPeerTx item state) := by
  snapshot_source [Leanux.WG.enqueuePerPeerTx, Leanux.peekQueuedUnit, Leanux.recordQueued] using [ownerPeerDeref_sameSnapshot, ownerPeerWord_sameSnapshot, cpumaskChooseOnline_sameSnapshot, getDev_sameSnapshot, getKeypair_sameSnapshot, getPeer_sameSnapshot, peerGet_sameSnapshot, peerPut_sameSnapshot, setPeer_sameSnapshot]

theorem enqueuePerPeerTx_spec (P : Snapshot → Prop) (item : List SkbId) (state : PacketState) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.enqueuePerPeerTx item state
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (enqueuePerPeerTx_sameSnapshot item state).wp P

theorem ipTunnelEcnEncap_sameSnapshot (pkt : Packet) : SameSnapshot (Leanux.WG.ipTunnelEcnEncap pkt) := by
  snapshot_source [Leanux.WG.ipTunnelEcnEncap] using [Packet_protocol_sameSnapshot, ipTunnelGetDsfield_sameSnapshot]

theorem ipTunnelEcnEncap_spec (P : Snapshot → Prop) (pkt : Packet) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.ipTunnelEcnEncap pkt
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (ipTunnelEcnEncap_sameSnapshot pkt).wp P

theorem keypairsClear_ordinary (pid : PeerId) : OrdinaryAction (Leanux.WG.keypairsClear pid) := by
  transition_ordinary [Leanux.WG.keypairsClear] using [getPeer_sameSnapshot, modifyPeer_sameSnapshot, keypairPut_ordinary]

theorem keypairsClear_spec (P : Snapshot → Prop) (hp : Stable P) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.keypairsClear pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (keypairsClear_ordinary pid).wp P hp

theorem messageEphemeral_sameSnapshot (copy : Bool) (e chainingKey hash : List UInt8) : SameSnapshot (Leanux.WG.messageEphemeral copy e chainingKey hash) :=
  (Framing.messageEphemeral_sameWGWorld copy e chainingKey hash).factor snapshot

theorem messageEphemeral_spec (P : Snapshot → Prop) (copy : Bool) (e chainingKey hash : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.messageEphemeral copy e chainingKey hash
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (messageEphemeral_sameSnapshot copy e chainingKey hash).wp P

theorem mixDh_sameSnapshot (key : Bool) (chainingKey priv pub : List UInt8) : SameSnapshot (Leanux.WG.mixDh key chainingKey priv pub) :=
  (Framing.mixDh_sameWGWorld key chainingKey priv pub).factor snapshot

theorem mixDh_spec (P : Snapshot → Prop) (key : Bool) (chainingKey priv pub : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.mixDh key chainingKey priv pub
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (mixDh_sameSnapshot key chainingKey priv pub).wp P

theorem mixPrecomputedDh_sameSnapshot (chainingKey precomputed : List UInt8) : SameSnapshot (Leanux.WG.mixPrecomputedDh chainingKey precomputed) :=
  (Framing.mixPrecomputedDh_sameWGWorld chainingKey precomputed).factor snapshot

theorem mixPrecomputedDh_spec (P : Snapshot → Prop) (chainingKey precomputed : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.mixPrecomputedDh chainingKey precomputed
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (mixPrecomputedDh_sameSnapshot chainingKey precomputed).wp P

theorem callerJiffies_spec (P : Snapshot → Prop) (site : HiddenSite) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ callerJiffies site
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ :=
  ((Framing.callerJiffies_sameWGWorld site).factor snapshot).wp P

theorem modPeerTimer_sameSnapshot (site : HiddenSite) (pid : PeerId) (t : PeerTimer) (delay : Nat) : SameSnapshot (Leanux.WG.modPeerTimer site pid t delay) := by
  snapshot_source [Leanux.WG.modPeerTimer] using [armTimer_sameSnapshot, modPeerTimerGuard_sameSnapshot]
  all_goals exact (Framing.callerJiffies_sameWGWorld _).factor snapshot

theorem modPeerTimer_spec (P : Snapshot → Prop) (site : HiddenSite) (pid : PeerId) (t : PeerTimer) (delay : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.modPeerTimer site pid t delay
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (modPeerTimer_sameSnapshot site pid t delay).wp P

theorem receivedWithKeypair_ordinary (pid : PeerId) (received : KeypairId) : OrdinaryAction (Leanux.WG.receivedWithKeypair pid received) := by
  transition_ordinary [Leanux.WG.receivedWithKeypair] using [getPeer_sameSnapshot, modifyPeer_sameSnapshot, keypairPut_ordinary]

theorem receivedWithKeypair_spec (P : Snapshot → Prop) (hp : Stable P) (pid : PeerId) (received : KeypairId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.receivedWithKeypair pid received
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (receivedWithKeypair_ordinary pid received).wp P hp

theorem setPeerEndpointFromSkb_sameSnapshot (pid : PeerId) (src : SkbSource) : SameSnapshot (Leanux.WG.setPeerEndpointFromSkb pid src) := by
  snapshot_source [Leanux.WG.setPeerEndpointFromSkb] using [endpointFromSkb_sameSnapshot, setPeerEndpoint_sameSnapshot]

theorem setPeerEndpointFromSkb_spec (P : Snapshot → Prop) (pid : PeerId) (src : SkbSource) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.setPeerEndpointFromSkb pid src
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setPeerEndpointFromSkb_sameSnapshot pid src).wp P

theorem timersDataSent_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.timersDataSent pid) := by
  snapshot_source [Leanux.WG.timersDataSent] using [armTimer_sameSnapshot, getPeer_sameSnapshot, jitterBelowRekeyTimeout_sameSnapshot, modPeerTimerGuard_sameSnapshot]
  all_goals exact (Framing.callerJiffies_sameWGWorld _).factor snapshot

theorem timersDataSent_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.timersDataSent pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (timersDataSent_sameSnapshot pid).wp P

theorem beginSession_ordinary (pid : PeerId) : OrdinaryAction (Leanux.WG.beginSession pid) := by
  let initCurrent (kp : KeypairId) (initiator : Bool) (remote : Nat) : WG.M Unit := do
    let key ← getKeypair kp
    setKeypair kp {key with iAmTheInitiator := initiator, remoteIndex := remote}
  have initCurrent_frame (kp : KeypairId) (initiator : Bool) (remote : Nat) :
      SameSnapshot (initCurrent kp initiator remote) := by
    apply sameSnapshot_of_wp
    intro initial
    unfold initCurrent
    refine Std.Do.Triple.bind _ _ (getKeypair_live_spec (fun s => s = initial) kp) ?_
    intro key
    exact setKeypair_live_spec (fun s => s = initial) kp
      {key with iAmTheInitiator := initiator, remoteIndex := remote}
  let factored : WG.M Bool := do
    let st := (← getPeer pid).handshakeState
    if ← WG.andM (branch .sessionNotCreatedResponse (st != HANDSHAKE_CREATED_RESPONSE))
        (branch .sessionNotConsumedResponse (st != HANDSHAKE_CONSUMED_RESPONSE)) then return false
    let created ← keypairCreate (← IndexOwner.peerWord (.handshake pid))
    if ← branch .sessionNoKeypair created.isNone then return false
    let some kp := created | invariant "unreachable"
    let p ← getPeer pid
    let initiator := st == HANDSHAKE_CONSUMED_RESPONSE
    initCurrent kp initiator p.remoteIndex
    if ← branch .sessionInitiator initiator then deriveKeys kp true p.chainingKey
    else deriveKeys kp false p.chainingKey
    handshakeZero pid
    if ← branch .sessionAlive !(← getPeer pid).isDead then
      addNewKeypair pid kp
      _ ← IndexOwner.peerDeref (.handshake pid)
      if !(← indexReplaceHandshake pid kp) then unsupported "begin_session: the handshake entry was unhashed"
      return true
    unsupported "a dead peer finishing a session"
  have source : Leanux.WG.beginSession pid = factored := by
    simp only [Leanux.WG.beginSession, factored, initCurrent, bind_assoc]
    rfl
  rw [source]
  unfold factored
  transition_ordinary [] using [getPeer_sameSnapshot, ownerPeerWord_sameSnapshot,
    ownerPeerDeref_sameSnapshot, deriveKeys_sameSnapshot, handshakeZero_sameSnapshot,
    addNewKeypair_ordinary, keypairCreate_ordinary]
  all_goals exact SameView.ordinary (initCurrent_frame _ _ _)

theorem beginSession_spec (P : Snapshot → Prop) (hp : Stable P) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.beginSession pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (beginSession_ordinary pid).wp P hp

theorem consumeInitiation_sameSnapshot (msg : List UInt8) : SameSnapshot (Leanux.WG.consumeInitiation msg) := by
  snapshot_source [Leanux.WG.consumeInitiation] using [getDev_sameSnapshot, getPeer_sameSnapshot, messageDecrypt_sameSnapshot, messageEphemeral_sameSnapshot, mixDh_sameSnapshot, mixPrecomputedDh_sameSnapshot, peerPut_sameSnapshot, pubkeyLookup_sameSnapshot, setPeer_sameSnapshot]

theorem consumeInitiation_spec (P : Snapshot → Prop) (msg : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.consumeInitiation msg
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (consumeInitiation_sameSnapshot msg).wp P

theorem consumeResponse_sameSnapshot (msg : List UInt8) : SameSnapshot (Leanux.WG.consumeResponse msg) := by
  snapshot_source [Leanux.WG.consumeResponse] using [getDev_sameSnapshot, getPeer_sameSnapshot, indexLookup_sameSnapshot, kdfOut_sameSnapshot, kdf_sameSnapshot, messageDecrypt_sameSnapshot, messageEphemeral_sameSnapshot, mixDh_sameSnapshot, peerPut_sameSnapshot, setPeer_sameSnapshot]

theorem consumeResponse_spec (P : Snapshot → Prop) (msg : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.consumeResponse msg
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (consumeResponse_sameSnapshot msg).wp P

theorem createData_ordinary (pid : PeerId) (item : List SkbId) : OrdinaryAction (Leanux.WG.createData pid item) := by
  transition_ordinary [Leanux.WG.createData] using [enqueuePerDeviceAndPeer_sameSnapshot, enqueuePerPeerTx_sameSnapshot, getPeer_sameSnapshot, peerPut_sameSnapshot, keypairPut_ordinary]

theorem createData_spec (P : Snapshot → Prop) (hp : Stable P) (pid : PeerId) (item : List SkbId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.createData pid item
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (createData_ordinary pid item).wp P hp

theorem createInitiation_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.createInitiation pid) := by
  snapshot_source [Leanux.WG.createInitiation] using [ownerPeerDeref_sameSnapshot, ownerPeerWord_sameSnapshot, generatePublic_sameSnapshot, getDev_sameSnapshot, getPeer_sameSnapshot, messageEphemeral_sameSnapshot, mixDh_sameSnapshot, mixPrecomputedDh_sameSnapshot, setChain_sameSnapshot, setPeer_sameSnapshot]

theorem createInitiation_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.createInitiation pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (createInitiation_sameSnapshot pid).wp P

theorem createResponse_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.createResponse pid) := by
  snapshot_source [Leanux.WG.createResponse] using [ownerPeerDeref_sameSnapshot, ownerPeerWord_sameSnapshot, generatePublic_sameSnapshot, getPeer_sameSnapshot, kdfOut_sameSnapshot, kdf_sameSnapshot, messageEphemeral_sameSnapshot, mixDh_sameSnapshot, setChain_sameSnapshot, setPeer_sameSnapshot]

theorem createResponse_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.createResponse pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (createResponse_sameSnapshot pid).wp P

theorem queuedExpiredZeroKeyMaterial_ordinary (pid : PeerId) : OrdinaryAction (Leanux.WG.queuedExpiredZeroKeyMaterial pid) := by
  transition_ordinary [Leanux.WG.queuedExpiredZeroKeyMaterial] using [handshakeClear_sameSnapshot, peerPut_sameSnapshot, keypairsClear_ordinary]

theorem queuedExpiredZeroKeyMaterial_spec (P : Snapshot → Prop) (hp : Stable P) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.queuedExpiredZeroKeyMaterial pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (queuedExpiredZeroKeyMaterial_ordinary pid).wp P hp

theorem timersDataReceived_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.timersDataReceived pid) := by
  snapshot_source [Leanux.WG.timersDataReceived] using [getDev_sameSnapshot, getPeer_sameSnapshot, modPeerTimer_sameSnapshot, setPeer_sameSnapshot]
  all_goals exact (modPeerTimer_sameSnapshot _ _ _ _).map (fun _ => PUnit.unit)

theorem timersDataReceived_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.timersDataReceived pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (timersDataReceived_sameSnapshot pid).wp P

theorem timersHandshakeInitiated_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.timersHandshakeInitiated pid) := by
  snapshot_source [Leanux.WG.timersHandshakeInitiated] using [jitterBelowRekeyTimeout_sameSnapshot, modPeerTimerGuard_sameSnapshot, armTimer_sameSnapshot]
  all_goals exact (Framing.callerJiffies_sameWGWorld _).factor snapshot

theorem timersHandshakeInitiated_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.timersHandshakeInitiated pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (timersHandshakeInitiated_sameSnapshot pid).wp P

theorem timersSessionDerived_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.timersSessionDerived pid) := by
  snapshot_source [Leanux.WG.timersSessionDerived] using [modPeerTimer_sameSnapshot]
  all_goals exact (modPeerTimer_sameSnapshot _ _ _ _).map (fun _ => PUnit.unit)

theorem timersSessionDerived_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.timersSessionDerived pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (timersSessionDerived_sameSnapshot pid).wp P

theorem timersTraversal_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.timersTraversal pid) := by
  snapshot_source [Leanux.WG.timersTraversal] using [getPeer_sameSnapshot, modPeerTimer_sameSnapshot]
  all_goals exact (modPeerTimer_sameSnapshot _ _ _ _).map (fun _ => PUnit.unit)

theorem timersTraversal_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.timersTraversal pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (timersTraversal_sameSnapshot pid).wp P

theorem sendHandshakeInitiation_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.sendHandshakeInitiation pid) := by
  snapshot_source [Leanux.WG.sendHandshakeInitiation] using [addMacToPacket_sameSnapshot, branchExpired_sameSnapshot, createInitiation_sameSnapshot, getPeer_sameSnapshot, sendBufferToPeer_sameSnapshot, setPeer_sameSnapshot, timersAnyAuthenticatedPacketSent_sameSnapshot, timersHandshakeInitiated_sameSnapshot, timersTraversal_sameSnapshot]

theorem sendHandshakeInitiation_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.sendHandshakeInitiation pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sendHandshakeInitiation_sameSnapshot pid).wp P

theorem sendHandshakeResponse_ordinary (pid : PeerId) : OrdinaryAction (Leanux.WG.sendHandshakeResponse pid) := by
  transition_ordinary [Leanux.WG.sendHandshakeResponse] using [addMacToPacket_sameSnapshot, createResponse_sameSnapshot, getPeer_sameSnapshot, sendBufferToPeer_sameSnapshot, setPeer_sameSnapshot, timersAnyAuthenticatedPacketSent_sameSnapshot, timersSessionDerived_sameSnapshot, timersTraversal_sameSnapshot, beginSession_ordinary]

theorem sendHandshakeResponse_spec (P : Snapshot → Prop) (hp : Stable P) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.sendHandshakeResponse pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sendHandshakeResponse_ordinary pid).wp P hp

theorem sendStagedPackets_ordinary (pid : PeerId) : OrdinaryAction (Leanux.WG.sendStagedPackets pid) := by
  let invalidate (kp : KeypairId) : WG.M Unit := do
    let key ← getKeypair kp
    setKeypair kp {key with sending := {key.sending with isValid := false}}
  have invalidate_frame (kp : KeypairId) : SameSnapshot (invalidate kp) := by
    apply sameSnapshot_of_wp
    intro initial
    unfold invalidate
    refine Std.Do.Triple.bind _ _ (getKeypair_live_spec (fun s => s = initial) kp) ?_
    intro key
    exact setKeypair_live_spec (fun s => s = initial) kp
      {key with sending := {key.sending with isValid := false}}
  let nextNonce (kp : KeypairId) : WG.M Nat := do
    let key ← getKeypair kp
    setKeypair kp {key with sendingCounter := key.sendingCounter + 1}
    return key.sendingCounter
  have nextNonce_frame (kp : KeypairId) : SameSnapshot (nextNonce kp) := by
    apply sameSnapshot_of_wp
    intro initial
    unfold nextNonce
    refine Std.Do.Triple.bind _ _ (getKeypair_live_spec (fun s => s = initial) kp) ?_
    intro key
    refine Std.Do.Triple.bind _ _
      (setKeypair_live_spec (fun s => s = initial) kp
        {key with sendingCounter := key.sendingCounter + 1}) ?_
    intro _
    exact (snapshot_pure key.sendingCounter).wp (fun s => s = initial)
  let outNokey (packets : List Packet) (keypair : Option KeypairId)
      (invalid : Bool) : WG.M Unit := do
    if invalid then
      let some kp := keypair | invariant "unreachable"
      invalidate kp
    keypairPut keypair false
    for _ in packets do _ ← branch .stagedOrphanWalk true
    _ ← branch .stagedOrphanWalk false
    setPeer pid {(← getPeer pid) with staged := packets ++ (← getPeer pid).staged}
    sendQueuedHandshakeInitiation pid false
  have outNokey_ordinary (packets : List Packet) (keypair : Option KeypairId)
      (invalid : Bool) : OrdinaryAction (outNokey packets keypair invalid) := by
    unfold outNokey
    transition_ordinary [] using [getPeer_sameSnapshot, setPeer_sameSnapshot,
      sendQueuedHandshakeInitiation_sameSnapshot, keypairPut_ordinary]
    all_goals exact SameView.ordinary (invalidate_frame _)
  have mapped (packets : List DataPacket) :
      SameSnapshot (packets.mapM newTxSkb) := by
    intro initial
    apply Framing.mapM_view_spec snapshot (fun s => s = initial)
    intro pkt
    apply Framing.hoare_liftSkb (SkbStore.newTx pkt) (fun w => snapshot w = initial)
    intro g d store hg hd
    simpa [snapshot, hd] using hg
  let factored : WG.M Unit := do
    let p ← getPeer pid
    if ← branch .stagedEmpty p.staged.isEmpty then return
    let packets := p.staged
    setPeer pid { p with staged := [] }
    let keypair ← keypairGet p.keypairCurrent
    if ← branch .stagedNoKeypair keypair.isNone then return ← outNokey packets keypair false
    let some id := keypair | invariant "unreachable"
    let k ← getKeypair id
    if ← branch .stagedKeyInvalid !k.sending.isValid then return ← outNokey packets keypair false
    if ← branchExpired .stagedBirthdateExpired k.sending.birthdate REJECT_AFTER_TIME then
      return ← outNokey packets keypair true
    let mut packetsCb : List DataPacket := []
    for pkt in packets do
      _ ← branch .stagedNonceIterate true
      let ds ← ipTunnelEcnEncap pkt
      let nonce ← nextNonce id
      if ← branchCmp .stagedNonceRejected (nonce ≥ REJECT_AFTER_MESSAGES) nonce REJECT_AFTER_MESSAGES then return ← outNokey packets keypair true
      packetsCb := packetsCb ++ [{ peer := pid, keypair := id, nonce, plaintext := pkt, ds }]
    _ ← branch .stagedNonceIterate false
    peerGet (← IndexOwner.peerDeref (.keypair id))
    let item ← packetsCb.mapM newTxSkb
    createData pid item
  have source : Leanux.WG.sendStagedPackets pid = factored := by
    simp only [Leanux.WG.sendStagedPackets, factored, invalidate, nextNonce, outNokey, bind_assoc, pure_bind]
    rfl
  rw [source]
  unfold factored
  transition_ordinary [] using [getPeer_sameSnapshot, setPeer_sameSnapshot,
    keypairGet_sameSnapshot, getKeypair_sameSnapshot, branchExpired_sameSnapshot,
    ipTunnelEcnEncap_sameSnapshot, ownerPeerDeref_sameSnapshot, peerGet_sameSnapshot,
    createData_ordinary]
  all_goals first
    | transition_fact nextNonce_frame
    | transition_fact mapped
    | transition_fact outNokey_ordinary

theorem sendStagedPackets_spec (P : Snapshot → Prop) (hp : Stable P) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.sendStagedPackets pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sendStagedPackets_ordinary pid).wp P hp

theorem handshakeSendWorker_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.handshakeSendWorker pid) := by
  snapshot_source [Leanux.WG.handshakeSendWorker] using [peerPut_sameSnapshot, sendHandshakeInitiation_sameSnapshot]

theorem handshakeSendWorker_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.handshakeSendWorker pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (handshakeSendWorker_sameSnapshot pid).wp P

theorem sendKeepalive_ordinary (pid : PeerId) : OrdinaryAction (Leanux.WG.sendKeepalive pid) := by
  transition_ordinary [Leanux.WG.sendKeepalive] using [getDev_sameSnapshot, getPeer_sameSnapshot, setPeer_sameSnapshot, sendStagedPackets_ordinary]

theorem sendKeepalive_spec (P : Snapshot → Prop) (hp : Stable P) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.sendKeepalive pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sendKeepalive_ordinary pid).wp P hp

end Leanux.Proofs.WG.Keypairs.WGTransitions
