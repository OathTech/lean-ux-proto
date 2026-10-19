import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueFrames
import Leanux.Proofs.WG.Queues.RxRingCallbackFrames

/-! Native data, timer and stack leaves retain the physical handshake ring.
These frames are separate from header validation and from ring offer/poll
transport, and impose no packet, peer or key residency assumption. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Queues.RxRing Std.Do

def productView (w : World) := view w.wg

theorem getPeer_cell (pid : PeerId) : SameView view (getPeer pid) := getPeer_frame pid
theorem getKeypair_cell (id : KeypairId) : SameView view (getKeypair id) := getKeypair_frame id
theorem keypairGet_cell (id : Option KeypairId) : SameView view (keypairGet id) := keypairGet_frame id
theorem keypairPut_cell (id : Option KeypairId) (now : Bool) : SameView view (keypairPut id now) := keypairPut_frame id now
theorem peerGet_cell (id : PeerId) : SameView view (peerGet id) := peerGet_frame id
theorem peerGetMaybeZero_cell (id : Option PeerId) : SameView view (peerGetMaybeZero id) := peerGetMaybeZero_frame id
theorem peerPut_cell (id : Option PeerId) : SameView view (peerPut id) := peerPut_frame id

theorem getPeer_cell_spec (P : (Option (PtrRing (List UInt8 × SkbSource))) → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (view w)⌝⦄ getPeer pid ⦃⇓? _ w => ⌜P (view w)⌝⦄ :=
  (getPeer_frame pid).wp P

theorem setPeer_cell_spec (P : (Option (PtrRing (List UInt8 × SkbSource))) → Prop) (pid : PeerId) (p : Peer) :
    ⦃fun w => ⌜P (view w)⌝⦄ setPeer pid p ⦃⇓? _ w => ⌜P (view w)⌝⦄ :=
  (setPeer_frame pid p).wp P

theorem modifyPeer_cell (pid : PeerId) (f : Peer → Peer)
    :
    SameView view (do let p ← getPeer pid; setPeer pid (f p)) :=
  (getPeer_frame pid).bind (fun p => setPeer_frame pid (f p))

theorem modifyDev_cell (f : Device → Device)
    (hq : ∀ d, (f d).handshakeQueue = d.handshakeQueue) : SameView view (modifyDev f) := modify f hq


/-- Native ring framing by existing checked composition and component adapters. -/
macro "handshake_cell_source" "[" fs:ident,* "]" "using" "[" facts:ident,* "]" : tactic => do
  let pinned := fs.getElems.map fun f =>
    if f.getId.toString.startsWith "_private." then
      Lean.mkCIdent (normalizePinnedName f.getId) else f
  let mut use ← `(tactic| fail "no named ring frame")
  for fact in facts.getElems.reverse do
    use ← `(tactic| first | env_operation_fact $fact | ($use:tactic))
  let mut atom ← `(tactic| fail "not a native wrapper")
  for name in #[
      ``Leanux.branch, ``Leanux.branchCmp, ``Leanux.branchCmpExcluded,
      ``Leanux.invariant, ``Leanux.unsupported, ``Leanux.hidden, ``Leanux.hiddenAlloc,
      ``Leanux.hiddenClock, ``Leanux.hiddenClock64, ``Leanux.hiddenJiffies,
      ``Leanux.getAmbient, ``Leanux.modifyAmbient, ``Leanux.peekHiddenSite,
      ``Leanux.skipCut, ``Leanux.skipCutSites, ``Leanux.envOk,
      ``Leanux.peekQueuedUnit, ``Leanux.recordQueued, ``Leanux.queueDeviceWork,
      ``Leanux.getRouting, ``Leanux.getWG,
      ``Leanux.WG.getDev, ``Leanux.WG.andM, ``Leanux.WG.orM,
      ``Leanux.WG.newTxSkb, ``Leanux.WG.getTxSkb, ``Leanux.WG.setTxSkb, ``Leanux.WG.freeTxSkb,
      ``Leanux.WG.newRxSkb, ``Leanux.WG.getRxSkb, ``Leanux.WG.setRxSkb, ``Leanux.WG.freeRxSkb,
      ``liftM].reverse do
    let n := Lean.mkCIdent name
    atom ← `(tactic| first | (snapshot_head $n; unfold $n) | ($atom:tactic))
  let expand ← if pinned.isEmpty then `(tactic| skip) else `(tactic| unfold $pinned:ident*)
  `(tactic|
    (have ringAmbient {α : Type} (a : AmbientM α) : SameView view (monadLift a : WG.M α) :=
       fun initial => hoare_liftAmbient a (fun w => view w = initial)
     have ringAip {α : Type} (a : AipM α) : SameView view (monadLift a : WG.M α) := by
       intro initial
       apply hoare_liftAip a
       intro g d store hg hd
       simpa [view, hd] using hg
     have ringIndex {α : Type} (a : IndexM α) : SameView view (monadLift a : WG.M α) := by
       intro initial
       apply hoare_liftIndex a
       intro g d store hg hd
       simpa [view, hd] using hg
     have ringSkb {α : Type} (a : SkbM α) : SameView view (liftSkb a) := by
       intro initial
       apply hoare_liftSkb a
       intro g d store hg hd
       simpa [view, hd] using hg
     have ringRouting {α : Type} (a : Net.M α) : SameView view (monadLift a : WG.M α) :=
       fun initial => hoare_liftRouting a (fun w => view w = initial) (fun _ _ h => h)
     have ringChoice {α : Type} (p : Prop) [Decidable p] (yes no : WG.M α)
         (hy : p → SameView view yes) (hn : ¬p → SameView view no) :
         SameView view (if p then yes else no) := by
       by_cases h : p
       · simpa only [ite_eq_left h] using hy h
       · simpa only [ite_eq_right h] using hn h
     have ringGet : SameView view (get : WG.M WGWorld) := by
       apply (ProjectedAction.iff_run_ambient _ _ _).mpr
       intro w ambient x v ambient' hr
       cases hr
       rfl
     have ringStop {α : Type} (e : Stop) : SameView view (throw e : WG.M α) := by
       apply (ProjectedAction.iff_run_ambient _ _ _).mpr
       intro w ambient x v ambient' hr
       cases hr
     have ringEdit (f : WGWorld → WGWorld) (hf : ∀ w, view (f w) = view w) :
         SameView view (_root_.modify f : WG.M Unit) := by
       intro initial
       apply hoare_modify
       intro w hw
       exact (hf w).trans hw
     have ringLoop {α β : Type} (xs : List α) (b : β) (f : α → β → WG.M (ForInStep β))
         (hf : ∀ x b, SameView view (f x b)) : SameView view (forIn xs b f) :=
       fun initial => list_view_spec view (fun s => s = initial) xs b f (fun x b => hf x b initial)
     have ringMap {α β : Type} (f : α → WG.M β) (xs : List α)
         (hf : ∀ x, SameView view (f x)) : SameView view (xs.mapM f) :=
       fun initial => mapM_view_spec view (fun s => s = initial) f xs (fun x => hf x initial)
     have ringDiscard {α : Type} (a : WG.M α) (ha : SameView view a) :
         SameView view (Functor.discard a) :=
       fun initial => discard_view_spec view (fun s => s = initial) a (ha initial)
     have ringOwner (o : IndexOwner) : SameView view o.peerDeref :=
       fun initial => indexOwner_peerDeref_preserves o (fun w => view w = initial)
     have ringWord (o : IndexOwner) : SameView view o.peerWord :=
       fun initial => indexOwner_peerWord_preserves o (fun w => view w = initial)
     $expand
     repeat' first
       | ring_cell_error_let
       | rxqueue_join_let
       | rxqueue_join_use
       | ($use:tactic)
       | env_operation_fact getPeer_frame
       | env_operation_fact setPeer_frame
       | env_operation_fact getKeypair_frame
       | env_operation_fact ringOwner
       | env_operation_fact ringWord
       | ($atom:tactic)
       | (snapshot_head MonadLiftT.monadLift; first | (ring_lift_source AmbientM; exact ringAmbient _) | (ring_lift_source AipM; exact ringAip _) | (ring_lift_source IndexM; exact ringIndex _) | (ring_lift_source SkbM; exact ringSkb _) | (ring_lift_source Net.M; exact ringRouting _))
       | (snapshot_head MonadLift.monadLift; first | (ring_lift_source AmbientM; exact ringAmbient _) | (ring_lift_source AipM; exact ringAip _) | (ring_lift_source IndexM; exact ringIndex _) | (ring_lift_source SkbM; exact ringSkb _) | (ring_lift_source Net.M; exact ringRouting _))
       | (snapshot_head liftSkb; exact ringSkb _)
       | (snapshot_head get; exact ringGet)
       | (snapshot_head MonadStateOf.get; exact ringGet)
       | (snapshot_head throw; exact ringStop _)
       | (snapshot_head MonadExceptOf.throw; exact ringStop _)
       | (snapshot_head modifyDev; exact modifyDev_cell _ (fun _ => rfl))
       | (snapshot_head _root_.modify; exact ringEdit _ (fun _ => rfl))
       | (snapshot_head ForIn.forIn; first | apply ringLoop | rw [Std.Legacy.Range.forIn_eq_forIn_range'])
       | (snapshot_head List.mapM; apply ringMap)
       | (snapshot_head Functor.discard; apply ringDiscard)
       | (snapshot_head ite; apply ringChoice)
       | env_operation_step))

theorem cell_kernel {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun w => wgStoreView (project w)) a) :
    SameView (fun w => view (project w)) a := kernel ha

theorem requireNotPending_cell (pid : PeerId) (why : String) :
    SameView view (requireNotPending pid why) := by
  handshake_cell_source [requireNotPending] using []

theorem setKeypair_cell (kp : KeypairId) (k : Keypair) : SameView view (setKeypair kp k) :=
  modifyDev_cell _ (fun _ => rfl)

theorem counterValidate_cell (kp : KeypairId) (nonce : Nat) :
    SameView view (counterValidate kp nonce) := by
  handshake_cell_source [counterValidate] using [setKeypair_cell]

theorem receivedWithKeypair_cell (pid : PeerId) (kp : KeypairId) :
    SameView view (receivedWithKeypair pid kp) := by
  handshake_cell_source [receivedWithKeypair, _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer] using [keypairPut_cell]

theorem dstCacheReset_cell (pid : PeerId) : SameView view (dstCacheReset pid) := by
  handshake_cell_source [dstCacheReset] using []

theorem setPeerEndpoint_cell (pid : PeerId) (e : Endpoint) : SameView view (setPeerEndpoint pid e) := by
  handshake_cell_source [setPeerEndpoint, endpointEq] using [requireNotPending_cell, dstCacheReset_cell]

theorem armTimer_cell (pid : PeerId) (timer : PeerTimer) (delay : Nat) (jc : Option UInt64 := none) :
    SameView view (armTimer pid timer delay jc) := by
  have wheel (t : PeerTimer) (expires clk : UInt64) (unit : Option Nat) :
      SameView view (placeOnWheel pid t expires clk unit) := by
    handshake_cell_source [placeOnWheel] using []
  handshake_cell_source [armTimer] using [wheel]

theorem delTimer_cell (pid : PeerId) (timer : PeerTimer) : SameView view (delTimer pid timer) :=
  modifyPeer_cell pid (fun p => (p.setTimer timer none).setWheel timer none)

theorem modPeerTimerGuard_cell (pid : PeerId) : SameView view (modPeerTimerGuard pid) := by
  handshake_cell_source [modPeerTimerGuard] using []

theorem modPeerTimer_cell (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    SameView view (modPeerTimer site pid timer delay) := by
  have clock : SameView view (callerJiffies site) := (callerJiffies_sameWGWorld site).factor view
  have arm := fun p t d jc => armTimer_cell p t d jc
  handshake_cell_source [modPeerTimer] using [modPeerTimerGuard_cell, arm, clock]


theorem timersHandshakeComplete_cell (pid : PeerId) (site : HiddenSite) :
    SameView view (timersHandshakeComplete pid site) := by
  handshake_cell_source [timersHandshakeComplete] using [delTimer_cell]

theorem timersAnyAuthenticatedPacketReceived_cell (pid : PeerId) :
    SameView view (timersAnyAuthenticatedPacketReceived pid) := delTimer_cell pid .newHandshake

theorem timersDataReceived_cell (pid : PeerId) : SameView view (timersDataReceived pid) := by
  handshake_cell_source [timersDataReceived] using [modPeerTimer_cell]

theorem timersTraversal_cell (pid : PeerId) : SameView view (timersTraversal pid) := by
  handshake_cell_source [timersTraversal] using [modPeerTimer_cell]

/-- Queueing a handshake can release the extra peer reference while preserving
the device index and complete decrypt ring. -/

theorem sendQueuedHandshakeInitiation_cell (pid : PeerId) (retry : Bool) :
    SameView view (sendQueuedHandshakeInitiation pid retry) := by
  have expired := fun date => show SameView view _ from (branchExpired_sameWGWorld .queuedNotExpired date REKEY_TIMEOUT (!·)).factor view
  handshake_cell_source [sendQueuedHandshakeInitiation] using [requireNotPending_cell, expired, peerGet_cell, peerPut_cell]

theorem keepKeyFreshRx_cell (pid : PeerId) : SameView view (keepKeyFreshRx pid) := by
  have expired := fun date delay => show SameView view _ from (branchExpired_sameWGWorld .rxFreshExpired date delay).factor view
  handshake_cell_source [keepKeyFreshRx] using [expired, sendQueuedHandshakeInitiation_cell]

theorem txDevice_cell (u : TxDeviceUpdate) : SameView view (modifyDev u.apply) :=
  modifyDev_cell _ (fun _ => by cases u <;> rfl)

theorem cpumaskChooseOnline_cell (pid : PeerId) : SameView view (cpumaskChooseOnline pid) := by
  handshake_cell_source [cpumaskChooseOnline] using []

theorem enqueuePerDeviceAndPeer_cell (pid : PeerId) (item : List SkbId) :
    SameView view (enqueuePerDeviceAndPeer pid item) := by
  have cpu := fun last => show SameView view _ from cell_kernel (cpumaskNextOnlineFrom_sameStore last)
  handshake_cell_source [enqueuePerDeviceAndPeer] using [cpu]

theorem enqueuePerPeerTx_cell (item : List SkbId) (state : PacketState) :
    SameView view (enqueuePerPeerTx item state) := by
  handshake_cell_source [enqueuePerPeerTx] using [keypairGet_cell, peerGet_cell, peerPut_cell, cpumaskChooseOnline_cell]

theorem createData_cell (pid : PeerId) (item : List SkbId) : SameView view (createData pid item) := by
  handshake_cell_source [createData] using [enqueuePerDeviceAndPeer_cell, enqueuePerPeerTx_cell, keypairPut_cell, peerPut_cell]

theorem stagedOutNokey_cell (pid : PeerId) (packets : List Packet)
    (keypair : Option KeypairId) (invalid : Bool) :
    SameView view (stagedOutNokey pid packets keypair invalid) := by
  handshake_cell_source [stagedOutNokey] using [setKeypair_cell, keypairPut_cell, sendQueuedHandshakeInitiation_cell]

theorem sendStagedPackets_cell (pid : PeerId) : SameView view (sendStagedPackets pid) := by
  have expired := fun date => show SameView view _ from (branchExpired_sameWGWorld .stagedBirthdateExpired date REJECT_AFTER_TIME).factor view
  have ecn := fun pkt => show SameView view _ from (ipTunnelEcnEncap_sameWGWorld pkt).factor view
  handshake_cell_source [sendStagedPackets] using [setKeypair_cell, keypairGet_cell, peerGet_cell, stagedOutNokey_cell, keypairPut_cell, sendQueuedHandshakeInitiation_cell, expired, ecn, createData_cell]

theorem lookup_cell (root : Option NodeId) (bits key : Nat) :
    SameView view (lookup root bits key) := by
  have ambient {α : Type} (action : AmbientM α) :
      SameView view (MonadLift.monadLift action : WG.M α) :=
    fun s => hoare_liftAmbient action (fun w => view w = s)
  have aip {α : Type} (action : AipM α) :
      SameView view (MonadLift.monadLift action : WG.M α) := by
    intro s
    apply hoare_liftAip action
    intro w d store hi hd
    simpa [view, hd] using hi
  have endian : SameView view (swapEndian bits) := by
    unfold swapEndian
    apply SameView.bind (ambient _)
    intro yes
    cases yes
    · exact SameView.bind (ambient _) (fun _ => SameView.pure _ _)
    · exact SameView.pure _ _
  unfold lookup
  apply SameView.bind endian
  intro _
  apply SameView.bind (aip _)
  intro node
  apply SameView.bind (ambient _)
  intro found
  cases found <;> dsimp only
  · exact SameView.pure _ _
  · cases node with
    | none => exact SameView.bind (ambient _) (fun _ => SameView.pure _ _)
    | some id =>
      apply SameView.bind (aip _)
      intro n
      apply SameView.bind (peerGetMaybeZero_cell n.peer)
      intro peer
      apply SameView.bind (ambient _)
      intro gone
      cases gone
      · exact SameView.pure _ _
      · exact SameView.bind (ambient _) (fun _ => SameView.pure _ _)

theorem lookupSrc_cell (protocol : Nat) (bytes : List UInt8) :
    SameView view (lookupSrc protocol bytes) := by
  handshake_cell_source [lookupSrc] using [lookup_cell]

theorem dishonest_cell (why : Dishonest) : SameView view (dishonest why) :=
  modifyDev_cell _ (fun _ => by cases why <;> rfl)

theorem updateRxStats_cell (pid : PeerId) (len : Nat) :
    SameView view (updateRxStats pid len) := by
  handshake_cell_source [updateRxStats] using []

theorem consumeDataDone_cell (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    SameView view (consumeDataDone pid pkt endpoint) := by
  have ecn := fun protocol outer bytes => show SameView view _ from cell_kernel (inetEcnDecapsulate_sameWGStore protocol outer bytes)
  handshake_cell_source [consumeDataDone] using [setPeerEndpoint_cell, receivedWithKeypair_cell, timersHandshakeComplete_cell, sendStagedPackets_cell, keepKeyFreshRx_cell, timersAnyAuthenticatedPacketReceived_cell, timersTraversal_cell, timersDataReceived_cell, updateRxStats_cell, dishonest_cell, ecn, lookupSrc_cell, peerPut_cell]

theorem lookupDst_cell (family addr : Nat) :
    SameView view (lookupDst family addr) := by
  handshake_cell_source [lookupDst] using [lookup_cell]

theorem xmitTrim_cell (pid : PeerId) : SameView view (xmitTrim pid) := by
  handshake_cell_source [xmitTrim] using []

theorem xmitSplice_cell (pid : PeerId) (packets : List Packet) :
    SameView view (xmitSplice pid packets) := by
  simp only [xmitSplice, getPeer_twice]
  exact modifyPeer_cell pid (fun p => {p with staged := p.staged ++ packets})

/-- Original transmit entry preserves the complete handshake-ring view on every
normal return, including negative status codes. Its full source factor keeps both
getters in the splice and all protocol, allocation and loopback error paths. -/
theorem wgXmit_cell (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    SameView view (wgXmit family addr packets mtu) := by
  have loopback := fun sites raised => show SameView view _ from cell_kernel (loopbackSend_kernel sites raised)
  rw [wgXmitSource_eq]
  handshake_cell_source [wgXmitSource] using [lookupDst_cell, xmitTrim_cell, xmitSplice_cell, sendStagedPackets_cell, peerPut_cell, loopback]

theorem reply4_cell (dst : Nat) (bytes : List UInt8) :
    SameView productView (Leanux.Env.Stack.reply4 dst bytes) := by
  have ambient {α : Type} (a : AmbientM α) : SameView productView (monadLift a : Leanux.M α) :=
    fun initial => productAmbient_spec a (fun w => productView w = initial) (fun _ _ h => h)
  have routing {α : Type} (a : Net.M α) : SameView productView (monadLift a : Leanux.M α) :=
    (liftWG_sameProductStore _ (liftRouting_sameWGStore a)).of_factor
      (fun store : ProductStore43 => store.2.2.2.dev.map fun d => d.handshakeQueue)
      productView (fun _ => rfl)
  have getDevice : SameView view getDev := by
    handshake_cell_source [getDev] using []
  have device : SameView productView (monadLift getDev : Leanux.M Device) :=
    sameView_liftWG productView view getDev getDevice (fun _ _ _ h => h)
  have xmit (family addr : Nat) (packets : List Packet) (mtu : Nat) :
      SameView productView (monadLift (wgXmit family addr packets mtu) : Leanux.M Int) :=
    sameView_liftWG productView view _ (wgXmit_cell family addr packets mtu) (fun _ _ _ h => h)
  have discardRule {α : Type} (a : Leanux.M α) (ha : SameView productView a) : SameView productView (Functor.discard a) :=
    fun initial => discard_view_spec productView (fun s => s = initial) a (ha initial)
  unfold Leanux.Env.Stack.reply4 skipCut unsupported
  repeat' first
    | env_operation_fact xmit
    | env_operation_fact device
    | env_operation_fact routing
    | env_operation_fact ambient
    | (snapshot_head Functor.discard; apply discardRule)
    | env_operation_step

theorem receive4_cell (bytes : List UInt8) :
    SameView productView (Leanux.Env.Stack.receive4 bytes) := by
  have stopped (a : Leanux.M Unit) (failure : ∀ w, ∃ e, a.run w = .error e)
      (tail : Unit → Leanux.M Unit) : SameView productView (a >>= tail) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    obtain ⟨e, he⟩ := failure w
    simp only [StateT.run_bind, he] at hr
    contradiction
  have excluded := fun row tail => stopped (Leanux.Env.Stack.excluded row)
    (stackExcluded_failure row) tail
  have invalid := fun why tail => stopped (Leanux.invariant why) (fun _ => ⟨_, rfl⟩) tail
  have unsupported := fun why tail => stopped (Leanux.unsupported why) (fun _ => ⟨_, rfl⟩) tail
  have excludedAlone (row : String) : SameView productView (Leanux.Env.Stack.excluded row) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    obtain ⟨e, he⟩ := stackExcluded_failure row w
    rw [he] at hr
    contradiction
  have route (src dst : Nat) : SameView productView
      (MonadLift.monadLift (MonadLift.monadLift (Net.routeInput4 src dst) : WG.M _) : Leanux.M _) :=
    ((liftWG_sameProductStore _ (liftRouting_sameWGStore _)).of_factor
      (fun store : ProductStore43 => store.2.2.2.dev.map fun d => d.handshakeQueue)
      (fun w => productView w) (fun _ => rfl))
  have read : SameView productView (getWG : Leanux.M WGWorld) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    cases hr
    rfl
  have write (f : EnvWorld → EnvWorld) : SameView productView (modifyEnv f) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    cases hr
    rfl
  have iteRule {α : Type} (p : Prop) [Decidable p] {a b : Leanux.M α}
      (ha : p → SameView productView a) (hb : ¬p → SameView productView b) :
      SameView productView (if p then a else b) := by
    by_cases hp : p
    · simpa only [ite_eq_left hp] using ha hp
    · simpa only [ite_eq_right hp] using hb hp
  unfold Leanux.Env.Stack.receive4
  repeat' first
    | (env_bind_head Leanux.Env.Stack.excluded; exact excluded _ _)
    | (env_bind_head Leanux.invariant; exact invalid _ _)
    | (env_bind_head Leanux.unsupported; exact unsupported _ _)
    | (snapshot_head Leanux.Env.Stack.excluded; exact excludedAlone _)
    | (snapshot_head Leanux.Env.Stack.reply4; exact reply4_cell _ _)
    | (snapshot_head MonadLift.monadLift; exact route _ _)
    | (snapshot_head liftM; exact route _ _)
    | (snapshot_head getWG; exact read)
    | (snapshot_head modifyEnv; exact write _)
    | (snapshot_head Pure.pure; exact SameView.pure _ _)
    | (snapshot_head Bind.bind; apply SameView.bind)
    | (snapshot_head ite; refine iteRule _ ?_ ?_)
    | keypairs_intro_forall
    | env_ordinary_head_reduce
    | env_ordinary_head_match

theorem deliverInner_cell (bytes : List UInt8) :
    SameView productView (Leanux.Env.deliverInner bytes) := by
  have six := (stackReceive6_sameKernel bytes).of_factor
    (fun store : ProductStore43 => store.2.2.2.dev.map fun d => d.handshakeQueue)
    productView (fun _ => rfl)
  have ambient {α : Type} (a : AmbientM α) : SameView productView (monadLift a : Leanux.M α) :=
    fun initial => productAmbient_spec a (fun w => productView w = initial) (fun _ _ h => h)
  env_operation_source [Leanux.Env.deliverInner, Leanux.Env.Stack.receive, invariant]
    using [receive4_cell, six, ambient]

theorem stackForM_cell (packets : List (List UInt8)) :
    SameView productView (packets.forM Leanux.Env.deliverInner) := by
  induction packets with
  | nil => simpa only [List.forM_eq_forM, List.forM_nil] using (SameView.pure productView PUnit.unit : SameView productView (pure PUnit.unit : Leanux.M PUnit))
  | cons bytes xs ih =>
    simpa only [List.forM_eq_forM, List.forM_cons] using
      (deliverInner_cell bytes).bind (fun _ => ih)

end Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths
