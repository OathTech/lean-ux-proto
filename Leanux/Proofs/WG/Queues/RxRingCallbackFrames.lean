import Leanux.Proofs.WG.Queues.RxRingWorker
import Leanux.Proofs.WG.Queues.RxStackFrames

/-! Full decrypt-ring cell frames for concrete receive callbacks. Peer/keypair
release and TX enqueue are allowed: this view retains the device index and
complete physical decrypt ring, not peer residency or packet ownership.
Source coverage of lifted helpers is separate from normal-endpoint framing. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxRing
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

theorem getPeer_cell (pid : PeerId) : SameView nativeCell (getPeer pid) := getPeer_frame pid
theorem getKeypair_cell (id : KeypairId) : SameView nativeCell (getKeypair id) := getKeypair_frame id
theorem keypairGet_cell (id : Option KeypairId) : SameView nativeCell (keypairGet id) := keypairGet_frame id
theorem keypairPut_cell (id : Option KeypairId) (now : Bool) : SameView nativeCell (keypairPut id now) := keypairPut_frame id now
theorem peerGet_cell (id : PeerId) : SameView nativeCell (peerGet id) := peerGet_frame id
theorem peerGetMaybeZero_cell (id : Option PeerId) : SameView nativeCell (peerGetMaybeZero id) := peerGetMaybeZero_frame id
theorem peerPut_cell (id : Option PeerId) : SameView nativeCell (peerPut id) := peerPut_frame id

theorem getPeer_cell_spec (P : (Option (Nat × PtrRing SkbId)) → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (nativeCell w)⌝⦄ getPeer pid ⦃⇓? _ w => ⌜P (nativeCell w)⌝⦄ :=
  (getPeer_frame pid).wp P

theorem setPeer_cell_spec (P : (Option (Nat × PtrRing SkbId)) → Prop) (pid : PeerId) (p : Peer) :
    ⦃fun w => ⌜P (nativeCell w)⌝⦄ setPeer pid p ⦃⇓? _ w => ⌜P (nativeCell w)⌝⦄ :=
  (setPeer_frame pid p).wp P

theorem modifyPeer_cell (pid : PeerId) (f : Peer → Peer)
    (_hs : ∀ p, (f p).internalId = p.internalId) (_hq : ∀ p, (f p).rxQueue = p.rxQueue) :
    SameView nativeCell (do let p ← getPeer pid; setPeer pid (f p)) :=
  (getPeer_frame pid).bind (fun p => setPeer_frame pid (f p))

theorem modifyDev_cell (f : Device → Device) (he : ∀ d, (f d).ifindex = d.ifindex)
    (hq : ∀ d, (f d).decryptQueue = d.decryptQueue) : SameView nativeCell (modifyDev f) := modify f he hq


/- Expose the actual transmit error continuation to the existing checked
join rule; renaming its local binder does not change the source expression. -/
open Lean Meta Elab Tactic in
elab "ring_cell_error_let" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``SameView do throwError "not a ring frame"
  let .app property action := target | throwError "missing action"
  let .letE name ty value body nonDep := action.consumeMData | throwError "not a let"
  unless name.eraseMacroScopes == `err do throwError "not the transmit error continuation"
  replaceMainGoal [← goal.replaceTargetDefEq
    (mkApp property (.letE `__do_jp_err ty value body nonDep))]

/- Select a component rule from the source action's type before unifying
the lifted program; unrelated component bodies need not be reduced. -/
open Lean Meta Elab Tactic in
elab "ring_lift_source " n:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``SameView do throwError "not a ring frame"
  let action := target.getAppArgs.back! |>.consumeMData |>.headBeta
  unless action.isAppOf ``MonadLift.monadLift || action.isAppOf ``MonadLiftT.monadLift do
    throwError "not a component lift"
  let args := action.getAppArgs
  if args.isEmpty then throwError "missing component action"
  let sourceType ← instantiateMVars (← inferType args.back!)
  let typeArgs := sourceType.getAppArgs
  if typeArgs.isEmpty then throwError "missing component result type"
  let name ← realizeGlobalConstNoOverloadWithInfo n
  let expected ← mkAppM name #[typeArgs.back!]
  unless ← withReducible (isDefEq sourceType expected) do
    throwError "different component state"

/-- Native ring framing by existing checked composition and component adapters. -/
macro "ring_cell_source" "[" fs:ident,* "]" "using" "[" facts:ident,* "]" : tactic => do
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
    (have ringAmbient {α : Type} (a : AmbientM α) : SameView nativeCell (monadLift a : WG.M α) :=
       fun initial => hoare_liftAmbient a (fun w => nativeCell w = initial)
     have ringAip {α : Type} (a : AipM α) : SameView nativeCell (monadLift a : WG.M α) := by
       intro initial
       apply hoare_liftAip a
       intro g d store hg hd
       simpa [nativeCell, hd] using hg
     have ringIndex {α : Type} (a : IndexM α) : SameView nativeCell (monadLift a : WG.M α) := by
       intro initial
       apply hoare_liftIndex a
       intro g d store hg hd
       simpa [nativeCell, hd] using hg
     have ringSkb {α : Type} (a : SkbM α) : SameView nativeCell (liftSkb a) := by
       intro initial
       apply hoare_liftSkb a
       intro g d store hg hd
       simpa [nativeCell, hd] using hg
     have ringRouting {α : Type} (a : Net.M α) : SameView nativeCell (monadLift a : WG.M α) :=
       fun initial => hoare_liftRouting a (fun w => nativeCell w = initial) (fun _ _ h => h)
     have ringChoice {α : Type} (p : Prop) [Decidable p] (yes no : WG.M α)
         (hy : p → SameView nativeCell yes) (hn : ¬p → SameView nativeCell no) :
         SameView nativeCell (if p then yes else no) := by
       by_cases h : p
       · simpa only [ite_eq_left h] using hy h
       · simpa only [ite_eq_right h] using hn h
     have ringGet : SameView nativeCell (get : WG.M WGWorld) := by
       apply (ProjectedAction.iff_run_ambient _ _ _).mpr
       intro w ambient x v ambient' hr
       cases hr
       rfl
     have ringStop {α : Type} (e : Stop) : SameView nativeCell (throw e : WG.M α) := by
       apply (ProjectedAction.iff_run_ambient _ _ _).mpr
       intro w ambient x v ambient' hr
       cases hr
     have ringEdit (f : WGWorld → WGWorld) (hf : ∀ w, nativeCell (f w) = nativeCell w) :
         SameView nativeCell (_root_.modify f : WG.M Unit) := by
       intro initial
       apply hoare_modify
       intro w hw
       exact (hf w).trans hw
     have ringLoop {α β : Type} (xs : List α) (b : β) (f : α → β → WG.M (ForInStep β))
         (hf : ∀ x b, SameView nativeCell (f x b)) : SameView nativeCell (forIn xs b f) :=
       fun initial => list_view_spec nativeCell (fun s => s = initial) xs b f (fun x b => hf x b initial)
     have ringMap {α β : Type} (f : α → WG.M β) (xs : List α)
         (hf : ∀ x, SameView nativeCell (f x)) : SameView nativeCell (xs.mapM f) :=
       fun initial => mapM_view_spec nativeCell (fun s => s = initial) f xs (fun x => hf x initial)
     have ringDiscard {α : Type} (a : WG.M α) (ha : SameView nativeCell a) :
         SameView nativeCell (discard a) :=
       fun initial => discard_view_spec nativeCell (fun s => s = initial) a (ha initial)
     have ringOwner (o : IndexOwner) : SameView nativeCell o.peerDeref :=
       fun initial => indexOwner_peerDeref_preserves o (fun w => nativeCell w = initial)
     have ringWord (o : IndexOwner) : SameView nativeCell o.peerWord :=
       fun initial => indexOwner_peerWord_preserves o (fun w => nativeCell w = initial)
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
       | (snapshot_head modifyDev; exact modifyDev_cell _ (fun _ => rfl) (fun _ => rfl))
       | (snapshot_head _root_.modify; exact ringEdit _ (fun _ => rfl))
       | (snapshot_head ForIn.forIn; first | apply ringLoop | rw [Std.Legacy.Range.forIn_eq_forIn_range'])
       | (snapshot_head List.mapM; apply ringMap)
       | (snapshot_head Functor.discard; apply ringDiscard)
       | (snapshot_head ite; apply ringChoice)
       | env_operation_step))

theorem cell_kernel {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun w => wgStoreView (project w)) a) :
    SameView (fun w => nativeCell (project w)) a := kernel ha

theorem requireNotPending_cell (pid : PeerId) (why : String) :
    SameView nativeCell (requireNotPending pid why) := by
  ring_cell_source [requireNotPending] using []

theorem setKeypair_cell (kp : KeypairId) (k : Keypair) : SameView nativeCell (setKeypair kp k) :=
  modifyDev_cell _ (fun _ => rfl) (fun _ => rfl)

theorem counterValidate_cell (kp : KeypairId) (nonce : Nat) :
    SameView nativeCell (counterValidate kp nonce) := by
  ring_cell_source [counterValidate] using [setKeypair_cell]

theorem receivedWithKeypair_cell (pid : PeerId) (kp : KeypairId) :
    SameView nativeCell (receivedWithKeypair pid kp) := by
  ring_cell_source [receivedWithKeypair, _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer] using [keypairPut_cell]

theorem dstCacheReset_cell (pid : PeerId) : SameView nativeCell (dstCacheReset pid) := by
  ring_cell_source [dstCacheReset] using []

theorem setPeerEndpoint_cell (pid : PeerId) (e : Endpoint) : SameView nativeCell (setPeerEndpoint pid e) := by
  ring_cell_source [setPeerEndpoint, endpointEq] using [requireNotPending_cell, dstCacheReset_cell]

theorem armTimer_cell (pid : PeerId) (timer : PeerTimer) (delay : Nat) (jc : Option UInt64 := none) :
    SameView nativeCell (armTimer pid timer delay jc) := by
  have wheel (t : PeerTimer) (expires clk : UInt64) (unit : Option Nat) :
      SameView nativeCell (placeOnWheel pid t expires clk unit) := by
    ring_cell_source [placeOnWheel] using []
  ring_cell_source [armTimer] using [wheel]

theorem delTimer_cell (pid : PeerId) (timer : PeerTimer) : SameView nativeCell (delTimer pid timer) :=
  modifyPeer_cell pid (fun p => (p.setTimer timer none).setWheel timer none)
    (fun p => by cases timer <;> rfl) (fun p => by cases timer <;> rfl)

theorem modPeerTimerGuard_cell (pid : PeerId) : SameView nativeCell (modPeerTimerGuard pid) := by
  ring_cell_source [modPeerTimerGuard] using []

theorem modPeerTimer_cell (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    SameView nativeCell (modPeerTimer site pid timer delay) := by
  have clock : SameView nativeCell (callerJiffies site) := (callerJiffies_sameWGWorld site).factor nativeCell
  have arm := fun p t d jc => armTimer_cell p t d jc
  ring_cell_source [modPeerTimer] using [modPeerTimerGuard_cell, arm, clock]


theorem timersHandshakeComplete_cell (pid : PeerId) (site : HiddenSite) :
    SameView nativeCell (timersHandshakeComplete pid site) := by
  ring_cell_source [timersHandshakeComplete] using [delTimer_cell]

theorem timersAnyAuthenticatedPacketReceived_cell (pid : PeerId) :
    SameView nativeCell (timersAnyAuthenticatedPacketReceived pid) := delTimer_cell pid .newHandshake

theorem timersDataReceived_cell (pid : PeerId) : SameView nativeCell (timersDataReceived pid) := by
  ring_cell_source [timersDataReceived] using [modPeerTimer_cell]

theorem timersTraversal_cell (pid : PeerId) : SameView nativeCell (timersTraversal pid) := by
  ring_cell_source [timersTraversal] using [modPeerTimer_cell]

/-- Queueing a handshake can release the extra peer reference while preserving
the device index and complete decrypt ring. -/

theorem sendQueuedHandshakeInitiation_cell (pid : PeerId) (retry : Bool) :
    SameView nativeCell (sendQueuedHandshakeInitiation pid retry) := by
  have expired := fun date => show SameView nativeCell _ from (branchExpired_sameWGWorld .queuedNotExpired date REKEY_TIMEOUT (!·)).factor nativeCell
  ring_cell_source [sendQueuedHandshakeInitiation] using [requireNotPending_cell, expired, peerGet_cell, peerPut_cell]

theorem keepKeyFreshRx_cell (pid : PeerId) : SameView nativeCell (keepKeyFreshRx pid) := by
  have expired := fun date delay => show SameView nativeCell _ from (branchExpired_sameWGWorld .rxFreshExpired date delay).factor nativeCell
  ring_cell_source [keepKeyFreshRx] using [expired, sendQueuedHandshakeInitiation_cell]

theorem txDevice_cell (u : TxDeviceUpdate) : SameView nativeCell (modifyDev u.apply) :=
  modifyDev_cell _ (fun d => by cases u <;> rfl) (fun d => by cases u <;> rfl)

theorem cpumaskChooseOnline_cell (pid : PeerId) : SameView nativeCell (cpumaskChooseOnline pid) := by
  ring_cell_source [cpumaskChooseOnline] using []

theorem enqueuePerDeviceAndPeer_cell (pid : PeerId) (item : List SkbId) :
    SameView nativeCell (enqueuePerDeviceAndPeer pid item) := by
  have cpu := fun last => show SameView nativeCell _ from cell_kernel (cpumaskNextOnlineFrom_sameStore last)
  ring_cell_source [enqueuePerDeviceAndPeer] using [cpu]

theorem enqueuePerPeerTx_cell (item : List SkbId) (state : PacketState) :
    SameView nativeCell (enqueuePerPeerTx item state) := by
  ring_cell_source [enqueuePerPeerTx] using [keypairGet_cell, peerGet_cell, peerPut_cell, cpumaskChooseOnline_cell]

theorem createData_cell (pid : PeerId) (item : List SkbId) : SameView nativeCell (createData pid item) := by
  ring_cell_source [createData] using [enqueuePerDeviceAndPeer_cell, enqueuePerPeerTx_cell, keypairPut_cell, peerPut_cell]

theorem stagedOutNokey_cell (pid : PeerId) (packets : List Packet)
    (keypair : Option KeypairId) (invalid : Bool) :
    SameView nativeCell (stagedOutNokey pid packets keypair invalid) := by
  ring_cell_source [stagedOutNokey] using [setKeypair_cell, keypairPut_cell, sendQueuedHandshakeInitiation_cell]

theorem sendStagedPackets_cell (pid : PeerId) : SameView nativeCell (sendStagedPackets pid) := by
  have expired := fun date => show SameView nativeCell _ from (branchExpired_sameWGWorld .stagedBirthdateExpired date REJECT_AFTER_TIME).factor nativeCell
  have ecn := fun pkt => show SameView nativeCell _ from (ipTunnelEcnEncap_sameWGWorld pkt).factor nativeCell
  ring_cell_source [sendStagedPackets] using [setKeypair_cell, keypairGet_cell, peerGet_cell, stagedOutNokey_cell, keypairPut_cell, sendQueuedHandshakeInitiation_cell, expired, ecn, createData_cell]

theorem lookup_cell (root : Option NodeId) (bits key : Nat) :
    SameView nativeCell (lookup root bits key) := by
  have ambient {α : Type} (action : AmbientM α) :
      SameView nativeCell (MonadLift.monadLift action : WG.M α) :=
    fun s => hoare_liftAmbient action (fun w => nativeCell w = s)
  have aip {α : Type} (action : AipM α) :
      SameView nativeCell (MonadLift.monadLift action : WG.M α) := by
    intro s
    apply hoare_liftAip action
    intro w d store hi hd
    simpa [nativeCell, hd] using hi
  have endian : SameView nativeCell (swapEndian bits) := by
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
    SameView nativeCell (lookupSrc protocol bytes) := by
  ring_cell_source [lookupSrc] using [lookup_cell]

theorem dishonest_cell (why : Dishonest) : SameView nativeCell (dishonest why) :=
  modifyDev_cell _ (fun d => by cases why <;> rfl) (fun d => by cases why <;> rfl)

theorem updateRxStats_cell (pid : PeerId) (len : Nat) :
    SameView nativeCell (updateRxStats pid len) := by
  ring_cell_source [updateRxStats] using []

theorem consumeDataDone_cell (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    SameView nativeCell (consumeDataDone pid pkt endpoint) := by
  have ecn := fun protocol outer bytes => show SameView nativeCell _ from cell_kernel (inetEcnDecapsulate_sameWGStore protocol outer bytes)
  ring_cell_source [consumeDataDone] using [setPeerEndpoint_cell, receivedWithKeypair_cell, timersHandshakeComplete_cell, sendStagedPackets_cell, keepKeyFreshRx_cell, timersAnyAuthenticatedPacketReceived_cell, timersTraversal_cell, timersDataReceived_cell, updateRxStats_cell, dishonest_cell, ecn, lookupSrc_cell, peerPut_cell]

theorem lookupDst_cell (family addr : Nat) :
    SameView nativeCell (lookupDst family addr) := by
  ring_cell_source [lookupDst] using [lookup_cell]

theorem xmitTrim_cell (pid : PeerId) : SameView nativeCell (xmitTrim pid) := by
  ring_cell_source [xmitTrim] using []

theorem xmitSplice_cell (pid : PeerId) (packets : List Packet) :
    SameView nativeCell (xmitSplice pid packets) := by
  simp only [xmitSplice, getPeer_twice]
  exact modifyPeer_cell pid (fun p => {p with staged := p.staged ++ packets})
    (fun _ => rfl) (fun _ => rfl)

/-- Original transmit entry preserves the complete decrypt-ring cell on every
normal return, including negative status codes. Its full source factor keeps both
getters in the splice and all protocol, allocation and loopback error paths. -/
theorem wgXmit_cell (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    SameView nativeCell (wgXmit family addr packets mtu) := by
  have loopback := fun sites raised => show SameView nativeCell _ from cell_kernel (loopbackSend_kernel sites raised)
  rw [wgXmitSource_eq]
  ring_cell_source [wgXmitSource] using [lookupDst_cell, xmitTrim_cell, xmitSplice_cell, sendStagedPackets_cell, peerPut_cell, loopback]

theorem reply4_cell (dst : Nat) (bytes : List UInt8) :
    SameView cell (Leanux.Env.Stack.reply4 dst bytes) := by
  have ambient {α : Type} (a : AmbientM α) : SameView cell (monadLift a : Leanux.M α) :=
    fun initial => productAmbient_spec a (fun w => cell w = initial) (fun _ _ h => h)
  have routing {α : Type} (a : Net.M α) : SameView cell (monadLift a : Leanux.M α) :=
    (liftWG_sameProductStore _ (liftRouting_sameWGStore a)).of_factor
      (fun store : ProductStore43 => store.2.2.2.dev.map fun d => (d.ifindex, d.decryptQueue))
      cell (fun _ => rfl)
  have getDevice : SameView nativeCell getDev := by
    ring_cell_source [getDev] using []
  have device : SameView cell (monadLift getDev : Leanux.M Device) :=
    sameView_liftWG cell nativeCell getDev getDevice (fun _ _ _ h => h)
  have xmit (family addr : Nat) (packets : List Packet) (mtu : Nat) :
      SameView cell (monadLift (wgXmit family addr packets mtu) : Leanux.M Int) :=
    sameView_liftWG cell nativeCell _ (wgXmit_cell family addr packets mtu) (fun _ _ _ h => h)
  have discardRule {α : Type} (a : Leanux.M α) (ha : SameView cell a) : SameView cell (discard a) :=
    fun initial => discard_view_spec cell (fun s => s = initial) a (ha initial)
  unfold Leanux.Env.Stack.reply4 skipCut unsupported
  repeat' first
    | env_operation_fact xmit
    | env_operation_fact device
    | env_operation_fact routing
    | env_operation_fact ambient
    | (snapshot_head Functor.discard; apply discardRule)
    | env_operation_step

theorem receive4_cell (bytes : List UInt8) :
    SameView cell (Leanux.Env.Stack.receive4 bytes) := by
  have stopped (a : Leanux.M Unit) (failure : ∀ w, ∃ e, a.run w = .error e)
      (tail : Unit → Leanux.M Unit) : SameView cell (a >>= tail) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    obtain ⟨e, he⟩ := failure w
    simp only [StateT.run_bind, he] at hr
    contradiction
  have excluded := fun row tail => stopped (Leanux.Env.Stack.excluded row)
    (stackExcluded_failure row) tail
  have invalid := fun why tail => stopped (Leanux.invariant why) (fun _ => ⟨_, rfl⟩) tail
  have unsupported := fun why tail => stopped (Leanux.unsupported why) (fun _ => ⟨_, rfl⟩) tail
  have excludedAlone (row : String) : SameView cell (Leanux.Env.Stack.excluded row) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    obtain ⟨e, he⟩ := stackExcluded_failure row w
    rw [he] at hr
    contradiction
  have route (src dst : Nat) : SameView cell
      (MonadLift.monadLift (MonadLift.monadLift (Net.routeInput4 src dst) : WG.M _) : Leanux.M _) :=
    ((liftWG_sameProductStore _ (liftRouting_sameWGStore _)).of_factor
      (fun store : ProductStore43 => store.2.2.2.dev.map fun d => (d.ifindex, d.decryptQueue))
      (fun w => cell w) (fun _ => rfl))
  have read : SameView cell (getWG : Leanux.M WGWorld) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    cases hr
    rfl
  have write (f : EnvWorld → EnvWorld) : SameView cell (modifyEnv f) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    cases hr
    rfl
  have iteRule {α : Type} (p : Prop) [Decidable p] {a b : Leanux.M α}
      (ha : p → SameView cell a) (hb : ¬p → SameView cell b) :
      SameView cell (if p then a else b) := by
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
    SameView cell (Leanux.Env.deliverInner bytes) := by
  have six := (stackReceive6_sameKernel bytes).of_factor
    (fun store : ProductStore43 => store.2.2.2.dev.map fun d => (d.ifindex, d.decryptQueue))
    cell (fun _ => rfl)
  have ambient {α : Type} (a : AmbientM α) : SameView cell (monadLift a : Leanux.M α) :=
    fun initial => productAmbient_spec a (fun w => cell w = initial) (fun _ _ h => h)
  env_operation_source [Leanux.Env.deliverInner, Leanux.Env.Stack.receive, invariant]
    using [receive4_cell, six, ambient]

theorem stackForM_cell (packets : List (List UInt8)) :
    SameView cell (packets.forM Leanux.Env.deliverInner) := by
  induction packets with
  | nil => simpa only [List.forM_eq_forM, List.forM_nil] using (SameView.pure cell PUnit.unit : SameView cell (pure PUnit.unit : Leanux.M PUnit))
  | cons bytes xs ih =>
    simpa only [List.forM_eq_forM, List.forM_cons] using
      (deliverInner_cell bytes).bind (fun _ => ih)

end Leanux.Proofs.WG.Queues.RxRing
