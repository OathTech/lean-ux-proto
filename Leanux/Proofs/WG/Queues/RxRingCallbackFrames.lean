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

theorem cell_kernel {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun w => wgStoreView (project w)) a) :
    SameView (fun w => nativeCell (project w)) a := kernel ha

theorem requireNotPending_cell (pid : PeerId) (why : String) :
    SameView nativeCell (requireNotPending pid why) := by
  apply SameView.of_wp
  intro s
  have hg := (getPeer_cell pid).wp (fun t => t = s)
  mvcgen [requireNotPending, hg, unsupported]

theorem setKeypair_cell (kp : KeypairId) (k : Keypair) : SameView nativeCell (setKeypair kp k) :=
  modifyDev_cell _ (fun _ => rfl) (fun _ => rfl)

theorem counterValidate_cell (kp : KeypairId) (nonce : Nat) :
    SameView nativeCell (counterValidate kp nonce) := by
  apply SameView.of_wp
  intro s
  mvcgen [counterValidate, getKeypair, getDev, setKeypair, modifyDev,
    branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, WG.orM, invariant, AmbientM.invariant]
  all_goals try exact ((⇓? _ w => ⌜nativeCell w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell, Option.map_map, Function.comp_def]

  all_goals trivial

theorem receivedWithKeypair_cell (pid : PeerId) (kp : KeypairId) :
    SameView nativeCell (receivedWithKeypair pid kp) := by
  apply SameView.of_wp
  intro s
  have hg := (getPeer_cell pid).wp (fun t => t = s)
  have hk := fun old => (keypairPut_cell old true).wp (fun t => t = s)
  have hm (f : Peer → Peer) (hs : ∀ p, (f p).internalId = p.internalId)
      (hq : ∀ p, (f p).rxQueue = p.rxQueue) :=
    (modifyPeer_cell pid f hs hq).wp (fun t => t = s)
  have hm1 := hm (fun p => {p with keypairPrevious := p.keypairCurrent}) (fun _ => rfl) (fun _ => rfl)
  have hm2 := hm (fun p => {p with keypairCurrent := some kp, keypairNext := none}) (fun _ => rfl) (fun _ => rfl)
  have hp1 : ⦃fun w => ⌜nativeCell w = s⌝⦄
      (pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid
        (fun p => {p with keypairPrevious := p.keypairCurrent})
      ⦃⇓? _ w => ⌜nativeCell w = s⌝⦄ := hm1
  have hp2 : ⦃fun w => ⌜nativeCell w = s⌝⦄
      (pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid
        (fun p => {p with keypairCurrent := some kp, keypairNext := none})
      ⦃⇓? _ w => ⌜nativeCell w = s⌝⦄ := hm2
  mvcgen [receivedWithKeypair, hg, hk, hp1, hp2, branch, AmbientM.branch, invariant, AmbientM.invariant]


theorem dstCacheReset_cell (pid : PeerId) : SameView nativeCell (dstCacheReset pid) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_cell_spec (fun t => t = s) pid
  have hs := fun p => setPeer_cell_spec (fun t => t = s) pid p
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient a (fun w => nativeCell w = s)
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, dstCacheReset, getAmbient, hiddenJiffies, hg, hs, ambient]
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold nativeCell at *; simp_all [CurrentRx]

theorem setPeerEndpoint_cell (pid : PeerId) (e : Endpoint) : SameView nativeCell (setPeerEndpoint pid e) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_cell_spec (fun t => t = s) pid
  have hs := fun p => setPeer_cell_spec (fun t => t = s) pid p
  have hn := (requireNotPending_cell pid "changing the endpoint").wp (fun t => t = s)
  have hc := (dstCacheReset_cell pid).wp (fun t => t = s)
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient a (fun w => nativeCell w = s)
  unfold Hoare at ambient
  have he (old : Option Endpoint) :
      ⦃fun w => ⌜nativeCell w = s⌝⦄ endpointEq e old ⦃⇓? _ w => ⌜nativeCell w = s⌝⦄ := by
    mvcgen [-Std.Do.Spec.monadLift_StateT, endpointEq, WG.andM, branch, ambient]
  mvcgen [-Std.Do.Spec.monadLift_StateT, setPeerEndpoint, he, hg, hs, hn, hc, branch, ambient]
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold nativeCell at *; simp_all [CurrentRx]

theorem armTimer_cell (pid : PeerId) (timer : PeerTimer) (delay : Nat) (jc : Option UInt64 := none) :
    SameView nativeCell (armTimer pid timer delay jc) := by
  have wheel (t : PeerTimer) (expires clk : UInt64) (unit : Option Nat) :
      SameView nativeCell (placeOnWheel pid t expires clk unit) := by
    apply SameView.of_wp
    intro s
    have hg := getPeer_cell_spec (fun q => q = s) pid
    have hs := fun p => setPeer_cell_spec (fun q => q = s) pid p
    have ambient {α : Type} (a : AmbientM α) :
        Hoare (MonadLift.monadLift a : WG.M α) (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
      hoare_liftAmbient a _
    unfold Hoare at ambient
    mvcgen [-Std.Do.Spec.monadLift_StateT, placeOnWheel, hg, hs, ambient,
      hidden, peekHiddenSite, invariant]
  have ambient {α : Type} (a : AmbientM α) : SameView nativeCell (monadLift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun w => nativeCell w = initial)
  have read : SameView nativeCell (get : WG.M WGWorld) := by
    apply SameView.of_wp; intro initial; mvcgen
  have dev : SameView nativeCell getDev := by
    apply SameView.of_wp; intro initial; mvcgen [getDev, invariant, AmbientM.invariant]
  have stopped {α : Type} (e : Stop) : SameView nativeCell (throw e : WG.M α) := by
    apply SameView.of_wp; intro initial; mvcgen
  have edit (f : WGWorld → WGWorld) (hf : ∀ w, nativeCell (f w) = nativeCell w) :
      SameView nativeCell (_root_.modify f : WG.M Unit) := by
    intro initial
    apply hoare_modify
    intro w hw
    exact (hf w).trans hw
  unfold armTimer
  simp (config := { zeta := false }) only [getAmbient, hidden, invariant, unsupported, liftM]
  repeat' first
    | rxqueue_join_let
    | rxqueue_join_use
    | (snapshot_head placeOnWheel; exact wheel _ _ _ _)
    | (snapshot_head getDev; exact dev)
    | (snapshot_head getPeer; exact getPeer_cell _)
    | (snapshot_head MonadLiftT.monadLift; exact ambient _)
    | (snapshot_head MonadLift.monadLift; exact ambient _)
    | (snapshot_head get; exact read)
    | (snapshot_head MonadStateOf.get; exact read)
    | (snapshot_head throw; exact stopped _)
    | (snapshot_head MonadExceptOf.throw; exact stopped _)
    | contradiction
    | keypairs_intro_forall
    | (snapshot_head Pure.pure; exact SameView.pure _ _)
    | (snapshot_head Bind.bind; apply SameView.bind)
    | (snapshot_head ite; split)
    | (snapshot_head _root_.modify; exact edit _ (fun _ => rfl))
    | snapshot_head_reduce
    | snapshot_head_match

theorem delTimer_cell (pid : PeerId) (timer : PeerTimer) : SameView nativeCell (delTimer pid timer) :=
  modifyPeer_cell pid (fun p => (p.setTimer timer none).setWheel timer none)
    (fun p => by cases timer <;> rfl) (fun p => by cases timer <;> rfl)

theorem modPeerTimerGuard_cell (pid : PeerId) : SameView nativeCell (modPeerTimerGuard pid) := by
  apply SameView.of_wp
  intro s
  have hg := (getPeer_cell pid).wp (fun t => t = s)
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient a (fun w => nativeCell w = s)
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, modPeerTimerGuard, getDev, hg, WG.andM, branch, invariant, AmbientM.invariant]

theorem modPeerTimer_cell (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    SameView nativeCell (modPeerTimer site pid timer delay) := by
  apply SameView.of_wp
  intro s
  have hg := (modPeerTimerGuard_cell pid).wp (fun t => t = s)
  have ha := fun jc => (armTimer_cell pid timer delay jc).wp (fun t => t = s)
  have hc := (callerJiffies_sameWGWorld site).wp (fun w => nativeCell w = s)
  mvcgen [modPeerTimer, hg, ha, hc]

theorem timersHandshakeComplete_cell (pid : PeerId) (site : HiddenSite) :
    SameView nativeCell (timersHandshakeComplete pid site) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_cell_spec (fun t => t = s) pid
  have hs := fun p => setPeer_cell_spec (fun t => t = s) pid p
  have hd := (delTimer_cell pid .retransmitHandshake).wp (fun t => t = s)
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient a (fun w => nativeCell w = s)
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, timersHandshakeComplete, hg, hs, hd, hidden, ambient]
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold nativeCell at *; simp_all [CurrentRx]

theorem timersAnyAuthenticatedPacketReceived_cell (pid : PeerId) :
    SameView nativeCell (timersAnyAuthenticatedPacketReceived pid) := delTimer_cell pid .newHandshake

theorem timersDataReceived_cell (pid : PeerId) : SameView nativeCell (timersDataReceived pid) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_cell_spec (fun t => t = s) pid
  have hs := fun p => setPeer_cell_spec (fun t => t = s) pid p
  have ht := (modPeerTimer_cell .timerJiffiesDataReceived pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS).wp (fun t => t = s)
  have hd := discard_view_spec nativeCell (fun t => t = s) _ ht
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient a (fun w => nativeCell w = s)
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, timersDataReceived, hg, hs, ht, hd, getDev, branch, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold nativeCell at *; simp_all [CurrentRx]

theorem timersTraversal_cell (pid : PeerId) : SameView nativeCell (timersTraversal pid) := by
  apply SameView.of_wp
  intro s
  have hg := (getPeer_cell pid).wp (fun t => t = s)
  have ht := fun delay => (modPeerTimer_cell .timerJiffiesTraversal pid .persistentKeepalive delay).wp (fun t => t = s)
  have hd := fun delay => discard_view_spec nativeCell (fun t => t = s) _ (ht delay)
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient a (fun w => nativeCell w = s)
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, timersTraversal, hg, ht, hd, branchCmp]

/-- Queueing a handshake can release the extra peer reference while preserving
the device index and complete decrypt ring. -/

theorem sendQueuedHandshakeInitiation_cell (pid : PeerId) (retry : Bool) :
    SameView nativeCell (sendQueuedHandshakeInitiation pid retry) := by
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have hg := getPeer_cell_spec P pid
  have hs := fun p => setPeer_cell_spec P pid p
  have hn := (requireNotPending_cell pid "queueing a handshake").wp P
  have hc := fun date => (branchExpired_sameWGWorld .queuedNotExpired date REKEY_TIMEOUT (!·)).wp (fun w => P (nativeCell w))
  have hget := (peerGet_cell pid).wp P
  have hput := (peerPut_cell (some pid)).wp P
  have hqueue := (modifyDev_cell (fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})
    (fun _ => rfl) (fun _ => rfl)).wp P
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => P (nativeCell w)) (fun _ w => P (nativeCell w)) :=
    hoare_liftAmbient a (fun w => P (nativeCell w))
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, sendQueuedHandshakeInitiation, hg, hs, hn, hc, hget, hput, hqueue, branch, peekQueuedUnit, recordQueued, ambient]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold nativeCell at *; simp_all [CurrentRx])
  all_goals subst s
  all_goals rfl

theorem keepKeyFreshRx_cell (pid : PeerId) : SameView nativeCell (keepKeyFreshRx pid) := by
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have hg := getPeer_cell_spec P pid
  have hs := fun p => setPeer_cell_spec P pid p
  have hk := fun id => (getKeypair_cell id).wp P
  have ht := fun date delay => (branchExpired_sameWGWorld .rxFreshExpired date delay).wp (fun w => P (nativeCell w))
  have hq := (sendQueuedHandshakeInitiation_cell pid false).wp P
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => P (nativeCell w)) (fun _ w => P (nativeCell w)) :=
    hoare_liftAmbient a (fun w => P (nativeCell w))
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, keepKeyFreshRx, hg, hs, hk, ht, hq, WG.andM, branch, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold nativeCell at *; simp_all [CurrentRx])
  all_goals subst s
  all_goals rfl

theorem txDevice_cell (u : TxDeviceUpdate) : SameView nativeCell (modifyDev u.apply) :=
  modifyDev_cell _ (fun d => by cases u <;> rfl) (fun d => by cases u <;> rfl)

theorem cpumaskChooseOnline_cell (pid : PeerId) : SameView nativeCell (cpumaskChooseOnline pid) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_cell_spec (fun t => t = s) pid
  have hs := fun p => setPeer_cell_spec (fun t => t = s) pid p
  mvcgen [cpumaskChooseOnline, hg, hs, branch, AmbientM.branch]
  all_goals try exact ((⇓? _ w => ⌜nativeCell w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals try (unfold nativeCell at *; simp_all [CurrentRx, Option.bind_map, Function.comp_def])
  all_goals trivial

theorem enqueuePerDeviceAndPeer_cell (pid : PeerId) (item : List SkbId) :
    SameView nativeCell (enqueuePerDeviceAndPeer pid item) := by
  apply SameView.of_wp
  intro s
  have skb {α : Type} (a : SkbM α) :
      Hoare (liftSkb a) (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) := by
    apply hoare_liftSkb a
    intro w d store hi hd
    simpa [nativeCell, hd] using hi
  unfold Hoare at skb
  have hg := getPeer_cell_spec (fun t => t = s) pid
  have hs := fun p => setPeer_cell_spec (fun t => t = s) pid p
  have hc := fun last => (cell_kernel (cpumaskNextOnlineFrom_sameStore last)).wp (fun t => t = s)
  have hd := fun u => (txDevice_cell u).wp (fun t => t = s)
  have hcpu := fun cpu => hd (.cpu cpu)
  have hring := hd (.ring item)
  have queued : Hoare (queueDeviceWork .encryptWorker : WG.M Unit)
      (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient (AmbientM.queueDeviceWork .encryptWorker) _
  unfold Hoare at queued
  mvcgen [enqueuePerDeviceAndPeer, hg, hs, hc, hcpu, hring,
    setTxSkb, skb, queued, getDev, modifyDev, branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold nativeCell at *; simp_all [CurrentRx, Option.bind_map, Function.comp_def]

theorem enqueuePerPeerTx_cell (item : List SkbId) (state : PacketState) :
    SameView nativeCell (enqueuePerPeerTx item state) := by
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have skb {α : Type} (a : SkbM α) :
      Hoare (liftSkb a) (fun w => P (nativeCell w)) (fun _ w => P (nativeCell w)) := by
    apply hoare_liftSkb a
    intro w d store hi hd
    simpa [nativeCell, hd] using hi
  unfold Hoare at skb
  have hk := fun id => (getKeypair_cell id).wp P
  have hg := fun pid => (getPeer_cell pid).wp P
  have hget := fun pid => (peerGet_cell pid).wp P
  have hput := fun pid => (peerPut_cell pid).wp P
  have hcpu := fun pid => (cpumaskChooseOnline_cell pid).wp P
  have hdev := fun pid => (txDevice_cell (.work pid)).wp P
  have peek (pid : PeerId) : Hoare (peekQueuedUnit .txWorker pid : WG.M Bool)
      (fun w => P (nativeCell w)) (fun _ w => P (nativeCell w)) :=
    hoare_liftAmbient (AmbientM.peekQueuedUnit .txWorker pid) _
  have recorded (pid : PeerId) : Hoare (recordQueued .txWorker pid : WG.M Unit)
      (fun w => P (nativeCell w)) (fun _ w => P (nativeCell w)) :=
    hoare_liftAmbient (AmbientM.recordQueued .txWorker pid) _
  unfold Hoare at peek recorded
  have howner := fun o => indexOwner_peerDeref_preserves o (fun w => P (nativeCell w))
  unfold Preserves Hoare at howner
  mvcgen [enqueuePerPeerTx, howner, hk, hg, hget, hput, hcpu, hdev,
    getTxSkb, setTxSkb, skb, peek, recorded, getDev, modifyDev,
    branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold nativeCell at *; simp_all [Option.bind_map, Function.comp_def])
  all_goals subst s
  all_goals rfl

theorem createData_cell (pid : PeerId) (item : List SkbId) : SameView nativeCell (createData pid item) := by
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have skb {α : Type} (a : SkbM α) :
      Hoare (liftSkb a) (fun w => P (nativeCell w)) (fun _ w => P (nativeCell w)) := by
    apply hoare_liftSkb a
    intro w d store hi hd
    simpa [nativeCell, hd] using hi
  unfold Hoare at skb
  have hg := (getPeer_cell pid).wp P
  have hd := (enqueuePerDeviceAndPeer_cell pid item).wp P
  have hp := (enqueuePerPeerTx_cell item .dead).wp P
  have hk := fun id => (keypairPut_cell id false).wp P
  have hr := (peerPut_cell (some pid)).wp P
  mvcgen [createData, hg, hd, hp, hk, hr,
    getTxSkb, freeTxSkb, skb, branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals try exact ((⇓? _ w => ⌜P (nativeCell w)⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold nativeCell at *; simp_all [Option.bind_map, Function.comp_def])
  all_goals try subst s
  all_goals first | rfl | trivial

theorem stagedOutNokey_cell (pid : PeerId) (packets : List Packet)
    (keypair : Option KeypairId) (invalid : Bool) :
    SameView nativeCell (stagedOutNokey pid packets keypair invalid) := by
  cases invalid <;> cases keypair <;> apply SameView.of_wp <;> intro s
  all_goals
    let P := fun t => t = s
    have hg := getPeer_cell_spec P pid
    have hs := fun p => setPeer_cell_spec P pid p
    have hk := fun id => (getKeypair_cell id).wp P
    have hset := fun id k => (setKeypair_cell id k).wp P
    have hp := fun kp => (keypairPut_cell kp false).wp P
    have hq := (sendQueuedHandshakeInitiation_cell pid false).wp P
    have hl (α β : Type) := list_view_spec (m := AmbientM) nativeCell (α := α) (β := β) P
    simp only [stagedOutNokey, getPeer_twice, Bool.false_eq_true, ↓reduceIte]
    mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
      hg, hs, hk, hset, hp, hq, branch, invariant, AmbientM.branch, AmbientM.invariant]
  all_goals try exact ((⇓? _ w => ⌜nativeCell w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals try (unfold nativeCell at *; simp_all [CurrentRx, Option.bind_map, Function.comp_def])
  all_goals try subst s
  all_goals first | rfl | trivial

theorem sendStagedPackets_cell (pid : PeerId) : SameView nativeCell (sendStagedPackets pid) := by
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have skb {α : Type} (a : SkbM α) :
      Hoare (liftSkb a) (fun w => P (nativeCell w)) (fun _ w => P (nativeCell w)) := by
    apply hoare_liftSkb a
    intro w d store hi hd
    simpa [nativeCell, hd] using hi
  unfold Hoare at skb
  have hg := getPeer_cell_spec P pid
  have hs := fun p => setPeer_cell_spec P pid p
  have hk := fun id => (getKeypair_cell id).wp P
  have hset := fun id k => (setKeypair_cell id k).wp P
  have hget := fun kp => (keypairGet_cell kp).wp P
  have hp := fun pid => (peerGet_cell pid).wp P
  have hout := fun packets kp invalid => (stagedOutNokey_cell pid packets kp invalid).wp P
  have hput := fun kp => (keypairPut_cell kp false).wp P
  have hqueue := (sendQueuedHandshakeInitiation_cell pid false).wp P
  have ht := fun date => (branchExpired_sameWGWorld .stagedBirthdateExpired date REJECT_AFTER_TIME).wp (fun w => P (nativeCell w))
  have he := fun pkt => (ipTunnelEcnEncap_sameWGWorld pkt).wp (fun w => P (nativeCell w))
  have hn (packets : List DataPacket) := mapM_view_spec nativeCell P newTxSkb packets
    (fun p => skb (SkbStore.newTx p))
  have hc := fun item => (createData_cell pid item).wp P
  have hl (α β : Type) := list_view_spec (m := AmbientM) nativeCell (α := α) (β := β) P
  simp only [sendStagedPackets, getPeer_twice]
  have hw := fun o => indexOwner_peerDeref_preserves o (fun w => P (nativeCell w))
  unfold Preserves Hoare at hw
  mvcgen [hw, -Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list,
    hl, hg, hs, hk, hset, hget, hp, hout, hput, hqueue, ht, he, hn, hc, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, invariant, AmbientM.invariant]
  all_goals try exact ((⇓? _ w => ⌜P (nativeCell w)⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold nativeCell at *; simp_all [CurrentRx, Option.bind_map, Function.comp_def])
  all_goals try subst s
  all_goals first | rfl | trivial

theorem lookup_cell (root : Option NodeId) (bits key : Nat) :
    SameView nativeCell (lookup root bits key) := by
  apply SameView.of_wp
  intro s
  have aip {α : Type} (a : AipM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) := by
    apply hoare_liftAip a
    intro w d trie hi hd
    simpa [nativeCell, hd] using hi
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftAmbient a _
  unfold Hoare at aip ambient
  have hp := fun pid => (peerGetMaybeZero_cell pid).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, lookup, swapEndian, aip, hp, ambient,
    branch, invariant, unsupported]

theorem lookupSrc_cell (protocol : Nat) (bytes : List UInt8) :
    SameView nativeCell (lookupSrc protocol bytes) := by
  apply SameView.of_wp
  intro s
  have hl := fun root bits key => (lookup_cell root bits key).wp (fun t => t = s)
  mvcgen [lookupSrc, hl, getDev, branch, AmbientM.branch, invariant, AmbientM.invariant]

theorem dishonest_cell (why : Dishonest) : SameView nativeCell (dishonest why) :=
  modifyDev_cell _ (fun d => by cases why <;> rfl) (fun d => by cases why <;> rfl)

theorem updateRxStats_cell (pid : PeerId) (len : Nat) :
    SameView nativeCell (updateRxStats pid len) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_cell_spec (fun t => t = s) pid
  have hs := fun p => setPeer_cell_spec (fun t => t = s) pid p
  have hd := (modifyDev_cell (fun d => {d with rxPackets := d.rxPackets + 1, rxBytes := d.rxBytes + len})
    (fun _ => rfl) (fun _ => rfl)).wp (fun t => t = s)
  mvcgen [updateRxStats, hg, hs, hd]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell, Option.map_map, Function.comp_def]

theorem consumeDataDone_cell (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    SameView nativeCell (consumeDataDone pid pkt endpoint) := by
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have hep := (setPeerEndpoint_cell pid endpoint).wp P
  have hk := (receivedWithKeypair_cell pid pkt.keypair).wp P
  have hh := (timersHandshakeComplete_cell pid .walltimeLastHandshakeData).wp P
  have hst := (sendStagedPackets_cell pid).wp P
  have hf := (keepKeyFreshRx_cell pid).wp P
  have ha := (timersAnyAuthenticatedPacketReceived_cell pid).wp P
  have htr := (timersTraversal_cell pid).wp P
  have hdata := (timersDataReceived_cell pid).wp P
  have hstats := fun len => (updateRxStats_cell pid len).wp P
  have herr := fun why => (dishonest_cell why).wp P
  have hecn := fun protocol outer bytes => (cell_kernel (inetEcnDecapsulate_sameWGStore protocol outer bytes)).wp P
  have hl := fun protocol bytes => (lookupSrc_cell protocol bytes).wp P
  have hp := fun peer => (peerPut_cell peer).wp P
  mvcgen [consumeDataDone, hep, hk, hh, hst, hf, ha, htr, hdata, hstats, herr, hecn, hl, hp,
    WG.andM, WG.orM, branch, AmbientM.branch]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold nativeCell at *; simp_all)
  all_goals try subst s
  all_goals rfl


theorem lookupDst_cell (family addr : Nat) :
    SameView nativeCell (lookupDst family addr) := by
  apply SameView.of_wp
  intro s
  have hl := fun root bits key => (lookup_cell root bits key).wp (fun t => t = s)
  mvcgen [lookupDst, hl, getDev, branch, AmbientM.branch, invariant, AmbientM.invariant]

theorem xmitTrim_cell (pid : PeerId) : SameView nativeCell (xmitTrim pid) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_cell_spec (fun t => t = s) pid
  have hs := fun p => setPeer_cell_spec (fun t => t = s) pid p
  have hd := (modifyDev_cell (fun d => {d with txDropped := d.txDropped + 1})
    (fun _ => rfl) (fun _ => rfl)).wp (fun t => t = s)
  have hl (α β : Type) := list_view_spec (m := AmbientM) nativeCell (α := α) (β := β) (fun t => t = s)
  simp only [xmitTrim, Std.Legacy.Range.forIn_eq_forIn_range']
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl, hg, hs, hd, branch, AmbientM.branch]
  all_goals try exact ((⇓? _ w => ⌜nativeCell w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell, Option.map_map, Function.comp_def]

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
  rw [wgXmitSource_eq]
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have hg := fun pid => (getPeer_cell pid).wp P
  have hlookup := (lookupDst_cell family addr).wp P
  have htrim := fun pid => (xmitTrim_cell pid).wp P
  have hsplice := fun pid packets => (xmitSplice_cell pid packets).wp P
  have hstage := fun pid => (sendStagedPackets_cell pid).wp P
  have hput := fun pid => (peerPut_cell pid).wp P
  have hloop := fun sites raised => (cell_kernel (loopbackSend_kernel sites raised)).wp P
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => P (nativeCell w)) (fun _ w => P (nativeCell w)) :=
    hoare_liftAmbient a _
  have routing {α : Type} (a : Net.M α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => P (nativeCell w)) (fun _ w => P (nativeCell w)) := by
    apply hoare_liftRouting a
    intro w route hi
    exact hi
  unfold Hoare at ambient routing
  have herr := (modifyDev_cell (fun d => {d with txErrors := d.txErrors + 1})
    (fun _ => rfl) (fun _ => rfl)).wp P
  have hl (α β : Type) := list_view_spec (m := AmbientM) nativeCell (α := α) (β := β) P
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, -Std.Do.Spec.monadLift_StateT,
    hl, wgXmitSource, hg, hlookup, htrim, hsplice, hstage, hput, hloop, ambient, routing, herr,
    WG.andM, branch, invariant, unsupported, skipCutSites, envOk]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | rfl | trivial

theorem reply4_cell (dst : Nat) (bytes : List UInt8) :
    SameView cell (Leanux.Env.Stack.reply4 dst bytes) := by
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (cell w)) (fun _ w => P (cell w)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have routing {α : Type} (a : Net.M α) :
      Hoare (MonadLift.monadLift (MonadLift.monadLift a : WG.M α) : Leanux.M α)
        (fun w => P (cell w)) (fun _ w => P (cell w)) :=
    ((liftWG_sameProductStore _ (liftRouting_sameWGStore a)).of_factor
      (fun store : ProductStore43 => store.2.2.2.dev.map fun d => (d.ifindex, d.decryptQueue))
      cell (fun _ => rfl)).wp P
  have hg : SameView nativeCell getDev := by
    apply SameView.of_wp
    intro initial
    mvcgen [getDev, invariant, AmbientM.invariant]
  have hd := (sameView_liftWG (fun w => cell w) nativeCell getDev hg
    (fun _ _ _ h => h)).wp P
  have hx (family addr : Nat) (packets : List Packet) (mtu : Nat) :
      ⦃fun w : World => ⌜P (cell w)⌝⦄
        (MonadLift.monadLift (wgXmit family addr packets mtu) : Leanux.M Int)
      ⦃⇓? _ w => ⌜P (cell w)⌝⦄ :=
    (sameView_liftWG cell nativeCell (wgXmit family addr packets mtu)
      (wgXmit_cell family addr packets mtu) (fun _ _ _ h => h)).wp P
  have discardSpec (α : Type) :=
    discard_view_spec (m := Except Stop) (fun w : World => cell w) (α := α) P
  unfold Hoare at ambient routing
  mvcgen [-Std.Do.Spec.monadLift_StateT, Leanux.Env.Stack.reply4,
    skipCut, ambient, routing, hd, hx, discardSpec, unsupported]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals subst s
  all_goals rfl

theorem receive4_cell (bytes : List UInt8) :
    SameView cell (Leanux.Env.Stack.receive4 bytes) := by
  have stopped (a : Leanux.M Unit) (failure : ∀ w, ∃ e, a.run w = .error e)
      (tail : Unit → Leanux.M Unit) : SameView cell (a >>= tail) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    obtain ⟨e, he⟩ := failure w
    simp only [StateT.run_bind, he, Except.bind] at hr
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
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have h4 := (receive4_cell bytes).wp P
  have h6 := ((stackReceive6_sameKernel bytes).of_factor
    (fun store : ProductStore43 => store.2.2.2.dev.map fun d => (d.ifindex, d.decryptQueue))
    (fun w => cell w) (fun _ => rfl)).wp P
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (cell w)) (fun _ w => P (cell w)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, Leanux.Env.deliverInner,
    Leanux.Env.Stack.receive, h4, h6, invariant, ambient]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals subst s
  all_goals rfl

theorem stackForM_cell (packets : List (List UInt8)) :
    SameView cell (packets.forM Leanux.Env.deliverInner) := by
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have hi : ∀ packets : List (List UInt8),
      ⦃fun w => ⌜P (cell w)⌝⦄ packets.forM Leanux.Env.deliverInner
        ⦃⇓? _ w => ⌜P (cell w)⌝⦄ := by
    intro xs
    induction xs with
    | nil => mvcgen
    | cons bytes xs ih =>
      have hb := (deliverInner_cell bytes).wp P
      simp only [List.forM_eq_forM, List.forM_cons] at *
      mvcgen [hb, ih]
  mvcgen [hi]
  all_goals try subst s
  all_goals rfl

end Leanux.Proofs.WG.Queues.RxRing
