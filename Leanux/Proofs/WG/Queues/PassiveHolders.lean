import Leanux.Proofs.WG.Queues.DurableHolders

/-! The actual receive completion and Stack reply paths retain base-list,
clear-work and active dump holders while their TX/send handoffs are accounted
separately. These are native field frames, not assumptions on final funding. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.PassiveHolders
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do Lifetimes
open DurableHolders

abbrev At (initial : List PeerId × List PeerId × Option PeerId × Option PeerId)
    (w : WGWorld) : Prop := passiveView w = initial

private theorem store {α : Type} {a : WG.M α} (ha : SameWGStore a) (initial) :
    Preserves (At initial) a :=
  (ha.of_factor (fun s : WGStoreView =>
    ((s.dev.map Device.peerList).getD [],(s.dev.map Device.clearWorkQueue).getD [],
      activeCursor s.nlSock7,activeCursor s.nlSock8)) passiveView (fun _ => rfl)).wp (· = initial)

private theorem modifyDevice (f : Device → Device)
    (list : ∀ d, (f d).peerList = d.peerList)
    (clear : ∀ d, (f d).clearWorkQueue = d.clearWorkQueue) (initial) :
    Preserves (At initial) (modifyDev f) := by
  apply hoare_modify
  intro w hi
  simpa only [At,passiveView,Option.map_map,Function.comp_def,list,clear] using hi

private theorem index {α : Type} (a : IndexM α) (initial) :
    Preserves (At initial) (liftIndex a) := by
  apply hoare_liftIndex
  intro w d table hi hd
  simpa only [At,passiveView,hd,Option.map_some] using hi

macro "passive_base " initial:term : tactic => `(tactic| first
  | rxstack_preserves_join
  | (rx_retention_head getPeer
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a p v b hi hr
     simpa only [(getPeer_normal _ w v p a b hr).1] using hi)
  | (rx_retention_head getDev; exact store getDev_sameWGStore $initial)
  | (rx_retention_head getKeypair
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a k v b hi hr
     simpa only [(KeyTimes.getKeypair_return _ w v k a b hr).1] using hi)
  | (rx_retention_head setPeer; unfold setPeer)
  | (rx_retention_head setKeypair; unfold setKeypair)
  | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (At $initial))
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (allocation_release_lift_from IndexM; exact index _ $initial)
  | (rx_retention_head get; exact hoare_consequence (hoare_get _)
      (fun _ h => h) (fun _ _ h => h.2))
  | (rx_retention_head modifyDev; apply modifyDevice; all_goals intro d; rfl)
  | (rx_retention_head modify; apply hoare_modify; intro w h; exact h)
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (At $initial)
     intro x b
     change Preserves (At $initial) _)
  | (rx_retention_head Functor.discard
     apply discard_view_spec id (At $initial)
     change Preserves (At $initial) _)
  | (first | rx_retention_head throw | rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b hi hr
     cases hr)
  | rx_retention_step)

private theorem peerGet_preserves (pid : PeerId) (initial) :
    Preserves (At initial) (peerGet pid) := by
  unfold peerGet refcountInc
  simp (config := {zeta := false}) only [requireNotPending,pure_bind,branch,branchCmp,unsupported]
  repeat' passive_base initial

private theorem peerMaybe_preserves (pid : Option PeerId) (initial) :
    Preserves (At initial) (peerGetMaybeZero pid) := by
  unfold peerGetMaybeZero refcountIncNotZero
  simp (config := {zeta := false}) only [requireNotPending,pure_bind,branch,branchCmp,invariant,unsupported]
  repeat' passive_base initial

theorem peerPut_preserves (pid : Option PeerId) (initial) :
    Preserves (At initial) (peerPut pid) := by
  unfold peerPut refcountDecAndTest retirePeerUnits
  simp (config := {zeta := false}) only [requireNotPending,pure_bind,branch,branchCmp,
    invariant,unsupported,modifyAmbient]
  repeat' passive_base initial

private theorem keypairGet_preserves (kid : Option KeypairId) (initial) :
    Preserves (At initial) (keypairGet kid) := by
  unfold keypairGet refcountIncNotZero
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,unsupported]
  repeat' passive_base initial

private theorem keypairPut_preserves (kid : Option KeypairId) (now : Bool) (initial) :
    Preserves (At initial) (keypairPut kid now) := by
  unfold keypairPut refcountDecAndTest
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,unsupported]
  repeat' passive_base initial

macro "passive_traffic " initial:term : tactic => `(tactic| first
  | (rx_retention_head peerGet; exact peerGet_preserves _ $initial)
  | (rx_retention_head peerPut; exact peerPut_preserves _ $initial)
  | (rx_retention_head keypairGet; exact keypairGet_preserves _ $initial)
  | (rx_retention_head keypairPut; exact keypairPut_preserves _ _ $initial)
  | passive_base $initial)

macro "passive_skb" : tactic => `(tactic| first
  | (rx_retention_head getTxSkb; unfold getTxSkb)
  | (rx_retention_head setTxSkb; unfold setTxSkb)
  | (rx_retention_head newTxSkb; unfold newTxSkb)
  | (rx_retention_head freeTxSkb; unfold freeTxSkb)
  | (rx_retention_head liftSkb
     apply hoare_liftSkb
     intro w d store hi hd
     simpa only [At,passiveView,hd,Option.map_some] using hi))

private theorem place_preserves (pid : PeerId) (t : PeerTimer) (expires clk : UInt64)
    (unit : Option Nat) (initial) : Preserves (At initial) (placeOnWheel pid t expires clk unit) := by
  unfold placeOnWheel
  simp (config := {zeta := false}) only [hidden,peekHiddenSite,invariant]
  repeat' passive_traffic initial

private theorem arm_preserves (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (jc : Option UInt64) (initial) : Preserves (At initial) (armTimer pid timer delay jc) := by
  unfold armTimer
  simp (config := {zeta := false}) only [getAmbient,hidden,invariant,unsupported]
  repeat' first
    | rxstack_preserves_join
    | (rx_retention_head placeOnWheel; exact place_preserves _ _ _ _ _ initial)
    | passive_traffic initial

private theorem del_preserves (pid : PeerId) (timer : PeerTimer) (initial) :
    Preserves (At initial) (delTimer pid timer) := by
  unfold delTimer
  repeat' passive_traffic initial

private theorem mod_preserves (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) (initial) :
    Preserves (At initial) (modPeerTimer site pid timer delay) := by
  unfold modPeerTimer modPeerTimerGuard WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp (At initial))
    | (rx_retention_head armTimer; exact arm_preserves _ _ _ _ initial)
    | passive_traffic initial

private theorem sendQueued_preserves (pid : PeerId) (retry : Bool) (initial) :
    Preserves (At initial) (sendQueuedHandshakeInitiation pid retry) := by
  unfold sendQueuedHandshakeInitiation
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' passive_traffic initial

private theorem received_preserves (pid : PeerId) (kid : KeypairId) (initial) :
    Preserves (At initial) (receivedWithKeypair pid kid) := by
  unfold receivedWithKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  simp (config := {zeta := false}) only [branch]
  repeat' passive_traffic initial

private theorem fresh_preserves (pid : PeerId) (initial) :
    Preserves (At initial) (keepKeyFreshRx pid) := by
  unfold keepKeyFreshRx WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact sendQueued_preserves _ _ initial)
    | passive_traffic initial

private theorem choose_preserves (pid : PeerId) (initial) :
    Preserves (At initial) (cpumaskChooseOnline pid) := by
  unfold cpumaskChooseOnline
  simp (config := {zeta := false}) only [branch,Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' passive_traffic initial

private theorem enqueueDevice_preserves (pid : PeerId) (item : List SkbId) (initial) :
    Preserves (At initial) (enqueuePerDeviceAndPeer pid item) := by
  unfold enqueuePerDeviceAndPeer
  simp (config := {zeta := false}) only [branch,queueDeviceWork,invariant]
  repeat' first
    | (rx_retention_head cpumaskNextOnlineFrom; exact store (cpumaskNextOnlineFrom_sameStore _) initial)
    | passive_skb
    | passive_traffic initial

private theorem enqueuePeer_preserves (item : List SkbId) (state : PacketState) (initial) :
    Preserves (At initial) (enqueuePerPeerTx item state) := by
  unfold enqueuePerPeerTx
  simp (config := {zeta := false}) only [peekQueuedUnit,recordQueued,invariant]
  repeat' first
    | (rx_retention_head cpumaskChooseOnline; exact choose_preserves _ initial)
    | passive_skb
    | passive_traffic initial

private theorem create_preserves (pid : PeerId) (item : List SkbId) (initial) :
    Preserves (At initial) (createData pid item) := by
  unfold createData
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head enqueuePerDeviceAndPeer; exact enqueueDevice_preserves _ _ initial)
    | (rx_retention_head enqueuePerPeerTx; exact enqueuePeer_preserves _ _ initial)
    | passive_skb
    | passive_traffic initial

private theorem noKey_preserves (pid : PeerId) (packets : List Leanux.WG.Packet)
    (keypair : Option KeypairId) (invalid : Bool) (initial) :
    Preserves (At initial) (stagedOutNokey pid packets keypair invalid) := by
  unfold stagedOutNokey
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact sendQueued_preserves _ _ initial)
    | passive_traffic initial

private theorem submit_preserves (pid kid : Nat) (packets : List DataPacket) (initial) :
    Preserves (At initial) (stagedSubmit pid kid packets) := by
  unfold stagedSubmit Affiliation.sendAcquire
  repeat' first
    | (rx_retention_head createData; exact create_preserves _ _ initial)
    | (rx_retention_head List.mapM
       apply mapM_view_spec id (At initial)
       intro packet
       change Preserves (At initial) _)
    | passive_skb
    | passive_traffic initial

private theorem stagedKey_preserves (pid kid : Nat) (packets : List Leanux.WG.Packet) (initial) :
    Preserves (At initial) (stagedKeySource pid kid packets) := by
  unfold stagedKeySource
  simp (config := {zeta := false}) only [branch,branchCmp]
  repeat' first
    | (rx_retention_head stagedOutNokey; exact noKey_preserves _ _ _ _ initial)
    | (rx_retention_head stagedSubmit; exact submit_preserves _ _ _ initial)
    | (rx_retention_head ipTunnelEcnEncap; exact (ipTunnelEcnEncap_sameWGWorld _).wp (At initial))
    | passive_traffic initial

theorem staged_preserves (pid : PeerId) (initial) :
    Preserves (At initial) (sendStagedPackets pid) := by
  rw [← stagedFullSource_eq]
  unfold stagedFullSource
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head stagedOutNokey; exact noKey_preserves _ _ _ _ initial)
    | (rx_retention_head stagedKeySource; exact stagedKey_preserves _ _ _ initial)
    | passive_traffic initial

private theorem endpoint_preserves (pid : PeerId) (e : Endpoint) (initial) :
    Preserves (At initial) (setPeerEndpoint pid e) := by
  unfold setPeerEndpoint dstCacheReset requireNotPending
  simp (config := {zeta := false}) only [branch,getAmbient,hiddenJiffies]
  repeat' first
    | (rx_retention_head endpointEq; exact store (endpointEq_sameStore _ _) initial)
    | passive_traffic initial

private theorem lookup_preserves (root : Option NodeId) (bits key : Nat) (initial) :
    Preserves (At initial) (lookup root bits key) := by
  have aip {α : Type} (a : AipM α) : Preserves (At initial) (monadLift a : WG.M α) := by
    apply hoare_liftAip
    intro w d s hi hd
    simpa only [At,passiveView,hd,Option.map_some] using hi
  unfold lookup swapEndian
  simp (config := {zeta := false}) only [branch,unsupported,invariant]
  repeat' first
    | (rx_retention_head peerGetMaybeZero; exact peerMaybe_preserves _ initial)
    | (allocation_release_lift_from AipM; exact aip _)
    | passive_traffic initial

private theorem lookupSrc_preserves (protocol : Nat) (bytes : List UInt8) (initial) :
    Preserves (At initial) (lookupSrc protocol bytes) := by
  unfold lookupSrc
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head lookup; exact lookup_preserves _ _ _ initial)
    | passive_traffic initial

private theorem handshake_preserves (pid : PeerId) (site : HiddenSite) (initial) :
    Preserves (At initial) (timersHandshakeComplete pid site) := by
  unfold timersHandshakeComplete
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | (rx_retention_head delTimer; exact del_preserves _ _ initial)
    | passive_traffic initial

private theorem traversal_preserves (pid : PeerId) (initial) :
    Preserves (At initial) (timersTraversal pid) := by
  unfold timersTraversal
  simp (config := {zeta := false}) only [branchCmp]
  repeat' first
    | (rx_retention_head modPeerTimer; exact mod_preserves _ _ _ _ initial)
    | passive_traffic initial

private theorem dataReceived_preserves (pid : PeerId) (initial) :
    Preserves (At initial) (timersDataReceived pid) := by
  unfold timersDataReceived
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head modPeerTimer; exact mod_preserves _ _ _ _ initial)
    | passive_traffic initial

private theorem stats_preserves (pid : PeerId) (len : Nat) (initial) :
    Preserves (At initial) (updateRxStats pid len) := by
  unfold updateRxStats
  repeat' passive_traffic initial

private theorem dishonest_preserves (why : Dishonest) (initial) :
    Preserves (At initial) (dishonest why) := by
  cases why <;> unfold dishonest <;> apply modifyDevice <;> intro d <;> rfl

/-- The complete native call retains the passive holder fields, including
staged sending and the source lookup's peer payment. -/
theorem consumeDataDone_preserves (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) (initial) :
    Preserves (At initial) (consumeDataDone pid pkt endpoint) := by
  unfold consumeDataDone WG.andM WG.orM timersAnyAuthenticatedPacketReceived
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head setPeerEndpoint; exact endpoint_preserves _ _ initial)
    | (rx_retention_head receivedWithKeypair; exact received_preserves _ _ initial)
    | (rx_retention_head sendStagedPackets; exact staged_preserves _ initial)
    | (rx_retention_head keepKeyFreshRx; exact fresh_preserves _ initial)
    | (rx_retention_head timersHandshakeComplete; exact handshake_preserves _ _ initial)
    | (rx_retention_head timersTraversal; exact traversal_preserves _ initial)
    | (rx_retention_head timersDataReceived; exact dataReceived_preserves _ initial)
    | (rx_retention_head delTimer; exact del_preserves _ _ initial)
    | (rx_retention_head updateRxStats; exact stats_preserves _ _ initial)
    | (rx_retention_head dishonest; exact dishonest_preserves _ initial)
    | (rx_retention_head lookupSrc; exact lookupSrc_preserves _ _ initial)
    | (rx_retention_head inetEcnDecapsulate; exact store (inetEcnDecapsulate_sameWGStore _ _ _) initial)
    | passive_traffic initial

private theorem lookupDst_preserves (family addr : Nat) (initial) :
    Preserves (At initial) (lookupDst family addr) := by
  unfold lookupDst
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head lookup; exact lookup_preserves _ _ _ initial)
    | passive_traffic initial

private theorem trim_preserves (pid : PeerId) (initial) :
    Preserves (At initial) (xmitTrim pid) := by
  unfold xmitTrim
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch]
  repeat' passive_traffic initial

private theorem splice_preserves (pid : PeerId) (packets : List WG.Packet) (initial) :
    Preserves (At initial) (xmitSplice pid packets) := by
  unfold xmitSplice
  repeat' passive_traffic initial

/-- Every normal transmit return, including negative status, retains passive
holder fields. Loopback's actual pending-NAPI guard is retained. -/
theorem wgXmit_preserves (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) (initial) :
    Preserves (At initial) (wgXmit family addr packets mtu) := by
  rw [wgXmitSource_eq]
  unfold wgXmitSource WG.andM
  simp (config := {zeta := false}) only [branch,invariant,skipCutSites,envOk]
  repeat' first
    | (rx_retention_head lookupDst; exact lookupDst_preserves _ _ initial)
    | (rx_retention_head xmitTrim; exact trim_preserves _ initial)
    | (rx_retention_head xmitSplice; exact splice_preserves _ _ initial)
    | (rx_retention_head sendStagedPackets; exact staged_preserves _ initial)
    | (rx_retention_head loopbackSend; exact store (loopbackSend_kernel _ _) initial)
    | (allocation_release_lift_from Net.M; exact hoare_liftRouting _ _ (fun _ _ hi => hi))
    | passive_traffic initial

private theorem product_store {α : Type} {a : Leanux.M α} (frame : SameProductStore a) (initial) :
    Preserves (fun w : World => At initial w.wg) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi hr
  have fields := (ProjectedAction.iff_run _ _ _).mp frame w result v hr
  have wg : wgStoreView v.wg = wgStoreView w.wg := congrArg (fun s : ProductStore43 => s.2.2.2) fields
  have passive : passiveView v.wg = passiveView w.wg := congrArg
    (fun s : WGStoreView => ((s.dev.map Device.peerList).getD [],
      (s.dev.map Device.clearWorkQueue).getD [],activeCursor s.nlSock7,activeCursor s.nlSock8)) wg
  exact passive.trans hi

private theorem reply4_preserves (dst : Nat) (bytes : List UInt8) (initial) :
    Preserves (fun w : World => At initial w.wg) (Leanux.Env.Stack.reply4 dst bytes) := by
  let P := fun w : World => At initial w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have routing {α : Type} (a : Net.M α) : Preserves P (monadLift a : Leanux.M α) :=
    PublicationPoll.native_product _ _ (store (liftRouting_sameWGStore a) initial)
  have dev : Preserves P (monadLift getDev : Leanux.M Device) :=
    PublicationPoll.native_product _ _ (store getDev_sameWGStore initial)
  have send (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
      Preserves P (monadLift (wgXmit family addr packets mtu) : Leanux.M Int) :=
    PublicationPoll.native_product _ _ (wgXmit_preserves family addr packets mtu initial)
  have discarded {α : Type} (a : Leanux.M α) (ha : Preserves P a) : Preserves P (Functor.discard a) :=
    discard_view_spec id P a ha
  rxstack_preserves_source [Leanux.Env.Stack.reply4,skipCut,unsupported]
    using [dev,send,ambient,routing,discarded]

private theorem receive4_preserves (bytes : List UInt8) (initial) :
    Preserves (fun w : World => At initial w.wg) (Leanux.Env.Stack.receive4 bytes) := by
  let P := fun w : World => At initial w.wg
  have stopped (a : Leanux.M Unit) (hs : ∀ w, ∃ e, a.run w = .error e)
      (next : Unit → Leanux.M Unit) : Preserves P (a >>= next) :=
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentStack.«0».Leanux.Proofs.WG.CurrentStack.stopped_bind) a hs next P
  have excluded := fun row tail => stopped (Leanux.Env.Stack.excluded row)
    (stackExcluded_failure row) tail
  have invalid := fun why tail => stopped (Leanux.invariant why) (fun _ => ⟨_,rfl⟩) tail
  have unsupported := fun why tail => stopped (Leanux.unsupported why) (fun _ => ⟨_,rfl⟩) tail
  have excludedAlone (row : String) : Preserves P (Leanux.Env.Stack.excluded row) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w x v hi hr
    obtain ⟨e,he⟩ := stackExcluded_failure row w
    rw [he] at hr
    contradiction
  have route (src dst : Nat) : Preserves P
      (monadLift (monadLift (Net.routeInput4 src dst) : WG.M _) : Leanux.M _) :=
    PublicationPoll.native_product _ _ (store (liftRouting_sameWGStore _) initial)
  have read : Preserves P (getWG : Leanux.M WGWorld) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w x v hi hr
    cases hr
    exact hi
  have write (f : EnvWorld → EnvWorld) : Preserves P (modifyEnv f) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w x v hi hr
    cases hr
    exact hi
  unfold Leanux.Env.Stack.receive4
  repeat' first
    | (env_bind_head Leanux.Env.Stack.excluded; exact excluded _ _)
    | (env_bind_head Leanux.invariant; exact invalid _ _)
    | (env_bind_head Leanux.unsupported; exact unsupported _ _)
    | (allocation_release_head Leanux.Env.Stack.excluded; exact excludedAlone _)
    | (allocation_release_head Leanux.Env.Stack.reply4; exact reply4_preserves _ _ initial)
    | (allocation_release_head MonadLift.monadLift; exact route _ _)
    | (allocation_release_head liftM; exact route _ _)
    | (allocation_release_head getWG; exact read)
    | (allocation_release_head modifyEnv; exact write _)
    | rx_retention_step
    | env_ordinary_head_reduce
    | env_ordinary_head_match

theorem deliverInner_preserves (bytes : List UInt8) (initial) :
    Preserves (fun w : World => At initial w.wg) (Leanux.Env.deliverInner bytes) := by
  have h4 := receive4_preserves bytes initial
  have h6 := product_store (stackReceive6_sameKernel bytes) initial
  have ambient {α : Type} (a : AmbientM α) :
      Preserves (fun w : World => At initial w.wg) (monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ hi => hi)
  rxstack_preserves_source [Leanux.Env.deliverInner,Leanux.Env.Stack.receive,invariant]
    using [h4,h6,ambient]

/-- The concrete product-domain Stack callback used by the actual receive
poll. Every source Stop remains allowed. -/
theorem stack_preserves (packets : List (List UInt8)) (initial) :
    Preserves (fun w : World => At initial w.wg) (packets.forM Leanux.Env.deliverInner) := by
  induction packets with
  | nil => exact preserves_pure _
  | cons bytes rest ih =>
    simp only [List.forM_eq_forM,List.forM_cons]
    exact preserves_bind (deliverInner_preserves bytes initial) (fun _ => ih)

end Leanux.Proofs.WG.Queues.RxCredits.PassiveHolders
