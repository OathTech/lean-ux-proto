import Leanux.Proofs.WG.Origins.OwnerDecrypt
import Leanux.Proofs.WG.Origins.OwnerFocus
import Leanux.Proofs.WG.Queues.RxIngressStable

/-! Native receive completion retains the receiving-owner carrier. The frame
omits the TX allocation frontier, which staged sending may advance. Every
contract concerns normal endpoints; source guards and failed records remain. -/
namespace Leanux.Proofs.WG.OwnerCompletion
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues.RxCredits OwnerBounds

def geometry (w : WGWorld) :=
  (w.dev.map fun d => (d.ifindex,d.nextPeer,d.nextKeypairId), rxView w)

private theorem frame {α : Type} {a : WG.M α}
    (metadata : SameView allocationMetadata a) (rx : SameView rxView a) :
    SameView geometry a := by
  apply SameView.product
  · exact metadata.of_factor (fun m : AllocationMetadata =>
      m.device.map fun d => (d.epoch,d.nextPeer,d.nextKeypair)) _ (fun _ => by simp only [allocationMetadata,Option.map_map,Function.comp_def,deviceAllocationMetadata])
  · exact rx

private theorem store {α : Type} {a : WG.M α} (ha : SameWGStore a) :
    SameView geometry a :=
  ha.of_factor (fun s : WGStoreView =>
    (s.dev.map fun d => (d.ifindex,d.nextPeer,d.nextKeypairId),
      (s.dev.map (·.ifindex), fun id => s.dev.bind fun d => d.rxSkbs[id]?))) _ (fun _ => rfl)

private theorem skb {α : Type} (a : SkbM α)
    (rx : SameView rxView (liftSkb a)) : SameView geometry (liftSkb a) := by
  apply SameView.product
  · intro initial
    apply hoare_liftSkb
    intro w d s hi hd
    simpa only [hd, Option.map_some] using hi
  · exact rx

private theorem protect_skb {α : Type} (a : SkbM α)
    (rx : SameView protectView (liftSkb a)) : SameView geometry (liftSkb a) :=
  skb a (rx.of_factor (fun v => v.2.1) _ (fun _ => rfl))

private theorem peerPay (pid : Option PeerId) : SameView geometry (peerPut pid) :=
  frame (peerPut_metadata pid) (peerPut_rxView pid)

private theorem keyPay (kid : Option KeypairId) (now : Bool) :
    SameView geometry (keypairPut kid now) :=
  frame (by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a result v b hr
    cases result
    exact (keypairPut_retention kid now w v a b hr).metadata)
    ((keypairPut_credit_frame kid now).factor Prod.snd)

private theorem readPeer (pid : PeerId) : SameView geometry (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a p v b hr
  exact congrArg geometry (Queues.getPeer_normal pid w v p a b hr).1

private theorem readKey (kid : KeypairId) : SameView geometry (getKeypair kid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a k v b hr
  exact congrArg geometry (KeyTimes.getKeypair_return kid w v k a b hr).1

private theorem modifyDevice (f : Device → Device)
    (he : ∀ d, (f d).ifindex = d.ifindex)
    (hp : ∀ d, (f d).nextPeer = d.nextPeer)
    (hk : ∀ d, (f d).nextKeypairId = d.nextKeypairId)
    (hr : ∀ d, (f d).rxSkbs = d.rxSkbs) : SameView geometry (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases run
  simp only [geometry,rxView,Option.map_map,Option.bind_map,Function.comp_def,he,hp,hk,hr]

macro "completion_step " initial:term : tactic => `(tactic| first
  | (allocation_release_head getDev; exact (store getDev_sameWGStore).wp (fun s => s = $initial))
  | (allocation_release_head getPeer; exact (readPeer _).wp (fun s => s = $initial))
  | (allocation_release_head getKeypair; exact (readKey _).wp (fun s => s = $initial))
  | (allocation_release_head peerPut; exact (peerPay _).wp (fun s => s = $initial))
  | (allocation_release_head keypairPut; exact (keyPay _ _).wp (fun s => s = $initial))
  | (allocation_release_head setPeer; unfold setPeer)
  | (allocation_release_head setKeypair; unfold setKeypair)
  | (allocation_release_head modifyDev
     apply (modifyDevice _ ?_ ?_ ?_ ?_).wp (fun s => s = $initial)
     all_goals intro d; rfl)
  | (allocation_release_head get
     exact hoare_consequence (hoare_get (fun w => geometry w = $initial))
       (fun _ h => h) (fun _ _ h => h.2))
  | (allocation_release_head modify
     apply hoare_modify
     intro w hi
     exact hi)
  | (allocation_release_head IndexOwner.peerDeref
     exact indexOwner_peerDeref_preserves _ (fun w => geometry w = $initial))
  | (allocation_release_lift_from AmbientM
     exact hoare_liftAmbient _ (fun w => geometry w = $initial))
  | (allocation_release_head ForIn.forIn
     apply list_view_spec geometry (fun s => s = $initial)
     intro x b
     change Preserves (fun w => geometry w = $initial) _)
  | (first | allocation_release_head throw | allocation_release_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b hi hr
     cases hr)
  | (allocation_release_head Functor.discard
     apply discard_view_spec geometry (fun s => s = $initial)
     change Preserves (fun w => geometry w = $initial) _)
  | allocation_release_step)

macro "completion_skb " initial:term : tactic => `(tactic| first
  | (allocation_release_head getTxSkb
     exact (protect_skb _ (getTx_protect _)).wp (fun s => s = $initial))
  | (allocation_release_head setTxSkb
     exact (protect_skb _ (setTx_protect _ _)).wp (fun s => s = $initial))
  | (allocation_release_head freeTxSkb
     exact (protect_skb _ (freeTx_protect _)).wp (fun s => s = $initial))
  | (allocation_release_head newTxSkb
     exact (protect_skb _ (newTx_protect _)).wp (fun s => s = $initial)))

private theorem peerGet_geometry (pid : PeerId) : SameView geometry (peerGet pid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold peerGet
  simp (config := {zeta := false}) only [requireNotPending,pure_bind,refcountInc,branch,branchCmp,unsupported]
  repeat' completion_step initial

private theorem keypairGet_geometry (kid : Option KeypairId) :
    SameView geometry (keypairGet kid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold keypairGet
  simp (config := {zeta := false}) only [refcountIncNotZero,branch,branchCmp,unsupported,invariant]
  repeat' completion_step initial


macro "completion_traffic " initial:term : tactic => `(tactic| first
  | (allocation_release_head peerGet; exact (peerGet_geometry _).wp (fun s => s = $initial))
  | (allocation_release_head keypairGet; exact (keypairGet_geometry _).wp (fun s => s = $initial))
  | (allocation_release_head branchExpired
     exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w => geometry w = $initial))
  | completion_skb $initial
  | completion_step $initial)

private theorem place_geometry (pid : PeerId) (t : PeerTimer) (expires clk : UInt64)
    (unit : Option Nat) : SameView geometry (placeOnWheel pid t expires clk unit) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold placeOnWheel
  simp (config := {zeta := false}) only [hidden,peekHiddenSite,invariant]
  repeat' completion_step initial

private theorem arm_geometry (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (jc : Option UInt64) : SameView geometry (armTimer pid timer delay jc) := by
  have ambient {α : Type} (a : AmbientM α) : SameView geometry (monadLift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun w => geometry w = initial)
  have read : SameView geometry (get : WG.M WGWorld) := by
    intro initial
    exact hoare_consequence (hoare_get (fun w => geometry w = initial))
      (fun _ h => h) (fun _ _ h => h.2)
  have dev : SameView geometry getDev := by
    unfold getDev
    apply SameView.bind read
    intro w
    cases w.dev with
    | none => exact ambient (AmbientM.invariant _)
    | some d => exact SameView.pure _ d
  have stopped {α : Type} (e : Stop) : SameView geometry (throw e : WG.M α) := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' hr
    cases hr
  have edit (f : WGWorld → WGWorld) (hf : ∀ w, geometry (f w) = geometry w) :
      SameView geometry (modify f : WG.M Unit) := by
    intro initial
    apply hoare_modify
    intro w hw
    exact (hf w).trans hw
  unfold armTimer
  simp (config := { zeta := false }) only [getAmbient, hidden, invariant, unsupported]
  repeat' first
    | rxqueue_join_let
    | rxqueue_join_use
    | (snapshot_head placeOnWheel; exact place_geometry pid _ _ _ _)
    | (snapshot_head getDev; exact dev)
    | (snapshot_head getPeer; exact readPeer _)
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
    | (snapshot_head modify; exact edit _ (fun _ => rfl))
    | snapshot_head_reduce
    | snapshot_head_match

private theorem del_geometry (pid : PeerId) (t : PeerTimer) :
    SameView geometry (delTimer pid t) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold delTimer
  repeat' completion_step initial

private theorem mod_geometry (site : HiddenSite) (pid : PeerId) (t : PeerTimer) (delay : Nat) :
    SameView geometry (modPeerTimer site pid t delay) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold modPeerTimer modPeerTimerGuard WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head callerJiffies
       exact (callerJiffies_sameWGWorld _).wp (fun w => geometry w = initial))
    | (allocation_release_head armTimer; exact (arm_geometry _ _ _ _).wp (fun s => s = initial))
    | completion_step initial

private theorem sendQueued_geometry (pid : PeerId) (retry : Bool) :
    SameView geometry (sendQueuedHandshakeInitiation pid retry) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold sendQueuedHandshakeInitiation
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' completion_traffic initial

private theorem received_geometry (pid : PeerId) (kid : KeypairId) :
    SameView geometry (receivedWithKeypair pid kid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold receivedWithKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  simp (config := {zeta := false}) only [branch]
  repeat' completion_traffic initial

private theorem fresh_geometry (pid : PeerId) : SameView geometry (keepKeyFreshRx pid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold keepKeyFreshRx WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (allocation_release_head sendQueuedHandshakeInitiation
       exact (sendQueued_geometry _ _).wp (fun s => s = initial))
    | completion_traffic initial

private theorem choose_geometry (pid : PeerId) : SameView geometry (cpumaskChooseOnline pid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold cpumaskChooseOnline
  simp (config := {zeta := false}) only [branch,Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' completion_step initial

private theorem enqueueDevice_geometry (pid : PeerId) (item : List SkbId) :
    SameView geometry (enqueuePerDeviceAndPeer pid item) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold enqueuePerDeviceAndPeer
  simp (config := {zeta := false}) only [branch,queueDeviceWork,invariant]
  repeat' first
    | (allocation_release_head cpumaskNextOnlineFrom
       exact (store (cpumaskNextOnlineFrom_sameStore _)).wp (fun s => s = initial))
    | completion_traffic initial

private theorem enqueuePeer_geometry (item : List SkbId) (state : PacketState) :
    SameView geometry (enqueuePerPeerTx item state) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold enqueuePerPeerTx
  simp (config := {zeta := false}) only [peekQueuedUnit,recordQueued,invariant]
  repeat' first
    | (allocation_release_head cpumaskChooseOnline; exact (choose_geometry _).wp (fun s => s = initial))
    | completion_traffic initial

private theorem create_geometry (pid : PeerId) (item : List SkbId) :
    SameView geometry (createData pid item) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold createData
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (allocation_release_head enqueuePerDeviceAndPeer
       exact (enqueueDevice_geometry _ _).wp (fun s => s = initial))
    | (allocation_release_head enqueuePerPeerTx; exact (enqueuePeer_geometry _ _).wp (fun s => s = initial))
    | completion_traffic initial

private theorem noKey_geometry (pid : PeerId) (packets : List Leanux.WG.Packet)
    (keypair : Option KeypairId) (invalid : Bool) :
    SameView geometry (stagedOutNokey pid packets keypair invalid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold stagedOutNokey
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (allocation_release_head sendQueuedHandshakeInitiation
       exact (sendQueued_geometry _ _).wp (fun s => s = initial))
    | completion_traffic initial

private theorem submit_geometry (pid kid : Nat) (packets : List DataPacket) :
    SameView geometry (stagedSubmit pid kid packets) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold stagedSubmit Affiliation.sendAcquire
  repeat' first
    | (allocation_release_head createData; exact (create_geometry _ _).wp (fun s => s = initial))
    | (allocation_release_head List.mapM
       apply mapM_view_spec geometry (fun s => s = initial)
       intro packet
       change Preserves (fun w => geometry w = initial) _)
    | completion_traffic initial

private theorem stagedKey_geometry (pid kid : Nat) (packets : List Leanux.WG.Packet) :
    SameView geometry (stagedKeySource pid kid packets) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold stagedKeySource
  simp (config := {zeta := false}) only [branch,branchCmp]
  repeat' first
    | (allocation_release_head stagedOutNokey; exact (noKey_geometry _ _ _ _).wp (fun s => s = initial))
    | (allocation_release_head stagedSubmit; exact (submit_geometry _ _ _).wp (fun s => s = initial))
    | (allocation_release_head ipTunnelEcnEncap
       exact (ipTunnelEcnEncap_sameWGWorld _).wp (fun w => geometry w = initial))
    | completion_traffic initial

private theorem staged_geometry (pid : PeerId) : SameView geometry (sendStagedPackets pid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  rw [← stagedFullSource_eq]
  unfold stagedFullSource
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (allocation_release_head stagedOutNokey; exact (noKey_geometry _ _ _ _).wp (fun s => s = initial))
    | (allocation_release_head stagedKeySource; exact (stagedKey_geometry _ _ _).wp (fun s => s = initial))
    | completion_traffic initial


private theorem endpoint_geometry (pid : PeerId) (e : Endpoint) :
    SameView geometry (setPeerEndpoint pid e) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold setPeerEndpoint dstCacheReset requireNotPending
  simp (config := {zeta := false}) only [branch,getAmbient,hiddenJiffies]
  repeat' first
    | (allocation_release_head endpointEq
       exact (store (endpointEq_sameStore _ _)).wp (fun s => s = initial))
    | completion_step initial

private theorem lookup_geometry (protocol : Nat) (bytes : List UInt8) :
    SameView geometry (lookupSrc protocol bytes) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b hr
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (Queues.RxBorrow.lookupSrc_spec protocol bytes (wgStoreView w)) w a result v b rfl hr
  cases result with
  | none =>
    change wgStoreView v = wgStoreView w at borrowed
    have same : v.dev = w.dev := congrArg WGStoreView.dev borrowed
    simp only [geometry,rxView,same]
  | some pid =>
    obtain ⟨d,p,hd,hp,_,hv⟩ := borrowed
    have same := congrArg WGStoreView.dev hv
    change v.dev = some _ at same
    change w.dev = some d at hd
    simp only [geometry,rxView,same,hd,Option.map_some,Option.bind_some]

private theorem handshake_geometry (pid : PeerId) (site : HiddenSite) :
    SameView geometry (timersHandshakeComplete pid site) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold timersHandshakeComplete
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | (allocation_release_head delTimer; exact (del_geometry _ _).wp (fun s => s = initial))
    | completion_step initial

private theorem traversal_geometry (pid : PeerId) : SameView geometry (timersTraversal pid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold timersTraversal
  simp (config := {zeta := false}) only [branchCmp]
  repeat' first
    | (allocation_release_head modPeerTimer; exact (mod_geometry _ _ _ _).wp (fun s => s = initial))
    | completion_step initial

private theorem dataReceived_geometry (pid : PeerId) : SameView geometry (timersDataReceived pid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold timersDataReceived
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head modPeerTimer; exact (mod_geometry _ _ _ _).wp (fun s => s = initial))
    | completion_step initial

private theorem stats_geometry (pid : PeerId) (len : Nat) : SameView geometry (updateRxStats pid len) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold updateRxStats
  repeat' completion_step initial

private theorem dishonest_geometry (why : Dishonest) : SameView geometry (dishonest why) := by
  cases why <;> exact modifyDevice _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

private theorem done_geometry (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    SameView geometry (consumeDataDone pid pkt endpoint) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold consumeDataDone WG.andM WG.orM timersAnyAuthenticatedPacketReceived
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head setPeerEndpoint; exact (endpoint_geometry _ _).wp (fun s => s = initial))
    | (allocation_release_head receivedWithKeypair; exact (received_geometry _ _).wp (fun s => s = initial))
    | (allocation_release_head sendStagedPackets; exact (staged_geometry _).wp (fun s => s = initial))
    | (allocation_release_head keepKeyFreshRx; exact (fresh_geometry _).wp (fun s => s = initial))
    | (allocation_release_head timersHandshakeComplete; exact (handshake_geometry _ _).wp (fun s => s = initial))
    | (allocation_release_head timersTraversal; exact (traversal_geometry _).wp (fun s => s = initial))
    | (allocation_release_head timersDataReceived; exact (dataReceived_geometry _).wp (fun s => s = initial))
    | (allocation_release_head delTimer; exact (del_geometry _ _).wp (fun s => s = initial))
    | (allocation_release_head updateRxStats; exact (stats_geometry _ _).wp (fun s => s = initial))
    | (allocation_release_head dishonest; exact (dishonest_geometry _).wp (fun s => s = initial))
    | (allocation_release_head lookupSrc; exact (lookup_geometry _ _).wp (fun s => s = initial))
    | (allocation_release_head inetEcnDecapsulate
       exact (store (inetEcnDecapsulate_sameWGStore _ _ _)).wp (fun s => s = initial))
    | completion_traffic initial

/-- The TX frontier is intentionally absent. This transport allows key/peer
removal and source promotions while preserving every resident RX owner word. -/
theorem carrier_transport (hi : OwnerBounds.Carrier w) (material : Origins.Retains w v)
    (fields : geometry v = geometry w) (keys : KeyEffect allowed w v) :
    OwnerBounds.Carrier v := by
  have frontiers (before after : Device) (hb : w.dev = some before) (ha : v.dev = some after) :
      after.nextPeer = before.nextPeer ∧ after.nextKeypairId = before.nextKeypairId := by
    have eq : (after.ifindex,after.nextPeer,after.nextKeypairId) =
        (before.ifindex,before.nextPeer,before.nextKeypairId) :=
      Option.some.inj (by simpa only [geometry,hb,ha,Option.map_some] using congrArg Prod.fst fields)
    exact ⟨congrArg (fun p => p.2.1) eq, congrArg (fun p => p.2.2) eq⟩
  have rx : rxView v = rxView w := congrArg Prod.snd fields
  constructor
  · apply owners_retain hi.owners material
    intro before after hb ha _
    exact Nat.le_of_eq (frontiers before after hb ha).1.symm
  · exact keys.rxCompatible rx hi.compatible
  · intro after ha id pkt hp
    have oldRx : (w.dev.bind fun d => d.rxSkbs[id]?) = some pkt := by
      simpa [rxView,ha,hp] using (congrFun (congrArg Prod.snd rx) id).symm
    obtain ⟨before,hb,packet⟩ := Option.bind_eq_some_iff.mp oldRx
    rw [(frontiers before after hb ha).2]
    exact hi.rxKeys before hb id pkt packet

theorem preserves_of_frames {α : Type} (a : WG.M α)
    (material : Origins.Retaining.RetainsCall a) (fields : SameView geometry a)
    (keys : KeyEffects allowed a) : Preserves OwnerBounds.Carrier a := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v finalAmbient hi hr
  exact carrier_transport hi
    ((ProjectedAction.iff_run_ambient _ _ _).mp material w ambient result v finalAmbient hr)
    ((ProjectedAction.iff_run_ambient _ _ _).mp fields w ambient result v finalAmbient hr)
    ((KeyEffects.iff_run_ambient _ _).mp keys w ambient result v finalAmbient hr)

theorem sendStagedPackets_preserves (pid : PeerId) :
    Preserves OwnerBounds.Carrier (sendStagedPackets pid) :=
  preserves_of_frames _ (Origins.Retaining.sendStagedPackets_material pid) (staged_geometry pid)
    (staged_send_keyEffect (allowed := NoPromotion) pid)

theorem receivedWithKeypair_preserves (pid : PeerId) (kid : KeypairId) :
    Preserves OwnerBounds.Carrier (receivedWithKeypair pid kid) :=
  preserves_of_frames _ (Origins.Retaining.receivedWithKeypair_material pid kid) (received_geometry pid kid)
    (receivedWithKeypair_keyEffect pid kid)

theorem keepKeyFreshRx_preserves (pid : PeerId) :
    Preserves OwnerBounds.Carrier (keepKeyFreshRx pid) :=
  preserves_of_frames _ (Origins.Retaining.keepKeyFreshRx_material pid) (fresh_geometry pid)
    (keepKeyFreshRx_keyEffect (allowed := NoPromotion) pid)

theorem consumeDataDone_preserves (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    Preserves OwnerBounds.Carrier (consumeDataDone pid pkt endpoint) :=
  preserves_of_frames _ (Origins.Retaining.consumeDataDone_material pid pkt endpoint)
    (done_geometry pid pkt endpoint) (consumeDataDone_keyEffect pid pkt endpoint)

/-- The unchanged lifetime observer now carries the concrete owner invariant
at its actual input and output journal. -/
theorem consumeDataDone_checked (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    OwnerChecks.Preserves (Queues.RxHistory.mixed (liftWGObserver (consumeDataDonePrefix pid pkt endpoint))) :=
  OwnerChecks.native_mixed _ _ (consumeDataDonePrefix_erases pid pkt endpoint)
    (consumeDataDonePrefix_preserves_ambient allocationAmbient allocationTx allocationRx pid pkt endpoint)
    (Origins.Retaining.consumeDataDone_material pid pkt endpoint)
    (CurrentRx.consumeDataDone_preserves pid pkt endpoint)
    (fun _ => hoare_consequence (consumeDataDone_preserves pid pkt endpoint)
      (fun _ h => h.2) (fun _ _ h => h))

end Leanux.Proofs.WG.OwnerCompletion
