import Leanux.Proofs.WG.Lifetimes.PeerRemoval
import Leanux.Proofs.WG.Lifetimes.TxStaging
import Leanux.Proofs.Framing.WGSocketLifecycle
import Leanux.WG.Device

/-! Complete socket and device control observations. Socket initialization,
reinitialization and freeing inspect only device/socket scalars and records;
their lifts add no resident-object events. Device loops retain saved scalar
peer IDs and resolve actual objects at each original access. Ordinary negative
returns and Stops keep their distinct cleanup behavior. No queue-progress,
reference-credit, valid-list or distinctness premise is imposed. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def socketStoreView (g : WGWorld) : WGStoreView := (socketView g).toWGStoreView

def productSocketView (w : World) : ProductStore43 :=
  (fsStoreView w.fs, w.tasks, (w.seccomp.filters, w.seccomp.nextFilter), socketStoreView w.wg)

theorem socketStore_identity_metadata (w v : WGWorld) (he : socketStoreView v = socketStoreView w) :
    (identityView v, allocationMetadata v) = (identityView w, allocationMetadata w) := by
  let observe : WGStoreView → IdentityView := fun s =>
    (⟨s.peerCounter, fun i => (s.dev.bind fun d => d.peers[i]?).map (·.internalId)⟩,
      (fun i => (s.dev.bind fun d => d.keypairs[i]?).map (·.internalId)),
      fun slot => s.dev.bind fun d => match slot with
        | .inl i => d.txSkbs[i]?.map (fun _ => (d.ifindex, i + 1))
        | .inr i => d.rxSkbs[i]?.map (fun _ => (d.ifindex, i + 1)))
  have hi := congrArg observe he
  have hm := congrArg (fun s : WGStoreView =>
    (⟨s.keypairCounter, s.netIfindexNext,
      s.dev.map deviceAllocationMetadata⟩ : AllocationMetadata)) he
  apply Prod.ext
  · apply Prod.ext
    · simpa [observe, identityView, Peers.snapshot, socketStoreView, socketView, socketDevice, wgOwnedView,
        wgStoreView, Option.bind_map, Function.comp_def] using congrArg Prod.fst hi
    · apply Prod.ext
      · change keypairResidents v = keypairResidents w
        unfold keypairResidents
        simpa [observe, socketStoreView, socketView, socketDevice, wgOwnedView,
          wgStoreView, Option.bind_map, Function.comp_def] using
          congrArg (fun s : IdentityView => s.2.1) hi
      · funext slot
        have ht := congrArg (fun s : IdentityView => s.2.2 slot) hi
        cases slot <;>
          simpa [observe, identityView, packetResidents, socketStoreView, socketView, socketDevice, wgOwnedView,
            wgStoreView, Option.bind_map, Function.comp_def] using ht
  · unfold allocationMetadata deviceAllocationMetadata
    simpa [deviceAllocationMetadata, socketStoreView, socketView, socketDevice, wgOwnedView, wgStoreView,
      Option.map_map, Function.comp_def] using hm

/-- Native socket stability masks only the original three socket scalars. -/
def SocketControlStable (I : List LifetimeEvent → WGWorld → Prop) : Prop :=
  ∀ h w v, socketStoreView v = socketStoreView w → I h w → I h v

/-- The original arbitrary product invariant keeps its full 43-field observation. -/
def ProductSocketControlStable (I : List LifetimeEvent → World → Prop) : Prop :=
  ∀ h w v, productSocketView v = productSocketView w → I h w → I h v

theorem allocationSocketControlStable : SocketControlStable AllocationInv := by
  intro h w v he hi
  have hf := socketStore_identity_metadata w v he
  exact hi.congr (congrArg Prod.fst hf) (congrArg Prod.snd hf)

theorem socketControlLift_preserves (c : AmbientContracts I) (hs : SocketControlStable I)
    (a : WG.M α) (ha : SameView socketStoreView a) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix a) := by
  apply StatePrefixEnsures.lift a (fun h w _ hi => c.safe h w hi)
  intro h w ambient x v ambient' hi hr
  exact hs h w v ((ProjectedAction.iff_run_ambient _ _ _).mp ha w ambient x v ambient' hr) hi

theorem socketControlLift_preserves_product (c : ProductAmbientContracts I)
    (hs : ProductSocketControlStable I) (a : Leanux.M α) (ha : SameView productSocketView a) :
    PrefixPreserves I LifetimeEvent.Safe (liftPrefix a) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift a c.safe
  intro h w x v hi hr
  exact hs h w v ((ProjectedAction.iff_run _ _ _).mp ha w x v hr) hi

theorem socketControlNative_preserves_product (c : ProductAmbientContracts I)
    (hs : ProductSocketControlStable I) (a : WG.M α) (ha : SameView socketStoreView a) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix a)) := by
  rw [liftWGObserver_lift]
  apply socketControlLift_preserves_product c hs (liftWG a)
  apply sameView_liftWG productSocketView socketStoreView a ha
  intro w g ambient hg
  simp only [productSocketView, hg]

def wgOpenPrefix : MixedM Int := do
  let dev ← liftWGPrefix getDev
  _ ← liftWGPrefix (branch .openHasInet dev.inet4Dev)
  _ ← liftWGPrefix (branch .openHasInet6 dev.inet6Dev)
  let d ← liftWGPrefix getDev
  let ret ← liftWGPrefix (socketInit d.incomingPort)
  if ← liftWGPrefix (branch .openSocketError (ret < 0)) then return ret
  for pid in d.peerList do
    _ ← liftWGPrefix (branch .openPeersIter true)
    sendStagedPacketsPrefix pid
    if ← liftWGPrefix (branch .openKeepalive ((← getPeerMixed pid).persistentKeepaliveInterval != 0)) then
      sendKeepalivePrefix pid
  _ ← liftWGPrefix (branch .openPeersIter false)
  return 0

def wgUpPrefix : MixedM Int := do
  liftWGPrefix (modifyDev fun d => {d with running := true})
  let ret ← wgOpenPrefix
  if ret < 0 then liftWGPrefix (modifyDev fun d => {d with running := false})
  return ret

def wgStopPrefix : MixedM Unit := do
  for pid in (← liftWGPrefix getDev).peerList do
    _ ← liftWGPrefix (branch .stopPeersIter true)
    requireNotPendingMixed pid "wg_stop while a handshake is queued"
    purgeStagedPacketsPrefix pid
    timersStopPrefix pid
    handshakeClearPrefix pid
    keypairsClearPrefix pid
    resetLastSentHandshakePrefix pid
  _ ← liftWGPrefix (branch .stopPeersIter false)
  if !(← liftWGPrefix getDev).handshakeQueue.empty then
    liftWGPrefix (unsupported "wg_stop with handshake messages queued for the receive worker (its timing)")
  _ ← liftWGPrefix (branch .stopDrainIter false)
  liftWGPrefix (modifyDev fun d => {d with handshakeQueueLen := 0})
  liftWGPrefix (socketReinit none none)

def wgDownPrefix : MixedM Unit := do
  liftWGPrefix (modifyDev fun d => {d with running := false})
  wgStopPrefix

def netnsPreExitPrefix : MixedM Unit := do
  if (← liftWGPrefix (get : WG.M WGWorld)).dev.isSome then
    _ ← liftWGPrefix (branch .preExitDevIter true)
    if ← liftWGPrefix (branch .preExitCreator (← liftWGPrefix getDev).creatingNet) then
      liftWGPrefix (modifyDev fun d => {d with carrier := false, creatingNet := false})
      liftWGPrefix (socketReinit none none)
      for pid in (← liftWGPrefix getDev).peerList do
        _ ← liftWGPrefix (branch .preExitPeerIter true)
        clearPeerEndpointSrcPrefix pid
      _ ← liftWGPrefix (branch .preExitPeerIter false)
  _ ← liftWGPrefix (branch .preExitDevIter false)

theorem wgOpenPrefix_erases : ErasesStatePrefix wgOpenPrefix wgOpen := by
  unfold wgOpenPrefix wgOpen
  repeat' first
    | with_reducible exact sendStagedPacketsPrefix_erases _
    | with_reducible exact sendKeepalivePrefix_erases _
    | with_reducible exact getPeerMixed_erases _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_forIn
    | with_reducible apply erasesStatePrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem wgUpPrefix_erases : ErasesStatePrefix wgUpPrefix wgUp := by
  unfold wgUpPrefix wgUp
  repeat' first
    | with_reducible exact wgOpenPrefix_erases
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem wgStopPrefix_erases : ErasesStatePrefix wgStopPrefix wgStop := by
  unfold wgStopPrefix wgStop
  repeat' first
    | with_reducible exact requireNotPendingMixed_erases _ _
    | with_reducible exact purgeStagedPacketsPrefix_erases _
    | with_reducible exact timersStopPrefix_erases _
    | with_reducible exact handshakeClearPrefix_erases _
    | with_reducible exact keypairsClearPrefix_erases _
    | with_reducible exact resetLastSentHandshakePrefix_erases _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_forIn
    | with_reducible apply erasesStatePrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem wgDownPrefix_erases : ErasesStatePrefix wgDownPrefix wgDown :=
  erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ => wgStopPrefix_erases)

theorem netnsPreExitPrefix_erases : ErasesStatePrefix netnsPreExitPrefix netnsPreExit := by
  unfold netnsPreExitPrefix netnsPreExit
  repeat' first
    | with_reducible exact clearPeerEndpointSrcPrefix_erases _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_forIn
    | with_reducible apply erasesStatePrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

structure DeviceControlContracts (I : List LifetimeEvent → WGWorld → Prop) : Prop where
  socket : SocketControlStable I
  tx : TxContracts I
  removal : PeerRemovalContracts I
  running : ∀ b, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
    (liftWGPrefix (modifyDev fun d => {d with running := b}))
  clearHandshakeQueue : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
    (liftWGPrefix (modifyDev fun d => {d with handshakeQueueLen := 0}))
  creatorExit : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
    (liftWGPrefix (modifyDev fun d => {d with carrier := false, creatingNet := false}))

structure ProductDeviceControlContracts (I : List LifetimeEvent → World → Prop) : Prop where
  socket : ProductSocketControlStable I
  tx : ProductTxContracts I
  removal : ProductPeerRemovalContracts I
  running : ∀ b, PrefixPreserves I LifetimeEvent.Safe
    (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with running := b})))
  clearHandshakeQueue : PrefixPreserves I LifetimeEvent.Safe
    (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with handshakeQueueLen := 0})))
  creatorExit : PrefixPreserves I LifetimeEvent.Safe
    (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with carrier := false, creatingNet := false})))

theorem allocationDeviceControl : DeviceControlContracts AllocationInv := by
  refine ⟨allocationSocketControlStable, allocationTx, allocationPeerRemoval, ?_, ?_, ?_⟩
  · intro b
    apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.safe)
    intro h w ambient x v ambient' hi hr
    cases hr
    apply hi.congr
    · unfold identityView Peers.snapshot keypairResidents packetResidents
      simp [Option.bind_map, Function.comp_def]
    · simp [allocationMetadata, deviceAllocationMetadata, Option.map_map, Function.comp_def] <;> rfl
  · apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.safe)
    intro h w ambient x v ambient' hi hr
    cases hr
    apply hi.congr
    · unfold identityView Peers.snapshot keypairResidents packetResidents
      simp [Option.bind_map, Function.comp_def]
    · simp [allocationMetadata, deviceAllocationMetadata, Option.map_map, Function.comp_def] <;> rfl
  · apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.safe)
    intro h w ambient x v ambient' hi hr
    cases hr
    apply hi.congr
    · unfold identityView Peers.snapshot keypairResidents packetResidents
      simp [Option.bind_map, Function.comp_def]
    · simp [allocationMetadata, deviceAllocationMetadata, Option.map_map, Function.comp_def] <;> rfl

private theorem control_forIn {α β : Type} (c : AmbientContracts I) (xs : List α) (init : β)
    (f : α → β → MixedM (ForInStep β))
    (hf : ∀ x b, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (f x b)) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (forIn xs init f) :=
  StatePrefixEnsures.forInInvariant xs init f (fun _ h w _ => I h w) LifetimeEvent.Safe
    (fun _ h w _ hi => c.safe h w hi) hf

theorem wgOpenPrefix_preserves (c : AmbientContracts I) (r : DeviceControlContracts I) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe wgOpenPrefix := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      AmbientSpec I P (liftWGPrefix (StateT.lift a)) (fun _ => P) :=
    c.store P _ (by intro initial; exact hoare_liftAmbient a _)
  change StatePrefixEnsures _ _ _ _
  unfold wgOpenPrefix
  repeat' first
    | (maintenance_head sendStagedPacketsPrefix; exact sendStagedPacketsPrefix_preserves_ambient c r.tx _)
    | (maintenance_head sendKeepalivePrefix; exact sendKeepalivePrefix_preserves_ambient c r.tx _)
    | (maintenance_lift_action_head socketInit; exact socketControlLift_preserves c r.socket _ ((socketInit_sameSocket _).factor WGOwnedView.toWGStoreView))
    | (maintenance_head getPeerMixed; exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    | (maintenance_lift_action_head getDev; exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.branch _ _)))
    | (maintenance_lift_action_head unsupported; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.unsupported _)))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head ForIn.forIn; apply control_forIn c; intro x b; change StatePrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem wgUpPrefix_preserves (c : AmbientContracts I) (r : DeviceControlContracts I) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe wgUpPrefix := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      AmbientSpec I P (liftWGPrefix (StateT.lift a)) (fun _ => P) :=
    c.store P _ (by intro initial; exact hoare_liftAmbient a _)
  change StatePrefixEnsures _ _ _ _
  unfold wgUpPrefix
  repeat' first
    | (maintenance_head wgOpenPrefix; exact wgOpenPrefix_preserves c r)
    | (maintenance_lift_action_head modifyDev; exact r.running true)
    | (maintenance_lift_action_head modifyDev; exact r.running false)
    | (maintenance_lift_action_head getDev; exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.branch _ _)))
    | (maintenance_lift_action_head unsupported; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.unsupported _)))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head ForIn.forIn; apply control_forIn c; intro x b; change StatePrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem wgStopPrefix_preserves (c : AmbientContracts I) (r : DeviceControlContracts I) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe wgStopPrefix := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      AmbientSpec I P (liftWGPrefix (StateT.lift a)) (fun _ => P) :=
    c.store P _ (by intro initial; exact hoare_liftAmbient a _)
  change StatePrefixEnsures _ _ _ _
  unfold wgStopPrefix
  repeat' first
    | (maintenance_head requireNotPendingMixed; exact AmbientContracts.drop (requireNotPendingMixed_spec c (fun _ => True) _ _))
    | (maintenance_head purgeStagedPacketsPrefix; exact purgeStagedPacketsPrefix_preserves_ambient c r.tx _)
    | (maintenance_head timersStopPrefix; exact timersStopPrefix_preserves c r.removal _)
    | (maintenance_head handshakeClearPrefix; exact handshakeClearPrefix_preserves c r.removal.indexRemove _)
    | (maintenance_head keypairsClearPrefix; exact keypairsClearPrefix_preserves_ambient c r.removal.keypairPut _)
    | (maintenance_head resetLastSentHandshakePrefix; exact AmbientContracts.drop (resetLastSentHandshakePrefix_spec c (fun _ => True) _))
    | (maintenance_lift_action_head socketReinit; exact socketControlLift_preserves c r.socket _ ((socketReinit_sameSocket _ _).factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head modifyDev; exact r.clearHandshakeQueue)
    | (maintenance_lift_action_head getDev; exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.branch _ _)))
    | (maintenance_lift_action_head unsupported; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.unsupported _)))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head ForIn.forIn; apply control_forIn c; intro x b; change StatePrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem wgDownPrefix_preserves (c : AmbientContracts I) (r : DeviceControlContracts I) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe wgDownPrefix :=
  StatePrefixEnsures.bind (r.running false) (fun _ => wgStopPrefix_preserves c r)

theorem netnsPreExitPrefix_preserves (c : AmbientContracts I) (r : DeviceControlContracts I) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe netnsPreExitPrefix := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      AmbientSpec I P (liftWGPrefix (StateT.lift a)) (fun _ => P) :=
    c.store P _ (by intro initial; exact hoare_liftAmbient a _)
  change StatePrefixEnsures _ _ _ _
  unfold netnsPreExitPrefix
  repeat' first
    | (maintenance_head clearPeerEndpointSrcPrefix; exact AmbientContracts.drop (clearPeerEndpointSrcPrefix_spec c (fun _ => True) _))
    | (maintenance_lift_action_head socketReinit; exact socketControlLift_preserves c r.socket _ ((socketReinit_sameSocket _ _).factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head modifyDev; exact r.creatorExit)
    | (maintenance_lift_action_head get; exact AmbientContracts.drop (c.store (fun _ => True) (get : WG.M WGWorld) (by apply (ProjectedAction.iff_run_ambient _ _ _).mpr; intro w ambient x v ambient' hr; cases hr; rfl)))
    | (maintenance_lift_action_head getDev; exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.branch _ _)))
    | (maintenance_lift_action_head unsupported; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.unsupported _)))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head ForIn.forIn; apply control_forIn c; intro x b; change StatePrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem wgOpenPrefix_preserves_product (c : ProductAmbientContracts I) (r : ProductDeviceControlContracts I) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver wgOpenPrefix) := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (StateT.lift a))) (fun _ => P) :=
    c.nativeStore P _ (by intro initial; exact hoare_liftAmbient a _)
  change PrefixEnsures _ _ _ _
  unfold wgOpenPrefix
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [liftWGObserver_forIn] | rw [apply_ite])
    | (maintenance_head sendStagedPacketsPrefix; exact sendStagedPacketsPrefix_preserves_product c r.tx _)
    | (maintenance_head sendKeepalivePrefix; exact sendKeepalivePrefix_preserves_product c r.tx _)
    | (maintenance_lift_action_head socketInit; exact socketControlNative_preserves_product c r.socket _ ((socketInit_sameSocket _).factor WGOwnedView.toWGStoreView))
    | (maintenance_head getPeerMixed; exact ProductAmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.branch _ _)))
    | (maintenance_lift_action_head unsupported; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.unsupported _)))
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ c.safe; intro x b; change PrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem wgUpPrefix_preserves_product (c : ProductAmbientContracts I) (r : ProductDeviceControlContracts I) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver wgUpPrefix) := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (StateT.lift a))) (fun _ => P) :=
    c.nativeStore P _ (by intro initial; exact hoare_liftAmbient a _)
  change PrefixEnsures _ _ _ _
  unfold wgUpPrefix
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [liftWGObserver_forIn] | rw [apply_ite])
    | (maintenance_head wgOpenPrefix; exact wgOpenPrefix_preserves_product c r)
    | (maintenance_lift_action_head modifyDev; exact r.running true)
    | (maintenance_lift_action_head modifyDev; exact r.running false)
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.branch _ _)))
    | (maintenance_lift_action_head unsupported; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.unsupported _)))
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ c.safe; intro x b; change PrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem wgStopPrefix_preserves_product (c : ProductAmbientContracts I) (r : ProductDeviceControlContracts I) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver wgStopPrefix) := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (StateT.lift a))) (fun _ => P) :=
    c.nativeStore P _ (by intro initial; exact hoare_liftAmbient a _)
  change PrefixEnsures _ _ _ _
  unfold wgStopPrefix
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [liftWGObserver_forIn] | rw [apply_ite])
    | (maintenance_head requireNotPendingMixed; exact ProductAmbientContracts.drop (requireNotPendingMixed_spec_product c (fun _ => True) _ _))
    | (maintenance_head purgeStagedPacketsPrefix; exact purgeStagedPacketsPrefix_preserves_product c r.tx _)
    | (maintenance_head timersStopPrefix; exact timersStopPrefix_preserves_product c r.removal _)
    | (maintenance_head handshakeClearPrefix; exact handshakeClearPrefix_preserves_product c r.removal.indexRemove _)
    | (maintenance_head keypairsClearPrefix; exact keypairsClearPrefix_preserves_product c r.removal.keypairPut _)
    | (maintenance_head resetLastSentHandshakePrefix; exact ProductAmbientContracts.drop (resetLastSentHandshakePrefix_spec_product c (fun _ => True) _))
    | (maintenance_lift_action_head socketReinit; exact socketControlNative_preserves_product c r.socket _ ((socketReinit_sameSocket _ _).factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head modifyDev; exact r.clearHandshakeQueue)
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.branch _ _)))
    | (maintenance_lift_action_head unsupported; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.unsupported _)))
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ c.safe; intro x b; change PrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem wgDownPrefix_preserves_product (c : ProductAmbientContracts I) (r : ProductDeviceControlContracts I) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver wgDownPrefix) := by
  simp only [wgDownPrefix, liftWGObserver_bind]
  exact PrefixPreserves.bind (r.running false) (fun _ => wgStopPrefix_preserves_product c r)

theorem netnsPreExitPrefix_preserves_product (c : ProductAmbientContracts I) (r : ProductDeviceControlContracts I) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver netnsPreExitPrefix) := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (StateT.lift a))) (fun _ => P) :=
    c.nativeStore P _ (by intro initial; exact hoare_liftAmbient a _)
  change PrefixEnsures _ _ _ _
  unfold netnsPreExitPrefix
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [liftWGObserver_forIn] | rw [apply_ite])
    | (maintenance_head clearPeerEndpointSrcPrefix; exact ProductAmbientContracts.drop (clearPeerEndpointSrcPrefix_spec_product c (fun _ => True) _))
    | (maintenance_lift_action_head socketReinit; exact socketControlNative_preserves_product c r.socket _ ((socketReinit_sameSocket _ _).factor WGOwnedView.toWGStoreView))
    | (maintenance_lift_action_head modifyDev; exact r.creatorExit)
    | (maintenance_lift_action_head get; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) (get : WG.M WGWorld) (by apply (ProjectedAction.iff_run_ambient _ _ _).mpr; intro w ambient x v ambient' hr; cases hr; rfl)))
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.branch _ _)))
    | (maintenance_lift_action_head unsupported; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.unsupported _)))
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ c.safe; intro x b; change PrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

inductive DeviceControlCall where
  | freeSocket (sock : Option Nat)
  | reinit (new4 new6 : Option Nat)
  | init (port : Nat)
  | openDevice
  | up
  | stopDevice
  | down
  | preExit

namespace DeviceControlCall

def Result : DeviceControlCall → Type
  | .init _ | .openDevice | .up => Int
  | _ => Unit

def original (call : DeviceControlCall) : WG.M call.Result := match call with
  | .freeSocket sock => sockFree sock
  | .reinit new4 new6 => socketReinit new4 new6
  | .init port => socketInit port
  | .openDevice => wgOpen
  | .up => wgUp
  | .stopDevice => wgStop
  | .down => wgDown
  | .preExit => netnsPreExit

def observed (call : DeviceControlCall) : MixedM call.Result := match call with
  | .freeSocket sock => liftWGPrefix (sockFree sock)
  | .reinit new4 new6 => liftWGPrefix (socketReinit new4 new6)
  | .init port => liftWGPrefix (socketInit port)
  | .openDevice => wgOpenPrefix
  | .up => wgUpPrefix
  | .stopDevice => wgStopPrefix
  | .down => wgDownPrefix
  | .preExit => netnsPreExitPrefix

theorem erases (call : DeviceControlCall) : ErasesStatePrefix call.observed call.original := by
  cases call with
  | freeSocket sock => exact erasesStatePrefix_lift _
  | reinit new4 new6 => exact erasesStatePrefix_lift _
  | init port => exact erasesStatePrefix_lift _
  | openDevice => exact wgOpenPrefix_erases
  | up => exact wgUpPrefix_erases
  | stopDevice => exact wgStopPrefix_erases
  | down => exact wgDownPrefix_erases
  | preExit => exact netnsPreExitPrefix_erases

theorem preserves_ambient (c : AmbientContracts I) (r : DeviceControlContracts I)
    (call : DeviceControlCall) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe call.observed := by
  cases call with
  | freeSocket sock => exact AmbientContracts.drop (c.store (fun _ => True) _ (((sockFree_sameWGWorld sock).factor wgStoreView)))
  | reinit new4 new6 => exact socketControlLift_preserves c r.socket _ (((socketReinit_sameSocket new4 new6).factor WGOwnedView.toWGStoreView))
  | init port => exact socketControlLift_preserves c r.socket _ (((socketInit_sameSocket port).factor WGOwnedView.toWGStoreView))
  | openDevice => exact wgOpenPrefix_preserves c r
  | up => exact wgUpPrefix_preserves c r
  | stopDevice => exact wgStopPrefix_preserves c r
  | down => exact wgDownPrefix_preserves c r
  | preExit => exact netnsPreExitPrefix_preserves c r

theorem preserves_ambient_product (c : ProductAmbientContracts I) (r : ProductDeviceControlContracts I)
    (call : DeviceControlCall) : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) := by
  cases call with
  | freeSocket sock => exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (((sockFree_sameWGWorld sock).factor wgStoreView)))
  | reinit new4 new6 => exact socketControlNative_preserves_product c r.socket _ (((socketReinit_sameSocket new4 new6).factor WGOwnedView.toWGStoreView))
  | init port => exact socketControlNative_preserves_product c r.socket _ (((socketInit_sameSocket port).factor WGOwnedView.toWGStoreView))
  | openDevice => exact wgOpenPrefix_preserves_product c r
  | up => exact wgUpPrefix_preserves_product c r
  | stopDevice => exact wgStopPrefix_preserves_product c r
  | down => exact wgDownPrefix_preserves_product c r
  | preExit => exact netnsPreExitPrefix_preserves_product c r

theorem allocation (call : DeviceControlCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient allocationDeviceControl

end DeviceControlCall
end Leanux.Proofs.WG.Lifetimes
