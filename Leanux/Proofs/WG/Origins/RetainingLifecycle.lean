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

/-- Canonical adapters and checked native composition, selected at the source
head. No per-leaf cross-component frame is introduced. -/
macro "lifecycle_basic " P:term : tactic => `(tactic|
  first
    | material_basic $P
    | (first | index_material_head liftAip | index_material_head monadLift
             | index_material_head MonadLift.monadLift | index_material_head MonadLiftT.monadLift
       apply hoare_liftAip _ (fun w => $P (view w))
       intro w d store hi hd
       simpa only [view,hd,Option.map_some] using hi)
    | (index_material_head getWG; unfold getWG; simp only [monadLift_self])
    | traffic_basic $P)

theorem handshakeZero_material (pid : PeerId) : SameView view (handshakeZero pid) := handshakeZero_view pid

theorem keypairsClear_material (pid : PeerId) : RetainsCall (keypairsClear pid) := by
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    change view w = initial at h
    rw [h]
    exact RetainsView.refl _
  unfold keypairsClear
  try material_lower
  repeat' first
    | traffic_key initial
    | lifecycle_basic (RetainsView initial)

theorem handshakeClear_material (pid : PeerId) : SameView view (handshakeClear pid) := by
  intro initial
  unfold handshakeClear
  try material_lower
  repeat' first
    | (index_material_head handshakeZero; exact (handshakeZero_material _).wp (fun t => t = initial))
    | lifecycle_basic (fun t => t = initial)

theorem handshakeSendWorker_material (pid : PeerId) : RetainsCall (handshakeSendWorker pid) := by
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    change view w = initial at h
    rw [h]
    exact RetainsView.refl _
  unfold handshakeSendWorker
  try material_lower
  repeat' first
    | (index_material_head sendHandshakeInitiation; exact (sendHandshakeInitiation_material _).wp (RetainsView initial))
    | traffic_key initial
    | lifecycle_basic (RetainsView initial)

theorem queuedExpiredZeroKeyMaterial_material (pid : PeerId) : RetainsCall (queuedExpiredZeroKeyMaterial pid) := by
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    change view w = initial at h
    rw [h]
    exact RetainsView.refl _
  unfold queuedExpiredZeroKeyMaterial
  try material_lower
  repeat' first
    | (index_material_head handshakeClear; exact (handshakeClear_material _).wp (RetainsView initial))
    | (index_material_head keypairsClear; exact (keypairsClear_material _).wp initial)
    | traffic_key initial
    | lifecycle_basic (RetainsView initial)

theorem runFlushedSendWork_material (pid : PeerId) : RetainsCall (runFlushedSendWork pid) := by
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    change view w = initial at h
    rw [h]
    exact RetainsView.refl _
  unfold runFlushedSendWork
  try material_lower
  repeat' first
    | (index_material_head handshakeSendWorker; exact (handshakeSendWorker_material _).wp initial)
    | traffic_key initial
    | lifecycle_basic (RetainsView initial)

theorem runFlushedClearWork_material (pid : PeerId) : RetainsCall (runFlushedClearWork pid) := by
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    change view w = initial at h
    rw [h]
    exact RetainsView.refl _
  unfold runFlushedClearWork
  try material_lower
  repeat' first
    | (index_material_head queuedExpiredZeroKeyMaterial; exact (queuedExpiredZeroKeyMaterial_material _).wp initial)
    | traffic_key initial
    | lifecycle_basic (RetainsView initial)

theorem drainHandshakeSendWq_material (upTo : Option PeerId) : RetainsCall (drainHandshakeSendWq upTo) := by
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    change view w = initial at h
    rw [h]
    exact RetainsView.refl _
  unfold drainHandshakeSendWq peekUnit resolveUnit
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range']
  try material_lower
  repeat' first
    | (index_material_head runFlushedSendWork; exact (runFlushedSendWork_material _).wp initial)
    | (index_material_head runFlushedClearWork; exact (runFlushedClearWork_material _).wp initial)
    | traffic_key initial
    | lifecycle_basic (RetainsView initial)

theorem timersStop_material (pid : PeerId) : RetainsCall (timersStop pid) := by
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    change view w = initial at h
    rw [h]
    exact RetainsView.refl _
  unfold timersStop
  try material_lower
  repeat' first
    | (index_material_head delTimer; exact (delTimer_material _ _).wp (RetainsView initial))
    | (index_material_head drainHandshakeSendWq; exact (drainHandshakeSendWq_material _).wp initial)
    | traffic_key initial
    | lifecycle_basic (RetainsView initial)

theorem peerRemoveAfterDead_material (pid : PeerId) : RetainsCall (peerRemoveAfterDead pid) := by
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    change view w = initial at h
    rw [h]
    exact RetainsView.refl _
  unfold peerRemoveAfterDead
  try material_lower
  repeat' first
    | (index_material_head keypairsClear; exact (keypairsClear_material _).wp initial)
    | (index_material_head timersStop; exact (timersStop_material _).wp initial)
    | (index_material_head drainHandshakeSendWq; exact (drainHandshakeSendWq_material _).wp initial)
    | traffic_key initial
    | lifecycle_basic (RetainsView initial)

theorem resetLastSentHandshake_material (pid : PeerId) : SameView view (resetLastSentHandshake pid) := by
  intro initial
  unfold resetLastSentHandshake
  try material_lower
  repeat' first
    | lifecycle_basic (fun t => t = initial)

/-- The original seven-field mask admits arbitrary actual action stacks. -/
theorem configuration_material {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} (a : StateT S m α)
    (ha : SameView (fun s => (configurationView (project s)).toWGStoreView) a) :
    SameView (fun s => view (project s)) a := by
  apply ha.of_factor (fun k : WGStoreView => k.dev.map materialState) _
  intro w
  simp [view, configurationView, configurationDevice, wgOwnedView, wgStoreView,
    materialState, Option.map_map, Function.comp_def]

/-- The original seven-field mask admits arbitrary actual action stacks. -/
theorem socketControl_material {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} (a : StateT S m α)
    (ha : SameView (fun s => (socketView (project s)).toWGStoreView) a) :
    SameView (fun s => view (project s)) a := by
  apply ha.of_factor (fun k : WGStoreView => k.dev.map materialState) _
  intro w
  simp [view, socketView, socketDevice, wgOwnedView, wgStoreView,
    materialState, Option.map_map, Function.comp_def]

theorem dstCacheResetNow_material (pid : PeerId) : SameView view (dstCacheResetNow pid) := by
  apply (dstCacheReset_material pid).bind
  intro _
  exact modifyPeer_material pid (fun p => {p with dstCache := {p.dstCache with slot := none}})

theorem clearPeerEndpointSrc_material (pid : PeerId) : SameView view (clearPeerEndpointSrc pid) := by
  intro initial
  unfold clearPeerEndpointSrc
  try material_lower
  repeat' first
    | (index_material_head dstCacheResetNow; exact (dstCacheResetNow_material _).wp (fun t => t = initial))
    | lifecycle_basic (fun t => t = initial)

theorem setPort_material (port : Nat) : SameView view (setPort port) := by
  intro initial
  unfold setPort
  try material_lower
  repeat' first
    | (index_material_head clearPeerEndpointSrc; exact (clearPeerEndpointSrc_material _).wp (fun t => t = initial))
    | (index_material_head socketInit; exact (socketControl_material (project := id) _ ((socketInit_sameSocket _).factor WGOwnedView.toWGStoreView)).wp (fun t => t = initial))
    | lifecycle_basic (fun t => t = initial)

theorem expireCurrentPeerKeypairs_material (pid : PeerId) :
    RetainsCall (expireCurrentPeerKeypairs pid) := by
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    change view w = initial at h
    rw [h]
    exact RetainsView.refl _
  let invalidateAction (kp : KeypairId) : WG.M Unit := do
    let k ← getKeypair kp
    setKeypair kp {k with sending := {k.sending with isValid := false}}
  have invalidate (kp : KeypairId) : Preserves (fun w => RetainsView initial (view w))
      (invalidateAction kp) := by
    apply hoare_bind (getKeypair kp) _ (getKeypair_spec (RetainsView initial) kp)
    intro k
    exact hoare_consequence
      (setKeypair_spec (RetainsView initial) (fun _ _ hr hi => hi.trans hr) kp
        {k with sending := {k.sending with isValid := false}})
      (fun _ h => ⟨h.1, fun hv => ⟨k,h.2,hv,⟨rfl,Or.inr rfl⟩⟩⟩) (fun _ _ h => h)
  change Hoare (do
    requireNotPending pid "clearing the handshake"
    handshakeClear pid
    resetLastSentHandshake pid
    let p ← getPeer pid
    if ← branch .expireNextKeypair p.keypairNext.isSome then
      let some kp := p.keypairNext | invariant "unreachable"
      invalidateAction kp
    if ← branch .expireCurrentKeypair p.keypairCurrent.isSome then
      let some kp := p.keypairCurrent | invariant "unreachable"
      invalidateAction kp)
    (fun w => RetainsView initial (view w)) (fun _ w => RetainsView initial (view w))
  try material_lower
  repeat' first
    | (traffic_local invalidateAction; exact invalidate _)
    | (index_material_head handshakeClear; exact (handshakeClear_material _).wp (RetainsView initial))
    | (index_material_head resetLastSentHandshake; exact (resetLastSentHandshake_material _).wp (RetainsView initial))
    | lifecycle_basic (RetainsView initial)

theorem purgeStagedPackets_material (pid : PeerId) : SameView view (purgeStagedPackets pid) := by
  intro initial
  unfold purgeStagedPackets
  try material_lower
  repeat' first
    | lifecycle_basic (fun t => t = initial)

theorem wgStop_material : RetainsCall wgStop := by
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    change view w = initial at h
    rw [h]
    exact RetainsView.refl _
  unfold wgStop
  try material_lower
  repeat' first
    | (index_material_head purgeStagedPackets; exact (purgeStagedPackets_material _).wp (RetainsView initial))
    | (index_material_head timersStop; exact (timersStop_material _).wp initial)
    | (index_material_head handshakeClear; exact (handshakeClear_material _).wp (RetainsView initial))
    | (index_material_head keypairsClear; exact (keypairsClear_material _).wp initial)
    | (index_material_head resetLastSentHandshake; exact (resetLastSentHandshake_material _).wp (RetainsView initial))
    | (index_material_head socketReinit; exact (socketControl_material (project := id) _ ((socketReinit_sameSocket _ _).factor WGOwnedView.toWGStoreView)).wp (RetainsView initial))
    | traffic_key initial
    | lifecycle_basic (RetainsView initial)

theorem wgDown_material : RetainsCall wgDown := by
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    change view w = initial at h
    rw [h]
    exact RetainsView.refl _
  unfold wgDown
  try material_lower
  repeat' first
    | (index_material_head wgStop; exact wgStop_material.wp initial)
    | traffic_key initial
    | lifecycle_basic (RetainsView initial)

theorem expiredRetransmitHandshake_material (pid : PeerId) : RetainsCall (expiredRetransmitHandshake pid) := by
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    change view w = initial at h
    rw [h]
    exact RetainsView.refl _
  unfold expiredRetransmitHandshake
  try material_lower
  repeat' first
    | (index_material_head delTimer; exact (delTimer_material _ _).wp (RetainsView initial))
    | (index_material_head purgeStagedPackets; exact (purgeStagedPackets_material _).wp (RetainsView initial))
    | (index_material_head modPeerTimer; exact (modPeerTimer_material _ _ _ _).wp (RetainsView initial))
    | (index_material_head clearPeerEndpointSrc; exact (clearPeerEndpointSrc_material _).wp (RetainsView initial))
    | (index_material_head sendQueuedHandshakeInitiation; exact (sendQueuedHandshakeInitiation_material _ _).wp initial)
    | traffic_key initial
    | lifecycle_basic (RetainsView initial)

theorem expiredSendKeepalive_material (pid : PeerId) : RetainsCall (expiredSendKeepalive pid) := by
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    change view w = initial at h
    rw [h]
    exact RetainsView.refl _
  unfold expiredSendKeepalive
  try material_lower
  repeat' first
    | (index_material_head sendKeepalive; exact (sendKeepalive_material _).wp initial)
    | (index_material_head modPeerTimer; exact (modPeerTimer_material _ _ _ _).wp (RetainsView initial))
    | traffic_key initial
    | lifecycle_basic (RetainsView initial)

theorem expiredNewHandshake_material (pid : PeerId) : RetainsCall (expiredNewHandshake pid) := by
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    change view w = initial at h
    rw [h]
    exact RetainsView.refl _
  unfold expiredNewHandshake
  try material_lower
  repeat' first
    | (index_material_head clearPeerEndpointSrc; exact (clearPeerEndpointSrc_material _).wp (RetainsView initial))
    | (index_material_head sendQueuedHandshakeInitiation; exact (sendQueuedHandshakeInitiation_material _ _).wp initial)
    | traffic_key initial
    | lifecycle_basic (RetainsView initial)

theorem expiredZeroKeyMaterial_material (pid : PeerId) : RetainsCall (expiredZeroKeyMaterial pid) := by
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    change view w = initial at h
    rw [h]
    exact RetainsView.refl _
  unfold expiredZeroKeyMaterial recordQueued peekQueuedUnit
  try material_lower
  repeat' first
    | traffic_key initial
    | lifecycle_basic (RetainsView initial)

theorem expiredSendPersistentKeepalive_material (pid : PeerId) : RetainsCall (expiredSendPersistentKeepalive pid) := by
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    change view w = initial at h
    rw [h]
    exact RetainsView.refl _
  unfold expiredSendPersistentKeepalive
  try material_lower
  repeat' first
    | (index_material_head sendKeepalive; exact (sendKeepalive_material _).wp initial)
    | traffic_key initial
    | lifecycle_basic (RetainsView initial)

theorem timerCallback_material (pid : PeerId) (timer : PeerTimer) :
    RetainsCall (timerCallback pid timer) := by
  cases timer with
  | retransmitHandshake => exact expiredRetransmitHandshake_material pid
  | sendKeepalive => exact expiredSendKeepalive_material pid
  | newHandshake => exact expiredNewHandshake_material pid
  | zeroKeyMaterial => exact expiredZeroKeyMaterial_material pid
  | persistentKeepalive => exact expiredSendPersistentKeepalive_material pid

theorem wgOpen_material : RetainsCall wgOpen := by
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    change view w = initial at h
    rw [h]
    exact RetainsView.refl _
  unfold wgOpen
  try material_lower
  repeat' first
    | (index_material_head socketInit; exact (socketControl_material (project := id) _ ((socketInit_sameSocket _).factor WGOwnedView.toWGStoreView)).wp (RetainsView initial))
    | (index_material_head sendStagedPackets; exact (sendStagedPackets_material _).wp initial)
    | (index_material_head sendKeepalive; exact (sendKeepalive_material _).wp initial)
    | traffic_key initial
    | lifecycle_basic (RetainsView initial)

theorem wgUp_material : RetainsCall wgUp := by
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    change view w = initial at h
    rw [h]
    exact RetainsView.refl _
  unfold wgUp
  try material_lower
  repeat' first
    | (index_material_head wgOpen; exact wgOpen_material.wp initial)
    | traffic_key initial
    | lifecycle_basic (RetainsView initial)

theorem netnsPreExit_material : SameView view netnsPreExit := by
  intro initial
  unfold netnsPreExit
  try material_lower
  repeat' first
    | (index_material_head socketReinit; exact (socketControl_material (project := id) _ ((socketReinit_sameSocket _ _).factor WGOwnedView.toWGStoreView)).wp (fun t => t = initial))
    | (index_material_head clearPeerEndpointSrc; exact (clearPeerEndpointSrc_material _).wp (fun t => t = initial))
    | lifecycle_basic (fun t => t = initial)

theorem node_material {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun s => nodeView (project s)) a) :
    SameView (fun s => view (project s)) a := by
  apply ha.of_factor (fun k : WGStoreView => k.dev.map materialState) _
  intro w
  simp [view,nodeView,nodeDevice,wgStoreView,materialState,Option.map_map,Function.comp_def]

theorem listDel_material (id : NodeId) : SameView view (listDel id) := by
  intro initial
  unfold listDel
  try material_lower
  repeat' first
    | lifecycle_basic (fun t => t = initial)

theorem rootRemovePeerLists_material (root : NodeId) : SameView view (rootRemovePeerLists root) := by
  intro initial
  unfold rootRemovePeerLists
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range']
  try material_lower
  repeat' first
    | (index_material_head listDel; exact (listDel_material _).wp (fun t => t = initial))
    | lifecycle_basic (fun t => t = initial)

theorem allowedipsFree_material : SameView view WG.free := by
  intro initial
  unfold WG.free
  try material_lower
  repeat' first
    | (index_material_head rootRemovePeerLists; exact (rootRemovePeerLists_material _).wp (fun t => t = initial))
    | lifecycle_basic (fun t => t = initial)

theorem removeByPeer_material (pid : PeerId) : SameView view (removeByPeer pid) := by
  rw [← AllowedIps.removeByPeerWithStep_eq]
  intro initial
  unfold AllowedIps.removeByPeerWithStep AllowedIps.removeStep
  try material_lower
  repeat' first
    | (index_material_head listDel; exact (listDel_material _).wp (fun t => t = initial))
    | (index_material_head AllowedIps.removeNodeBody; exact (node_material (project := id) (removeNodeBody_sameNode _)).wp (fun t => t = initial))
    | lifecycle_basic (fun t => t = initial)

theorem peerMakeDead_material (pid : PeerId) : SameView view (peerMakeDead pid) := by
  intro initial
  unfold peerMakeDead
  try material_lower
  repeat' first
    | (index_material_head removeByPeer; exact (removeByPeer_material _).wp (fun t => t = initial))
    | lifecycle_basic (fun t => t = initial)

theorem peerRemove_material (peer : Option PeerId) : RetainsCall (peerRemove peer) := by
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    change view w = initial at h
    rw [h]
    exact RetainsView.refl _
  unfold peerRemove
  try material_lower
  repeat' first
    | (index_material_head peerMakeDead; exact (peerMakeDead_material _).wp (RetainsView initial))
    | (index_material_head peerRemoveAfterDead; exact (peerRemoveAfterDead_material _).wp initial)
    | traffic_key initial
    | lifecycle_basic (RetainsView initial)

theorem peerRemoveAll_material : RetainsCall peerRemoveAll := by
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    change view w = initial at h
    rw [h]
    exact RetainsView.refl _
  unfold peerRemoveAll
  try material_lower
  repeat' first
    | (index_material_head WG.free; exact allowedipsFree_material.wp (RetainsView initial))
    | (index_material_head peerMakeDead; exact (peerMakeDead_material _).wp (RetainsView initial))
    | (index_material_head peerRemoveAfterDead; exact (peerRemoveAfterDead_material _).wp initial)
    | traffic_key initial
    | lifecycle_basic (RetainsView initial)

theorem materialView_link (w : WGWorld) :
    (linkView w).dev.map materialState = view w := by
  simp [linkView,linkStore,linkDevice,wgStoreView,view,materialState,Option.map_map,Function.comp_def]

theorem wgCreate_material : RetainsCall wgCreate := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  change RetainsView (view w) (view v)
  have hc := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w))
    w ambient result v ambient' rfl hr
  rcases hc with he | ⟨hn,he⟩
  · have hv := congrArg (fun s : WGStoreView => s.dev.map materialState) he
    rw [materialView_link,materialView_link] at hv
    rw [hv]
    exact RetainsView.refl _
  · have hv := congrArg (fun s : WGStoreView => s.dev.map materialState) he
    rw [materialView_link] at hv
    intro epoch keys heq id k hk valid
    rw [hv] at heq
    simp [registeredLink,setupLink,linkDevice,materialState] at heq
    obtain ⟨rfl,rfl⟩ := heq
    simp at hk

theorem ratelimiter_material {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun s => ratelimiterView (project s)) a) :
    SameView (fun s => view (project s)) a :=
  ha.of_factor (fun k : WGStoreView => k.dev.map materialState) _ (fun _ => rfl)

theorem wgDestruct_material : RetainsCall wgDestruct := by
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    change view w = initial at h
    rw [h]
    exact RetainsView.refl _
  unfold wgDestruct mayHaveSlept retireDeviceUnits
  try material_lower
  repeat' first
    | (index_material_head socketReinit; exact (socketControl_material (project := id) _ ((socketReinit_sameSocket _ _).factor WGOwnedView.toWGStoreView)).wp (RetainsView initial))
    | (index_material_head peerRemoveAll; exact peerRemoveAll_material.wp initial)
    | (index_material_head ratelimiterUninit; exact (ratelimiter_material (project := id) ratelimiterUninit_sameRatelimiter).wp (RetainsView initial))
    | (index_material_head modify; apply hoare_modify; intro w hi; exact hi.trans (retains_absent _))
    | traffic_key initial
    | lifecycle_basic (RetainsView initial)

theorem wgDelete_material : RetainsCall (wgDelete : WG.M Int) := by
  intro initial
  refine hoare_consequence
    (P := fun w => RetainsView initial (view w))
    (Q := fun _ w => RetainsView initial (view w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    change view w = initial at h
    rw [h]
    exact RetainsView.refl _
  unfold wgDelete skipCut
  simp only [monadLift_self]
  try material_lower
  repeat' first
    | (index_material_head wgDown; exact wgDown_material.wp initial)
    | (index_material_head wgDestruct; exact wgDestruct_material.wp initial)
    | (index_material_head mayHaveSlept; unfold mayHaveSlept)
    | traffic_key initial
    | lifecycle_basic (RetainsView initial)

end Leanux.Proofs.WG.Origins.Retaining
