import Leanux.Proofs.WG.Queues.SlotRemoval
import Leanux.Proofs.WG.Queues.HolderTimerPhysical

/-! Three-slot compatibility follows the actual timer callbacks and their
recorded dispatch. Timer detachment and saved wheel bounds retain their
original source order; only normal endpoints have state conclusions. -/
namespace Leanux.Proofs.WG.CurrentSlots.Timer
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Queues

private theorem endpoint (pid : PeerId) : Preserves Inv (clearPeerEndpointSrc pid) := by
  apply fields_preserves (project := id)
  intro initial
  change Preserves (fun w => fields w=initial) _
  unfold clearPeerEndpointSrc dstCacheResetNow dstCacheReset getAmbient hiddenJiffies
  repeat' slot_fields_step initial

private theorem purge (pid : PeerId) : Preserves Inv (purgeStagedPackets pid) := by
  apply fields_preserves (project := id)
  intro initial
  change Preserves (fun w => fields w=initial) _
  unfold purgeStagedPackets
  repeat' slot_fields_step initial

private theorem keepalive (pid : PeerId) : Preserves Inv (WG.sendKeepalive pid) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.keepalive_slots) pid

macro "timer_slot_step" : tactic => `(tactic| first
  | (rx_retention_head clearPeerEndpointSrc; exact endpoint _)
  | (rx_retention_head purgeStagedPackets; exact purge _)
  | (rx_retention_head WG.sendKeepalive; exact keepalive _)
  | (rx_retention_head sendQueuedHandshakeInitiation; exact sendQueuedHandshakeInitiation_preserves _ _)
  | (rx_retention_head delTimer; exact delTimer_preserves _ _)
  | (rx_retention_head modPeerTimer; exact modPeerTimer_preserves _ _ _ _)
  | (rx_retention_head discard
     change Preserves Inv (modPeerTimer _ _ _ _ >>= fun _ => pure ())
     exact preserves_bind (modPeerTimer_preserves _ _ _ _) (fun _ => preserves_pure ()))
  | slot_remove_step)

/-- Every actual callback retains compatibility even when it queues work,
sends a keepalive, clears the endpoint or releases a peer. -/
theorem callback (pid : PeerId) (timer : PeerTimer) : Preserves Inv (timerCallback pid timer) := by
  cases timer with
  | retransmitHandshake =>
    change Preserves Inv (expiredRetransmitHandshake pid)
    unfold expiredRetransmitHandshake
    simp (config := {zeta := false}) only [branch,branchCmp]
    repeat' timer_slot_step
  | sendKeepalive =>
    change Preserves Inv (expiredSendKeepalive pid)
    unfold expiredSendKeepalive
    simp (config := {zeta := false}) only [branch]
    repeat' timer_slot_step
  | newHandshake =>
    change Preserves Inv (expiredNewHandshake pid)
    unfold expiredNewHandshake
    repeat' timer_slot_step
  | zeroKeyMaterial =>
    change Preserves Inv (expiredZeroKeyMaterial pid)
    unfold expiredZeroKeyMaterial
    simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
    repeat' timer_slot_step
  | persistentKeepalive =>
    change Preserves Inv (expiredSendPersistentKeepalive pid)
    unfold expiredSendPersistentKeepalive
    simp (config := {zeta := false}) only [branch]
    repeat' timer_slot_step

private theorem stored (action : Leanux.M α) (frame : SameProductStore action) :
    Preserves (fun w : World => Inv w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  apply fields_transport hi
  have same := congrArg (fun p : ProductStore43 => p.2.2.2.dev)
    ((ProjectedAction.iff_run _ _ _).mp frame w x v run)
  change v.wg.dev=w.wg.dev at same
  unfold fields RxCredits.keyWords
  rw [same]

private theorem native (rule : Preserves Inv action) :
    Preserves (fun w : World => Inv w.wg) (liftWG action) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  exact (hoare_iff_run_ambient _ _ _).mp rule w.wg w.ambient x v.wg v.ambient hi
    ((pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt) action w v x run)

private theorem ambient (action : AmbientM α) :
    Preserves (fun w : World => Inv w.wg) (liftAmbient action) :=
  productAmbient_spec action _ (fun _ _ hi => hi)

private theorem worker (kind : Worker) (body : Leanux.M Unit)
    (keeps : Preserves (fun w : World => Inv w.wg) body) :
    Preserves (fun w : World => Inv w.wg) (Env.runWorker kind body) := by
  unfold Env.runWorker
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | exact keeps
    | (rx_retention_head modifyAmbient; unfold modifyAmbient; exact ambient _)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | rx_retention_step

private theorem timerSection (kind : Worker) (body : Leanux.M Unit)
    (keeps : Preserves (fun w : World => Inv w.wg) body) :
    Preserves (fun w : World => Inv w.wg) (Env.runTimerSection kind body) := by
  unfold Env.runTimerSection
  simp (config := {zeta := false}) only [invariant]
  repeat' first
    | (rx_retention_head Env.runWorker; exact worker kind body keeps)
    | (rx_retention_head modifyAmbient; unfold modifyAmbient; exact ambient _)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | rx_retention_step

theorem stepComplete (bucket : UInt64) :
    Preserves (fun w : World => Inv w.wg) (Env.requireStepComplete bucket) := by
  unfold Env.requireStepComplete
  apply preserves_bind (stored _ (liftWG_sameProductStore getDev getDev_sameWGStore))
  intro d
  cases TimerWheel.anotherAtStep d bucket with
  | none => exact preserves_pure _
  | some pair => cases pair; exact hoare_throw _

macro "timer_slot_product_step" : tactic => `(tactic| first
  | (rx_retention_head Env.timerWorker; exact stored _ (timerWorker_sameKernel _))
  | (rx_retention_head Env.requireStepComplete; exact stepComplete _)
  | (rx_retention_head getWG; exact stored _ (fun initial => productGetWG_spec (fun s => s = initial)))
  | (rx_retention_head modifyWG; exact stored _ (fun initial => productModifyWG_spec
      (fun s => s = initial) _ (fun _ => rfl)))
  | (rx_retention_head throw; exact hoare_throw _)
  | (allocation_release_lift_from AmbientM; exact ambient _)
  | rx_retention_step)

/-- The source only reads the wheel/records and rejects an overdue entry. -/
theorem nothingDue (j : UInt64) :
    Preserves (fun w : World => Inv w.wg) (Env.requireNothingDue j) := by
  have later (kind : Worker) (unit : Nat) : SameProductStore (Env.sectionAppearsLater kind unit) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v run
    cases run
    rfl
  unfold Env.requireNothingDue
  simp (config := {zeta := false}) only [unsupported]
  repeat' first
    | (rx_retention_head Env.sectionAppearsLater; exact stored _ (later _ _))
    | timer_slot_product_step

theorem dispatch (kind : Worker) (pid : PeerId) (timer : PeerTimer)
    (entry : WheelEntry) (prior : Option UInt64) :
    Preserves (fun w : World => Inv w.wg) (timerDispatchUnit kind pid timer entry prior) := by
  unfold timerDispatchUnit
  simp (config := {zeta := false}) only [peekUnit]
  repeat' first
    | (rx_retention_head Env.runTimerSection; exact timerSection _ _ (native (callback _ _)))
    | (allocation_release_lift_from WG.M; exact native (delTimer_preserves _ _))
    | timer_slot_product_step

theorem placeholder (j : UInt64) :
    Preserves (fun w : World => Inv w.wg) (RxHistory.placeholderTimerPassSource j) := by
  unfold RxHistory.placeholderTimerPassSource
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (rx_retention_head Env.runTimerSection; exact timerSection _ _ (native (callback _ _)))
    | (allocation_release_lift_from WG.M; first
        | exact stored _ (liftWG_sameProductStore getDev getDev_sameWGStore)
        | exact native (delTimer_preserves _ _))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w : World => Inv w.wg)
       intro _ _
       change Preserves (fun w : World => Inv w.wg) _)
    | timer_slot_product_step

end Leanux.Proofs.WG.CurrentSlots.Timer
