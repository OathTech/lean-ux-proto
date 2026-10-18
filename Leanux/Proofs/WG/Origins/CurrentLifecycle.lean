import Leanux.Proofs.WG.Origins.ConfiguredHandshake
import Leanux.Proofs.WG.Origins.CurrentMaintenance
import Leanux.Proofs.WG.Origins.CurrentPeerRetains
import Leanux.Proofs.WG.Peers.ConfiguredTimers

/-! Normal configured/current identity transport through native flushed work
and peer removal. Actual failed records and release guards remain Stops; peers
and keys may be erased, so the worker and removal contracts are invariants,
not equality of the entry and exit views. -/
namespace Leanux.Proofs.WG.CurrentLifecycle
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues

def Inv (history : List SessionOrigin.Receipt) (w : WGWorld) : Prop :=
  ConfiguredIdentity.Inv w ∧ CurrentIdentity.Inv history w

private theorem retained_preserves {α : Type} (a : WG.M α)
    (configured : Preserves ConfiguredIdentity.Inv a)
    (current : ProjectedAction id CurrentIdentity.Retains a)
    (history : List SessionOrigin.Receipt) : Preserves (Inv history) a := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi hr
  exact ⟨(hoare_iff_run_ambient _ _ _).mp configured w ambient result v ambient' hi.1 hr,
    hi.2.retain ((ProjectedAction.iff_run_ambient _ _ _).mp current
      w ambient result v ambient' hr)⟩

private theorem store_preserves {α : Type} (a : WG.M α)
    (frame : SameView wgStoreView a) (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) a := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi hr
  have fields := (ProjectedAction.iff_run_ambient _ _ _).mp frame
    w ambient result v ambient' hr
  have dev : v.dev = w.dev := congrArg WGStoreView.dev fields
  constructor
  · intro s hs
    exact hi.1 s (by simpa only [ConfiguredIdentity.view,dev] using hs)
  · intro d hd slot key hk valid
    exact hi.2 d (dev.symm.trans hd) slot key hk valid

private theorem modifyDev_preserves (f : Device → Device)
    (configured : ∀ d, ConfiguredIdentity.state (f d) = ConfiguredIdentity.state d)
    (material : ∀ d, ((f d).ifindex,(f d).keypairs) = (d.ifindex,d.keypairs))
    (history : List SessionOrigin.Receipt) : Preserves (Inv history) (modifyDev f) :=
  ConfiguredHandshake.current_preserves _
    (fun initial => ConfiguredIdentity.modifyDev_spec (fun s => s = initial) f configured)
    (Origins.Retaining.of_view (Origins.Retaining.modifyDev_material f material)) history

private theorem readPeer_preserves (pid : PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (getPeer pid) :=
  ConfiguredHandshake.current_preserves _
    (fun initial => hoare_consequence (ConfiguredIdentity.getPeer_spec (fun s => s = initial) pid)
      (fun _ h => h) (fun _ _ h => h.1))
    (Origins.Retaining.of_view (Origins.getPeer_view pid)) history

private theorem pay_preserves (peer : Option PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (peerPut peer) :=
  retained_preserves _ (ConfiguredIdentity.peerPut_preserves peer)
    (CurrentIdentity.peerPut_retains peer) history

theorem markDead_preserves (pid : PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (peerMakeDead pid) := by
  apply retained_preserves _ _ (CurrentIdentity.peerMakeDead_retains pid) history
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi hr
  cases result
  exact ConfiguredIdentity.peerMakeDead_preserves pid w v ambient ambient' hi hr

macro "current_lifecycle_step " history:term : tactic => `(tactic| first
  | (rx_retention_head getDev; exact store_preserves _ getDev_sameWGStore $history)
  | (rx_retention_head getPeer; exact readPeer_preserves _ $history)
  | (rx_retention_head modifyDev
     apply modifyDev_preserves _ ?_ ?_ $history
     all_goals intro d; rfl)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (Inv $history)
     intro x b
     change Preserves (Inv $history) _)
  | (first | rx_retention_head throw | rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w ambient result v ambient' hi hr
     cases hr)
  | rx_retention_step)

theorem queuedExpiredZeroKeyMaterial_preserves (pid : PeerId)
    (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (queuedExpiredZeroKeyMaterial pid) := by
  unfold queuedExpiredZeroKeyMaterial
  apply preserves_bind (ConfiguredHandshake.current_preserves _
    (ConfiguredMaintenance.handshakeClear_view pid)
    (Origins.Retaining.of_view (Origins.Retaining.handshakeClear_material pid)) history)
  intro _
  apply preserves_bind (ConfiguredHandshake.current_preserves _
    (ConfiguredMaintenance.keypairsClear_view pid)
    (Origins.Retaining.keypairsClear_material pid) history)
  intro _
  exact pay_preserves (some pid) history

theorem runFlushedSendWork_preserves (pid : PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (runFlushedSendWork pid) := by
  let dequeue : WG.M Unit := do
    modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid}
    let p ← getPeer pid
    if !p.handshakePending then invariant "queued work without a pending flag"
    setPeer pid {p with handshakePending := (← getDev).sendWorkQueue.contains pid}
  have configured : SameView ConfiguredIdentity.view dequeue := by
    intro initial
    unfold dequeue
    change Preserves (fun w => ConfiguredIdentity.view w = initial) _
    simp (config := {zeta := false}) only [invariant]
    repeat' configured_step initial
  have material : SameView Origins.view dequeue := by
    intro initial
    unfold dequeue
    material_lower
    repeat' material_basic (fun s => s = initial)
  have factor : runFlushedSendWork pid = (do
      dequeue
      _ ← hidden (.sectionStart .sendWorker)
      handshakeSendWorker pid
      _ ← hidden (.sectionStop .sendWorker)) := by
    have bind_congr {α β : Type} (a : WG.M α) (f g : α → WG.M β)
        (h : ∀ x, f x = g x) : (a >>= f) = (a >>= g) :=
      congrArg (fun k => a >>= k) (funext h)
    simp only [runFlushedSendWork,dequeue,bind_assoc]
    apply bind_congr
    intro _
    apply bind_congr
    intro p
    by_cases h : (!p.handshakePending) = true
    all_goals simp only [h,Bool.false_eq_true,ite_true,ite_false,bind_assoc]
  rw [factor]
  apply preserves_bind (ConfiguredHandshake.current_preserves _ configured
    (Origins.Retaining.of_view material) history)
  intro _
  apply preserves_bind (hoare_liftAmbient (AmbientM.hidden (.sectionStart .sendWorker)) (Inv history))
  intro _
  apply preserves_bind (ConfiguredHandshake.handshakeSendWorker_preserves pid history)
  intro _
  apply preserves_bind (hoare_liftAmbient (AmbientM.hidden (.sectionStop .sendWorker)) (Inv history))
  intro _
  exact preserves_pure _

theorem runFlushedClearWork_preserves (pid : PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (runFlushedClearWork pid) := by
  unfold runFlushedClearWork
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | (rx_retention_head queuedExpiredZeroKeyMaterial
       exact queuedExpiredZeroKeyMaterial_preserves _ history)
    | current_lifecycle_step history

/-- Both recorded dispatch and the no-record fallback order are the actual
bounded source loop. Exhaustion and malformed section records remain Stops. -/
theorem drainHandshakeSendWq_preserves (upTo : Option PeerId)
    (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (drainHandshakeSendWq upTo) := by
  unfold drainHandshakeSendWq
  simp (config := {zeta := false}) only
    [Std.Legacy.Range.forIn_eq_forIn_range',peekUnit,resolveUnit,getAmbient,invariant]
  repeat' first
    | (rx_retention_head runFlushedSendWork; exact runFlushedSendWork_preserves _ history)
    | (rx_retention_head runFlushedClearWork; exact runFlushedClearWork_preserves _ history)
    | current_lifecycle_step history

theorem timersStop_preserves (pid : PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (timersStop pid) := by
  unfold timersStop
  repeat' first
    | (rx_retention_head delTimer
       exact ConfiguredHandshake.current_preserves _ (ConfiguredIdentity.delTimer_view _ _)
         (Origins.Retaining.of_view (Origins.Retaining.delTimer_material _ _)) history)
    | (rx_retention_head drainHandshakeSendWq; exact drainHandshakeSendWq_preserves _ history)
    | current_lifecycle_step history

theorem peerRemoveAfterDead_preserves (pid : PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (peerRemoveAfterDead pid) := by
  unfold peerRemoveAfterDead
  simp (config := {zeta := false}) only [branch,unsupported,invariant]
  repeat' first
    | (rx_retention_head keypairsClear
       exact ConfiguredHandshake.current_preserves _ (ConfiguredMaintenance.keypairsClear_view _)
         (Origins.Retaining.keypairsClear_material _) history)
    | (rx_retention_head timersStop; exact timersStop_preserves _ history)
    | (rx_retention_head drainHandshakeSendWq; exact drainHandshakeSendWq_preserves _ history)
    | (rx_retention_head peerPut; exact pay_preserves _ history)
    | current_lifecycle_step history

theorem peerRemove_preserves (peer : Option PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (peerRemove peer) := by
  unfold peerRemove
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerMakeDead; exact markDead_preserves _ history)
    | (rx_retention_head peerRemoveAfterDead; exact peerRemoveAfterDead_preserves _ history)
    | current_lifecycle_step history

end Leanux.Proofs.WG.CurrentLifecycle
