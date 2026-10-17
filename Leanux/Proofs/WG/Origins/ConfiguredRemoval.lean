import Leanux.Proofs.WG.Origins.CurrentLifecycle
import Leanux.Proofs.WG.Queues.BaseCoherenceRemoval
import Leanux.Proofs.WG.Peers.ConfiguredAllowedIps

/-! Configured identity alone survives the actual release and bounded removal
paths. No historical current-key support, credit, or residency premise is added. -/
namespace Leanux.Proofs.WG.ConfiguredRemoval
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues ConfiguredHandshake

/-- An exact configured frame transports the existing registry predicate. -/
theorem frame {action : WG.M α} (same : SameView ConfiguredIdentity.view action) :
    Preserves ConfiguredIdentity.Inv action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have eq := (ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run
  intro s hs
  exact hi s (eq.symm.trans hs)

private theorem read (pid : PeerId) : Preserves ConfiguredIdentity.Inv (getPeer pid) := by
  apply frame
  intro initial
  exact hoare_consequence (ConfiguredIdentity.getPeer_spec (fun s => s=initial) pid)
    (fun _ h => h) (fun _ _ h => h.1)

private theorem modifyDevice (f : Device → Device)
    (same : ∀ d, ConfiguredIdentity.state (f d)=ConfiguredIdentity.state d) :
    Preserves ConfiguredIdentity.Inv (modifyDev f) :=
  frame (fun initial => ConfiguredIdentity.modifyDev_spec (fun s => s=initial) f same)

macro "configured_removal_step" : tactic => `(tactic| first
  | (rx_retention_head getDev; exact frame (ConfiguredIdentity.sameWG (project := id) getDev_sameWGStore))
  | (rx_retention_head getPeer; exact read _)
  | (rx_retention_head modifyDev; apply modifyDevice _; intro d; rfl)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id ConfiguredIdentity.Inv
     intro x b
     change Preserves ConfiguredIdentity.Inv _)
  | (first | rx_retention_head throw | rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b hi run
     cases run)
  | rx_retention_step)

theorem queuedClear (pid : PeerId) :
    Preserves ConfiguredIdentity.Inv (queuedExpiredZeroKeyMaterial pid) := by
  unfold queuedExpiredZeroKeyMaterial
  exact preserves_bind (frame (ConfiguredMaintenance.handshakeClear_view pid)) (fun _ =>
    preserves_bind (frame (ConfiguredMaintenance.keypairsClear_view pid)) (fun _ =>
      ConfiguredIdentity.peerPut_preserves (some pid)))

theorem handshakeWorker (pid : PeerId) :
    Preserves ConfiguredIdentity.Inv (handshakeSendWorker pid) := by
  unfold handshakeSendWorker
  exact preserves_bind (frame (ConfiguredHandshake.sendHandshakeInitiation_view pid))
    (fun _ => ConfiguredIdentity.peerPut_preserves (some pid))

theorem flushedSend (pid : PeerId) :
    Preserves ConfiguredIdentity.Inv (runFlushedSendWork pid) := by
  let dequeue : WG.M Unit := do
    modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid}
    let p ← getPeer pid
    if !p.handshakePending then invariant "queued work without a pending flag"
    setPeer pid {p with handshakePending := (← getDev).sendWorkQueue.contains pid}
  have configured : SameView ConfiguredIdentity.view dequeue := by
    intro initial
    unfold dequeue
    change Preserves (fun w => ConfiguredIdentity.view w=initial) _
    simp (config := {zeta := false}) only [invariant]
    repeat' configured_step initial
  have factor : runFlushedSendWork pid = (do
      dequeue
      _ ← hidden (.sectionStart .sendWorker)
      handshakeSendWorker pid
      _ ← hidden (.sectionStop .sendWorker)) := by
    have bind_congr {α β : Type} (a : WG.M α) (f g : α → WG.M β)
        (h : ∀ x, f x=g x) : (a >>= f)=(a >>= g) :=
      congrArg (fun k => a >>= k) (funext h)
    simp only [runFlushedSendWork,dequeue,bind_assoc]
    apply bind_congr
    intro _
    apply bind_congr
    intro p
    by_cases h : (!p.handshakePending)=true
    all_goals simp only [h,Bool.false_eq_true,ite_true,ite_false,bind_assoc]
  rw [factor]
  exact preserves_bind (frame configured) (fun _ =>
    preserves_bind (hoare_liftAmbient (AmbientM.hidden (.sectionStart .sendWorker)) ConfiguredIdentity.Inv) (fun _ =>
      preserves_bind (handshakeWorker pid) (fun _ =>
        preserves_bind (hoare_liftAmbient (AmbientM.hidden (.sectionStop .sendWorker)) ConfiguredIdentity.Inv)
          (fun _ => preserves_pure _))))

theorem flushedClear (pid : PeerId) :
    Preserves ConfiguredIdentity.Inv (runFlushedClearWork pid) := by
  unfold runFlushedClearWork
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | (rx_retention_head queuedExpiredZeroKeyMaterial; exact queuedClear _)
    | configured_removal_step

theorem drain (upTo : Option PeerId) :
    Preserves ConfiguredIdentity.Inv (drainHandshakeSendWq upTo) := by
  unfold drainHandshakeSendWq
  simp (config := {zeta := false}) only
    [Std.Legacy.Range.forIn_eq_forIn_range',peekUnit,resolveUnit,getAmbient,invariant]
  repeat' first
    | (rx_retention_head runFlushedSendWork; exact flushedSend _)
    | (rx_retention_head runFlushedClearWork; exact flushedClear _)
    | configured_removal_step

theorem stopTimers (pid : PeerId) : Preserves ConfiguredIdentity.Inv (timersStop pid) := by
  unfold timersStop
  repeat' first
    | (rx_retention_head delTimer; exact frame (ConfiguredIdentity.delTimer_view _ _))
    | (rx_retention_head drainHandshakeSendWq; exact drain _)
    | configured_removal_step

theorem afterDead (pid : PeerId) : Preserves ConfiguredIdentity.Inv (peerRemoveAfterDead pid) := by
  unfold peerRemoveAfterDead
  simp (config := {zeta := false}) only [branch,unsupported,invariant]
  repeat' first
    | (rx_retention_head keypairsClear; exact frame (ConfiguredMaintenance.keypairsClear_view _))
    | (rx_retention_head timersStop; exact stopTimers _)
    | (rx_retention_head drainHandshakeSendWq; exact drain _)
    | (rx_retention_head peerPut; exact ConfiguredIdentity.peerPut_preserves _)
    | configured_removal_step

theorem makeDead (pid : PeerId) : Preserves ConfiguredIdentity.Inv (peerMakeDead pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  cases result
  exact ConfiguredIdentity.peerMakeDead_preserves pid w v a b hi run

theorem remove (peer : Option PeerId) : Preserves ConfiguredIdentity.Inv (peerRemove peer) := by
  unfold peerRemove
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerMakeDead; exact makeDead _)
    | (rx_retention_head peerRemoveAfterDead; exact afterDead _)
    | configured_removal_step

theorem removeAll : Preserves ConfiguredIdentity.Inv peerRemoveAll := by
  unfold peerRemoveAll
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head free; exact frame ConfiguredIdentity.allowedipsFree_view)
    | (rx_retention_head peerMakeDead; exact makeDead _)
    | (rx_retention_head peerRemoveAfterDead; exact afterDead _)
    | configured_removal_step

end Leanux.Proofs.WG.ConfiguredRemoval
