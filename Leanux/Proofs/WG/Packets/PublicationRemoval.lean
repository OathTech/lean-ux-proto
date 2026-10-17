import Leanux.Proofs.WG.Packets.PublicationClear
import Leanux.Proofs.WG.Packets.PublicationHandshakeSend
import Leanux.Proofs.WG.AllowedIps.ClearEndpoint
import Leanux.Proofs.WG.Origins.CurrentDevice
import Leanux.Proofs.WG.Origins.OwnerDevice

/-! Exact native work flushing and peer removal retain packet publications.
The concrete handshake send-worker contract closes the callback. All drain
decisions, the original finite bound and rejection paths remain. -/
namespace Leanux.Proofs.WG.PublicationFrontier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues

theorem runFlushedSendWork_preserves (pid : PeerId) (history : List RxHistory.Event)
    :
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
  have geometry : SameView OwnerCompletion.geometry dequeue := by
    intro initial
    unfold dequeue
    change Preserves (fun w => OwnerCompletion.geometry w = initial) _
    simp (config := {zeta := false}) only [invariant]
    repeat' completion_step initial
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
  apply preserves_bind (preserves_of_configured _ (geometry.factor Prod.snd) configured history)
  intro _
  apply preserves_bind (hoare_liftAmbient (AmbientM.hidden (.sectionStart .sendWorker)) (Inv history))
  intro _
  apply preserves_bind (handshakeSendWorker_preserves pid history)
  intro _
  apply preserves_bind (hoare_liftAmbient (AmbientM.hidden (.sectionStop .sendWorker)) (Inv history))
  intro _
  exact preserves_pure _

/-- Both the recorded dispatch and source fallback use the actual 4096-step
loop. Exhaustion, malformed sections and worker failures remain Stops. -/
theorem drainHandshakeSendWq_preserves (upTo : Option PeerId)
    (history : List RxHistory.Event)
    :
    Preserves (Inv history) (drainHandshakeSendWq upTo) := by
  unfold drainHandshakeSendWq
  simp (config := {zeta := false}) only
    [Std.Legacy.Range.forIn_eq_forIn_range',peekUnit,resolveUnit,getAmbient,invariant]
  repeat' first
    | (rx_retention_head runFlushedSendWork; exact runFlushedSendWork_preserves _ history)
    | (rx_retention_head runFlushedClearWork; exact runFlushedClearWork_preserves _ history)
    | publication_removal_step history

theorem timersStop_preserves (pid : PeerId) (history : List RxHistory.Event)
    :
    Preserves (Inv history) (timersStop pid) := by
  unfold timersStop
  repeat' first
    | (rx_retention_head delTimer; exact delTimer_preserves _ _ history)
    | (rx_retention_head drainHandshakeSendWq; exact drainHandshakeSendWq_preserves _ history)
    | publication_removal_step history

theorem peerRemoveAfterDead_preserves (pid : PeerId) (history : List RxHistory.Event)
    :
    Preserves (Inv history) (peerRemoveAfterDead pid) := by
  unfold peerRemoveAfterDead
  simp (config := {zeta := false}) only [branch,unsupported,invariant]
  repeat' first
    | (rx_retention_head keypairsClear; exact keypairsClear_preserves _ history)
    | (rx_retention_head timersStop; exact timersStop_preserves _ history)
    | (rx_retention_head drainHandshakeSendWq; exact drainHandshakeSendWq_preserves _ history)
    | (rx_retention_head peerPut; exact peerPut_preserves _ history)
    | publication_removal_step history

theorem peerRemove_preserves (peer : Option PeerId) (history : List RxHistory.Event)
    :
    Preserves (Inv history) (peerRemove peer) := by
  unfold peerRemove
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerMakeDead; exact peerMakeDead_preserves _ history)
    | (rx_retention_head peerRemoveAfterDead; exact peerRemoveAfterDead_preserves _ history)
    | publication_removal_step history

private theorem allowedipsFree_geometry : SameView OwnerCompletion.geometry WG.free := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v finalAmbient hr
  have fields := (hoare_iff_run_ambient _ _ _).mp
    (AllowedIps.free_storeView (wgStoreView w)) w ambient result v finalAmbient rfl hr
  have projected := congrArg (fun s : WGStoreView × (PeerId → Option Peer) =>
    OwnerCompletion.geometry {dev := s.1.dev}) fields
  simpa only [OwnerCompletion.geometry,RxCredits.rxView,AllowedIps.clearStoreView,
    AllowedIps.clearStoreProjection,wgStoreView,AllowedIps.resetAllowedips,
    Option.map_map,Option.bind_map,Function.comp_def] using projected

theorem allowedipsFree_preserves (history : List RxHistory.Event) :
    Preserves (Inv history) WG.free :=
  preserves_of_configured _ (allowedipsFree_geometry.factor Prod.snd)
    ConfiguredIdentity.allowedipsFree_view history

/-- Both passes use the original saved peer list; no distinctness, liveness,
empty workqueue or successful-drain premise is introduced. -/
theorem peerRemoveAll_preserves (history : List RxHistory.Event)
    :
    Preserves (Inv history) peerRemoveAll := by
  unfold peerRemoveAll
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.free; exact allowedipsFree_preserves history)
    | (rx_retention_head peerMakeDead; exact peerMakeDead_preserves _ history)
    | (rx_retention_head peerRemoveAfterDead; exact peerRemoveAfterDead_preserves _ history)
    | publication_removal_step history

theorem removalCall_preserves (call : PeerRemovalCall) (history : List RxHistory.Event)
    :
    Preserves (Inv history) call.original := by
  cases call with
  | sendWork pid => exact runFlushedSendWork_preserves pid history
  | clearWork pid => exact runFlushedClearWork_preserves pid history
  | drain upTo => exact drainHandshakeSendWq_preserves upTo history
  | stopTimers pid => exact timersStop_preserves pid history
  | afterDead pid => exact peerRemoveAfterDead_preserves pid history
  | remove peer => exact peerRemove_preserves peer history
  | removeAll => exact peerRemoveAll_preserves history

end Leanux.Proofs.WG.PublicationFrontier
