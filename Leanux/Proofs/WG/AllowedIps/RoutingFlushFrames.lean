import Leanux.Proofs.WG.AllowedIps.RoutingHandshakeFrames

/-! Concrete original inline flushes preserve routing while permitting resident
peer deletion. The finite drain's exhaustion and record failures remain Stops;
no progress, reference-credit or worker-affiliation premise is imposed. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1200000
set_option pp.structureInstances false

theorem runFlushedSendWork_routing (pid : PeerId) : RetainsRoutingCall (runFlushedSendWork pid) := by
  let prelude : WG.M Unit := do
    modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid}
    let p ← getPeer pid
    if !p.handshakePending then invariant "queued work without a pending flag"
    setPeer pid {p with handshakePending := (← getDev).sendWorkQueue.contains pid}
  have hp : SameView routingView prelude := by
    have queue := modifyDev_routing (fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid})
      (fun _ => rfl)
    routing_handshake_source [prelude] using [queue]
  intro s
  let P := fun w : WGWorld => RetainsRouting s (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have main : Preserves P (runFlushedSendWork pid) := by
    have source : runFlushedSendWork pid = (do
        prelude
        _ ← hidden (.sectionStart .sendWorker)
        handshakeSendWorker pid
        _ ← hidden (.sectionStop .sendWorker)) := by
      have distribute {α β : Type} (test : Prop) [Decidable test]
          (yes no : WG.M α) (f : α → WG.M β) :
          ((if test then yes else no) >>= f) =
            (if test then yes >>= f else no >>= f) := by split <;> rfl
      simp only [runFlushedSendWork, prelude, bind_assoc, distribute]
    rw [source]
    apply preserves_bind (hp.wp (RetainsRouting s))
    intro _
    apply preserves_bind (ambient (AmbientM.hidden (.sectionStart .sendWorker)))
    intro _
    apply preserves_bind (RetainsRoutingCall.wp (handshakeSendWorker_routing pid) s)
    intro _
    apply preserves_bind (ambient (AmbientM.hidden (.sectionStop .sendWorker)))
    intro _
    exact preserves_pure ()
  apply hoare_consequence main
  · intro w h
    change RetainsRouting s (routingView w)
    dsimp only [_root_.id] at h
    rw [h]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h


theorem runFlushedClearWork_routing (pid : PeerId) : RetainsRoutingCall (runFlushedClearWork pid) := by
  intro s
  let P := fun w : WGWorld => RetainsRouting s (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have hm := (modifyDev_routing (fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid})
    (fun _ => rfl)).wp (RetainsRouting s)
  have main : Preserves P (runFlushedClearWork pid) := by
    unfold runFlushedClearWork
    apply preserves_bind hm
    intro _
    apply preserves_bind (ambient (AmbientM.hidden (.sectionStart .clearPeerWorker)))
    intro _
    apply preserves_bind (RetainsRoutingCall.wp (queuedExpiredZeroKeyMaterial_routing pid) s)
    intro _
    apply preserves_bind (ambient (AmbientM.hidden (.sectionStop .clearPeerWorker)))
    intro _
    exact preserves_pure ()
  apply hoare_consequence main
  · intro w h
    change RetainsRouting s (routingView w)
    dsimp only [_root_.id] at h
    rw [h]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h


theorem drainHandshakeSendWq_routing (upTo : Option PeerId) : RetainsRoutingCall (drainHandshakeSendWq upTo) := by
  intro s
  let Q := RetainsRouting s
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have dev : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp Q
  have stopped {α : Type} (e : Stop) : Preserves P (throw e : WG.M α) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' _ hr
    cases hr
  have loop {α β : Type} (xs : List α) (b : β) (f : α → β → WG.M (ForInStep β))
      (hf : ∀ x b, Preserves P (f x b)) : Preserves P (forIn xs b f) :=
    list_view_spec id P xs b f hf
  have send := fun pid => RetainsRoutingCall.wp (runFlushedSendWork_routing pid) s
  have clear := fun pid => RetainsRoutingCall.wp (runFlushedClearWork_routing pid) s
  have main : Preserves P (drainHandshakeSendWq upTo) := by
    unfold drainHandshakeSendWq
    simp (config := { zeta := false }) only [peekUnit, resolveUnit, getAmbient, invariant]
    repeat' first
      | (rx_retention_head runFlushedSendWork; exact send _)
      | (rx_retention_head runFlushedClearWork; exact clear _)
      | (rx_retention_head getDev; exact dev)
      | (rx_retention_head MonadLiftT.monadLift; exact ambient _)
      | (rx_retention_head MonadLift.monadLift; exact ambient _)
      | (rx_retention_head MonadExceptOf.throw; exact stopped _)
      | (rx_retention_head throw; exact stopped _)
      | (rx_retention_head ForIn.forIn; first | apply loop | rw [Std.Legacy.Range.forIn_eq_forIn_range'])
      | rx_retention_step
  apply hoare_consequence main
  · intro w h
    change RetainsRouting s (routingView w)
    dsimp only [_root_.id] at h
    rw [h]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h


theorem timersStop_routing (pid : PeerId) : RetainsRoutingCall (timersStop pid) := by
  intro s
  let Q := RetainsRouting s
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have dev : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp Q
  have stopped {α : Type} (e : Stop) : Preserves P (throw e : WG.M α) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' _ hr
    cases hr
  have loop {α β : Type} (xs : List α) (b : β) (f : α → β → WG.M (ForInStep β))
      (hf : ∀ x b, Preserves P (f x b)) : Preserves P (forIn xs b f) :=
    list_view_spec id P xs b f hf
  have del := fun t => (delTimer_routing pid t).wp Q
  have drain := RetainsRoutingCall.wp (drainHandshakeSendWq_routing (some pid)) s
  have main : Preserves P (timersStop pid) := by
    unfold timersStop

    repeat' first
      | (rx_retention_head delTimer; exact del _)
      | (rx_retention_head drainHandshakeSendWq; exact drain)
      | (rx_retention_head getDev; exact dev)
      | (rx_retention_head MonadLiftT.monadLift; exact ambient _)
      | (rx_retention_head MonadLift.monadLift; exact ambient _)
      | (rx_retention_head MonadExceptOf.throw; exact stopped _)
      | (rx_retention_head throw; exact stopped _)
      | (rx_retention_head ForIn.forIn; first | apply loop | rw [Std.Legacy.Range.forIn_eq_forIn_range'])
      | rx_retention_step
  apply hoare_consequence main
  · intro w h
    change RetainsRouting s (routingView w)
    dsimp only [_root_.id] at h
    rw [h]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h


theorem peerRemoveAfterDead_routing (pid : PeerId) : RetainsRoutingCall (peerRemoveAfterDead pid) := by
  intro s
  let Q := RetainsRouting s
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have dev : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp Q
  have stopped {α : Type} (e : Stop) : Preserves P (throw e : WG.M α) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' _ hr
    cases hr
  have loop {α β : Type} (xs : List α) (b : β) (f : α → β → WG.M (ForInStep β))
      (hf : ∀ x b, Preserves P (f x b)) : Preserves P (forIn xs b f) :=
    list_view_spec id P xs b f hf
  have peer := (getPeer_routing pid).wp Q
  have keys := (keypairsClear_routing pid).wp Q
  have timers := RetainsRoutingCall.wp (timersStop_routing pid) s
  have drain := RetainsRoutingCall.wp (drainHandshakeSendWq_routing none) s
  have modify := (modifyDev_routing (fun d => {d with numPeers := d.numPeers - 1})
    (fun _ => rfl)).wp Q
  have release := RetainsRoutingCall.wp (peerPut_retainsRouting (some pid)) s
  have main : Preserves P (peerRemoveAfterDead pid) := by
    unfold peerRemoveAfterDead
    simp (config := { zeta := false }) only [branch, invariant, unsupported]
    repeat' first
      | (rx_retention_head getPeer; exact peer)
      | (rx_retention_head keypairsClear; exact keys)
      | (rx_retention_head timersStop; exact timers)
      | (rx_retention_head drainHandshakeSendWq; exact drain)
      | (rx_retention_head modifyDev; exact modify)
      | (rx_retention_head peerPut; exact release)
      | (rx_retention_head getDev; exact dev)
      | (rx_retention_head MonadLiftT.monadLift; exact ambient _)
      | (rx_retention_head MonadLift.monadLift; exact ambient _)
      | (rx_retention_head MonadExceptOf.throw; exact stopped _)
      | (rx_retention_head throw; exact stopped _)
      | (rx_retention_head ForIn.forIn; first | apply loop | rw [Std.Legacy.Range.forIn_eq_forIn_range'])
      | rx_retention_step
  apply hoare_consequence main
  · intro w h
    change RetainsRouting s (routingView w)
    dsimp only [_root_.id] at h
    rw [h]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h


end Leanux.Proofs.WG.AllowedIps
