import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialQuiet
import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialActorFrames
import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialBounds
import Leanux.Proofs.WG.TransmitSecurity.DriverEffectsNeutral

/-! Shared staging and keepalive retain the RX allocation carrier while
recording their actual TX events. Native erasure transfers only state frames. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues AuthenticatedEffects Responder TransmitSecurity
set_option maxHeartbeats 600000

theorem selection_history (pid : PeerId) : Driver.StateHistorySafe Safe (Journal.selection pid) := by
  apply history_focused_receipt
  intro r
  exact ⟨rfl,by intro p k receipt impossible; cases impossible⟩

theorem reserve_history (kid : KeypairId) : Driver.StateHistorySafe Safe (Journal.reserve kid) :=
  history_receipt_state _ _ (fun _ => ⟨rfl,by intro p k receipt impossible; cases impossible⟩)
    (history_focus_state _ _ (fun _ => ⟨rfl,by intro p k receipt impossible; cases impossible⟩) _)

theorem allocate_history (packets : List DataPacket) : Driver.StateHistorySafe Safe (Journal.allocate packets) :=
  history_receipt_state _ _ (fun _ => ⟨rfl,by intro p k receipt impossible; cases impossible⟩)
    (Driver.History.state_lift _)

theorem create_history (pid : PeerId) (items : List SkbId) : Driver.StateHistorySafe Safe (Journal.create pid items) :=
  history_lower _ (history_focus_product _ _ (fun _ => ⟨rfl,by intro p k receipt impossible; cases impossible⟩) _)

theorem staging_history (pid : PeerId) : Driver.StateHistorySafe Safe (Driver.stagingObserved Journal.hooks pid) := by
  unfold Driver.stagingObserved
  simp only [Driver.noKey_lift Journal.hooks rfl]
  repeat' first
    | (driver_history_head Driver.Hooks.selection; exact selection_history _)
    | (driver_history_head Driver.Hooks.reserve; exact reserve_history _)
    | (driver_history_head Driver.Hooks.allocate; exact allocate_history _)
    | (driver_history_head Driver.Hooks.create; exact create_history _ _)
    | driver_state_history_step

theorem staging (pid : PeerId) : StateSafe (Driver.stagingObserved Journal.hooks pid) :=
  state_observed (staging_history pid) (ResidentMaterial.staging_erases pid) (fun _ => bounded_staging pid)

theorem state_ambient (action : AmbientM α) : StateSafe (liftWGPrefix (monadLift action)) :=
  state_native _ (fun _ => hoare_liftAmbient action _)

macro "receive_execution_state_step" : tactic => `(tactic| first
  | (nonce_source_head branch; exact state_ambient _)
  | (nonce_source_head hiddenAlloc; exact state_ambient _)
  | (nonce_source_head getPeer; exact state_native _ (fun _ => bounded_read_peer _))
  | (nonce_source_head setPeer; exact state_native _ (fun _ => bounded_set_peer _ _))
  | (nonce_source_head getDev; exact state_native _ (fun _ => bounded_store getDev_sameWGStore))
  | (nonce_source_head Pure.pure; exact state_pure _)
  | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
  | split
  | (with_reducible intro x; try dsimp only))

theorem keepalive (pid : PeerId) : StateSafe (Driver.keepaliveObserved Journal.hooks pid) := by
  change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
  rw [Driver.keepalive_native _ rfl]
  unfold Driver.keepaliveInline
  repeat' first
    | (nonce_source_head Driver.stagingObserved; exact staging _)
    | receive_execution_state_step

theorem receive_tail (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    StateSafe (Driver.receiveTailObserved Journal.hooks pid pkt confirmed) := by
  change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
  unfold Driver.receiveTailObserved
  simp only [Driver.prepare_lift Journal.hooks rfl]
  repeat' first
    | (nonce_source_head Driver.stagingObserved; exact staging _)
    | (nonce_source_head timersHandshakeComplete; exact state_native _ (fun _ => bounded_complete _ _))
    | (nonce_source_head RxCredits.prepareRest; exact state_native _ (fun _ => bounded_prepare_rest _ _))
    | (nonce_source_head Packets.rxFinish; exact state_native _ (fun _ => bounded_finish _ _))
    | receive_execution_state_step

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
