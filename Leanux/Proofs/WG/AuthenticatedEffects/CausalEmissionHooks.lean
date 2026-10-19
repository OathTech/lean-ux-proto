import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionOld
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionCallbackFrames
import Leanux.Proofs.WG.AuthenticatedEffects.EmissionStagingFrames

/-! Actual key selection, confirmation, reservation and allocation callbacks
preserve socket-append accounting. Their quiet-history facts are independent
of the native state frames and retain failed callback prefixes. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing TransmitSecurity HandshakeSecurity

private theorem native_appends (action : WG.M α) : StateAppends (liftWGPrefix action : WGPrefix Journal.Event α) :=
  fun _ _ _ => ⟨[],by simp only [List.append_nil]; rfl⟩

private theorem responder (body : WGPrefix Responder.DriverCuts.Event α) (native : WG.M α)
    (erases : ErasesStatePrefix body native) (frame : SameView WGWorld.sent native) :
    StateSafe (state (focusStatePrefix Journal.Event.responder Journal.responder? body)) :=
  old_state _ native (focusStatePrefix_erases _ _ erases) (StateAppends.focus _ _ _)
    (fun w a h => focusPrefix_other _ _ oldSocket? (fun _ => rfl) (body.run w) a h) frame

theorem selection (pid : PeerId) : StateSafe (hooks.selection pid) :=
  state_callback _ (CallbackQuiet.selection contributing? (fun _ => rfl) (fun _ _ => rfl) pid)
    (RetirementSecurity.NestedPeerRelease.projects_erases old? (CausalJournal.selection_projects pid)
      (focusStatePrefix_erases _ _ (Responder.DriverCuts.selection_erases pid)))
    (EmissionFrames.selection pid)

theorem confirmation (pid : PeerId) (key : KeypairId) : StateSafe (hooks.confirmation pid key) :=
  responder _ _ (Responder.DriverCuts.confirmation_erases pid key) (EmissionFrames.confirmed pid key)

theorem session (pid : PeerId) : StateSafe (hooks.session pid) :=
  state_receipt _ (responder _ _ (Responder.DriverCuts.session_erases pid) (EmissionFrames.session pid))
    _ (fun _ => rfl)

theorem reserve (slot : KeypairId) : StateSafe (hooks.reserve slot) :=
  old_state _ _
    (receiptWGObserved_erases (focusStatePrefix_erases _ _ (Nonce.reserveObserved_erases slot)) _)
    ((StateAppends.focus _ _ _).receiptWGObserved _)
    (StateHistoryFrame.receiptWGObserved
      (fun w a h => focusPrefix_other _ _ oldSocket? (fun _ => rfl) (Nonce.reserveObserved slot |>.run w) a h)
      _ (fun _ => rfl)) (EmissionFrames.reserve slot)

theorem allocate (packets : List DataPacket) : StateSafe (hooks.allocate packets) :=
  old_state _ _ (receiptWGObserved_erases (erasesStatePrefix_lift _) _)
    ((native_appends _).receiptWGObserved _)
    (StateHistoryFrame.receiptWGObserved (fun _ _ _ => rfl) _ (fun _ => rfl))
    (EmissionFrames.allocate packets)

theorem create (pid : PeerId) (items : List SkbId) : StateSafe (hooks.create pid items) :=
  state_callback _ (CallbackQuiet.create contributing? (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) pid items)
    (RetirementSecurity.NestedPeerRelease.projects_erases old? (CausalJournal.create_projects pid items)
      (Delayed.projected_erases _ _ Journal.nonce? (Journal.create_projects pid items)))
    (EmissionFrames.create pid items)

theorem keepalive_prepare (pid : PeerId) : StateSafe (hooks.keepalivePrepare pid) :=
  state_receipt _ (state_native _ (EmissionFrames.keepalive pid)) _ (fun _ => rfl)

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
