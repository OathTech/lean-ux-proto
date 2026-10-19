import Leanux.Proofs.WG.AuthenticatedEffects.CausalCallbackQuiet
import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptNestedHandshake

/-! Exact native endpoints and append-only histories for the enriched consumer
callbacks. These facts do not assert any peer, timer, or egress state invariant. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.CallbackFrames
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity RetirementSecurity
open NestedPeerRelease
variable {F : Type}

private theorem trivial_state {body : WGPrefix Event α} (ha : StateAppends body) :
    Driver.StateHistorySafe (fun _ => True) body := by
  intro w a h _
  obtain ⟨suffix,eq⟩ := ha w a h
  refine ⟨suffix,eq,True.intro,?_⟩
  split <;> trivial

private theorem state_appends {body : WGPrefix Event α}
    (ha : Driver.StateHistorySafe (fun _ => True) body) : StateAppends body := by
  intro w a h
  obtain ⟨suffix,eq,_,_⟩ := ha w a h True.intro
  exact ⟨suffix,eq⟩

private theorem trivial_ops : Ops.History (fun _ => True)
    (observedOps Event.stagedDisposal stagedDisposal?) where
  step := Driver.History.state_lift
  release := fun _ => trivial_state (StateAppends.focus _ _ _)

private theorem trivial_emit (event : Event) :
    Driver.StateHistorySafe (fun _ => True) (emitStatePrefix event) := by
  intro _ _ _ _
  exact ⟨[event],rfl,True.intro,True.intro⟩

abbrev admissionRecord := Event.old ∘ Journal.Event.handshake ∘ HandshakeCausal.Event.admission
abbrev nested := observedOps Event.stagedDisposal stagedDisposal?

theorem initiation_appends (mac : HandshakeMac) :
    StateAppends (admitInitiationWith nested admissionRecord mac) :=
  state_appends (CallbackHistory.initiation trivial_ops admissionRecord (fun _ => trivial_emit _) mac)

theorem response_appends (mac : HandshakeMac) :
    StateAppends (admitResponseWith nested admissionRecord mac) :=
  state_appends (CallbackHistory.response trivial_ops admissionRecord (fun _ => trivial_emit _) mac)

theorem cookie_appends (msg : Key) :
    StateAppends (NestedPeerRelease.cookieObserved nested Event.cookieConsumed msg) :=
  state_appends (CallbackHistory.cookie trivial_ops (observedOps_erases _ _)
    Event.cookieConsumed (fun _ _ _ _ => True.intro) msg)

theorem initiation_erases (mac : HandshakeMac) :
    ErasesStatePrefix (admitInitiationWith nested admissionRecord mac) (consumeInitiation mac.input) :=
  projects_erases (fun event => (handshake? event).bind HandshakeCausal.admission)
    (initiation_old Event.stagedDisposal stagedDisposal? admissionRecord _ (fun _ => rfl)
      (fun _ => rfl) mac) (admitInitiation_erases mac)

theorem response_erases (mac : HandshakeMac) :
    ErasesStatePrefix (admitResponseWith nested admissionRecord mac) (consumeResponse mac.input) :=
  projects_erases (fun event => (handshake? event).bind HandshakeCausal.admission)
    (response_old Event.stagedDisposal stagedDisposal? admissionRecord _ (fun _ => rfl)
      (fun _ => rfl) mac) (admitResponse_erases mac)

theorem cookie_erases (msg : Key) :
    ErasesStatePrefix (NestedPeerRelease.cookieObserved nested Event.cookieConsumed msg)
      (cookieMessageConsume msg) := by
  unfold NestedPeerRelease.cookieObserved
  apply receiptWGObserved_erases
  simpa only [cookie_native] using NestedPeerRelease.cookie_erases (observedOps_erases _ _) msg

private theorem quiet_ops (ρ : Event → Option F)
    (disposal : ∀ event, ρ (.stagedDisposal event) = none) (before : List F) :
    Ops.History (fun h => h.filterMap ρ = before) nested where
  step := Driver.History.state_lift
  release := fun _ => CallbackQuiet.state_history
    (CallbackQuiet.state_focus ρ Event.stagedDisposal stagedDisposal? disposal _) before

theorem initiation_quiet (ρ : Event → Option F)
    (disposal : ∀ event, ρ (.stagedDisposal event) = none)
    (admission : ∀ event, ρ (admissionRecord event) = none) (mac : HandshakeMac) :
    CallbackQuiet.StateQuiet ρ (admitInitiationWith nested admissionRecord mac) := by
  apply CallbackQuiet.state_of_history
  intro before
  exact CallbackHistory.initiation (quiet_ops ρ disposal before) admissionRecord
    (fun event => CallbackQuiet.state_history (CallbackQuiet.state_emit ρ _ (admission event)) before) mac

theorem response_quiet (ρ : Event → Option F)
    (disposal : ∀ event, ρ (.stagedDisposal event) = none)
    (admission : ∀ event, ρ (admissionRecord event) = none) (mac : HandshakeMac) :
    CallbackQuiet.StateQuiet ρ (admitResponseWith nested admissionRecord mac) := by
  apply CallbackQuiet.state_of_history
  intro before
  exact CallbackHistory.response (quiet_ops ρ disposal before) admissionRecord
    (fun event => CallbackQuiet.state_history (CallbackQuiet.state_emit ρ _ (admission event)) before) mac

theorem cookie_quiet (ρ : Event → Option F)
    (disposal : ∀ event, ρ (.stagedDisposal event) = none)
    (cookie : ∀ event, ρ (.cookieConsumed event) = none) (msg : Key) :
    CallbackQuiet.StateQuiet ρ (NestedPeerRelease.cookieObserved nested Event.cookieConsumed msg) := by
  apply CallbackQuiet.state_of_history
  intro before
  apply CallbackHistory.cookie (quiet_ops ρ disposal before) (observedOps_erases _ _)
    Event.cookieConsumed
  intro h receipt kept _
  simpa only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,cookie,
    Option.toList_none,List.nil_append,List.append_nil] using kept

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.CallbackFrames
