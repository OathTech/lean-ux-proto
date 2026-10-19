import Leanux.Proofs.WG.TransmitSecurity.StagedMoreEffects
import Leanux.Proofs.WG.TransmitSecurity.StagedNativeTactics

/-! Native handshake observations and lexical scope markers preserve the exact
staged-origin carrier. The handshake call itself is never executed twice. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects AuthenticatedEffects.CausalJournal
set_option maxHeartbeats 600000

theorem handshake_focus (body : WGPrefix HandshakeCausal.Event α) (native : WG.M α)
    (erase : ErasesStatePrefix body native) (kept : ∀ h, Preserves (Inv h) native) : StateSafe
    (HandshakeWorker.old (Event.old ∘ Journal.Event.handshake) handshake? body) :=
  state_quiet (StateAppends.focus _ _ _)
    (fun w => focusPrefix_other _ _ _ (fun _ => rfl) (body.run w))
    (focusStatePrefix_erases _ _ erase) kept

theorem handshake_call (kind : HandshakeCausal.Kind) (pid : PeerId) (native : WG.M α)
    (kept : ∀ h, Preserves (Inv h) native) : StateSafe
    (HandshakeWorker.old (Event.old ∘ Journal.Event.handshake) handshake? (HandshakeCausal.call kind pid native)) :=
  handshake_focus _ _ (HandshakeCausal.call_erases kind pid native) kept

theorem handshake_initiation (mac : HandshakeMac) : StateSafe
    (HandshakeWorker.old (Event.old ∘ Journal.Event.handshake) handshake? (HandshakeCausal.initiation mac)) :=
  handshake_focus _ _ (HandshakeCausal.initiation_erases mac) (fun _ => Native.initiation mac.input)

theorem handshake_response (mac : HandshakeMac) : StateSafe
    (HandshakeWorker.old (Event.old ∘ Journal.Event.handshake) handshake? (HandshakeCausal.response mac)) :=
  handshake_focus _ _ (HandshakeCausal.response_erases mac) (fun _ => Native.response mac.input)

theorem session_observed (pid : PeerId) : StateSafe (CausalJournal.session pid) := by
  unfold CausalJournal.session HandshakeSecurity.ExchangeJoint.session
  apply state_receipt
  · unfold state Journal.session HandshakeSecurity.Responder.DriverCuts.session
    rw [focused_native_receipt,focused_native_receipt]
    exact state_receipt (state_lift _ (fun _ => Native.session pid)) _ (fun _ => True.intro)
  · intro r; trivial

theorem confirmation_observed (pid : PeerId) (kid : KeypairId) :
    StateSafe (state (Journal.confirmation pid kid)) := by
  unfold state Journal.confirmation HandshakeSecurity.Responder.DriverCuts.confirmation
  rw [focused_native_receipt,focused_native_receipt]
  exact state_receipt (state_lift _ (fun _ => Native.confirm pid kid)) _ (fun _ => True.intro)

theorem handshake_callback (kind : HandshakeCausal.Kind) (pid : PeerId) (body : WGPrefix Event α)
    (safe : StateSafe body) : StateSafe
    (HandshakeWorker.callback (Event.old ∘ Journal.Event.handshake) kind pid body) :=
  state_bind (state_emit _ True.intro) (fun _ => safe)


open Lean Meta Elab Tactic in
elab "staged_origin_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``StateSafe do throwError "not a staged-origin state contract"
  let some action := target.getAppArgs.back? | throwError "missing action"
  let .const actual _ := action.consumeMData.headBeta.getAppFn | throwError "not a constant-headed action"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do throwError "different source head"

open Lean Meta Elab Tactic in
elab "staged_origin_old_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``StateSafe do throwError "not a staged-origin state contract"
  let some action := target.getAppArgs.back? | throwError "missing action"
  let action := action.consumeMData.headBeta
  unless action.isAppOf ``HandshakeWorker.old do throwError "not an old handshake callback"
  let some body := action.getAppArgs.back? | throwError "missing callback"
  let .const actual _ := body.consumeMData.headBeta.getAppFn | throwError "not a constant callback"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do throwError "different callback"

macro "staged_origin_step" : tactic => `(tactic| first
  | (staged_origin_head Pure.pure; exact state_pure _)
  | (staged_origin_head Bind.bind; apply state_bind)
  | (staged_origin_head ite; apply state_ite)
  | (staged_origin_head ForIn.forIn; apply state_forIn)
  | maintenance_intro
  | (split; all_goals try simp_all only []; all_goals try subst_vars)
  | simp +failIfUnchanged only [bind_assoc,pure_bind])

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
