import Leanux.Proofs.WG.AuthenticatedEffects.ResponseAcceptanceSource
import Leanux.Proofs.WG.AuthenticatedEffects.CookieObservation
import Leanux.Proofs.WG.AuthenticatedEffects.SocketObservation

/-! Native response acceptance receipts precede every peer protocol write,
including a stopped state-update suffix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Logged

structure ResponseAcceptance where
  input : Key
  checked : WGRunWitness (Option AcceptedResponse)

def ResponseAcceptance.Valid (r : ResponseAcceptance) : Prop :=
  r.checked.Valid (responseAcceptedCheck r.input) ∧ r.checked.value.isSome = true

def acceptedResponse (msg : Key) : WGPrefix ResponseAcceptance (Option PeerId) := do
  let checked ← captureWGRun (responseAcceptedCheck msg)
  if checked.value.isSome then emitStatePrefix ⟨msg,checked⟩
  liftWGPrefix (responseAcceptedContinue msg checked.value)

theorem acceptedResponse_run (msg : Key)
    (w : WGWorld) (a : Ambient) (h : List ResponseAcceptance) :
    runWGPrefix (acceptedResponse msg) w a h =
      match ((responseAcceptedCheck msg).run w).run a with
      | .error err => (.error err,h)
      | .ok ((admission,u),b) =>
        (((responseAcceptedContinue msg admission).run u).run b,
          if admission.isSome then h ++ [⟨msg,⟨admission,w,u,a,b⟩⟩] else h) := by
  unfold acceptedResponse
  change runStatePrefix _ w a h = _
  rw [runStatePrefix_bind]
  have capture := runWGPrefix_captureWGRun (E := ResponseAcceptance) (responseAcceptedCheck msg) w a h
  change runStatePrefix _ w a h = _ at capture
  rw [capture]
  cases checked : ((responseAcceptedCheck msg).run w).run a with
  | error err => rfl
  | ok out =>
    rcases out with ⟨⟨admission,u⟩,b⟩
    cases admission <;> simp only [Except.map,Option.isSome_none,Option.isSome_some,
      Bool.false_eq_true,↓reduceIte,runStatePrefix_bind,runStatePrefix_emit] <;> rfl

theorem acceptedResponse_erases (msg : Key) :
    ErasesStatePrefix (acceptedResponse msg) (responseAcceptedCheck msg >>= responseAcceptedContinue msg) := by
  intro w a h
  change (runWGPrefix (acceptedResponse msg) w a h).1 = _
  rw [acceptedResponse_run,native_bind_run]
  cases checked : ((responseAcceptedCheck msg).run w).run a with
  | error err => rfl
  | ok out => rcases out with ⟨⟨admission,u⟩,b⟩; rfl

theorem acceptedResponse_receipts (msg : Key)
    (w : WGWorld) (a : Ambient) (h : List ResponseAcceptance) :
    ∃ suffix, (runWGPrefix (acceptedResponse msg) w a h).2 = h ++ suffix ∧
      suffix.length ≤ 1 ∧ ∀ r ∈ suffix, r.input = msg ∧ r.Valid := by
  rw [acceptedResponse_run]
  cases checked : ((responseAcceptedCheck msg).run w).run a with
  | error err => exact ⟨[],by simp⟩
  | ok out =>
    rcases out with ⟨⟨admission,u⟩,b⟩
    cases admission with
    | none => exact ⟨[],by simp⟩
    | some value =>
      refine ⟨[⟨msg,⟨some value,w,u,a,b⟩⟩],rfl,by simp,?_⟩
      intro r mem
      simp only [List.mem_singleton] at mem
      subst r
      exact ⟨rfl,checked,rfl⟩

theorem acceptedResponse_original (msg : Key) :
    ErasesStatePrefix (acceptedResponse msg) (consumeResponse msg) := by
  rw [←responseAcceptedCheck_factor]
  exact acceptedResponse_erases msg

theorem acceptedResponse_retains_before_stop (msg : Key)
    (w u : WGWorld) (a b : Ambient) (accepted : AcceptedResponse)
    (h : List ResponseAcceptance) (err : Stop)
    (checked : ((responseAcceptedCheck msg).run w).run a = .ok ((some accepted,u),b))
    (stopped : ((responseAcceptedFinish msg accepted).run u).run b = .error err) :
    runWGPrefix (acceptedResponse msg) w a h =
      (.error err,h ++ [⟨msg,⟨some accepted,w,u,a,b⟩⟩]) := by
  rw [acceptedResponse_run,checked]
  simp only [responseAcceptedContinue,stopped,Option.isSome_some,↓reduceIte]

end Leanux.Proofs.WG.AuthenticatedEffects
