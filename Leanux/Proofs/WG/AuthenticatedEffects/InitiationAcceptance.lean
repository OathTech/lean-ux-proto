import Leanux.Proofs.WG.AuthenticatedEffects.InitiationAcceptanceSource
import Leanux.Proofs.WG.AuthenticatedEffects.CookieObservation
import Leanux.Proofs.WG.AuthenticatedEffects.SocketObservation

/-! Native initiation acceptance receipts precede every peer protocol write,
including writes before a stopped consumption-clock read. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Logged

structure InitiationAcceptance where
  input : Key
  checked : WGRunWitness (Option AcceptedInitiation)

def InitiationAcceptance.Valid (r : InitiationAcceptance) : Prop :=
  r.checked.Valid (initiationAcceptedCheck r.input) ∧ r.checked.value.isSome = true

def acceptedInitiation (msg : Key) : WGPrefix InitiationAcceptance (Option PeerId) := do
  let checked ← captureWGRun (initiationAcceptedCheck msg)
  if checked.value.isSome then emitStatePrefix ⟨msg,checked⟩
  liftWGPrefix (initiationAcceptedContinue msg checked.value)

theorem acceptedInitiation_run (msg : Key)
    (w : WGWorld) (a : Ambient) (h : List InitiationAcceptance) :
    runWGPrefix (acceptedInitiation msg) w a h =
      match ((initiationAcceptedCheck msg).run w).run a with
      | .error err => (.error err,h)
      | .ok ((admission,u),b) =>
        (((initiationAcceptedContinue msg admission).run u).run b,
          if admission.isSome then h ++ [⟨msg,⟨admission,w,u,a,b⟩⟩] else h) := by
  unfold acceptedInitiation
  change runStatePrefix _ w a h = _
  rw [runStatePrefix_bind]
  have capture := runWGPrefix_captureWGRun (E := InitiationAcceptance) (initiationAcceptedCheck msg) w a h
  change runStatePrefix _ w a h = _ at capture
  rw [capture]
  cases checked : ((initiationAcceptedCheck msg).run w).run a with
  | error err => rfl
  | ok out =>
    rcases out with ⟨⟨admission,u⟩,b⟩
    cases admission <;> simp only [Except.map,Option.isSome_none,Option.isSome_some,
      Bool.false_eq_true,↓reduceIte,runStatePrefix_bind,runStatePrefix_emit] <;> rfl

theorem acceptedInitiation_erases (msg : Key) :
    ErasesStatePrefix (acceptedInitiation msg) (initiationAcceptedCheck msg >>= initiationAcceptedContinue msg) := by
  intro w a h
  change (runWGPrefix (acceptedInitiation msg) w a h).1 = _
  rw [acceptedInitiation_run,native_bind_run]
  cases checked : ((initiationAcceptedCheck msg).run w).run a with
  | error err => rfl
  | ok out => rcases out with ⟨⟨admission,u⟩,b⟩; rfl

theorem acceptedInitiation_receipts (msg : Key)
    (w : WGWorld) (a : Ambient) (h : List InitiationAcceptance) :
    ∃ suffix, (runWGPrefix (acceptedInitiation msg) w a h).2 = h ++ suffix ∧
      suffix.length ≤ 1 ∧ ∀ r ∈ suffix, r.input = msg ∧ r.Valid := by
  rw [acceptedInitiation_run]
  cases checked : ((initiationAcceptedCheck msg).run w).run a with
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

theorem acceptedInitiation_original (msg : Key) :
    ErasesStatePrefix (acceptedInitiation msg) (consumeInitiation msg) := by
  rw [←initiationAcceptedCheck_factor]
  exact acceptedInitiation_erases msg

theorem acceptedInitiation_retains_before_stop (msg : Key)
    (w u : WGWorld) (a b : Ambient) (accepted : AcceptedInitiation)
    (h : List InitiationAcceptance) (err : Stop)
    (checked : ((initiationAcceptedCheck msg).run w).run a = .ok ((some accepted,u),b))
    (stopped : ((initiationAcceptedFinish msg accepted).run u).run b = .error err) :
    runWGPrefix (acceptedInitiation msg) w a h =
      (.error err,h ++ [⟨msg,⟨some accepted,w,u,a,b⟩⟩]) := by
  rw [acceptedInitiation_run,checked]
  simp only [initiationAcceptedContinue,stopped,Option.isSome_some,↓reduceIte]

end Leanux.Proofs.WG.AuthenticatedEffects
