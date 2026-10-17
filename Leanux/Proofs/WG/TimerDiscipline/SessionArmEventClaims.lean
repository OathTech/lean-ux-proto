import Leanux.Proofs.WG.TimerDiscipline.SessionArmEventSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG

/-- A normal full incoming response retains its existing complete observation,
now with the exact all-mode session arm event at the real hook cut. The original
observer erasure preserves every failure; no later final-state arm is inferred. -/
theorem observedResponseSession_arm_event (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    Campaign2.Product.Ensures (observedResponseSession msg src) (fun _ => True)
      (fun observation _ => ResponseSessionObservation msg observation ∧
        ∀ cut afterPrefix, observation = .ok (some cut,afterPrefix) →
          SessionArmEvent cut.response.consumed.input.pid cut.session) := by
  intro initial observation final pre run
  refine ⟨observedResponseSession_facts msg src kind initial observation final pre run,?_⟩
  rw [observedResponseSession_source msg src kind] at run
  change ((responseSessionCallPrefix msg src).run initial >>= _) = _ at run
  cases prefixRun : (responseSessionCallPrefix msg src).run initial with
  | error stop => rw [prefixRun] at run; cases run
  | ok pair =>
    obtain ⟨candidate,afterPrefix⟩ := pair
    rw [prefixRun] at run
    change ((responseSessionCallSuffix msg candidate).run afterPrefix >>= _) = _ at run
    cases suffixRun : (responseSessionCallSuffix msg candidate).run afterPrefix with
    | error stop => rw [suffixRun] at run; cases run
    | ok out =>
      rw [suffixRun] at run
      cases run
      intro cut observed same
      cases same
      exact responseSessionCallPrefix_event msg src initial _ afterPrefix True.intro prefixRun cut rfl

/-- The actual full outgoing response carries exactly the reached session event,
including guard suppression and kept/enqueued wheel outcomes in either mode. -/
theorem observedOutgoingResponseSession_arm_event (pid : PeerId) :
    Campaign2.Product.Ensures (observedOutgoingResponseSession pid) (fun _ => True)
      (fun observation _ => OutgoingResponseSessionObservation pid observation ∧
        ∀ cut afterPrefix, observation = .ok (some cut,afterPrefix) → SessionArmEvent pid cut.session) := by
  intro initial observation final pre run
  refine ⟨observedOutgoingResponseSession_facts pid initial observation final pre run,?_⟩
  rw [observedOutgoingResponseSession_source pid] at run
  change ((outgoingResponseSessionPrefix pid).run initial >>= _) = _ at run
  cases prefixRun : (outgoingResponseSessionPrefix pid).run initial with
  | error stop => rw [prefixRun] at run; cases run
  | ok pair =>
    obtain ⟨candidate,afterPrefix⟩ := pair
    rw [prefixRun] at run
    change ((outgoingResponseSessionSuffix pid candidate).run afterPrefix >>= _) = _ at run
    cases suffixRun : (outgoingResponseSessionSuffix pid candidate).run afterPrefix with
    | error stop => rw [suffixRun] at run; cases run
    | ok out =>
      rw [suffixRun] at run
      cases run
      intro cut observed same
      cases same
      exact outgoingResponseSessionPrefix_event pid initial _ afterPrefix True.intro prefixRun cut rfl

end Leanux.Proofs.WG.TimerDiscipline
