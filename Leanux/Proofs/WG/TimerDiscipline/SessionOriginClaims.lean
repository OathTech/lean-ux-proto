import Leanux.Proofs.WG.TimerDiscipline.SessionOriginSource
import Leanux.Proofs.WG.TimerDiscipline.SessionArmEventClaims

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Noise Std.Do

/-- A reached session event in the actual full outgoing call is labelled from
that call's entry serial. This states no final-call counter delta, and no
cross-call uniqueness. The original observer retains all stopped executions. -/
theorem observedOutgoingResponseSession_counter_origin (pid : PeerId)
    (entry : Campaign2.Product.Snapshot) :
    Campaign2.Product.Ensures (observedOutgoingResponseSession pid)
      (fun initial => initial = entry)
      (fun observation _ => OutgoingResponseSessionObservation pid observation ∧
        ∀ cut afterPrefix, observation = .ok (some cut,afterPrefix) →
          SessionArmEvent pid cut.session ∧
          cut.session.beforeSession.wg.keypairCounter = entry.wg.keypairCounter) := by
  intro initial observation final pre run
  obtain ⟨base,events⟩ := observedOutgoingResponseSession_arm_event pid initial observation final True.intro run
  refine ⟨base,?_⟩
  intro cut afterPrefix same
  refine ⟨events cut afterPrefix same,?_⟩
  rw [observedOutgoingResponseSession_source pid] at run
  change ((outgoingResponseSessionPrefix pid).run initial >>= _) = _ at run
  cases prefixRun : (outgoingResponseSessionPrefix pid).run initial with
  | error stop => rw [prefixRun] at run; cases run
  | ok pair =>
    obtain ⟨candidate,atCut⟩ := pair
    rw [prefixRun] at run
    change ((outgoingResponseSessionSuffix pid candidate).run atCut >>= _) = _ at run
    cases suffixRun : (outgoingResponseSessionSuffix pid candidate).run atCut with
    | error stop => rw [suffixRun] at run; cases run
    | ok out =>
      rw [suffixRun] at run
      cases run
      cases same
      exact outgoingResponseSessionPrefix_counter_origin pid entry.wg.keypairCounter
        initial _ atCut (congrArg (fun s : Campaign2.Product.Snapshot => s.wg.keypairCounter) pre)
        prefixRun cut rfl

end Leanux.Proofs.WG.TimerDiscipline
