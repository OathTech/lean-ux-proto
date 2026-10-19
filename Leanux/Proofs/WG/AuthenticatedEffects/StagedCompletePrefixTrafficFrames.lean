import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixDeferred
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteTrafficFrames

/-! Traffic and fixture wrappers retain the native carrier and every logical
prefix. Fixture scope markers are quiet; their body supplies admission. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal Driver

theorem multicast (family addr : Nat) : Checked (multicastObserved family addr) :=
  native _ (CompleteProduct.multicast family addr)

theorem drain (what : String) (flags : List Bool) : Checked (drainObserved what flags) :=
  native _ (CompleteProduct.drain what flags)

theorem fixture_marker (event : CausalScope.Event Cause)
    (before : WithState (CompleteAllocated.Carrier [] []) CompleteProduct.Safe h w a) :
    WithState (CompleteAllocated.Carrier [] []) CompleteProduct.Safe (h++[.scope event]) w a := by
  have after := CompleteAllocatedFixture.marker event before.1
  have safe : CompleteProduct.Safe (h++[.scope event]) := by
    obtain ⟨ledger,accounted⟩ := after.1
    exact ⟨[],.accounted ledger [] _ w accounted⟩
  exact ⟨after,before.2.append (Cuts.singleton before.2.last safe)⟩

theorem fixture (trigger : FixtureEffects.Trigger) (body : WGPrefix Event α) (checked : StateChecked body) :
    StateChecked (FixtureEffects.runWith (fixtureOps hooks) trigger body) := by
  unfold FixtureEffects.runWith
  apply StatePrefixEnsures.bind
    (CausalScope.enterState_preserves Event.scope _ (fun _ _ _ before=>before.2)
      (fun event _ _ _ before=>fixture_marker event before))
  intro position
  apply StatePrefixEnsures.bind checked
  intro value
  apply StatePrefixEnsures.bind
    (CausalScope.leaveState_preserves Event.scope position (fun _ _ _ before=>before.2)
      (fun event _ _ _ before=>fixture_marker event before))
  intro ignored
  exact StateEnsures.pure value (fun _ _ _ before=>before)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product
