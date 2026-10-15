import Leanux.Proofs.WG.TimerDiscipline.OutgoingResponseSessionSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Noise Std.Do

theorem outgoingResponseSessionPrefix_facts (pid : PeerId) :
    Noise.Ensures (outgoingResponseSessionPrefix pid) (fun _ => True)
      (fun candidate final => ∀ cut, candidate = some cut →
        ResponseSessionFacts pid cut.session ∧
        responseSessionEnd cut.session = Campaign2.snapshot final) := by
  have trivial_call {α : Type} (operation : M α) :
      ⦃fun _ => ⌜True⌝⦄ operation ⦃⇓? _ _ => ⌜True⌝⦄ := by
    apply (ensures_iff _ _ _).mp
    intro entry result final pre run
    trivial
  have hh := trivial_call (hiddenClock64 .respLastSent)
  have hg := trivial_call (getPeer pid)
  have hw := fun peer => trivial_call (setPeer pid peer)
  have hc := trivial_call (createResponse pid)
  have hm := fun msg => trivial_call (addMacToPacket pid msg)
  have hs := (ensures_iff _ _ _).mp (outgoingSessionPrefix_facts pid)
  rw [ensures_iff]
  mvcgen [outgoingResponseSessionPrefix, branch, invariant, hh, hg, hw, hc, hm, hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all
  all_goals subst_vars
  all_goals simp_all

theorem observedOutgoingResponseSession_facts (pid : PeerId) :
    Campaign2.Ensures (observedOutgoingResponseSession pid) (fun _ => True)
      (fun observation _ => OutgoingResponseSessionObservation pid observation) := by
  intro entry observation final pre run
  change ((sendHandshakeResponse pid).run entry >>= fun out =>
    Except.ok (Campaign2.observeResult ((outgoingResponseSessionPrefix pid).run entry), out.2)) =
      .ok (observation, final) at run
  cases full : (sendHandshakeResponse pid).run entry with
  | error err => rw [full] at run; cases run
  | ok pair =>
    rcases pair with ⟨returned, finish⟩
    rw [full] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
    rw [← outgoingResponseSession_source pid] at full
    simp only [StateT.run_bind] at full
    cases hp : (outgoingResponseSessionPrefix pid).run entry with
    | error err => rw [hp] at full; cases full
    | ok pair =>
      rcases pair with ⟨candidate, afterPrefix⟩
      refine ⟨candidate, Campaign2.snapshot afterPrefix, rfl, ?_⟩
      exact outgoingResponseSessionPrefix_facts pid entry candidate afterPrefix trivial hp

end Leanux.Proofs.WG.TimerDiscipline
