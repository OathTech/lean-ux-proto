import Leanux.Proofs.WG.TimerDiscipline.OutgoingResponseSessionSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2 Noise Roaming Std.Do

theorem outgoingResponseSessionPrefix_facts (pid : PeerId) :
    Noise.Product.Ensures (outgoingResponseSessionPrefix pid) (fun _ => True)
      (fun candidate final => ∀ cut, candidate = some cut →
        ResponseSessionFacts pid cut.session ∧
        responseSessionEnd cut.session = Campaign2.Product.snapshot final) := by
  have keep {α : Type} (action : Leanux.M α) :
      Noise.Product.Ensures action (fun _ => True) (fun _ _ => True) := by
    intro initial result final pre run
    trivial
  unfold outgoingResponseSessionPrefix
  refine Noise.Product.ensures_bind _ _ (keep _) ?_
  intro now
  refine Noise.Product.ensures_bind _ _ (keep _) ?_
  intro peer
  refine Noise.Product.ensures_bind _ _ (keep _) ?_
  intro ignored
  refine Noise.Product.ensures_bind _ _ (keep _) ?_
  intro created
  refine Noise.Product.ensures_bind _ _ (keep _) ?_
  intro accepted
  cases accepted with
  | false =>
    intro initial out final pre run cut impossible
    cases run
    cases impossible
  | true =>
    cases created with
    | none => intro initial out final pre run; cases run
    | some msg =>
      refine Noise.Product.ensures_bind _ _ (keep _) ?_
      intro message
      refine Noise.Product.ensures_bind _ _ (outgoingSessionPrefix_facts pid) ?_
      intro session initial out final facts run cut same
      cases run
      cases same
      exact facts

theorem observedOutgoingResponseSession_facts (pid : PeerId) :
    Campaign2.Product.Ensures (observedOutgoingResponseSession pid) (fun _ => True)
      (fun observation _ => OutgoingResponseSessionObservation pid observation) := by
  intro entry observation final pre run
  change ((liftWG (sendHandshakeResponse pid)).run entry >>= fun out =>
    Except.ok (Campaign2.Product.observeResult ((outgoingResponseSessionPrefix pid).run entry), out.2)) =
      .ok (observation, final) at run
  cases full : (liftWG (sendHandshakeResponse pid)).run entry with
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
      refine ⟨candidate, Campaign2.Product.snapshot afterPrefix, rfl, ?_⟩
      exact outgoingResponseSessionPrefix_facts pid entry candidate afterPrefix trivial hp



end Leanux.Proofs.WG.TimerDiscipline
