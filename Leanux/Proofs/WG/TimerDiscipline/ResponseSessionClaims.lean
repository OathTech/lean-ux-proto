import Leanux.Proofs.WG.TimerDiscipline.ResponseSessionSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Noise Roaming Std.Do

theorem responseSessionCallPrefix_facts (msg : List UInt8) (src : SkbSource) :
    Noise.Ensures (responseSessionCallPrefix msg src) (fun _ => True)
      (fun candidate final => ∀ cut, candidate = some cut →
        ResponseCallFacts msg cut.response ∧
        ResponseSessionFacts cut.response.consumed.input.pid cut.session ∧
        responseSessionEnd cut.session = Campaign2.snapshot final) := by
  have hp := (ensures_iff _ _ _).mp (responseCallPrefix_facts msg src)
  have hs := fun pid => (ensures_iff _ _ _).mp (responseSessionPrefix_facts pid)
  have he (pid : PeerId) :
      ⦃fun _ => ⌜True⌝⦄ setPeerEndpointFromSkb pid src ⦃⇓? _ _ => ⌜True⌝⦄ := by
    apply (ensures_iff _ _ _).mp
    intro w result final pre run
    trivial
  rw [ensures_iff]
  mvcgen [responseSessionCallPrefix, hp, hs, he]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all
  all_goals subst_vars
  all_goals simp_all

theorem observedResponseSession_facts (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    Campaign2.Ensures (observedResponseSession msg src) (fun _ => True)
      (fun observation _ => ResponseSessionObservation msg observation) := by
  intro entry observation final pre run
  change ((receiveHandshakePacket msg src).run entry >>= fun out =>
    Except.ok (Campaign2.observeResult ((responseSessionCallPrefix msg src).run entry), out.2)) =
      .ok (observation, final) at run
  cases full : (receiveHandshakePacket msg src).run entry with
  | error err => rw [full] at run; cases run
  | ok pair =>
    rcases pair with ⟨returned, finish⟩
    rw [full] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
    rw [← responseSessionCall_source msg src kind] at full
    simp only [StateT.run_bind] at full
    cases hp : (responseSessionCallPrefix msg src).run entry with
    | error err => rw [hp] at full; cases full
    | ok pair =>
      rcases pair with ⟨candidate, afterPrefix⟩
      refine ⟨candidate, Campaign2.snapshot afterPrefix, rfl, ?_⟩
      exact responseSessionCallPrefix_facts msg src entry candidate afterPrefix trivial hp

end Leanux.Proofs.WG.TimerDiscipline
