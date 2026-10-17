import Leanux.Proofs.WG.TimerDiscipline.ResponseSessionSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2 Noise Roaming Std.Do

theorem responseSessionCallPrefix_facts (msg : List UInt8) (src : SkbSource) :
    Noise.Product.Ensures (responseSessionCallPrefix msg src) (fun _ => True)
      (fun candidate final => ∀ cut, candidate = some cut →
        Roaming.Product.ResponseCallFacts msg cut.response ∧
        ResponseSessionFacts cut.response.consumed.input.pid cut.session ∧
        responseSessionEnd cut.session = Campaign2.Product.snapshot final) := by
  unfold responseSessionCallPrefix
  refine Noise.Product.ensures_bind
    (Q := fun candidate _ => ∀ cut, candidate = some cut → Roaming.Product.ResponseCallFacts msg cut)
    _ _ (fun initial candidate final pre run cut same =>
      (Roaming.Product.responseCallPrefix_facts msg src initial candidate final pre run cut same).2) ?_
  intro candidate
  cases candidate with
  | none =>
    intro initial out final h run cut impossible
    cases run
    cases impossible
  | some cut =>
    refine Noise.Product.ensures_bind (Q := fun _ _ => Roaming.Product.ResponseCallFacts msg cut) _ _
      (fun _ _ _ h _ => h cut rfl) ?_
    intro ignored
    refine Noise.Product.ensures_bind
      (Q := fun session final => Roaming.Product.ResponseCallFacts msg cut ∧
        ResponseSessionFacts cut.consumed.input.pid session ∧
        responseSessionEnd session = Campaign2.Product.snapshot final)
      _ _ (fun initial session final h run =>
        ⟨h, responseSessionPrefix_facts cut.consumed.input.pid initial session final trivial run⟩) ?_
    intro session initial out final facts run other same
    cases run
    cases same
    exact facts

theorem observedResponseSession_facts (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    Campaign2.Product.Ensures (observedResponseSession msg src) (fun _ => True)
      (fun observation _ => ResponseSessionObservation msg observation) := by
  intro entry observation final pre run
  change ((liftWG (receiveHandshakePacket msg src)).run entry >>= fun out =>
    Except.ok (Campaign2.Product.observeResult ((responseSessionCallPrefix msg src).run entry), out.2)) =
      .ok (observation, final) at run
  cases full : (liftWG (receiveHandshakePacket msg src)).run entry with
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
      refine ⟨candidate, Campaign2.Product.snapshot afterPrefix, rfl, ?_⟩
      exact responseSessionCallPrefix_facts msg src entry candidate afterPrefix trivial hp



end Leanux.Proofs.WG.TimerDiscipline
