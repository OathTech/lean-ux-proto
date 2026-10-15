import Leanux.Proofs.WG.Roaming.InitiationCallSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem initiationPacketPrefix_facts (msg : List UInt8) (src : SkbSource) (underLoad : Bool) :
    Ensures (initiationPacketPrefix msg src underLoad) (fun _ => True)
      (fun result w => ∀ cut, result = some cut →
        cut.beforeSetter = Campaign2.snapshot w ∧ InitiationCallFacts msg cut) := by
  rw [ensures_iff]
  have macEq (a b : MacState) : (a == b) = true ↔ a = b := by
    cases a <;> cases b <;> constructor <;> intro h <;> first | rfl | cases h
  have hv : ⦃fun _ => ⌜True⌝⦄ cookieValidatePacket msg src underLoad
      ⦃⇓? _ _ => ⌜True⌝⦄ := by
    apply (ensures_iff _ _ _).mp
    intro w x final pre run
    trivial
  have hc : ⦃fun _ => ⌜True⌝⦄ sendHandshakeCookie msg src ⦃⇓? _ _ => ⌜True⌝⦄ := by
    apply (ensures_iff _ _ _).mp
    intro w x final pre run
    trivial
  have hr := (ensures_iff _ _ _).mp (initiationConsume_facts msg)
  mvcgen [initiationPacketPrefix, WG.andM, WG.orM, branch, invariant, Campaign2.read,
    hv, hc, hr]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [InitiationCallFacts, Campaign2.snapshot, Campaign2.core, macEq]
  all_goals grind

theorem initiationCallPrefix_facts (msg : List UInt8) (src : SkbSource) :
    Ensures (initiationCallPrefix msg src) (fun _ => True)
      (fun result w => ∀ cut, result = some cut →
        cut.beforeSetter = Campaign2.snapshot w ∧ InitiationCallFacts msg cut) := by
  rw [ensures_iff]
  have hl : ⦃fun _ => ⌜True⌝⦄ responseLoad ⦃⇓? _ _ => ⌜True⌝⦄ := by
    apply (ensures_iff _ _ _).mp
    intro w x final pre run
    trivial
  have hp := fun loaded => (ensures_iff _ _ _).mp (initiationPacketPrefix_facts msg src loaded)
  mvcgen [initiationCallPrefix, branch, hl, hp]

theorem observedInitiationHandshake_facts (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION) :
    Campaign2.Ensures (observedInitiationHandshake msg src) (fun _ => True)
      (fun observed _ => InitiationCallObservation msg observed) := by
  intro w observed final pre run
  change ((receiveHandshakePacket msg src).run w >>= fun out =>
    Except.ok (Campaign2.observeResult ((initiationCallPrefix msg src).run w), out.2)) =
      .ok (observed, final) at run
  cases full : (receiveHandshakePacket msg src).run w with
  | error err => rw [full] at run; cases run
  | ok pair =>
    rcases pair with ⟨ignored, finish⟩
    rw [full] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
    rw [← receiveHandshakePacket_initiation msg src kind] at full
    simp only [StateT.run_bind] at full
    cases prefixRun : (initiationCallPrefix msg src).run w with
    | error err => rw [prefixRun] at full; cases full
    | ok pair =>
      rcases pair with ⟨candidate, atCut⟩
      refine ⟨candidate, Campaign2.snapshot atCut, ?_, ?_⟩
      · rfl
      · exact initiationCallPrefix_facts msg src w candidate atCut trivial prefixRun

end Leanux.Proofs.WG.Roaming
