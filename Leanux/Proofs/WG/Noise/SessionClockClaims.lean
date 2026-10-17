import Leanux.Proofs.WG.Noise.SessionClockSource
import Leanux.Proofs.WG.TimerDiscipline.ObservationProductSource

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

theorem beginSession_clock_observation (pid : PeerId) (entry : Campaign2.Product.Snapshot) :
    Campaign2.Product.Ensures
      (TimerDiscipline.observed (liftWG (beginSession pid)) (sessionClockPath pid))
      (fun s => s = entry)
      (fun result final => SessionClockObservation pid entry result.1 result.2 final) := by
  apply TimerDiscipline.observed_effect
  intro initial ok final pre run
  subst entry
  have resident : ∃ d p, initial.wg.dev = some d ∧ d.peers[pid]? = some p := by
    cases device : initial.wg.dev with
    | none =>
      have stop : ((getPeer pid).run initial.wg).run initial.ambient =
          .error (.invariant "no WireGuard device in this trace's fixture") := by
        simp [getPeer, getDev, device]
        rfl
      change ((((getPeer pid).run initial.wg).run initial.ambient >>= _) >>= _) = _ at run
      rw [stop] at run
      cases run
    | some d =>
      cases peer : d.peers[pid]? with
      | none =>
        have stop : ((getPeer pid).run initial.wg).run initial.ambient =
            .error (.invariant s!"dangling peer {pid}") := by
          simp [getPeer, getDev, device, peer]
          rfl
        change ((((getPeer pid).run initial.wg).run initial.ambient >>= _) >>= _) = _ at run
        rw [stop] at run
        cases run
      | some p => exact ⟨d, p, rfl, peer⟩
  obtain ⟨d, p, device, peer⟩ := resident
  change (((beginSession pid).run initial.wg).run initial.ambient >>= fun ((value, current), inputs) =>
    .ok (value, {initial with wg := current, ambient := inputs})) = _ at run
  cases native : ((beginSession pid).run initial.wg).run initial.ambient with
  | error stop => rw [native] at run; cases run
  | ok pair =>
    obtain ⟨⟨value, current⟩, inputs⟩ := pair
    rw [native] at run
    cases run
    have source := beginSession_clock_run pid d p initial.wg.keypairCounter peer
      initial.wg current initial.ambient inputs ok device rfl native
    refine ⟨d, p, device, peer, ?_⟩
    cases ok with
    | false =>
      obtain ⟨prefixRun, finalDevice, finalCount⟩ := source
      have path : (sessionClockPath pid).run initial =
          .ok (none, {initial with wg := current, ambient := inputs}) := by
        change ((((sessionClockPrefix pid).run initial.wg).run initial.ambient >>= _) >>= _) = _
        rw [prefixRun]
        rfl
      exact ⟨TimerDiscipline.observe_ok path, finalDevice.trans device.symm, finalCount⟩
    | true =>
      obtain ⟨before, beforeAmbient, birth, afterClock, clockAmbient, out,
        prefixRun, clockRun, beforeDevice, same, finalDevice, effect⟩ := source
      subst afterClock
      let beforeWorld := {initial with wg := before, ambient := beforeAmbient}
      let afterWorld := {initial with wg := before, ambient := clockAmbient}
      let seen : SessionClockReceipt := {
        input := ⟨d.nextKeypairId, p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE, p.chainingKey⟩
        before := Campaign2.Product.snapshot beforeWorld
        birth := birth
        after := Campaign2.Product.snapshot afterWorld}
      have liftedClock : (liftWG (hiddenClock64 .deriveKeysBirthdate : WG.M Int64)).run beforeWorld =
          .ok (birth, afterWorld) := by
        change (((hiddenClock64 .deriveKeysBirthdate : WG.M Int64).run before).run beforeAmbient >>= _) = _
        rw [clockRun]
        rfl
      have path : (sessionClockPath pid).run initial = .ok (some seen, afterWorld) := by
        change ((((sessionClockPrefix pid).run initial.wg).run initial.ambient >>= _) >>= _) = _
        rw [prefixRun]
        change ((liftWG (hiddenClock64 .deriveKeysBirthdate : WG.M Int64)).run beforeWorld >>=
          fun result => .ok (some (SessionClockReceipt.mk
            ⟨d.nextKeypairId, p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE, p.chainingKey⟩
            (Campaign2.Product.snapshot beforeWorld) result.1
            (Campaign2.Product.snapshot result.2)), result.2)) = _
        rw [liftedClock]
        rfl
      exact ⟨seen, out, TimerDiscipline.observe_ok path, rfl, beforeDevice, rfl, finalDevice, effect⟩
end Leanux.Proofs.WG.Noise
