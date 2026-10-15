import Leanux.Proofs.WG.TimerDiscipline.RxDataTimersSource
import Leanux.Proofs.WG.TimerDiscipline.DataDoneClaims

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Noise Campaign2 Std.Do

theorem rxDataReceipt_facts (pid : PeerId) :
    Noise.Ensures (dataDoneCapture (timersDataReceived pid)
      (prefixClockPath (dataReceivedPrefix pid) .timerJiffiesDataReceived))
      (fun _ => True) (fun cut _ => RxDataReceiptFacts pid cut) := by
  intro entry cut final pre run
  constructor
  · intro d p device resident
    have contract : Campaign2.Ensures (observed (timersDataReceived pid)
        (prefixClockPath (dataReceivedPrefix pid) .timerJiffiesDataReceived))
        (fun s => s.wg.device = some d)
        (fun _ after => RxDataReceiptEffect pid d p after) := by
      apply observed_effect
      intro initial result finish initialDevice original
      exact source_data_received pid d p resident initial result finish initialDevice original
    have effect := dataDoneCapture_facts _ _ _ _ contract entry cut final trivial run
    exact effect.2 device
  · intro d p device resident absent running alive records
    have effect := dataDoneCapture_facts _ _ _ _
      (projected_data_received_recorded pid d p resident absent running alive)
      entry cut final trivial run
    exact effect.2 ⟨device, records⟩

theorem rxDataTimersObservedPrefix_facts (pid : PeerId) (pkt : RxPacket) (e : Endpoint) :
    Noise.Ensures (rxDataTimersObservedPrefix pid pkt e) (fun _ => True)
      (fun cut _ => RxDataTimersFacts pid pkt cut) := by
  have trivial_call {α : Type} (a : M α) :
      ⦃fun _ => ⌜True⌝⦄ a ⦃⇓? _ _ => ⌜True⌝⦄ := by
    apply (ensures_iff _ _ _).mp
    intro entry result final pre run
    trivial
  have hp := trivial_call (rxDataTimersPrelude pid pkt e)
  have ht := (ensures_iff _ _ _).mp (dataDoneTraversal_facts pid)
  have hr := (ensures_iff _ _ _).mp (rxDataReceipt_facts pid)
  have hs := trivial_call (updateRxStats pid MESSAGE_DATA_LEN_0)
  rw [ensures_iff]
  mvcgen [rxDataTimersObservedPrefix, branch, hp, ht, hr, hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [RxDataTimersFacts]

theorem observedRxDataTimers_facts (pid : PeerId) (pkt : RxPacket) (e : Endpoint) :
    Campaign2.Ensures (observedRxDataTimers pid pkt e) (fun _ => True)
      (fun result _ => RxDataTimersFacts pid pkt result.1) := by
  have trivial_call {α : Type} (a : M α) :
      ⦃fun _ => ⌜True⌝⦄ a ⦃⇓? _ _ => ⌜True⌝⦄ := by
    apply (ensures_iff _ _ _).mp
    intro entry result final pre run
    trivial
  have hp := (ensures_iff _ _ _).mp (rxDataTimersObservedPrefix_facts pid pkt e)
  have hs := fun keepalive => trivial_call (rxDataTimersSuffix pid pkt keepalive)
  change Noise.Ensures _ _ _
  rw [ensures_iff]
  mvcgen [observedRxDataTimers, hp, hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

end Leanux.Proofs.WG.TimerDiscipline
