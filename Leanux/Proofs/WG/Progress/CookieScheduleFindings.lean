import Leanux.Proofs.WG.Progress.CookieScheduleOutcomeSource
import Leanux.Proofs.WG.Progress.CookieActivationBoundFindings

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress.CookieFull
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.WG.Progress

/-- The old full-drain domain permits this malformed tail. The actual scheduler
propagates the receive activation's occupancy-exhaustion invariant while probing;
no reachable-state or kernel-behavior assertion is made. -/
theorem schedule_cookieBadTail_counterexample (base : World) :
    ∃ (a : Activation) (w : World) (d : Device) (stop : List UInt8),
      a.worker = .receiveWorker ∧ w.wg.dev = some d ∧ d.indexTable = [] ∧ CookieOnly d ∧
      stop.length = 8 ∧ w.ambient.hidden = some (records [] stop) ∧ w.ambient.suspended = [a] ∧
      ([] : List (List UInt8)).length ≤ d.handshakeQueue.count ∧
      (schedule none).run w = .error (.invariant
        "wg_packet_handshake_receive_worker consumed more items than its queue held (1) in one run") := by
  let src : SkbSource := {family := 0, saddr := 0, sport := 0, daddr := 0, iif := 0}
  let msg : List UInt8 := [3, 0, 0, 0]
  let d : Device := {
    ifindex := 0
    ifname := "wg0"
    handshakeQueue := cookieBadTailRing msg src
    handshakeQueueLen := 1 }
  let a : Activation := {worker := .receiveWorker}
  let stop : List UInt8 := List.replicate 8 0
  let w := {base with
    wg := {base.wg with dev := some d}
    ambient := {base.ambient with hidden := some (records [] stop), suspended := [a]}}
  have cookies : CookieOnly d := by
    intro bytes source member
    have items : d.handshakeQueue.items = [(msg, src)] := by
      simp [d, cookieBadTailRing, PtrRing.items, PtrRing.count, PtrRing.peek]
    rw [items] at member
    simp only [List.mem_singleton, Prod.mk.injEq] at member
    obtain ⟨rfl, rfl⟩ := member
    rfl
  refine ⟨a, w, d, stop, rfl, rfl, rfl, cookies, by simp [stop], rfl, rfl, by simp, ?_⟩
  have activation := cookieBadTail_activation_run a w d msg src rfl rfl rfl rfl rfl
    (by rfl)
  have bounded : cookieHybridRun a d.handshakeQueue.count w = .error (.invariant
      "wg_packet_handshake_receive_worker consumed more items than its queue held (1) in one run") := by
    rw [← cookieActivation_run a w d (records [] stop) rfl rfl rfl cookies rfl]
    exact activation
  have peek : (peekHiddenSite : Leanux.M (Option Nat)).run w =
      .ok (some (HiddenSite.sectionStop .receiveWorker).info.id, w) := by
    have read := cookiePeek_run w (records [] stop) rfl
    rw [records_drop] at read
    simpa [records, control, cookieControlSite, w] using read
  rw [schedule_run [] a w d stop rfl rfl rfl cookies rfl rfl (by simp) (by simp [stop]) (by simp)]
  simp only [boundedSchedule, cookieBoundedScheduler, StateT.run_bind, peek]
  dsimp only [bind, Except.bind, StateT.run]
  rw [bounded]
  rfl

end Leanux.Proofs.WG.Progress.CookieFull
