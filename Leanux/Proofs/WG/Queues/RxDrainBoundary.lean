import Leanux.Proofs.WG.Queues.RxIngressStable
import Leanux.Proofs.Framing.EnvLeaves

/-! The actual environment completion guards imply the physical emptiness
and cold NAPI facts used by carrier conservation. These are successful-return
contracts; no endpoint is assigned to an indexed Stop. -/
namespace Leanux.Proofs.WG.Queues.RxCredits
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

private theorem readWG (s : World) : (getWG : Leanux.M WGWorld).run s = .ok (s.wg, s) := rfl
private theorem readDev (s : World) : (monadLift getDev : Leanux.M Device).run s =
      match s.wg.dev with
      | none => .error (.invariant "no WireGuard device in this trace's fixture")
      | some d => .ok (d, s) := by
  change (liftWG getDev).run s = _
  rw [liftWG_run]
  cases hd : s.wg.dev <;> simp [getDev, hd, invariant, AmbientM.invariant] <;> rfl

/-- An ordinary return of the exact idle-device guard retains the native
world and reads an empty decrypt ring with no scheduled peer poll. -/
theorem idleDevice_normal (w v : World)
    (run : Env.requireIdleDevice.run w = .ok ((), v)) :
    v = w ∧ ∃ d, w.wg.dev = some d ∧ d.decryptQueue.empty = true ∧
      d.peers.toList.any (·.2.napiScheduled) = false := by
  simp only [Env.requireIdleDevice, Env.requireNoCryptWork, readWG, readDev,
    StateT.run_bind] at run
  cases hd : w.wg.dev with
  | none => simp [hd] at run
  | some d =>
    simp only [CounterWindow.except_ok_bind, hd] at run
    split at run
    · cases run
    · simp only [StateT.run_pure, CounterWindow.except_pure, CounterWindow.except_ok_bind, hd] at run
      split at run
      · cases run
      · rename_i noCrypt noRx
        have same : v = w := (congrArg Prod.snd (Except.ok.inj run)).symm
        refine ⟨same,d,rfl,?_,?_⟩ <;> simp_all
        exact noRx.2

/-- The original completion guard returns only if every supplied work flag
and every peer's NAPI flag is false; it leaves the entire product unchanged. -/
theorem requireDrained_normal (what : String) (queues : List Bool) (w v : World)
    (run : (Env.requireDrained what queues).run w = .ok ((), v)) :
    v = w ∧ queues.any id = false ∧ ∃ d, w.wg.dev = some d ∧
      d.peers.toList.any (·.2.napiScheduled) = false := by
  unfold Env.requireDrained at run
  split at run
  · cases run
  · rename_i quiet
    simp only [StateT.run_bind, readDev] at run
    cases hd : w.wg.dev with
    | none => simp [hd] at run
    | some d =>
      simp only [hd, CounterWindow.except_ok_bind] at run
      split at run
      · cases run
      · rename_i cold
        have same : v = w := (congrArg Prod.snd (Except.ok.inj run)).symm
        exact ⟨same, Bool.eq_false_iff.mpr quiet, d, rfl, Bool.eq_false_iff.mpr cold⟩

/-- The actual idle-device return discharges the stable-drain tests. It
cannot silently abandon a funded, queued receive carrier. -/
theorem idleDevice_empty (w v : World) (cs : Ledger) (loans : Reservations)
    (hi : CarrierState cs loans w.wg) (hs : StableRx cs w.wg)
    (physical : NativeRxInv epoch (PtrRing.init n) h w.wg)
    (run : Env.requireIdleDevice.run w = .ok ((), v)) :
    cs = [] ∧ ∀ (d : Device) (id : SkbId) (pkt : RxPacket),
      v.wg.dev = some d → d.rxSkbs[id]? ≠ some pkt := by
  obtain ⟨rfl, d, hd, empty, cold⟩ := idleDevice_normal w v run
  apply stable_drained hi hs physical
  · intro target ht
    cases hd.symm.trans ht
    exact empty
  · intro target pid p ht hp
    cases hd.symm.trans ht
    have peers : ∀ (pid : PeerId) (p : Peer), d.peers[pid]? = some p →
        p.napiScheduled = false := by simpa using cold
    exact peers pid p hp

/-- When the caller included its actual decrypt-ring work flag, a normal
completion guard discharges the same stable-carrier drain obligation. -/
theorem requireDrained_empty (what : String) (queues : List Bool)
    (w v : World) (cs : Ledger) (loans : Reservations)
    (hi : CarrierState cs loans w.wg) (hs : StableRx cs w.wg)
    (physical : NativeRxInv epoch (PtrRing.init n) h w.wg)
    (ringFlag : ∀ d, w.wg.dev = some d → (!d.decryptQueue.empty) ∈ queues)
    (run : (Env.requireDrained what queues).run w = .ok ((), v)) :
    cs = [] ∧ ∀ (d : Device) (id : SkbId) (pkt : RxPacket),
      v.wg.dev = some d → d.rxSkbs[id]? ≠ some pkt := by
  obtain ⟨rfl, quiet, d, hd, cold⟩ := requireDrained_normal what queues w v run
  apply stable_drained hi hs physical
  · intro target ht
    have flags : ∀ b ∈ queues, b = false := by simpa using quiet
    simpa using flags (!target.decryptQueue.empty) (ringFlag target ht)
  · intro target pid p ht hp
    cases hd.symm.trans ht
    have peers : ∀ (pid : PeerId) (p : Peer), d.peers[pid]? = some p →
        p.napiScheduled = false := by simpa using cold
    exact peers pid p hp

end Leanux.Proofs.WG.Queues.RxCredits
