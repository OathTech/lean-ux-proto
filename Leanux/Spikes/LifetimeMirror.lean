import Leanux.Spikes.Lifetimes
import Leanux.Spikes.FramingWP
import Leanux.Runner

/-! The projection is tied to actual mirror worlds and validator executions. -/
namespace Leanux.Spikes.Lifetimes
open Leanux Leanux.WG Leanux.Spikes.Window Leanux.Spikes.Ghost

@[simp] theorem snapshot_record (w : World) (d : Decision) (b : Bool) :
    snapshot (record w d b) = snapshot w := rfl

@[simp] theorem snapshot_clearRecords (w : World) (xs : List Nat) :
    snapshot (clearRecords w xs) = snapshot w := by
  simp [snapshot, clearRecords_k]

theorem snapshot_lookup (w : World) (d : Device) (i : Nat) (k : Keypair)
    (hd : w.k.wg = some d) (hk : d.keypairs[i]? = some k) :
    (snapshot w).slots i = some (cell k) := by simp [snapshot, hd, hk]

theorem snapshot_store (w : World) (d : Device) (i : Nat) (k : Keypair)
    (hd : w.k.wg = some d) :
    snapshot (store w i k) = (snapshot w).put i (some (cell k)) := by
  apply Snapshot.ext
  · rfl
  · funext j
    simp [snapshot, store, hd, Snapshot.put, Std.TreeMap.getElem?_insert]
    split <;> simp_all [eq_comm]

@[simp] theorem put_existing (s : Snapshot) (i : Nat) (c : Cell)
    (hc : s.slots i = some c) : s.put i (some c) = s := by
  apply Snapshot.ext
  · rfl
  · funext j
    by_cases hj : j = i
    · subst j; simp [hc]
    · simp [hj]

/-- The full receive-state projection, including identities and other slots. -/
theorem cExecution_snapshot (w : World) (d : Device) (i : Nat) (k : Keypair)
    (nonce : Nat) (hd : w.k.wg = some d) (hk : d.keypairs[i]? = some k) :
    snapshot (cExecution i nonce k w).2 = validate (snapshot w) i (cell k) nonce := by
  have hc := snapshot_lookup w d i k hd hk
  by_cases he : eligible k.receivingCounter nonce
  · have h1 : ¬ k.receivingCounter.counter ≥ REJECT_AFTER_MESSAGES + 1 := by have := he.1; omega
    have h2 : ¬ nonce ≥ REJECT_AFTER_MESSAGES := by have := he.2.1; omega
    have h3 : ¬8128 + (nonce + 1) < k.receivingCounter.counter := by have := he.2.2; omega
    change snapshot (cExecution i nonce k w).2 = (snapshot w).put i (some ⟨k.internalId, (step k.receivingCounter nonce).2⟩)
    rw [step, if_pos he]
    by_cases h4 : nonce + 1 > k.receivingCounter.counter
    · simp [cExecution, h1, h2, h3, h4, cell, update, prepared,
        Nat.max_eq_right (by omega : k.receivingCounter.counter ≤ nonce + 1),
        snapshot_store, record_k, clearRecords_k, hd]
    · simp [cExecution, h1, h2, h3, h4, cell, update, prepared,
        Nat.max_eq_left (by omega : nonce + 1 ≤ k.receivingCounter.counter),
        snapshot_store, record_k, hd]
  · have hv : validate (snapshot w) i (cell k) nonce = snapshot w := by
      simpa [validate, cell, step, he] using put_existing (snapshot w) i (cell k) hc
    rw [hv]
    by_cases h1 : k.receivingCounter.counter ≥ REJECT_AFTER_MESSAGES + 1
    · simp [cExecution, h1]
    · by_cases h2 : nonce ≥ REJECT_AFTER_MESSAGES
      · simp [cExecution, h1, h2]
      · have h3 : 8128 + (nonce + 1) < k.receivingCounter.counter := by unfold eligible at he; omega
        simp [cExecution, h1, h2, h3]

/-- The initial runner fixture has no allocated keypair lifetime. -/
theorem initial_snapshot (rlimit : Nat) (net bare foreign stepped : Bool) (w : World)
    (hk : w.k = Runner.initialKernel rlimit net bare foreign stepped) :
    snapshot w = ⟨0, fun _ => none⟩ := by
  apply Snapshot.ext
  · simp [snapshot, hk, Runner.initialKernel]
  · funext i
    simp [snapshot, hk, Runner.initialKernel]

/-- Successful original validator calls realize one evolution step and one
exact history append, including false returns that still update the bitmap. -/
theorem counterLogged_evolves (i nonce : Nat) (w w' : World)
    (history history' : History) (ok : Bool)
    (hi : Inv (snapshot w) history)
    (hr : ((counterLogged i nonce).run history).run w = .ok ((ok, history'), w')) :
    Evolution (snapshot w) history (snapshot w') history' := by
  have hv : (counterValidate i nonce).run w = .ok (ok, w') := by
    rw [← counterLogged_erases i nonce history w, hr]
    rfl
  cases hd : w.k.wg with
  | none => simp [counterValidate, getKeypair, getDev, getK, hd, invariant] at hv
  | some d =>
    cases hk : d.keypairs[i]? with
    | none => simp [counterValidate, getKeypair, getDev, getK, hd, hk, invariant] at hv
    | some k =>
      have hc := snapshot_lookup w d i k hd hk
      have hs := hi.shaped i (cell k) hc
      have hex := counterValidate_execution w d i k nonce hd hk hs
      have hp := cExecution_refines_step w d i k nonce hd hk
      rw [hv] at hex
      have hw := congrArg Prod.snd (Except.ok.inj hex)
      have ho := congrArg Prod.fst (Except.ok.inj hex)
      have hh := counterLogged_run i nonce history w w' d k ok hd hk hv
      rw [hr] at hh
      have hh' := congrArg (fun x => x.1.2) (Except.ok.inj hh)
      dsimp only at hh' hw ho
      rw [hh', hw, cExecution_snapshot w d i k nonce hd hk]
      have hok : ok = (step k.receivingCounter nonce).1 := ho.trans hp.1
      rw [hok]
      exact Evolution.validate hc nonce

theorem counterLogged_preserves (i nonce : Nat) (w w' : World)
    (history history' : History) (ok : Bool)
    (hi : Inv (snapshot w) history)
    (hr : ((counterLogged i nonce).run history).run w = .ok ((ok, history'), w')) :
    Inv (snapshot w') history' := (counterLogged_evolves i nonce w w' history history' ok hi hr).preserves hi

end Leanux.Spikes.Lifetimes
