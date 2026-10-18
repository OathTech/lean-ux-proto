import Leanux.Proofs.WG.TransmitSecurity.Nonce
import Leanux.Proofs.WG.Keypairs.LifetimeMirror
import Leanux.Proofs.Logged.WGPrefix

/-! The original get/increment block at Send.lean's nonce assignment.
Observation occurs after the increment and before the rejection branch, so
neither refusal nor a later Stop can erase an allocated nonce. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.WG.CounterWindow

def reserveNative (slot : KeypairId) : WG.M Nat := do
  let k ← getKeypair slot
  setKeypair slot { k with sendingCounter := k.sendingCounter + 1 }
  return k.sendingCounter

def reserveObserved (slot : KeypairId) : WGPrefix Allocation Nat := do
  let k ← liftWGPrefix (getKeypair slot)
  liftWGPrefix (setKeypair slot { k with sendingCounter := k.sendingCounter + 1 })
  emitStatePrefix (allocation (cell k))
  return k.sendingCounter

theorem view_lookup (w : WGWorld) (d : Device) (slot : KeypairId) (k : Keypair)
    (hd : w.dev = some d) (hk : d.keypairs[slot]? = some k) :
    (view w).cells slot = some (cell k) := by simp [view, hd, hk]

theorem view_store (w : WGWorld) (d : Device) (slot : KeypairId) (k : Keypair)
    (hd : w.dev = some d) :
    view (store w slot k) = (view w).put slot (some (cell k)) := by
  apply View.ext
  · rfl
  · funext j
    simp [view, store, hd, View.put, Std.TreeMap.getElem?_insert]
    split <;> simp_all [eq_comm]

theorem reserveNative_run (w : WGWorld) (a : Ambient) (d : Device)
    (slot : KeypairId) (k : Keypair) (hd : w.dev = some d)
    (hk : d.keypairs[slot]? = some k) :
    ((reserveNative slot).run w).run a =
      .ok ((k.sendingCounter, store w slot {k with sendingCounter := k.sendingCounter + 1}), a) := by
  simp [reserveNative, StateT.run_bind, getKeypair_run w a d slot k hd hk]

theorem reserveObserved_erases (slot : KeypairId) :
    ErasesStatePrefix (reserveObserved slot) (reserveNative slot) := by
  unfold reserveObserved reserveNative
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro k
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro _
  intro w a h
  rfl

theorem reserveObserved_run (w : WGWorld) (a : Ambient) (d : Device)
    (slot : KeypairId) (k : Keypair) (hd : w.dev = some d)
    (hk : d.keypairs[slot]? = some k) (h : List Allocation) :
    runStatePrefix (reserveObserved slot) w a h =
      (.ok ((k.sendingCounter, store w slot {k with sendingCounter := k.sendingCounter + 1}), a),
        h ++ [allocation (cell k)]) := by
  simp only [reserveObserved, runStatePrefix_bind, liftWGPrefix, runStatePrefix_lift,
    getKeypair_run w a d slot k hd hk, setKeypair_run]
  rfl

/-- This native increment keeps the sending material and reserves exactly the
old counter. A subsequent rejection cannot make that allocation available again. -/
theorem reserveObserved_safe (slot : KeypairId) :
    StatePrefixEnsures (fun h w _ => Inv (view w) h) List.Nodup
      (reserveObserved slot) (fun _ h w _ => Inv (view w) h) := by
  intro w a h hi
  cases hd : w.dev with
  | none =>
    have hr : runStatePrefix (reserveObserved slot) w a h =
        (.error (.invariant "no WireGuard device in this trace's fixture"), h) := by
      simp only [reserveObserved, runStatePrefix_bind, liftWGPrefix, runStatePrefix_lift]
      have hg : ((getKeypair slot).run w).run a =
          .error (.invariant "no WireGuard device in this trace's fixture") := by
        simp [getKeypair, getDev, hd, invariant, AmbientM.invariant]
        rfl
      rw [hg]
    simp only [runStatePrefix] at hr
    refine ⟨[], ?_, ?_, ?_⟩
    · simp [hr]
    · simpa [hr] using hi.nodup
    · simp [hr]
  | some d =>
    cases hk : d.keypairs[slot]? with
    | none =>
      have hr : runStatePrefix (reserveObserved slot) w a h =
          (.error (.invariant ("dangling keypair " ++ Nat.repr slot)), h) := by
        simp only [reserveObserved, runStatePrefix_bind, liftWGPrefix, runStatePrefix_lift]
        have hg : ((getKeypair slot).run w).run a =
            .error (.invariant ("dangling keypair " ++ Nat.repr slot)) := by
          simp [getKeypair, getDev, hd, hk, invariant, AmbientM.invariant]
          rfl
        rw [hg]
      simp only [runStatePrefix] at hr
      refine ⟨[], by simp [hr], by simpa [hr] using hi.nodup, by simp [hr]⟩
    | some k =>
      have hr := reserveObserved_run w a d slot k hd hk h
      simp only [runStatePrefix] at hr
      have hv : view (store w slot {k with sendingCounter := k.sendingCounter + 1}) =
          reserve (view w) slot (cell k) := by
        rw [view_store w d slot _ hd]
        rfl
      have hs := hi.reserve_preserves (view_lookup w d slot k hd hk)
      refine ⟨[allocation (cell k)], by simp [hr], ?_, ?_⟩
      · simpa [hr] using hs.nodup
      · simpa [hr, hv] using hs

theorem initial_view (net bare : Bool) :
    view (Runner.initialWG net bare) = ⟨0, fun _ => none⟩ := by
  apply View.ext
  · simp [view, Runner.initialWG]
  · funext i
    simp [view, Runner.initialWG]

end Leanux.Proofs.WG.TransmitSecurity.Nonce
