import Leanux.Proofs.WG.HandshakeSecurity.Observation

namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG Leanux.Proofs.Logged

private theorem native_branch (decision : Decision) (value : Bool) (w : WGWorld) (a : Ambient) :
    ((branch decision value : WG.M Bool).run w).run a =
      .ok ((value, w), CounterWindow.record a decision value) := rfl

theorem timestamp_run (pid : PeerId) (old t : List UInt8) (w : WGWorld)
    (a : Ambient) (h : List TimestampReceipt) :
    runWGPrefix (timestampObserved pid old t) w a h =
      if memcmp t old == .gt then
        match ((writeTimestamp pid t).run w).run
            (CounterWindow.record a .consumeNewerTimestamp true) with
        | .error e => (.error e, h)
        | .ok ((x, v), b) => (.ok ((x, v), b),
            h ++ [⟨pid, old, t, ⟨x, w, v,
              CounterWindow.record a .consumeNewerTimestamp true, b⟩⟩])
      else (.ok (((), w), CounterWindow.record a .consumeNewerTimestamp false), h) := by
  change runStatePrefix (timestampObserved pid old t) w a h = _
  unfold timestampObserved
  rw [runStatePrefix_bind, liftWGPrefix, runStatePrefix_lift, native_branch]
  by_cases hc : (memcmp t old == .gt) = true
  · simp only [hc, ite_true]
    have he := runWGPrefix_receiptWGObserved (liftWGPrefix (writeTimestamp pid t))
      (fun r => ⟨pid, old, t, r⟩) w (CounterWindow.record a .consumeNewerTimestamp true) h
    rw [runWGPrefix_lift] at he
    cases hr : ((writeTimestamp pid t).run w).run (CounterWindow.record a .consumeNewerTimestamp true) with
    | error e => simpa only [hr, runWGPrefix] using he
    | ok out =>
      rcases out with ⟨⟨x, v⟩, b⟩
      simpa only [hr, runWGPrefix] using he
  · have hf : (memcmp t old == .gt) = false := Bool.eq_false_iff.mpr hc
    simp only [hf, Bool.false_eq_true, ite_false]
    rfl

def SoundReceipts (h : List TimestampReceipt) : Prop :=
  ∀ r ∈ h, r.Valid ∧ r.Newer

theorem timestamp_sound (pid : PeerId) (old t : List UInt8) :
    StatePrefixPreserves (fun h _ _ => SoundReceipts h) SoundReceipts
      (timestampObserved pid old t) := by
  intro w a h hi
  have he := timestamp_run pid old t w a h
  unfold runWGPrefix runStatePrefix at he
  rw [he]
  split
  next newer =>
    cases hr : ((writeTimestamp pid t).run w).run
        (CounterWindow.record a .consumeNewerTimestamp true) with
    | error e => exact ⟨[], by simp, hi, trivial⟩
    | ok out =>
      rcases out with ⟨⟨x, v⟩, b⟩
      have hs : SoundReceipts (h ++ [⟨pid, old, t, ⟨x, w, v,
          CounterWindow.record a .consumeNewerTimestamp true, b⟩⟩]) := by
        intro r member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with prior | rfl
        · exact hi r prior
        · exact ⟨hr, by simpa only [TimestampReceipt.Newer, beq_iff_eq] using newer⟩
      exact ⟨_, rfl, hs, hs⟩
  next => exact ⟨[], by simp, hi, hi⟩

theorem consume_sound (msg : List UInt8) :
    StatePrefixPreserves (fun h _ _ => SoundReceipts h) SoundReceipts (consumeObserved msg) := by
  have silent {α : Type} (a : WG.M α) :
      StatePrefixPreserves (fun h _ _ => SoundReceipts h) SoundReceipts (liftWGPrefix a) :=
    StatePrefixEnsures.lift a (fun _ _ _ h => h) (fun _ _ _ _ _ _ h _ => h)
  have unit {α : Type} (x : α) :
      StatePrefixPreserves (fun h _ _ => SoundReceipts h) SoundReceipts (pure x : WGPrefix TimestampReceipt α) :=
    StatePrefixEnsures.pure x (fun _ _ _ h => h) (fun _ _ _ h => h)
  unfold consumeObserved consumeWith checkedWith successWith
  repeat' first
    | with_reducible exact timestamp_sound _ _ _
    | with_reducible exact silent _
    | with_reducible exact unit _
    | with_reducible apply StatePrefixEnsures.bind
    | (session_origin_intro_forall; try dsimp only)
    | split

end Leanux.Proofs.WG.HandshakeSecurity
