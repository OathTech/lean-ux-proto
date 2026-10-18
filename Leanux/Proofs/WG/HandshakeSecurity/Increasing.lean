import Leanux.Proofs.WG.HandshakeSecurity.TimestampFrames

namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged

def TimestampReceipt.Increasing (r : TimestampReceipt) : Prop :=
  ∃ old, latestAt r.execution.before r.peer = some old ∧ memcmp r.received old = .gt

def IncreasingReceipts (h : List TimestampReceipt) : Prop :=
  ∀ r ∈ h, r.Valid ∧ r.Increasing

theorem timestamp_increasing (pid : PeerId) (old t : List UInt8) :
    StatePrefixEnsures
      (fun h w _ => IncreasingReceipts h ∧ latestAt w pid = some old)
      IncreasingReceipts (timestampObserved pid old t)
      (fun _ h _ _ => IncreasingReceipts h) := by
  intro w a h hi
  have he := timestamp_run pid old t w a h
  unfold runWGPrefix runStatePrefix at he
  rw [he]
  split
  next newer =>
    cases hr : ((writeTimestamp pid t).run w).run
        (CounterWindow.record a .consumeNewerTimestamp true) with
    | error stop => exact ⟨[], by simp, hi.1, trivial⟩
    | ok out =>
      rcases out with ⟨⟨x, v⟩, b⟩
      have hs : IncreasingReceipts (h ++ [⟨pid, old, t, ⟨x, w, v,
          CounterWindow.record a .consumeNewerTimestamp true, b⟩⟩]) := by
        intro r member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with prior | rfl
        · exact hi.1 r prior
        · exact ⟨hr, old, hi.2, by simpa only [beq_iff_eq] using newer⟩
      exact ⟨_, rfl, hs, hs⟩
  next => exact ⟨[], by simp, hi.1, hi.1⟩

private theorem silent {α : Type} (action : WG.M α) :
    StatePrefixPreserves (fun h _ _ => IncreasingReceipts h) IncreasingReceipts
      (liftWGPrefix action) :=
  StatePrefixEnsures.lift action (fun _ _ _ h => h) (fun _ _ _ _ _ _ h _ => h)

private theorem ambient {α : Type} (action : AmbientM α) (pid : PeerId) (old : List UInt8) :
    StatePrefixPreserves (fun h w _ => IncreasingReceipts h ∧ latestAt w pid = some old)
      IncreasingReceipts (liftWGPrefix (StateT.lift action)) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ h => h.1)
  intro h w a x v b hi run
  have hw : v = w := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient action (fun g : WGWorld => g = w)) w a x v b rfl run
  simpa only [hw] using hi

theorem checked_increasing (msg e ck hash t : List UInt8) (peer : Option PeerId)
    (pid : PeerId) (p : Peer) :
    StatePrefixEnsures
      (fun h w _ => IncreasingReceipts h ∧ latestAt w pid = some p.latestTimestamp)
      IncreasingReceipts (checkedWith liftWGPrefix timestampObserved msg e ck hash t peer pid p)
      (fun _ h _ _ => IncreasingReceipts h) := by
  unfold checkedWith successWith
  dsimp only
  apply StatePrefixEnsures.bind (ambient (AmbientM.hiddenClock64 .floodNow) pid p.latestTimestamp)
  intro now
  apply StatePrefixEnsures.bind (StatePrefixEnsures.lift
    (P := fun h w _ => IncreasingReceipts h ∧ latestAt w pid = some p.latestTimestamp)
    (Q := fun (_ : Bool) h w _ => IncreasingReceipts h ∧ latestAt w pid = some p.latestTimestamp)
    _ (fun _ _ _ h => h.1) ?_)
  · intro rejected
    split
    · exact (silent _).consequence (fun _ _ _ h => h.1) (fun _ _ _ _ h => h)
    · apply StatePrefixEnsures.bind (StatePrefixEnsures.lift
        (P := fun h w _ => IncreasingReceipts h ∧ latestAt w pid = some p.latestTimestamp)
        (Q := fun (_ : Unit) h w _ => IncreasingReceipts h ∧ latestAt w pid = some p.latestTimestamp)
        _ (fun _ _ _ h => h.1) ?_)
      · intro _
        apply StatePrefixEnsures.bind (timestamp_increasing pid p.latestTimestamp t)
        intro _
        repeat' first
          | with_reducible exact silent _
          | with_reducible apply StatePrefixEnsures.bind
          | (session_origin_intro_forall; try dsimp only)
          | split
      · intro h w a x v b hi run
        exact ⟨hi.1, (writeEphemeral_latest pid e w v a b x run).trans hi.2⟩
  · intro h w a x v b hi run
    have same := guards_same_world (memcmp t p.latestTimestamp != .gt)
      (p.lastInitiationConsumption + NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64) now
      w v a b x run
    simpa only [same] using hi

theorem read_checked_increasing (msg e ck hash t : List UInt8) (peer : Option PeerId)
    (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => IncreasingReceipts h) IncreasingReceipts
      (do
        let p ← liftWGPrefix (getPeer pid)
        checkedWith liftWGPrefix timestampObserved msg e ck hash t peer pid p) := by
  apply StatePrefixEnsures.bind (StatePrefixEnsures.lift
    (P := fun h _ _ => IncreasingReceipts h)
    (Q := fun p h w _ => IncreasingReceipts h ∧ latestAt w pid = some p.latestTimestamp)
    (getPeer pid) (fun _ _ _ h => h) ?_)
  · intro p
    exact checked_increasing msg e ck hash t peer pid p
  · intro h w a p v b hi run
    obtain ⟨same, _, d, hd, hp⟩ := Queues.getPeer_normal pid w v p a b run
    exact ⟨hi, by simp [latestAt, same, hd, hp]⟩

theorem consume_increasing (msg : List UInt8) :
    StatePrefixPreserves (fun h _ _ => IncreasingReceipts h) IncreasingReceipts
      (consumeObserved msg) := by
  unfold consumeObserved consumeWith
  repeat' first
    | with_reducible exact read_checked_increasing _ _ _ _ _ _ _
    | with_reducible exact silent _
    | with_reducible apply StatePrefixEnsures.bind
    | (session_origin_intro_forall; try dsimp only)
    | split

end Leanux.Proofs.WG.HandshakeSecurity
