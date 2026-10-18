import Leanux.Proofs.WG.HandshakeSecurity.TimestampHistory

namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged

theorem timestamp_history (initial : WGWorld) (pid : PeerId) (old t : List UInt8) :
    StatePrefixEnsures
      (fun h w _ => TimestampInv initial h w ∧ latestAt w pid = some old)
      (TimestampHistory initial) (timestampObserved pid old t)
      (fun _ h w _ => TimestampInv initial h w) := by
  intro w a h hi
  have he := timestamp_run pid old t w a h
  unfold runWGPrefix runStatePrefix at he
  rw [he]
  split
  next newer =>
    cases hr : ((writeTimestamp pid t).run w).run
        (CounterWindow.record a .consumeNewerTimestamp true) with
    | error stop => exact ⟨[], by simp, hi.1.1, trivial⟩
    | ok out =>
      rcases out with ⟨⟨x, v⟩, b⟩
      have hs := history_append initial h
        ⟨pid, old, t, ⟨x, w, v, CounterWindow.record a .consumeNewerTimestamp true, b⟩⟩
        hi.1 hr ⟨old, hi.2, by simpa only [beq_iff_eq] using newer⟩
      exact ⟨_, rfl, hs.1, hs⟩
  next => exact ⟨[], by simp, hi.1.1, hi.1⟩

theorem history_lift {α : Type} (initial : WGWorld) (action : WG.M α)
    (frame : ∀ w a x v b, (action.run w).run a = .ok ((x, v), b) → RetainsFreshness w v) :
    StatePrefixPreserves (fun h w _ => TimestampInv initial h w) (TimestampHistory initial)
      (liftWGPrefix action) :=
  StatePrefixEnsures.lift action (fun _ _ _ h => h.1)
    (fun _ w a x v b hi run => ⟨hi.1, hi.2.retained (frame w a x v b run)⟩)

theorem history_same {α : Type} (initial : WGWorld) (action : WG.M α)
    (frame : SameView (id : WGWorld → WGWorld) action) :
    StatePrefixPreserves (fun h w _ => TimestampInv initial h w) (TimestampHistory initial)
      (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift action (fun _ _ _ h => h.1)
  intro h w a x v b hi run
  exact (hoare_iff_run_ambient _ _ _).mp (frame.wp (TimestampInv initial h)) w a x v b hi run

private theorem ambient {α : Type} (initial : WGWorld) (action : AmbientM α) :
    StatePrefixPreserves (fun h w _ => TimestampInv initial h w) (TimestampHistory initial)
      (liftWGPrefix (monadLift action : WG.M α)) :=
  history_same initial _ (fun w => hoare_liftAmbient action (fun v => v = w))

private theorem getPeer_history (initial : WGWorld) (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => TimestampInv initial h w) (TimestampHistory initial)
      (liftWGPrefix (getPeer pid)) := by
  apply history_lift
  intro w a p v b run
  rw [(Queues.getPeer_normal pid w v p a b run).1]
  exact .refl _

private theorem out_history (initial : WGWorld) (peer ret : Option PeerId) :
    StatePrefixPreserves (fun h w _ => TimestampInv initial h w) (TimestampHistory initial)
      (liftWGPrefix (Queues.RxCredits.HandshakeLoans.initiationOut peer ret)) :=
  history_lift initial _ (fun w a x v b run => out_freshness peer ret w v a b x run)

private theorem material_history (initial : WGWorld) (pid : PeerId)
    (hash ck : List UInt8) (index : Nat) :
    StatePrefixPreserves (fun h w _ => TimestampInv initial h w) (TimestampHistory initial)
      (liftWGPrefix (writeMaterial pid hash ck index)) :=
  history_lift initial _ (fun w a x v b run => writeMaterial_freshness pid hash ck index w v a b x run)

private theorem consumption_history (initial : WGWorld) (pid : PeerId) (time : Int64) :
    StatePrefixPreserves (fun h w _ => TimestampInv initial h w) (TimestampHistory initial)
      (liftWGPrefix (writeConsumption pid time)) :=
  history_lift initial _ (fun w a x v b run => writeConsumption_freshness pid time w v a b x run)

private theorem tag_history (initial : WGWorld) (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => TimestampInv initial h w) (TimestampHistory initial)
      (liftWGPrefix (writeConsumedTag pid)) :=
  history_lift initial _ (fun w a x v b run => writeConsumedTag_freshness pid w v a b x run)

private theorem ambient_read {α : Type} (initial : WGWorld) (action : AmbientM α)
    (pid : PeerId) (old : List UInt8) :
    StatePrefixPreserves
      (fun h w _ => TimestampInv initial h w ∧ latestAt w pid = some old)
      (TimestampHistory initial) (liftWGPrefix (StateT.lift action)) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ h => h.1.1)
  intro h w a x v b hi run
  have hw : v = w := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient action (fun g : WGWorld => g = w)) w a x v b rfl run
  simpa only [hw] using hi

theorem checked_history (initial : WGWorld) (msg e ck hash t : List UInt8)
    (peer : Option PeerId) (pid : PeerId) (p : Peer) :
    StatePrefixEnsures
      (fun h w _ => TimestampInv initial h w ∧ latestAt w pid = some p.latestTimestamp)
      (TimestampHistory initial)
      (checkedWith liftWGPrefix timestampObserved msg e ck hash t peer pid p)
      (fun _ h w _ => TimestampInv initial h w) := by
  unfold checkedWith successWith
  dsimp only
  apply StatePrefixEnsures.bind (ambient_read initial (AmbientM.hiddenClock64 .floodNow) pid p.latestTimestamp)
  intro now
  apply StatePrefixEnsures.bind (StatePrefixEnsures.lift
    (P := fun h w _ => TimestampInv initial h w ∧ latestAt w pid = some p.latestTimestamp)
    (Q := fun (_ : Bool) h w _ => TimestampInv initial h w ∧ latestAt w pid = some p.latestTimestamp)
    _ (fun _ _ _ h => h.1.1) ?_)
  · intro rejected
    split
    · exact (out_history initial _ _).consequence (fun _ _ _ h => h.1) (fun _ _ _ _ h => h)
    · apply StatePrefixEnsures.bind (StatePrefixEnsures.lift
        (P := fun h w _ => TimestampInv initial h w ∧ latestAt w pid = some p.latestTimestamp)
        (Q := fun (_ : Unit) h w _ => TimestampInv initial h w ∧ latestAt w pid = some p.latestTimestamp)
        _ (fun _ _ _ h => h.1.1) ?_)
      · intro _
        apply StatePrefixEnsures.bind (timestamp_history initial pid p.latestTimestamp t)
        intro _
        repeat' first
          | with_reducible exact out_history initial _ _
          | with_reducible exact material_history initial _ _ _ _
          | with_reducible exact consumption_history initial _ _
          | with_reducible exact tag_history initial _
          | with_reducible exact getPeer_history initial _
          | with_reducible exact ambient initial _
          | with_reducible apply StatePrefixEnsures.bind
          | (session_origin_intro_forall; try dsimp only)
          | split
          | unfold branchCmp
          | unfold hiddenClock64
      · intro h w a x v b hi run
        exact ⟨⟨hi.1.1, hi.1.2.retained (writeEphemeral_freshness pid e w v a b x run)⟩,
          (writeEphemeral_latest pid e w v a b x run).trans hi.2⟩
  · intro h w a x v b hi run
    have same := guards_same_world (memcmp t p.latestTimestamp != .gt)
      (p.lastInitiationConsumption + NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64) now
      w v a b x run
    simpa only [same] using hi

theorem read_checked_history (initial : WGWorld) (msg e ck hash t : List UInt8)
    (peer : Option PeerId) (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => TimestampInv initial h w) (TimestampHistory initial)
      (do
        let p ← liftWGPrefix (getPeer pid)
        checkedWith liftWGPrefix timestampObserved msg e ck hash t peer pid p) := by
  apply StatePrefixEnsures.bind (StatePrefixEnsures.lift
    (P := fun h w _ => TimestampInv initial h w)
    (Q := fun p h w _ => TimestampInv initial h w ∧ latestAt w pid = some p.latestTimestamp)
    (getPeer pid) (fun _ _ _ hi => hi.1) ?_)
  · intro p
    exact checked_history initial msg e ck hash t peer pid p
  · intro h w a p v b hi run
    obtain ⟨same, _, d, hd, hp⟩ := Queues.getPeer_normal pid w v p a b run
    refine ⟨by simpa only [same] using hi, ?_⟩
    simp [latestAt, same, hd, hp]

theorem consume_history (initial : WGWorld) (msg : List UInt8) :
    StatePrefixPreserves (fun h w _ => TimestampInv initial h w) (TimestampHistory initial)
      (consumeObserved msg) := by
  have getDev : StatePrefixPreserves (fun h w _ => TimestampInv initial h w)
      (TimestampHistory initial) (liftWGPrefix WG.getDev) :=
    history_lift initial _ (fun w a x v b run => getDev_freshness w v a b x run)
  have lookup (key : Key) : StatePrefixPreserves (fun h w _ => TimestampInv initial h w)
      (TimestampHistory initial) (liftWGPrefix (pubkeyLookup key)) :=
    history_lift initial _ (fun w a x v b run => (pubkeyLookup_retains_handshake key w v a b x run).freshness)
  have ephemeral (copy : Bool) (e ck hash : List UInt8) :
      StatePrefixPreserves (fun h w _ => TimestampInv initial h w)
        (TimestampHistory initial) (liftWGPrefix (messageEphemeral copy e ck hash)) :=
    history_same initial _ (messageEphemeral_sameWGWorld copy e ck hash)
  have dh (flag : Bool) (ck privateKey publicKey : List UInt8) :
      StatePrefixPreserves (fun h w _ => TimestampInv initial h w)
        (TimestampHistory initial) (liftWGPrefix (mixDh flag ck privateKey publicKey)) :=
    history_same initial _ (mixDh_sameWGWorld flag ck privateKey publicKey)
  have precomputed (ck key : List UInt8) :
      StatePrefixPreserves (fun h w _ => TimestampInv initial h w)
        (TimestampHistory initial) (liftWGPrefix (mixPrecomputedDh ck key)) :=
    history_same initial _ (mixPrecomputedDh_sameWGWorld ck key)
  have decrypt (msg key hash : List UInt8) :
      StatePrefixPreserves (fun h w _ => TimestampInv initial h w)
        (TimestampHistory initial) (liftWGPrefix (messageDecrypt msg key hash)) :=
    history_same initial _ (messageDecrypt_sameWGWorld msg key hash)
  unfold consumeObserved consumeWith
  repeat' first
    | with_reducible exact read_checked_history initial _ _ _ _ _ _ _
    | with_reducible exact out_history initial _ _
    | with_reducible exact getDev
    | with_reducible exact getPeer_history initial _
    | with_reducible exact lookup _
    | with_reducible exact ephemeral _ _ _ _
    | with_reducible exact dh _ _ _ _
    | with_reducible exact precomputed _ _
    | with_reducible exact decrypt _ _ _
    | with_reducible exact ambient initial _
    | with_reducible apply StatePrefixEnsures.bind
    | (session_origin_intro_forall; try dsimp only)
    | split
    | unfold branch
    | unfold invariant

/-- Arbitrarily many original initiation-consumer calls, with no allocation
between them. A full fixture lift must additionally observe allocation and
prove frames for all intervening driver operations. -/
def consumeManyObserved : List (List UInt8) → WGPrefix TimestampReceipt Unit
  | [] => pure ()
  | msg :: rest => do
    _ ← consumeObserved msg
    consumeManyObserved rest

def consumeMany : List (List UInt8) → WG.M Unit
  | [] => pure ()
  | msg :: rest => do
    _ ← consumeInitiation msg
    consumeMany rest

theorem consumeMany_erases (messages : List (List UInt8)) :
    ErasesStatePrefix (consumeManyObserved messages) (consumeMany messages) := by
  induction messages with
  | nil => exact erasesStatePrefix_pure ()
  | cons msg rest ih => exact erasesStatePrefix_bind (consume_erases msg) (fun _ => ih)

theorem consumeMany_history (initial : WGWorld) (messages : List (List UInt8)) :
    StatePrefixPreserves (fun h w _ => TimestampInv initial h w) (TimestampHistory initial)
      (consumeManyObserved messages) := by
  induction messages with
  | nil => exact StatePrefixEnsures.pure () (fun _ _ _ hi => hi.1) (fun _ _ _ hi => hi)
  | cons msg rest ih => exact StatePrefixEnsures.bind (consume_history initial msg) (fun _ => ih)

end Leanux.Proofs.WG.HandshakeSecurity
