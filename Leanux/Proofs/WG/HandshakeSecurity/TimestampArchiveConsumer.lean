import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
import Leanux.Proofs.WG.HandshakeSecurity.PeerCounterFrames

/-! The original initiation consumer transports the allocation-indexed timestamp
archive through authentication, refusal, all committed timestamp writes and
later Stops. Peer creation is accounted for by the separate archive allocation
contract; this file requires the current archive carrier at entry. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes

theorem history_lift {α : Type} (action : WG.M α)
    (frame : ∀ w a x v b, (action.run w).run a = .ok ((x, v), b) → RetainsFreshness w v)
    (counter : PeerCounter.Same action) :
    StatePrefixPreserves (fun h w _ => StateInv h w) History
      (liftWGPrefix action) :=
  StatePrefixEnsures.lift action (fun _ _ _ h => h.1)
    (fun _ w a x v b hi run => state_retained hi (frame w a x v b run)
      (by rw [(Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp counter w a x v b run]; exact Nat.le_refl _))

theorem history_same {α : Type} (action : WG.M α)
    (frame : SameView (id : WGWorld → WGWorld) action) :
    StatePrefixPreserves (fun h w _ => StateInv h w) History
      (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift action (fun _ _ _ h => h.1)
  intro h w a x v b hi run
  exact (hoare_iff_run_ambient _ _ _).mp (frame.wp (StateInv h)) w a x v b hi run

private theorem ambient {α : Type} (action : AmbientM α) :
    StatePrefixPreserves (fun h w _ => StateInv h w) History
      (liftWGPrefix (monadLift action : WG.M α)) :=
  history_same _ (fun w => hoare_liftAmbient action (fun v => v = w))

private theorem getPeer_history (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => StateInv h w) History
      (liftWGPrefix (getPeer pid)) := by
  apply history_lift
  · intro w a p v b run
    rw [(Queues.getPeer_normal pid w v p a b run).1]
    exact .refl _
  · apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a p v b run
    rw [(Queues.getPeer_normal pid w v p a b run).1]

private theorem out_history (peer ret : Option PeerId) :
    StatePrefixPreserves (fun h w _ => StateInv h w) History
      (liftWGPrefix (Queues.RxCredits.HandshakeLoans.initiationOut peer ret)) :=
  history_lift _ (fun w a x v b run => out_freshness peer ret w v a b x run) (PeerCounter.out peer ret)

private theorem material_history (pid : PeerId)
    (hash ck : List UInt8) (index : Nat) :
    StatePrefixPreserves (fun h w _ => StateInv h w) History
      (liftWGPrefix (writeMaterial pid hash ck index)) :=
  history_lift _ (fun w a x v b run => writeMaterial_freshness pid hash ck index w v a b x run) (PeerCounter.update pid _)

private theorem consumption_history (pid : PeerId) (time : Int64) :
    StatePrefixPreserves (fun h w _ => StateInv h w) History
      (liftWGPrefix (writeConsumption pid time)) :=
  history_lift _ (fun w a x v b run => writeConsumption_freshness pid time w v a b x run) (PeerCounter.update pid _)

private theorem tag_history (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => StateInv h w) History
      (liftWGPrefix (writeConsumedTag pid)) :=
  history_lift _ (fun w a x v b run => writeConsumedTag_freshness pid w v a b x run) (PeerCounter.update pid _)

private theorem ambient_read {α : Type} (action : AmbientM α)
    (pid : PeerId) (old : List UInt8) :
    StatePrefixPreserves
      (fun h w _ => StateInv h w ∧ latestAt w pid = some old)
      History (liftWGPrefix (StateT.lift action)) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ h => h.1.1)
  intro h w a x v b hi run
  have hw : v = w := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient action (fun g : WGWorld => g = w)) w a x v b rfl run
  simpa only [hw] using hi

theorem checked_history (msg e ck hash t : List UInt8)
    (peer : Option PeerId) (pid : PeerId) (p : Peer) :
    StatePrefixEnsures
      (fun h w _ => StateInv h w ∧ latestAt w pid = some p.latestTimestamp)
      History
      (checkedWith liftWGPrefix timestampObserved msg e ck hash t peer pid p)
      (fun _ h w _ => StateInv h w) := by
  unfold checkedWith successWith
  dsimp only
  apply StatePrefixEnsures.bind (ambient_read (AmbientM.hiddenClock64 .floodNow) pid p.latestTimestamp)
  intro now
  apply StatePrefixEnsures.bind (StatePrefixEnsures.lift
    (P := fun h w _ => StateInv h w ∧ latestAt w pid = some p.latestTimestamp)
    (Q := fun (_ : Bool) h w _ => StateInv h w ∧ latestAt w pid = some p.latestTimestamp)
    _ (fun _ _ _ h => h.1.1) ?_)
  · intro rejected
    split
    · exact (out_history _ _).consequence (fun _ _ _ h => h.1) (fun _ _ _ _ h => h)
    · apply StatePrefixEnsures.bind (StatePrefixEnsures.lift
        (P := fun h w _ => StateInv h w ∧ latestAt w pid = some p.latestTimestamp)
        (Q := fun (_ : Unit) h w _ => StateInv h w ∧ latestAt w pid = some p.latestTimestamp)
        _ (fun _ _ _ h => h.1.1) ?_)
      · intro _
        apply StatePrefixEnsures.bind (timestamp pid p.latestTimestamp t)
        intro _
        repeat' first
          | with_reducible exact out_history _ _
          | with_reducible exact material_history _ _ _ _
          | with_reducible exact consumption_history _ _
          | with_reducible exact tag_history _
          | with_reducible exact getPeer_history _
          | with_reducible exact ambient _
          | with_reducible apply StatePrefixEnsures.bind
          | (session_origin_intro_forall; try dsimp only)
          | split
          | unfold branchCmp
          | unfold hiddenClock64
      · intro h w a x v b hi run
        exact ⟨state_retained hi.1 (writeEphemeral_freshness pid e w v a b x run)
          (by rw [(Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp (PeerCounter.update pid _) w a x v b run]; exact Nat.le_refl _),
          (writeEphemeral_latest pid e w v a b x run).trans hi.2⟩
  · intro h w a x v b hi run
    have same := guards_same_world (memcmp t p.latestTimestamp != .gt)
      (p.lastInitiationConsumption + NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64) now
      w v a b x run
    simpa only [same] using hi

theorem read_checked_history (msg e ck hash t : List UInt8)
    (peer : Option PeerId) (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => StateInv h w) History
      (do
        let p ← liftWGPrefix (getPeer pid)
        checkedWith liftWGPrefix timestampObserved msg e ck hash t peer pid p) := by
  apply StatePrefixEnsures.bind (StatePrefixEnsures.lift
    (P := fun h w _ => StateInv h w)
    (Q := fun p h w _ => StateInv h w ∧ latestAt w pid = some p.latestTimestamp)
    (getPeer pid) (fun _ _ _ hi => hi.1) ?_)
  · intro p
    exact checked_history msg e ck hash t peer pid p
  · intro h w a p v b hi run
    obtain ⟨same, _, d, hd, hp⟩ := Queues.getPeer_normal pid w v p a b run
    refine ⟨by simpa only [same] using hi, ?_⟩
    simp [latestAt, same, hd, hp]

/-- Every actual initiation write extends the history of its peer allocation
strictly, and all completed native suffixes preserve that allocation's ledger.
An internally stopped consumer still retains the committed history prefix. -/
theorem consume_history (msg : List UInt8) :
    StatePrefixPreserves (fun h w _ => StateInv h w) History
      (consumeObserved msg) := by
  have getDev : StatePrefixPreserves (fun h w _ => StateInv h w)
      History (liftWGPrefix WG.getDev) :=
    history_lift _ (fun w a x v b run => getDev_freshness w v a b x run) (SameView.factor getDev_sameWGStore WGStoreView.peerCounter)
  have lookup (key : Key) : StatePrefixPreserves (fun h w _ => StateInv h w)
      History (liftWGPrefix (pubkeyLookup key)) :=
    history_lift _ (fun w a x v b run => (pubkeyLookup_retains_handshake key w v a b x run).freshness) (PeerCounter.lookup key)
  have ephemeral (copy : Bool) (e ck hash : List UInt8) :
      StatePrefixPreserves (fun h w _ => StateInv h w)
        History (liftWGPrefix (messageEphemeral copy e ck hash)) :=
    history_same _ (messageEphemeral_sameWGWorld copy e ck hash)
  have dh (flag : Bool) (ck privateKey publicKey : List UInt8) :
      StatePrefixPreserves (fun h w _ => StateInv h w)
        History (liftWGPrefix (mixDh flag ck privateKey publicKey)) :=
    history_same _ (mixDh_sameWGWorld flag ck privateKey publicKey)
  have precomputed (ck key : List UInt8) :
      StatePrefixPreserves (fun h w _ => StateInv h w)
        History (liftWGPrefix (mixPrecomputedDh ck key)) :=
    history_same _ (mixPrecomputedDh_sameWGWorld ck key)
  have decrypt (msg key hash : List UInt8) :
      StatePrefixPreserves (fun h w _ => StateInv h w)
        History (liftWGPrefix (messageDecrypt msg key hash)) :=
    history_same _ (messageDecrypt_sameWGWorld msg key hash)
  unfold consumeObserved consumeWith
  repeat' first
    | with_reducible exact read_checked_history _ _ _ _ _ _ _
    | with_reducible exact out_history _ _
    | with_reducible exact getDev
    | with_reducible exact getPeer_history _
    | with_reducible exact lookup _
    | with_reducible exact ephemeral _ _ _ _
    | with_reducible exact dh _ _ _ _
    | with_reducible exact precomputed _ _
    | with_reducible exact decrypt _ _ _
    | with_reducible exact ambient _
    | with_reducible apply StatePrefixEnsures.bind
    | (session_origin_intro_forall; try dsimp only)
    | split
    | unfold branch
    | unfold invariant


end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
