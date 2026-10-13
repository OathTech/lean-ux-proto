import Leanux.Proofs.WG.KeyTimes.Receive
import Leanux.Proofs.WG.KeyTimes.ZeroTimer
import Leanux.Proofs.WG.KeyTimes.Staging
import Leanux.Proofs.Logged.TimerPass

/-! R5's original receive/staging admission and clock boundaries. These are local
operation contracts; TX admission-to-encryption transport and post-clearance
schedule exclusion remain separate obligations. -/
namespace Leanux.Proofs.WG.KeyLifetime
open Leanux Leanux.WG Leanux.Proofs.WG.CounterWindow

/-- The original age test returns exactly the signed 64-bit deadline
comparison and its two integer operands. Its clock is the value returned by
the original clock consumer at this World, with no arithmetic range premise. -/
theorem original_age_test (birthday : Int64) (seconds : Nat)
    (w v : World) (result : Bool × Int × Int) :
    (birthdateTest birthday seconds).run w = .ok (result, v) ↔
      ∃ now, (hiddenClock64 .birthdateExpired).run w = .ok (now, v) ∧
        result = (decide (KeyTimes.deadline birthday seconds ≤ now),
          (KeyTimes.deadline birthday seconds).toInt, now.toInt) :=
  KeyTimes.birthdateTest_run_iff birthday seconds w v result

/-- An original age branch preserves the exact clock-consumption World and
appends the specified outcome and both signed operands, including negated
call-site outcomes. Deadline equality counts as expired before that negation. -/
theorem original_age_branch (d : Decision) (birthday : Int64) (seconds : Nat)
    (f : Bool → Bool) (w v : World) (outcome : Bool) :
    (branchExpired d birthday seconds f).run w = .ok (outcome, v) ↔
      ∃ now u, (hiddenClock64 .birthdateExpired).run w = .ok (now, u) ∧
        outcome = f (decide (KeyTimes.deadline birthday seconds ≤ now)) ∧
        v = recordCmp u d outcome (KeyTimes.deadline birthday seconds).toInt now.toInt :=
  KeyTimes.branchExpired_run_iff d birthday seconds f w v outcome

/-- The exact rejection expression factored from original decryption admits
only a valid receiving key, an unexpired clock comparison and a stored
receiving counter below the limit. This guard contract does not assume that
the later authentication attempt succeeds. -/
theorem receive_guard (k : Keypair) (w v : World)
    (h : (KeyTimes.receiveReject k).run w = .ok (false, v)) :
    k.receiving.isValid = true ∧ k.receivingCounter.counter < REJECT_AFTER_MESSAGES ∧
      ∃ now u, (hiddenClock64 .birthdateExpired).run (record w .decKeyInvalid false) = .ok (now, u) ∧
        ¬ KeyTimes.deadline k.receiving.birthdate REJECT_AFTER_TIME ≤ now :=
  KeyTimes.receiveReject_false k w v h

/-- Every successful authenticated original decryption used the entry
keypair's valid receiving key after an actual unexpired clock read and a
stored-counter check below the limit. The theorem recovers the entry lookup
and exact clock-read World without a residency or bitmap-shape premise.
It does not assert a bound on this packet's wire nonce. -/
theorem original_decryption_admission (pkt out : RxPacket) (w v : World)
    (hr : (decryptPacket pkt).run w = .ok (some out, v)) :
    ∃ d k, w.k.wg = some d ∧ d.keypairs[pkt.keypair]? = some k ∧
      k.receiving.isValid = true ∧ k.receivingCounter.counter < REJECT_AFTER_MESSAGES ∧
      ∃ now u, (hiddenClock64 .birthdateExpired).run
        (record (record w .decNoKeypair false) .decKeyInvalid false) = .ok (now, u) ∧
        ¬ KeyTimes.deadline k.receiving.birthdate REJECT_AFTER_TIME ≤ now :=
  KeyTimes.decryptPacket_admission pkt out w v hr

/-- The later original replay validator accepts only wire nonces strictly
below the message limit. Even malformed bitmap states need no shape premise
for this scalar guard implication. -/
theorem original_accepted_wire_nonce (kp : KeypairId) (nonce : Nat) (w v : World)
    (hr : (counterValidate kp nonce).run w = .ok (true, v)) :
    nonce < REJECT_AFTER_MESSAGES :=
  KeyTimes.counterValidate_wire_bound kp nonce w v hr

/-- The zero-key timer callback leaves the entire transport-keypair store
unchanged on every ordinary return. Its live, unqueued arm schedules separate
clear work; this
endpoint theorem does not assert that work ran or that later key use is absent. -/
theorem original_zero_timer_preserves_transport_keys (pid : PeerId) (w v : World)
    (hr : (expiredZeroKeyMaterial pid).run w = .ok ((), v)) :
    KeyTimes.keypairStore v = KeyTimes.keypairStore w :=
  KeyTimes.expiredZeroKeyMaterial_store pid w () v hr

/-- The staging observer executes the original action exactly on every World:
normal returns retain the complete original World and failures retain the
exact original Stop. Its sole event is the completed allocation batch at the
boundary immediately preceding original createData with those allocated IDs. -/
theorem original_staging_erasure (pid : PeerId) :
    Leanux.Proofs.Logged.ErasesPrefix (KeyTimes.stagingObserved pid) (sendStagedPackets pid) :=
  KeyTimes.stagingObserved_erases pid

/-- Every batch observed at original staging submission has a captured original
key lookup with sending validity, an actual unexpired signed-clock read, bounded
assigned nonces and the original completed newTxSkb map execution. The event
prefix survives a later Stop. This certifies submitted arguments, not their
final store contents, subsequent encryption, or immutable key material. -/
theorem original_staging_admissions (pid : PeerId) (w : World) :
    ∀ admission ∈ (Leanux.Proofs.Logged.runPrefix (KeyTimes.stagingObserved pid) w []).2,
      admission.Valid := by
  have hs := KeyTimes.stagingObserved_safe pid w []
    (show KeyTimes.keep True [] w from ⟨by simp [KeyTimes.admissionsGood], trivial⟩)
  exact hs.choose_spec.2.1

/-- Observing completed timer, clear/send-worker and crypt-scheduler units
preserves the exact original timer-pass result and World on success, and its
exact Stop on failure. Each unit observation records the original before/after
Worlds; a crypt scheduler call may be empty. This is not a non-use theorem. -/
theorem original_timer_pass_erasure (jHi : UInt64) :
    Leanux.Proofs.Logged.ErasesPrefix
      (Leanux.Proofs.Logged.timerPassObserved jHi) (Leanux.Env.runTimers jHi) :=
  Leanux.Proofs.Logged.timerPassObserved_erases jHi

end Leanux.Proofs.WG.KeyLifetime
