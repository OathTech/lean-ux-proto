import Leanux.Proofs.WG.KeyTimes.Receive
import Leanux.Proofs.WG.KeyTimes.ReceiveAttempts
import Leanux.Proofs.WG.KeyTimes.ZeroTimer
import Leanux.Proofs.WG.KeyTimes.Staging
import Leanux.Proofs.Logged.TimerPass

/-! R5's original receive/staging admission and clock boundaries. These are local
operation contracts. Accepted-run counterexamples in the accompanying replays
refute the original unconditional age/use claim; universal TX admission transport
and whole-run attempt coverage are not asserted here. -/
namespace Leanux.Proofs.WG.KeyLifetime
open Leanux Leanux.WG Leanux.Proofs.WG.CounterWindow Leanux.Proofs.Logged

/-- The original age test returns exactly the signed 64-bit deadline
comparison and its two integer operands. Its clock is the value returned by
the original clock consumer at these WG/Ambient inputs, with no arithmetic range premise. -/
theorem original_age_test (birthday : Int64) (seconds : Nat)
    (w v : WGWorld) (a b : Ambient) (result : Bool × Int × Int) :
    ((birthdateTest birthday seconds).run w).run a = .ok ((result, v), b) ↔
      ∃ now, (((hiddenClock64 .birthdateExpired : WG.M Int64).run w).run a) =
          .ok ((now, v), b) ∧
        result = (decide (KeyTimes.deadline birthday seconds ≤ now),
          (KeyTimes.deadline birthday seconds).toInt, now.toInt) :=
  KeyTimes.birthdateTest_run_iff birthday seconds w v a b result

/-- An original age branch preserves the exact clock-consumption WG/Ambient endpoints and
appends the specified outcome and both signed operands, including negated
call-site outcomes. Deadline equality counts as expired before that negation. -/
theorem original_age_branch (d : Decision) (birthday : Int64) (seconds : Nat)
    (f : Bool → Bool) (w v : WGWorld) (a b : Ambient) (outcome : Bool) :
    ((branchExpired d birthday seconds f).run w).run a = .ok ((outcome, v), b) ↔
      ∃ now u c, (((hiddenClock64 .birthdateExpired : WG.M Int64).run w).run a) =
          .ok ((now, u), c) ∧
        outcome = f (decide (KeyTimes.deadline birthday seconds ≤ now)) ∧
        v = u ∧ b = recordCmp c d outcome (KeyTimes.deadline birthday seconds).toInt now.toInt :=
  KeyTimes.branchExpired_run_iff d birthday seconds f w v a b outcome

/-- The exact rejection expression factored from original decryption admits
only a valid receiving key, an unexpired clock comparison and a stored
receiving counter below the limit. This guard contract does not assume that
the later authentication attempt succeeds. -/
theorem receive_guard (k : Keypair) (w v : WGWorld) (ambient ambient' : Ambient)
    (h : ((KeyTimes.receiveReject k).run w).run ambient = .ok ((false, v), ambient')) :
    k.receiving.isValid = true ∧ k.receivingCounter.counter < REJECT_AFTER_MESSAGES ∧
      ∃ now u clockAmbient,
        ((hiddenClock64 .birthdateExpired : WG.M Int64).run w).run
          (record ambient .decKeyInvalid false) = .ok ((now, u), clockAmbient) ∧
        ¬ KeyTimes.deadline k.receiving.birthdate REJECT_AFTER_TIME ≤ now :=
  KeyTimes.receiveReject_false k w v ambient ambient' h

/-- Every successful authenticated original decryption used the entry
keypair's valid receiving key after an actual unexpired clock read and a
stored-counter check below the limit. The theorem recovers the entry lookup
and exact clock-read WG/Ambient endpoints without a residency or bitmap-shape premise.
It does not assert a bound on this packet's wire nonce. -/
theorem original_decryption_admission (pkt out : RxPacket) (w v : WGWorld)
    (ambient ambient' : Ambient)
    (hr : ((decryptPacket pkt).run w).run ambient = .ok ((some out, v), ambient')) :
    ∃ d k, w.dev = some d ∧ d.keypairs[pkt.keypair]? = some k ∧
      k.receiving.isValid = true ∧ k.receivingCounter.counter < REJECT_AFTER_MESSAGES ∧
      ∃ now u clockAmbient, ((hiddenClock64 .birthdateExpired : WG.M Int64).run w).run
        (record (record ambient .decNoKeypair false) .decKeyInvalid false) =
          .ok ((now, u), clockAmbient) ∧
        ¬ KeyTimes.deadline k.receiving.birthdate REJECT_AFTER_TIME ≤ now :=
  KeyTimes.decryptPacket_admission pkt out w v ambient ambient' hr

/-- The later original replay validator accepts only wire nonces strictly
below the message limit. Even malformed bitmap states need no shape premise
for this scalar guard implication. -/
theorem original_accepted_wire_nonce (kp : KeypairId) (nonce : Nat)
    (w v : WGWorld) (ambient ambient' : Ambient)
    (hr : ((counterValidate kp nonce).run w).run ambient = .ok ((true, v), ambient')) :
    nonce < REJECT_AFTER_MESSAGES :=
  KeyTimes.counterValidate_wire_bound kp nonce w v ambient ambient' hr

/-- The zero-key timer callback leaves the entire transport-keypair store
unchanged on every ordinary return. Its live, unqueued arm schedules separate
clear work; this
endpoint theorem does not assert that work ran or that later key use is absent. -/
theorem original_zero_timer_preserves_transport_keys (pid : PeerId) (w v : WGWorld)
    (ambient ambient' : Ambient)
    (hr : ((expiredZeroKeyMaterial pid).run w).run ambient = .ok (((), v), ambient')) :
    KeyTimes.keypairStore v = KeyTimes.keypairStore w :=
  (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    (KeyTimes.expiredZeroKeyMaterial_store pid) w ambient () v ambient' hr

/-- The staging observer executes the original action on every WG/Ambient input:
normal returns retain both complete native endpoints and failures retain the
exact original Stop. Its sole event is the completed allocation batch at the
boundary immediately preceding original createData with those allocated IDs. -/
theorem original_staging_erasure (pid : PeerId) :
    ErasesStatePrefix (KeyTimes.stagingObserved pid) (sendStagedPackets pid) :=
  KeyTimes.stagingObserved_erases pid

/-- Every batch observed at original staging submission has a captured original
key lookup with sending validity, an actual unexpired signed-clock read, bounded
assigned nonces and the original completed newTxSkb map execution. The event
prefix survives a later Stop. This certifies submitted arguments, not their
final store contents, subsequent encryption, or immutable key material. -/
theorem original_staging_admissions (pid : PeerId) (w : WGWorld) (ambient : Ambient) :
    ∀ admission ∈ (runStatePrefix (KeyTimes.stagingObserved pid) w ambient []).2,
      admission.Valid := by
  have hs := KeyTimes.stagingObserved_safe pid w ambient []
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

/-- Observing the original AEAD boundary preserves every normal return and
both native endpoints, and every exact original Stop. The event precedes the
AEAD call and the subsequent authentication-result branch. -/
theorem original_receive_attempt_erasure (pkt : RxPacket) :
    ErasesStatePrefix (KeyTimes.receiveAttemptsObserved pkt) (decryptPacket pkt) :=
  KeyTimes.receiveAttemptsObserved_erases pkt

/-- Every original AEAD attempt uses the observed key lookup and false guard:
receiving validity, stored counter below the limit, and an actual unexpired
signed-clock read hold regardless of authentication success. This does not
bound the packet's wire nonce or assert later delivery. -/
theorem original_receive_attempt_admission (pkt : RxPacket) (w : WGWorld) (ambient : Ambient) :
    ∀ attempt ∈ (runStatePrefix (KeyTimes.receiveAttemptsObserved pkt) w ambient []).2,
      attempt.Valid := by
  have hs := KeyTimes.ReceiveAttempts.safe pkt w ambient []
    (show KeyTimes.ReceiveAttempts.Keep True [] w from
      ⟨by simp [KeyTimes.ReceiveAttempts.Good], trivial⟩)
  exact hs.choose_spec.2.1

/-- A successful original getter, false rejection guard and successful RX
copy allocation produce exactly one attempt event. No authentication-success
premise is needed; the result component remains the complete original run. -/
theorem original_receive_attempt_coverage (pkt : RxPacket)
    (w entered checked allocated : WGWorld)
    (ambient enteredAmbient checkedAmbient allocatedAmbient : Ambient)
    (k : Keypair) (h : List KeyTimes.RxAttempt)
    (hg : ((getKeypair pkt.keypair).run w).run (record ambient .decNoKeypair false) =
      .ok ((k, entered), enteredAmbient))
    (hr : ((KeyTimes.receiveReject k).run entered).run enteredAmbient =
      .ok ((false, checked), checkedAmbient))
    (ha : ((hiddenAlloc .skbCowDataRx : WG.M Bool).run checked).run checkedAmbient =
      .ok ((true, allocated), allocatedAmbient)) :
    runWGPrefix (KeyTimes.receiveAttemptsObserved pkt) w ambient h =
      (((decryptPacket pkt).run w).run ambient,
        h ++ [KeyTimes.receiveAttemptWitness pkt w entered checked ambient enteredAmbient checkedAmbient k]) :=
  KeyTimes.receiveAttemptsObserved_singleton pkt w entered checked allocated ambient enteredAmbient checkedAmbient allocatedAmbient k h hg hr ha

/-- Failed authentication still records the attempt and returns none with
the exact original preparation and failed-authentication branch records.
The premises are actual original guard/allocation runs and the actual pure
AEAD result, with no residency invariant or cryptographic security assumption. -/
theorem original_receive_failed_authentication (pkt : RxPacket)
    (w entered checked allocated : WGWorld)
    (ambient enteredAmbient checkedAmbient allocatedAmbient : Ambient)
    (k : Keypair) (h : List KeyTimes.RxAttempt)
    (hg : ((getKeypair pkt.keypair).run w).run (record ambient .decNoKeypair false) =
      .ok ((k, entered), enteredAmbient))
    (hr : ((KeyTimes.receiveReject k).run entered).run enteredAmbient =
      .ok ((false, checked), checkedAmbient))
    (ha : ((hiddenAlloc .skbCowDataRx : WG.M Bool).run checked).run checkedAmbient =
      .ok ((true, allocated), allocatedAmbient))
    (hbad : aeadDecrypt k.receiving.key (counterNonce (u64le pkt.bytes 8)) (pkt.bytes.drop 16) [] = none) :
    runWGPrefix (KeyTimes.receiveAttemptsObserved pkt) w ambient h =
      (.ok ((none, allocated),
        record (record (record (record allocatedAmbient .decCowDataFailed false)
          .decTooManyFrags false) .decSgvecFailed false) .decDecryptFailed true),
        h ++ [KeyTimes.receiveAttemptWitness pkt w entered checked ambient enteredAmbient checkedAmbient k]) :=
  KeyTimes.receiveAttemptsObserved_failed_tag pkt w entered checked allocated ambient enteredAmbient checkedAmbient allocatedAmbient k h hg hr ha hbad

end Leanux.Proofs.WG.KeyLifetime
