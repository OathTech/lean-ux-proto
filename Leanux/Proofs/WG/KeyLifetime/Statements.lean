import Leanux.Proofs.WG.KeyTimes.Receive
import Leanux.Proofs.WG.KeyTimes.ZeroTimer

/-! R5's original receive admission and clock boundaries. These are local
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

end Leanux.Proofs.WG.KeyLifetime
