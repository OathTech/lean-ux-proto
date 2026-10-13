import Leanux.Proofs.Logged.Capture
import Leanux.Proofs.WG.KeyTimes.Receive

set_option maxHeartbeats 600000

/-! Original receive AEAD attempts, including failed authentication. The sole
observation sits after the original allocation/fragment checks and immediately
before AEAD; execution witnesses are proof-side data only. -/
namespace Leanux.Proofs.WG.KeyTimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.WG.CounterWindow

structure RxAttempt where
  packet : RxPacket
  keyRead : RunWitness Keypair
  guardRead : RunWitness Bool

def RxAttempt.Valid (a : RxAttempt) : Prop :=
  a.keyRead.Valid (getKeypair a.packet.keypair) ∧
  a.guardRead.Valid (receiveReject a.keyRead.value) ∧
  a.guardRead.value = false ∧
  a.keyRead.value.receiving.isValid = true ∧
  a.keyRead.value.receivingCounter.counter < REJECT_AFTER_MESSAGES ∧
  ∃ now u, (hiddenClock64 .birthdateExpired).run
      (record a.guardRead.before .decKeyInvalid false) = .ok (now, u) ∧
    ¬ deadline a.keyRead.value.receiving.birthdate REJECT_AFTER_TIME ≤ now

/-- The unchanged original suffix starting with its pure AEAD call. -/
def receiveAeadTail (pkt : RxPacket) (k : Keypair) : M (Option RxPacket) := do
  let nonce := u64le pkt.bytes 8
  let plain := aeadDecrypt k.receiving.key (counterNonce nonce) (pkt.bytes.drop 16) []
  if ← branch .decDecryptFailed plain.isNone then return none
  let some bytes := plain | invariant "unreachable"
  if ← branch .decTrimFailed false then return none
  return some {pkt with nonce, bytes}

def receiveAttemptTail (a : RxAttempt) : PrefixM RxAttempt (Option RxPacket) := do
  let cowOk ← liftPrefix (hiddenAlloc .skbCowDataRx)
  if ← liftPrefix (WG.orM (branch .decCowDataFailed !cowOk) (branch .decTooManyFrags false)) then return none
  if ← liftPrefix (branch .decSgvecFailed false) then return none
  emitPrefix a
  liftPrefix (receiveAeadTail a.packet a.keyRead.value)

def receiveAttemptsObserved (pkt : RxPacket) : PrefixM RxAttempt (Option RxPacket) := do
  if ← liftPrefix (branch .decNoKeypair false) then return none
  let keyRead ← captureRun (getKeypair pkt.keypair)
  let guardRead ← captureRun (receiveReject keyRead.value)
  if guardRead.value then
    let k ← liftPrefix (getKeypair pkt.keypair)
    liftPrefix (setKeypair pkt.keypair {k with receiving := {k.receiving with isValid := false}})
    return none
  receiveAttemptTail {packet := pkt, keyRead, guardRead}

theorem receiveAttemptTail_erases (a : RxAttempt) :
    ErasesPrefix (receiveAttemptTail a) (receiveTail a.packet a.keyRead.value) := by
  unfold receiveAttemptTail receiveTail
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro cowOk
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro cowBad
  split
  · exact erasesPrefix_pure _
  · apply erasesPrefix_bind (erasesPrefix_lift _)
    intro sgBad
    split
    · exact erasesPrefix_pure _
    · exact emitThen_erases a (receiveAeadTail a.packet a.keyRead.value)

theorem receiveAttemptsObserved_erases (pkt : RxPacket) :
    ErasesPrefix (receiveAttemptsObserved pkt) (decryptPacket pkt) := by
  rw [decryptPacket_factor]
  unfold receiveAttemptsObserved
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro noKey
  split
  · exact erasesPrefix_pure _
  · apply captureRun_bind_erases
    intro keyRead
    apply captureRun_bind_erases
    intro guardRead
    split
    · apply erasesPrefix_bind (erasesPrefix_lift _)
      intro k
      apply erasesPrefix_bind (erasesPrefix_lift _)
      intro _
      exact erasesPrefix_pure _
    · exact receiveAttemptTail_erases _

namespace ReceiveAttempts

def Good (h : List RxAttempt) : Prop := ∀ a ∈ h, a.Valid

def Keep (C : Prop) (h : List RxAttempt) (_ : World) : Prop := Good h ∧ C

theorem liftKeep (a : M α) (C : Prop) :
    PrefixEnsures (Keep C) Good (liftPrefix a) (fun _ => Keep C) :=
  PrefixEnsures.lift a (fun _ _ hi => hi.1) (fun _ _ _ _ hi _ => hi)

theorem liftForget (a : M α) (C : Prop) :
    PrefixEnsures (Keep C) Good (liftPrefix a) (fun _ => Keep True) :=
  (liftKeep a C).consequence (fun _ _ hi => hi) (fun _ _ _ hi => ⟨hi.1, trivial⟩)

theorem pureForget (x : α) (C : Prop) :
    PrefixEnsures (Keep C) Good (pure x) (fun _ => Keep True) :=
  PrefixEnsures.pure (fun _ _ hi => hi.1) (fun _ _ hi => ⟨hi.1, trivial⟩)

theorem captureKeep (a : M α) (C : Prop) :
    PrefixEnsures (Keep C) Good (captureRun a)
      (fun r => Keep (C ∧ r.Valid a)) := by
  apply PrefixEnsures.captureRun _ (fun _ _ hi => hi.1)
  intro h w x v hi hr
  exact ⟨hi.1, hi.2, hr⟩

theorem emitGood (a : RxAttempt) :
    PrefixEnsures (Keep a.Valid) Good (emitPrefix a) (fun _ => Keep True) := by
  intro w h hi
  have hg : Good (h ++ [a]) := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hi.1 b hb
    · have he : b = a := by simpa using hb
      subst b
      exact hi.2
  exact ⟨[a], by simp, by simpa using hg, by simpa [Keep] using hg⟩

theorem tail_safe (a : RxAttempt) :
    PrefixEnsures (Keep a.Valid) Good (receiveAttemptTail a) (fun _ => Keep True) := by
  unfold receiveAttemptTail
  apply PrefixEnsures.bind (liftKeep _ _)
  intro cowOk
  apply PrefixEnsures.bind (liftKeep _ _)
  intro cowBad
  split
  · exact pureForget _ _
  · apply PrefixEnsures.bind (liftKeep _ _)
    intro sgBad
    split
    · exact pureForget _ _
    · apply PrefixEnsures.bind (emitGood a)
      intro _
      exact liftForget _ _

theorem safe (pkt : RxPacket) :
    PrefixEnsures (Keep True) Good (receiveAttemptsObserved pkt) (fun _ => Keep True) := by
  unfold receiveAttemptsObserved
  apply PrefixEnsures.bind (liftKeep _ True)
  intro noKey
  split
  · exact pureForget _ _
  · apply PrefixEnsures.bind (captureKeep _ True)
    intro keyRead
    apply PrefixEnsures.bind (captureKeep _ _)
    intro guardRead
    split
    · apply PrefixEnsures.bind (liftKeep _ _)
      intro k
      apply PrefixEnsures.bind (liftKeep _ _)
      intro _
      exact pureForget _ _
    · rename_i hf
      apply (tail_safe _).consequence
      · intro h w hi
        have hz : guardRead.value = false := by simpa using hf
        have hr : (receiveReject keyRead.value).run guardRead.before = .ok (false, guardRead.after) := by
          simpa [RunWitness.Valid, hz] using hi.2.2
        obtain ⟨valid, bound, clock⟩ := receiveReject_false keyRead.value _ _ hr
        exact ⟨hi.1, hi.2.1.2, hi.2.2, hz, valid, bound, clock⟩
      · intro _ _ _ hi
        exact hi

end ReceiveAttempts

/-- Allocation success reaches exactly one AEAD event. The equation is
independent of whether the tag authenticates. -/
theorem receiveAttemptTail_singleton (a : RxAttempt) (w u : World) (h : List RxAttempt)
    (ha : (hiddenAlloc .skbCowDataRx).run w = .ok (true, u)) :
    runPrefix (receiveAttemptTail a) w h =
      ((receiveTail a.packet a.keyRead.value).run w, h ++ [a]) := by
  unfold receiveAttemptTail receiveTail
  simp only [runPrefix_bind, runPrefix_lift, ha, StateT.run_bind, except_ok_bind]
  simp [WG.orM, branch_run, receiveAeadTail, runPrefix_bind, StateT.run_bind]
  rfl

/-- The concrete execution witnesses carried by the unique original attempt. -/
def receiveAttemptWitness (pkt : RxPacket) (w entered checked : World) (k : Keypair) : RxAttempt :=
  {packet := pkt, keyRead := ⟨k, record w .decNoKeypair false, entered⟩,
    guardRead := ⟨false, entered, checked⟩}

/-- Getter, guard and allocation success suffice for exactly one original
attempt. No premise mentions the authentication result. -/
theorem receiveAttemptsObserved_singleton (pkt : RxPacket)
    (w entered checked allocated : World) (k : Keypair) (h : List RxAttempt)
    (hg : (getKeypair pkt.keypair).run (record w .decNoKeypair false) = .ok (k, entered))
    (hr : (receiveReject k).run entered = .ok (false, checked))
    (ha : (hiddenAlloc .skbCowDataRx).run checked = .ok (true, allocated)) :
    runPrefix (receiveAttemptsObserved pkt) w h =
      ((decryptPacket pkt).run w, h ++ [receiveAttemptWitness pkt w entered checked k]) := by
  have ht := receiveAttemptTail_singleton (receiveAttemptWitness pkt w entered checked k)
    checked allocated h ha
  rw [decryptPacket_factor]
  unfold receiveAttemptsObserved
  simpa only [runPrefix_bind, runPrefix_lift, branch_run, runPrefix_captureRun,
    StateT.run_bind, except_ok_bind, hg, hr, Bool.false_eq_true, ↓reduceIte,
    receiveAttemptWitness] using ht

/-- Failed authentication still emits the attempt and returns the original
none endpoint, with all four preparation/authentication branch records. -/
theorem receiveAttemptsObserved_failed_tag (pkt : RxPacket)
    (w entered checked allocated : World) (k : Keypair) (h : List RxAttempt)
    (hg : (getKeypair pkt.keypair).run (record w .decNoKeypair false) = .ok (k, entered))
    (hr : (receiveReject k).run entered = .ok (false, checked))
    (ha : (hiddenAlloc .skbCowDataRx).run checked = .ok (true, allocated))
    (hbad : aeadDecrypt k.receiving.key (counterNonce (u64le pkt.bytes 8)) (pkt.bytes.drop 16) [] = none) :
    runPrefix (receiveAttemptsObserved pkt) w h =
      (.ok (none, record (record (record (record allocated .decCowDataFailed false)
        .decTooManyFrags false) .decSgvecFailed false) .decDecryptFailed true),
        h ++ [receiveAttemptWitness pkt w entered checked k]) := by
  rw [receiveAttemptsObserved_singleton pkt w entered checked allocated k h hg hr ha]
  rw [decryptPacket_factor]
  simp [StateT.run_bind, branch_run, hg, hr, receiveTail, ha, WG.orM, hbad]

end Leanux.Proofs.WG.KeyTimes
