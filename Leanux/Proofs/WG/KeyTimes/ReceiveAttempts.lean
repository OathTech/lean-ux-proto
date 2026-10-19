import Leanux.Proofs.Logged.NativeCapture
import Leanux.Proofs.WG.KeyTimes.Receive

set_option maxHeartbeats 600000

/-! Original receive AEAD attempts, including failed authentication. The sole
observation sits after the original allocation/fragment checks and immediately
before AEAD; execution witnesses are proof-side data only. -/
namespace Leanux.Proofs.WG.KeyTimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.WG.CounterWindow

structure RxAttempt where
  packet : RxPacket
  keyRead : WGRunWitness Keypair
  guardRead : WGRunWitness Bool

def RxAttempt.Valid (a : RxAttempt) : Prop :=
  a.keyRead.Valid (getKeypair a.packet.keypair) ∧
  a.guardRead.Valid (receiveReject a.keyRead.value) ∧
  a.guardRead.value = false ∧
  a.keyRead.value.receiving.isValid = true ∧
  a.keyRead.value.receivingCounter.counter < REJECT_AFTER_MESSAGES ∧
  ∃ now u clockAmbient, ((hiddenClock64 .birthdateExpired : WG.M Int64).run
      a.guardRead.before).run (record a.guardRead.ambientBefore .decKeyInvalid false) =
      .ok ((now, u), clockAmbient) ∧
    ¬ deadline a.keyRead.value.receiving.birthdate REJECT_AFTER_TIME ≤ now

/-- The unchanged original suffix starting with its pure AEAD call. -/
def receiveAeadTail (pkt : RxPacket) (k : Keypair) : WG.M (Option RxPacket) := do
  let nonce := u64le pkt.bytes 8
  let plain := aeadDecrypt k.receiving.key (counterNonce nonce) (pkt.bytes.drop 16) []
  if ← branch .decDecryptFailed plain.isNone then return none
  let some bytes := plain | invariant "unreachable"
  if ← branch .decTrimFailed false then return none
  return some {pkt with nonce, bytes}

def receiveAttemptTail (a : RxAttempt) : WGPrefix RxAttempt (Option RxPacket) := do
  let cowOk ← liftWGPrefix (hiddenAlloc .skbCowDataRx)
  if ← liftWGPrefix (WG.orM (branch .decCowDataFailed !cowOk) (branch .decTooManyFrags false)) then return none
  if ← liftWGPrefix (branch .decSgvecFailed false) then return none
  emitStatePrefix a
  liftWGPrefix (receiveAeadTail a.packet a.keyRead.value)

def receiveAttemptsObserved (pkt : RxPacket) : WGPrefix RxAttempt (Option RxPacket) := do
  if ← liftWGPrefix (branch .decNoKeypair false) then return none
  let keyRead ← captureWGRun (getKeypair pkt.keypair)
  let guardRead ← captureWGRun (receiveReject keyRead.value)
  if guardRead.value then
    let k ← liftWGPrefix (getKeypair pkt.keypair)
    liftWGPrefix (setKeypair pkt.keypair {k with receiving := {k.receiving with isValid := false}})
    return none
  receiveAttemptTail {packet := pkt, keyRead, guardRead}

theorem receiveAttemptTail_erases (a : RxAttempt) :
    ErasesStatePrefix (receiveAttemptTail a) (receiveTail a.packet a.keyRead.value) := by
  unfold receiveAttemptTail receiveTail
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro cowOk
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro cowBad
  split
  · exact erasesStatePrefix_pure _
  · apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro sgBad
    split
    · exact erasesStatePrefix_pure _
    · intro w ambient h
      change (runStatePrefix (do emitStatePrefix a; liftWGPrefix (receiveAeadTail a.packet a.keyRead.value)) w ambient h).1 = _
      simp only [runStatePrefix_bind, runStatePrefix_emit, liftWGPrefix, runStatePrefix_lift]
      rfl

theorem captureWGRun_bind_erases (a : WG.M α) (g : WGRunWitness α → WGPrefix E β)
    (f : α → WG.M β) (he : ∀ r, ErasesStatePrefix (g r) (f r.value)) :
    ErasesStatePrefix (captureWGRun a >>= g) (a >>= f) := by
  intro w ambient h
  change (runWGPrefix (captureWGRun a >>= g) w ambient h).1 = _
  simp only [runWGPrefix, runStatePrefix_bind]
  have hc := runWGPrefix_captureWGRun (E := E) a w ambient h
  simp only [runWGPrefix] at hc
  rw [hc]
  cases hr : (a.run w).run ambient with
  | error e => simp [hr, Except.map, StateT.run_bind]; rfl
  | ok out =>
    rcases out with ⟨⟨x, v⟩, ambient'⟩
    simpa only [hr, Except.map, StateT.run_bind, except_ok_bind, runStatePrefix] using
      he ⟨x, w, v, ambient, ambient'⟩ v ambient' h

theorem receiveAttemptsObserved_erases (pkt : RxPacket) :
    ErasesStatePrefix (receiveAttemptsObserved pkt) (decryptPacket pkt) := by
  rw [decryptPacket_factor]
  unfold receiveAttemptsObserved
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro noKey
  split
  · exact erasesStatePrefix_pure _
  · apply captureWGRun_bind_erases
    intro keyRead
    apply captureWGRun_bind_erases
    intro guardRead
    split
    · apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
      intro k
      apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
      intro _
      exact erasesStatePrefix_pure _
    · exact receiveAttemptTail_erases _

namespace ReceiveAttempts

variable {S T : Type}

def Good (h : List RxAttempt) : Prop := ∀ a ∈ h, a.Valid

def Keep (C : Prop) (h : List RxAttempt) (_ : S) : Prop := Good h ∧ C

theorem liftKeep (a : StateT S (Except Stop) α) (C : Prop) :
    PrefixEnsures (Keep C) Good (liftPrefix a) (fun _ => Keep C) :=
  PrefixEnsures.lift a (fun _ _ hi => hi.1) (fun _ _ _ _ hi _ => hi)

theorem liftForget (a : StateT S (Except Stop) α) (C : Prop) :
    PrefixEnsures (Keep C) Good (liftPrefix a) (fun _ => Keep True) :=
  (liftKeep a C).consequence (fun _ _ hi => hi) (fun _ _ _ hi => ⟨hi.1, trivial⟩)

theorem pureForget (x : α) (C : Prop) :
    PrefixEnsures (Keep (S := S) C) Good (pure x) (fun _ => Keep True) :=
  PrefixEnsures.pure (fun _ _ hi => hi.1) (fun _ _ hi => ⟨hi.1, trivial⟩)

theorem captureKeep (a : StateT S (Except Stop) α) (C : Prop) :
    PrefixEnsures (Keep C) Good (captureRun a)
      (fun r => Keep (C ∧ r.Valid a)) := by
  apply PrefixEnsures.captureRun _ (fun _ _ hi => hi.1)
  intro h w x v hi hr
  exact ⟨hi.1, hi.2, hr⟩

theorem emitGood (a : RxAttempt) :
    PrefixEnsures (Keep (S := S) a.Valid) Good (emitPrefix a) (fun _ => Keep True) := by
  intro w h hi
  have hg : Good (h ++ [a]) := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hi.1 b hb
    · have he : b = a := by simpa using hb
      subst b
      exact hi.2
  exact ⟨[a], by simp, by simpa using hg, by simpa [Keep] using hg⟩

theorem liftStateKeep (a : StateT S (StateT T (Except Stop)) α) (C : Prop) :
    StatePrefixEnsures (fun h s _ => Keep C h s) Good (liftStatePrefix a)
      (fun _ h s _ => Keep C h s) :=
  fun s => liftKeep (a.run s) C

theorem liftStateForget (a : StateT S (StateT T (Except Stop)) α) (C : Prop) :
    StatePrefixEnsures (fun h s _ => Keep C h s) Good (liftStatePrefix a)
      (fun _ h s _ => Keep True h s) :=
  fun s => liftForget (a.run s) C

theorem pureStateForget (x : α) (C : Prop) :
    StatePrefixEnsures (fun h (s : S) (_ : T) => Keep C h s) Good (pure x)
      (fun _ h s _ => Keep True h s) :=
  fun s => pureForget (x, s) C

theorem captureKeepWG (a : WG.M α) (C : Prop) :
    StatePrefixEnsures (fun h s _ => Keep C h s) Good (captureWGRun a)
      (fun r h s _ => Keep (C ∧ r.Valid a) h s) := by
  apply StatePrefixEnsures.captureWGRun _ (fun _ _ _ hi => hi.1)
  intro h w ambient x v ambient' hi hr
  exact ⟨hi.1, hi.2, hr⟩

theorem emitGoodState (a : RxAttempt) :
    StatePrefixEnsures (fun h (s : S) (_ : T) => Keep a.Valid h s) Good (emitStatePrefix a)
      (fun _ h s _ => Keep True h s) := by
  intro s t h hi
  have hg := emitGood (S := T) a t h hi
  exact hg

theorem tail_safe (a : RxAttempt) :
    StatePrefixEnsures (fun h s _ => Keep a.Valid h s) Good (receiveAttemptTail a) (fun _ h s _ => Keep True h s) := by
  unfold receiveAttemptTail
  apply StatePrefixEnsures.bind (liftStateKeep _ _)
  intro cowOk
  apply StatePrefixEnsures.bind (liftStateKeep _ _)
  intro cowBad
  split
  · exact pureStateForget _ _
  · apply StatePrefixEnsures.bind (liftStateKeep _ _)
    intro sgBad
    split
    · exact pureStateForget _ _
    · apply StatePrefixEnsures.bind (emitGoodState a)
      intro _
      exact liftStateForget _ _

theorem safe (pkt : RxPacket) :
    StatePrefixEnsures (fun h s _ => Keep True h s) Good (receiveAttemptsObserved pkt) (fun _ h s _ => Keep True h s) := by
  unfold receiveAttemptsObserved
  apply StatePrefixEnsures.bind (liftStateKeep _ True)
  intro noKey
  split
  · exact pureStateForget _ _
  · apply StatePrefixEnsures.bind (captureKeepWG _ True)
    intro keyRead
    apply StatePrefixEnsures.bind (captureKeepWG _ _)
    intro guardRead
    split
    · apply StatePrefixEnsures.bind (liftStateKeep _ _)
      intro k
      apply StatePrefixEnsures.bind (liftStateKeep _ _)
      intro _
      exact pureStateForget _ _
    · rename_i hf
      apply (tail_safe _).consequence
      · intro h w ambient hi
        have hz : guardRead.value = false := by simpa using hf
        have hr : ((receiveReject keyRead.value).run guardRead.before).run guardRead.ambientBefore =
            .ok ((false, guardRead.after), guardRead.ambientAfter) := by
          simpa [WGRunWitness.Valid, hz] using hi.2.2
        obtain ⟨valid, bound, clock⟩ := receiveReject_false keyRead.value _ _ _ _ hr
        exact ⟨hi.1, hi.2.1.2, hi.2.2, hz, valid, bound, clock⟩
      · intro _ _ _ _ hi
        exact hi

end ReceiveAttempts

/-- Allocation success reaches exactly one AEAD event. The equation is
independent of whether the tag authenticates. -/
theorem receiveAttemptTail_singleton (a : RxAttempt) (w u : WGWorld)
    (ambient allocatedAmbient : Ambient) (h : List RxAttempt)
    (ha : ((hiddenAlloc .skbCowDataRx : WG.M Bool).run w).run ambient =
      .ok ((true, u), allocatedAmbient)) :
    runWGPrefix (receiveAttemptTail a) w ambient h =
      (((receiveTail a.packet a.keyRead.value).run w).run ambient, h ++ [a]) := by
  unfold receiveAttemptTail receiveTail
  simp only [runWGPrefix, runStatePrefix_bind, liftWGPrefix, runStatePrefix_lift,
    ha, StateT.run_bind, except_ok_bind]
  simp [WG.orM, branch, StateT.run_monadLift, monadLift_self, branch_run,
    receiveAeadTail, runStatePrefix_bind, StateT.run_bind]
  rfl

/-- The concrete execution witnesses carried by the unique original attempt. -/
def receiveAttemptWitness (pkt : RxPacket) (w entered checked : WGWorld)
    (ambient enteredAmbient checkedAmbient : Ambient) (k : Keypair) : RxAttempt :=
  {packet := pkt,
    keyRead := ⟨k, w, entered, record ambient .decNoKeypair false, enteredAmbient⟩,
    guardRead := ⟨false, entered, checked, enteredAmbient, checkedAmbient⟩}

/-- Getter, guard and allocation success suffice for exactly one original
attempt. No premise mentions the authentication result. -/
theorem receiveAttemptsObserved_singleton (pkt : RxPacket)
    (w entered checked allocated : WGWorld)
    (ambient enteredAmbient checkedAmbient allocatedAmbient : Ambient)
    (k : Keypair) (h : List RxAttempt)
    (hg : ((getKeypair pkt.keypair).run w).run (record ambient .decNoKeypair false) =
      .ok ((k, entered), enteredAmbient))
    (hr : ((receiveReject k).run entered).run enteredAmbient =
      .ok ((false, checked), checkedAmbient))
    (ha : ((hiddenAlloc .skbCowDataRx : WG.M Bool).run checked).run checkedAmbient =
      .ok ((true, allocated), allocatedAmbient)) :
    runWGPrefix (receiveAttemptsObserved pkt) w ambient h =
      (((decryptPacket pkt).run w).run ambient,
        h ++ [receiveAttemptWitness pkt w entered checked ambient enteredAmbient checkedAmbient k]) := by
  have ht := receiveAttemptTail_singleton
    (receiveAttemptWitness pkt w entered checked ambient enteredAmbient checkedAmbient k)
    checked allocated checkedAmbient allocatedAmbient h ha
  rw [decryptPacket_factor]
  have capture {α : Type} (a : WG.M α) (wg : WGWorld) (amb : Ambient) (hist : List RxAttempt) :
      runStatePrefix (captureWGRun a) wg amb hist =
        (((a.run wg).run amb).map
          (fun ((x, wg'), amb') => ((⟨x, wg, wg', amb, amb'⟩, wg'), amb')), hist) :=
    runWGPrefix_captureWGRun a wg amb hist
  unfold receiveAttemptsObserved
  simpa only [runWGPrefix, runStatePrefix_bind, liftWGPrefix, runStatePrefix_lift,
    branch, StateT.run_monadLift, monadLift_self, branch_run, capture,
    StateT.run_pure, except_pure, StateT.run_bind, except_ok_bind, hg, hr, Bool.false_eq_true, ↓reduceIte,
    receiveAttemptWitness, Except.map] using ht

/-- Failed authentication still emits the attempt and returns the original
none endpoint, with all four preparation/authentication branch records. -/
theorem receiveAttemptsObserved_failed_tag (pkt : RxPacket)
    (w entered checked allocated : WGWorld)
    (ambient enteredAmbient checkedAmbient allocatedAmbient : Ambient)
    (k : Keypair) (h : List RxAttempt)
    (hg : ((getKeypair pkt.keypair).run w).run (record ambient .decNoKeypair false) =
      .ok ((k, entered), enteredAmbient))
    (hr : ((receiveReject k).run entered).run enteredAmbient =
      .ok ((false, checked), checkedAmbient))
    (ha : ((hiddenAlloc .skbCowDataRx : WG.M Bool).run checked).run checkedAmbient =
      .ok ((true, allocated), allocatedAmbient))
    (hbad : aeadDecrypt k.receiving.key (counterNonce (u64le pkt.bytes 8)) (pkt.bytes.drop 16) [] = none) :
    runWGPrefix (receiveAttemptsObserved pkt) w ambient h =
      (.ok ((none, allocated),
        record (record (record (record allocatedAmbient .decCowDataFailed false)
          .decTooManyFrags false) .decSgvecFailed false) .decDecryptFailed true),
        h ++ [receiveAttemptWitness pkt w entered checked ambient enteredAmbient checkedAmbient k]) := by
  rw [receiveAttemptsObserved_singleton pkt w entered checked allocated
    ambient enteredAmbient checkedAmbient allocatedAmbient k h hg hr ha]
  rw [decryptPacket_factor]
  simp [StateT.run_bind, branch, StateT.run_monadLift, monadLift_self,
    branch_run, hg, hr, receiveTail, ha, WG.orM, hbad]

end Leanux.Proofs.WG.KeyTimes
