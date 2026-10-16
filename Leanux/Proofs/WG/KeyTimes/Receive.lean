import Leanux.Proofs.WG.KeyTimes.Clock
import Leanux.Proofs.WG.CounterWindow.Bounds

/-! Local admission boundaries of the original receive operation. Successful
authenticated decryption and later replay-window acceptance are distinct. -/
namespace Leanux.Proofs.WG.KeyTimes
open Leanux Leanux.WG Leanux.Proofs.WG.CounterWindow

def receiveReject (k : Keypair) : WG.M Bool :=
  WG.orM (branch .decKeyInvalid !k.receiving.isValid) do
    WG.orM (branchExpired .decKeyExpired k.receiving.birthdate REJECT_AFTER_TIME)
      (branchCmp .decCounterLimit (k.receivingCounter.counter ≥ REJECT_AFTER_MESSAGES)
        k.receivingCounter.counter REJECT_AFTER_MESSAGES)

def receiveTail (pkt : RxPacket) (k : Keypair) : WG.M (Option RxPacket) := do
  let nonce := u64le pkt.bytes 8
  let cowOk ← hiddenAlloc .skbCowDataRx
  if ← WG.orM (branch .decCowDataFailed !cowOk) (branch .decTooManyFrags false) then return none
  if ← branch .decSgvecFailed false then return none
  let plain := aeadDecrypt k.receiving.key (counterNonce nonce) (pkt.bytes.drop 16) []
  if ← branch .decDecryptFailed plain.isNone then return none
  let some bytes := plain | invariant "unreachable"
  if ← branch .decTrimFailed false then return none
  return some {pkt with nonce, bytes}

theorem decryptPacket_factor (pkt : RxPacket) :
    decryptPacket pkt = (do
      if ← branch .decNoKeypair false then return none
      let k ← getKeypair pkt.keypair
      let reject ← receiveReject k
      if reject then
        let k ← getKeypair pkt.keypair
        setKeypair pkt.keypair {k with receiving := {k.receiving with isValid := false}}
        return none
      receiveTail pkt k) := by
  rfl

theorem receiveReject_false (k : Keypair) (w v : WGWorld) (ambient ambient' : Ambient)
    (h : ((receiveReject k).run w).run ambient = .ok ((false, v), ambient')) :
    k.receiving.isValid = true ∧ k.receivingCounter.counter < REJECT_AFTER_MESSAGES ∧
      ∃ now u clockAmbient,
        ((hiddenClock64 .birthdateExpired : WG.M Int64).run w).run
          (record ambient .decKeyInvalid false) = .ok ((now, u), clockAmbient) ∧
        ¬ deadline k.receiving.birthdate REJECT_AFTER_TIME ≤ now := by
  unfold receiveReject WG.orM at h
  simp only [branch, branchCmp, StateT.run_monadLift, monadLift_self, StateT.run_bind,
    branch_run, except_ok_bind, StateT.run_pure, except_pure] at h
  cases hv : k.receiving.isValid with
  | false => simp [hv] at h
  | true =>
    simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    cases he : ((branchExpired .decKeyExpired k.receiving.birthdate REJECT_AFTER_TIME).run w).run
        (record ambient .decKeyInvalid false) with
    | error e =>
      simp only [StateT.run_bind, he] at h
      change (Except.error e : Except Stop _) = _ at h
      cases h
    | ok out =>
      rcases out with ⟨⟨expired, t⟩, checkedAmbient⟩
      cases expired with
      | true => simp [he] at h
      | false =>
        simp only [he, except_ok_bind, Bool.false_eq_true, ↓reduceIte,
          StateT.run_monadLift, monadLift_self, StateT.run_bind, branchCmp_run,
          StateT.run_pure, except_pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨now, u, clockAmbient, hc, hn, _, _⟩ := branchExpired_false .decKeyExpired
          k.receiving.birthdate REJECT_AFTER_TIME w t _ checkedAmbient he
        exact ⟨rfl, by simpa using h.1.1, now, u, clockAmbient, hc, hn⟩

theorem getKeypair_return (id : KeypairId) (w v : WGWorld) (k : Keypair)
    (ambient ambient' : Ambient)
    (hr : ((getKeypair id).run w).run ambient = .ok ((k, v), ambient')) :
    v = w ∧ ambient' = ambient ∧ ∃ d, w.dev = some d ∧ d.keypairs[id]? = some k := by
  cases hd : w.dev with
  | none =>
    simp [getKeypair, getDev, hd, invariant, AmbientM.invariant] at hr
    change (Except.error _ : Except Stop _) = _ at hr
    cases hr
  | some d =>
    cases hk : d.keypairs[id]? with
    | none =>
      simp [getKeypair, getDev, hd, hk, invariant, AmbientM.invariant] at hr
      change (Except.error _ : Except Stop _) = _ at hr
      cases hr
    | some actual =>
      have hg := getKeypair_run w ambient d id actual hd hk
      rw [hg] at hr
      cases hr
      exact ⟨rfl, rfl, d, rfl, hk⟩

theorem decryptPacket_admission (pkt out : RxPacket) (w v : WGWorld)
    (ambient ambient' : Ambient)
    (hr : ((decryptPacket pkt).run w).run ambient = .ok ((some out, v), ambient')) :
    ∃ d k, w.dev = some d ∧ d.keypairs[pkt.keypair]? = some k ∧
      k.receiving.isValid = true ∧ k.receivingCounter.counter < REJECT_AFTER_MESSAGES ∧
      ∃ now u clockAmbient, ((hiddenClock64 .birthdateExpired : WG.M Int64).run w).run
        (record (record ambient .decNoKeypair false) .decKeyInvalid false) =
          .ok ((now, u), clockAmbient) ∧
        ¬ deadline k.receiving.birthdate REJECT_AFTER_TIME ≤ now := by
  rw [decryptPacket_factor] at hr
  simp only [branch, StateT.run_monadLift, monadLift_self, StateT.run_bind,
    branch_run, except_ok_bind, StateT.run_pure, except_pure, Bool.false_eq_true, ↓reduceIte] at hr
  cases hg : ((getKeypair pkt.keypair).run w).run (record ambient .decNoKeypair false) with
  | error e =>
    simp only [hg] at hr
    change (Except.error e : Except Stop _) = _ at hr
    cases hr
  | ok result =>
    rcases result with ⟨⟨k, entered⟩, enteredAmbient⟩
    obtain ⟨he, ha, d, hd, hk⟩ := getKeypair_return pkt.keypair w entered k _ enteredAmbient hg
    subst entered
    subst enteredAmbient
    simp only [hg, except_ok_bind] at hr
    cases hj : ((receiveReject k).run w).run (record ambient .decNoKeypair false) with
    | error e =>
      simp only [hj] at hr
      change (Except.error e : Except Stop _) = _ at hr
      cases hr
    | ok result =>
      rcases result with ⟨⟨reject, checked⟩, checkedAmbient⟩
      cases reject with
      | false =>
        obtain ⟨valid, bound, now, u, clockAmbient, hc, hn⟩ :=
          receiveReject_false k w checked _ checkedAmbient hj
        exact ⟨d, k, hd, hk, valid, bound, now, u, clockAmbient, hc, hn⟩
      | true =>
        simp only [hj, except_ok_bind, ↓reduceIte] at hr
        cases hp : ((getKeypair pkt.keypair).run checked).run checkedAmbient with
        | error e =>
          simp only [StateT.run_bind, hp] at hr
          change (Except.error e : Except Stop _) = _ at hr
          cases hr
        | ok result =>
          rcases result with ⟨⟨fresh, updated⟩, updatedAmbient⟩
          simp [hp, setKeypair_run] at hr
          cases hr

theorem counterValidate_wire_bound (kp : KeypairId) (nonce : Nat)
    (w v : WGWorld) (ambient ambient' : Ambient)
    (hr : ((counterValidate kp nonce).run w).run ambient = .ok ((true, v), ambient')) :
    nonce < REJECT_AFTER_MESSAGES := by
  by_cases hn : nonce < REJECT_AFTER_MESSAGES
  · exact hn
  exfalso
  have hn' : nonce ≥ REJECT_AFTER_MESSAGES := by omega
  unfold counterValidate at hr
  simp only [StateT.run_bind] at hr
  cases hg : ((getKeypair kp).run w).run ambient with
  | error e =>
    simp only [hg] at hr
    change (Except.error e : Except Stop _) = _ at hr
    cases hr
  | ok result =>
    rcases result with ⟨⟨k, entered⟩, enteredAmbient⟩
    simp only [hg, except_ok_bind] at hr
    by_cases hc : k.receivingCounter.counter ≥ REJECT_AFTER_MESSAGES + 1
    · simp [WG.orM, branchCmp, StateT.run_monadLift, monadLift_self, StateT.run_bind,
        branchCmp_run, hc] at hr
    · simp [WG.orM, branchCmp, StateT.run_monadLift, monadLift_self, StateT.run_bind,
        branchCmp_run, hc, hn'] at hr

end Leanux.Proofs.WG.KeyTimes
