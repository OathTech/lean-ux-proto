import Leanux.Proofs.WG.KeyTimes.Clock
import Leanux.Proofs.WG.CounterWindow.Bounds

/-! Local admission boundaries of the original receive operation. Successful
authenticated decryption and later replay-window acceptance are distinct. -/
namespace Leanux.Proofs.WG.KeyTimes
open Leanux Leanux.WG Leanux.Proofs.WG.CounterWindow

def receiveReject (k : Keypair) : M Bool :=
  WG.orM (branch .decKeyInvalid !k.receiving.isValid) do
    WG.orM (branchExpired .decKeyExpired k.receiving.birthdate REJECT_AFTER_TIME)
      (branchCmp .decCounterLimit (k.receivingCounter.counter ≥ REJECT_AFTER_MESSAGES)
        k.receivingCounter.counter REJECT_AFTER_MESSAGES)

def receiveTail (pkt : RxPacket) (k : Keypair) : M (Option RxPacket) := do
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

theorem receiveReject_false (k : Keypair) (w v : World)
    (h : (receiveReject k).run w = .ok (false, v)) :
    k.receiving.isValid = true ∧ k.receivingCounter.counter < REJECT_AFTER_MESSAGES ∧
      ∃ now u, (hiddenClock64 .birthdateExpired).run (record w .decKeyInvalid false) = .ok (now, u) ∧
        ¬ deadline k.receiving.birthdate REJECT_AFTER_TIME ≤ now := by
  unfold receiveReject WG.orM at h
  simp only [StateT.run_bind, branch_run, except_ok_bind] at h
  cases hv : k.receiving.isValid with
  | false => simp [hv] at h
  | true =>
    simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    cases he : (branchExpired .decKeyExpired k.receiving.birthdate REJECT_AFTER_TIME).run
        (record w .decKeyInvalid false) with
    | error e => simp [he] at h
    | ok out =>
      rcases out with ⟨expired, t⟩
      cases expired with
      | true => simp [he] at h
      | false =>
        simp only [StateT.run_bind, he, except_ok_bind, Bool.false_eq_true, ↓reduceIte, branchCmp_run, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨now, u, hc, hn, _⟩ := branchExpired_false .decKeyExpired
          k.receiving.birthdate REJECT_AFTER_TIME _ t he
        exact ⟨rfl, by simpa using h.1, now, u, hc, hn⟩

theorem getKeypair_return (id : KeypairId) (w v : World) (k : Keypair)
    (hr : (getKeypair id).run w = .ok (k, v)) :
    v = w ∧ ∃ d, w.k.wg = some d ∧ d.keypairs[id]? = some k := by
  cases hd : w.k.wg with
  | none => simp [getKeypair, getDev, getK, hd, invariant] at hr
  | some d =>
    cases hk : d.keypairs[id]? with
    | none => simp [getKeypair, getDev, getK, hd, hk, invariant] at hr
    | some actual =>
      have hg := getKeypair_run w d id actual hd hk
      rw [hg] at hr
      cases hr
      exact ⟨rfl, d, rfl, hk⟩

theorem decryptPacket_admission (pkt out : RxPacket) (w v : World)
    (hr : (decryptPacket pkt).run w = .ok (some out, v)) :
    ∃ d k, w.k.wg = some d ∧ d.keypairs[pkt.keypair]? = some k ∧
      k.receiving.isValid = true ∧ k.receivingCounter.counter < REJECT_AFTER_MESSAGES ∧
      ∃ now u, (hiddenClock64 .birthdateExpired).run
        (record (record w .decNoKeypair false) .decKeyInvalid false) = .ok (now, u) ∧
        ¬ deadline k.receiving.birthdate REJECT_AFTER_TIME ≤ now := by
  rw [decryptPacket_factor] at hr
  simp only [StateT.run_bind, branch_run, except_ok_bind, Bool.false_eq_true, ↓reduceIte] at hr
  cases hg : (getKeypair pkt.keypair).run (record w .decNoKeypair false) with
  | error e => simp [hg] at hr
  | ok result =>
    rcases result with ⟨k, entered⟩
    obtain ⟨he, d, hd, hk⟩ := getKeypair_return pkt.keypair _ entered k hg
    subst entered
    simp only [hg, except_ok_bind] at hr
    cases hj : (receiveReject k).run (record w .decNoKeypair false) with
    | error e => simp [hj] at hr
    | ok result =>
      rcases result with ⟨reject, checked⟩
      cases reject with
      | false =>
        obtain ⟨valid, bound, now, u, hc, hn⟩ := receiveReject_false k _ checked hj
        exact ⟨d, k, hd, hk, valid, bound, now, u, hc, hn⟩
      | true =>
        simp only [StateT.run_bind, hj, except_ok_bind, ↓reduceIte] at hr
        cases hp : (getKeypair pkt.keypair).run checked with
        | error e => simp [hp] at hr
        | ok result =>
          rcases result with ⟨fresh, updated⟩
          simp [hp, setKeypair_run] at hr

theorem counterValidate_wire_bound (kp : KeypairId) (nonce : Nat) (w v : World)
    (hr : (counterValidate kp nonce).run w = .ok (true, v)) :
    nonce < REJECT_AFTER_MESSAGES := by
  by_cases hn : nonce < REJECT_AFTER_MESSAGES
  · exact hn
  exfalso
  have hn' : nonce ≥ REJECT_AFTER_MESSAGES := by omega
  unfold counterValidate at hr
  simp only [StateT.run_bind] at hr
  cases hg : (getKeypair kp).run w with
  | error e => simp [hg] at hr
  | ok result =>
    rcases result with ⟨k, entered⟩
    simp only [hg, except_ok_bind] at hr
    by_cases hc : k.receivingCounter.counter ≥ REJECT_AFTER_MESSAGES + 1
    · simp [WG.orM, branchCmp_run, hc] at hr
    · simp [WG.orM, branchCmp_run, hc, hn'] at hr

end Leanux.Proofs.WG.KeyTimes
