import Leanux.Proofs.Framing.Hoare
import Leanux.Proofs.WG.CounterWindow.Refinement
import Leanux.WG.Keypair

/-! Operational framing, including the lifetime distinction needed when a
device-local keypair slot is deleted and later reused. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG

/-- A protected lifetime may disappear. Any surviving copy in its slot must
retain its counter. The frontier condition rules out reusing its lifetime ID
when a new keypair is allocated. -/
def Protected (slot stamp : Nat) (counter : ReplayCounter) (w : WGWorld) : Prop :=
  stamp ≤ w.keypairCounter ∧
  ∀ d k, w.dev = some d → d.keypairs[slot]? = some k →
    k.internalId = stamp → k.receivingCounter = counter

theorem getKeypair_spec (query slot stamp : Nat) (counter : ReplayCounter) :
    Hoare (getKeypair query) (Protected slot stamp counter)
      (fun k w => Protected slot stamp counter w ∧
        (query = slot → k.internalId = stamp → k.receivingCounter = counter)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient k w' ambient' hp hr
  cases hd : w.dev with
  | none =>
    simp [getKeypair, getDev, hd, invariant, AmbientM.invariant] at hr
    cases hr
  | some d =>
    cases hk : d.keypairs[query]? with
    | none =>
      simp [getKeypair, getDev, hd, hk, invariant, AmbientM.invariant] at hr
      cases hr
    | some value =>
      rw [Leanux.Proofs.WG.CounterWindow.getKeypair_run w ambient d query value hd hk] at hr
      cases hr
      refine ⟨hp, ?_⟩
      intro hquery hstamp
      subst query
      exact hp.2 d k hd hk hstamp

theorem setKeypair_preserves (query slot stamp : Nat) (counter : ReplayCounter)
    (k : Keypair)
    (hk : query = slot → k.internalId = stamp → k.receivingCounter = counter) :
    Preserves (Protected slot stamp counter) (setKeypair query k) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient a w' ambient' hp hr
  rw [Leanux.Proofs.WG.CounterWindow.setKeypair_run] at hr
  cases hr
  rcases hp with ⟨hfront, hp⟩
  refine ⟨hfront, ?_⟩
  intro d v hd hv hid
  cases hw : w.dev with
  | none => simp [Leanux.Proofs.WG.CounterWindow.store, hw] at hd
  | some old =>
    simp only [Leanux.Proofs.WG.CounterWindow.store, hw, Option.map_some, Option.some.injEq] at hd
    subst d
    simp only [Std.TreeMap.getElem?_insert] at hv
    by_cases hq : query = slot
    · subst query
      simp at hv
      subst v
      exact hk rfl hid
    · simp [hq] at hv
      exact hp old v hw hv hid

@[simp] theorem counterAt_store_other (w : WGWorld) (query other : KeypairId)
    (k : Keypair) (hne : query ≠ other) :
    Leanux.Proofs.WG.CounterWindow.counterAt (Leanux.Proofs.WG.CounterWindow.store w query k) other = Leanux.Proofs.WG.CounterWindow.counterAt w other := by
  cases hd : w.dev <;>
    simp [Leanux.Proofs.WG.CounterWindow.counterAt, Leanux.Proofs.WG.CounterWindow.store, hd, Std.TreeMap.getElem?_insert, hne]

theorem cExecution_other (query other nonce : Nat) (k : Keypair) (w : WGWorld) (ambient : Ambient)
    (hne : query ≠ other) :
    Leanux.Proofs.WG.CounterWindow.counterAt (Leanux.Proofs.WG.CounterWindow.cExecution query nonce k w ambient).1.2 other =
      Leanux.Proofs.WG.CounterWindow.counterAt w other := by
  by_cases h1 : k.receivingCounter.counter ≥ REJECT_AFTER_MESSAGES + 1
  · simp [Leanux.Proofs.WG.CounterWindow.cExecution, h1]
  · by_cases h2 : nonce ≥ REJECT_AFTER_MESSAGES
    · simp [Leanux.Proofs.WG.CounterWindow.cExecution, h1, h2]
    · by_cases h3 : 8128 + (nonce + 1) < k.receivingCounter.counter
      · simp [Leanux.Proofs.WG.CounterWindow.cExecution, h1, h2, h3]
      · by_cases h4 : nonce + 1 > k.receivingCounter.counter <;>
          simp [Leanux.Proofs.WG.CounterWindow.cExecution, h1, h2, h3, h4, counterAt_store_other, hne]

/-- The actual validator, whether it accepts or rejects, leaves all other
keypairs' receive windows unchanged. -/
theorem counterValidate_other (query other nonce : Nat) (w w' : WGWorld) (ambient ambient' : Ambient)
    (d : Device) (k : Keypair) (ok : Bool)
    (hd : w.dev = some d) (hk : d.keypairs[query]? = some k)
    (hs : k.receivingCounter.backtrack.size = 128) (hne : query ≠ other)
    (hr : ((counterValidate query nonce).run w).run ambient = .ok ((ok, w'), ambient')) :
    Leanux.Proofs.WG.CounterWindow.counterAt w' other = Leanux.Proofs.WG.CounterWindow.counterAt w other := by
  rw [Leanux.Proofs.WG.CounterWindow.counterValidate_execution w ambient d query k nonce hd hk hs] at hr
  have hw := congrArg (fun out => out.1.2) (Except.ok.inj hr)
  dsimp only at hw
  rw [← hw]
  exact cExecution_other query other nonce k w ambient hne

end Leanux.Proofs.Framing
