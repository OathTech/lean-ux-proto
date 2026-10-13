import Leanux.Spikes.Ghost
import Leanux.WG.Keypair

/-! Operational framing, including the lifetime distinction needed when a
device-local keypair slot is deleted and later reused. -/
namespace Leanux.Spikes.Framing
open Leanux Leanux.WG

def Hoare (action : M α) (pre : World → Prop)
    (post : α → World → Prop) : Prop :=
  ∀ w a w', pre w → action.run w = .ok (a, w') → post a w'

def Preserves (pre : World → Prop) (action : M α) : Prop :=
  Hoare action pre (fun _ => pre)

theorem hoare_pure (a : α) (P : World → Prop) :
    Hoare (pure a) P (fun b w => b = a ∧ P w) := by
  intro w b w' hp hr
  cases hr
  exact ⟨rfl, hp⟩

theorem hoare_bind (a : M α) (f : α → M β)
    (ha : Hoare a P Q) (hf : ∀ x, Hoare (f x) (Q x) R) :
    Hoare (a >>= f) P R := by
  intro w b w' hp hr
  simp only [StateT.run_bind] at hr
  cases he : a.run w with
  | error e => simp [he] at hr
  | ok out =>
    rcases out with ⟨x, v⟩
    simp only [he, Leanux.Spikes.Window.except_ok_bind] at hr
    exact hf x v b w' (ha w x v hp he) hr

theorem hoare_consequence (h : Hoare a P Q)
    (hp : ∀ w, P' w → P w) (hq : ∀ x w, Q x w → Q' x w) :
    Hoare a P' Q' := fun w x w' hpre hrun => hq x w' (h w x w' (hp w hpre) hrun)

theorem preserves_bind (ha : Preserves P a) (hf : ∀ x, Preserves P (f x)) :
    Preserves P (a >>= f) := hoare_bind a f ha hf

theorem preserves_pure (a : α) : Preserves P (pure a) :=
  hoare_consequence (hoare_pure a P) (fun _ h => h) (fun _ _ h => h.2)

theorem hoare_get (P : World → Prop) :
    Hoare (get : M World) P (fun v w => v = w ∧ P w) := by
  intro w v w' hp hr
  cases hr
  exact ⟨rfl, hp⟩

theorem hoare_modify (f : World → World) (h : ∀ w, P w → Q () (f w)) :
    Hoare (modify f : M Unit) P Q := by
  intro w a w' hp hr
  cases hr
  exact h w hp

theorem hoare_throw (e : Stop) : Hoare (throw e : M α) P Q := by
  intro w a w' hp hr
  cases hr

/-- A protected lifetime may disappear. Any surviving copy in its slot must
retain its counter. The frontier condition rules out reusing its lifetime ID
when a new keypair is allocated. -/
def Protected (slot stamp : Nat) (counter : ReplayCounter) (w : World) : Prop :=
  stamp ≤ w.k.keypairCounter ∧
  ∀ d k, w.k.wg = some d → d.keypairs[slot]? = some k →
    k.internalId = stamp → k.receivingCounter = counter

theorem protected_same_kernel (h : Protected slot stamp counter w)
    (hk : w'.k = w.k) : Protected slot stamp counter w' := by
  simpa only [Protected, hk] using h

def SameKernel (action : M α) : Prop :=
  ∀ w a w', action.run w = .ok (a, w') → w'.k = w.k

theorem sameKernel_preserves (h : SameKernel a) :
    Preserves (Protected slot stamp counter) a :=
  fun w x w' hp hr => protected_same_kernel hp (h w x w' hr)

theorem sameKernel_pure (a : α) : SameKernel (pure a) := by
  intro w x w' hr
  cases hr
  rfl

theorem sameKernel_bind (ha : SameKernel a) (hf : ∀ x, SameKernel (f x)) :
    SameKernel (a >>= f) := by
  intro w b w' hr
  simp only [StateT.run_bind] at hr
  cases he : a.run w with
  | error e => simp [he] at hr
  | ok out =>
    rcases out with ⟨x, v⟩
    simp only [he, Leanux.Spikes.Window.except_ok_bind] at hr
    exact (hf x v b w' hr).trans (ha w x v he)

theorem sameKernel_branch (d : Decision) (b : Bool) : SameKernel (branch d b) := by
  intro w x w' hr
  cases hr
  rfl

theorem getKeypair_spec (query slot stamp : Nat) (counter : ReplayCounter) :
    Hoare (getKeypair query) (Protected slot stamp counter)
      (fun k w => Protected slot stamp counter w ∧
        (query = slot → k.internalId = stamp → k.receivingCounter = counter)) := by
  intro w k w' hp hr
  cases hd : w.k.wg with
  | none => simp [getKeypair, getDev, getK, hd, invariant,
      StateT.run_bind, StateT.run_get] at hr
  | some d =>
    cases hk : d.keypairs[query]? with
    | none => simp [getKeypair, getDev, getK, hd, hk, invariant,
        StateT.run_bind, StateT.run_get] at hr
    | some value =>
      rw [Leanux.Spikes.Window.getKeypair_run w d query value hd hk] at hr
      cases hr
      refine ⟨hp, ?_⟩
      intro hquery hstamp
      subst query
      exact hp.2 d k hd hk hstamp

theorem setKeypair_preserves (query slot stamp : Nat) (counter : ReplayCounter)
    (k : Keypair)
    (hk : query = slot → k.internalId = stamp → k.receivingCounter = counter) :
    Preserves (Protected slot stamp counter) (setKeypair query k) := by
  intro w a w' hp hr
  rw [Leanux.Spikes.Window.setKeypair_run] at hr
  cases hr
  rcases hp with ⟨hfront, hp⟩
  refine ⟨hfront, ?_⟩
  intro d v hd hv hid
  cases hw : w.k.wg with
  | none => simp [Leanux.Spikes.Window.store, hw] at hd
  | some old =>
    simp only [Leanux.Spikes.Window.store, hw, Option.map_some, Option.some.injEq] at hd
    subst d
    simp only [Std.TreeMap.getElem?_insert] at hv
    by_cases hq : query = slot
    · subst query
      simp at hv
      subst v
      exact hk rfl hid
    · simp [hq] at hv
      exact hp old v hw hv hid

@[simp] theorem counterAt_store_other (w : World) (query other : KeypairId)
    (k : Keypair) (hne : query ≠ other) :
    Window.counterAt (Window.store w query k) other = Window.counterAt w other := by
  cases hd : w.k.wg <;>
    simp [Window.counterAt, Window.store, hd, Std.TreeMap.getElem?_insert, hne]

theorem cExecution_other (query other nonce : Nat) (k : Keypair) (w : World)
    (hne : query ≠ other) :
    Window.counterAt (Window.cExecution query nonce k w).2 other =
      Window.counterAt w other := by
  by_cases h1 : k.receivingCounter.counter ≥ REJECT_AFTER_MESSAGES + 1
  · simp [Window.cExecution, h1]
  · by_cases h2 : nonce ≥ REJECT_AFTER_MESSAGES
    · simp [Window.cExecution, h1, h2]
    · by_cases h3 : 8128 + (nonce + 1) < k.receivingCounter.counter
      · simp [Window.cExecution, h1, h2, h3]
      · by_cases h4 : nonce + 1 > k.receivingCounter.counter <;>
          simp [Window.cExecution, h1, h2, h3, h4, counterAt_store_other, hne]

/-- The actual validator, whether it accepts or rejects, leaves all other
keypairs' receive windows unchanged. -/
theorem counterValidate_other (query other nonce : Nat) (w w' : World)
    (d : Device) (k : Keypair) (ok : Bool)
    (hd : w.k.wg = some d) (hk : d.keypairs[query]? = some k)
    (hs : k.receivingCounter.backtrack.size = 128) (hne : query ≠ other)
    (hr : (counterValidate query nonce).run w = .ok (ok, w')) :
    Window.counterAt w' other = Window.counterAt w other := by
  rw [Window.counterValidate_execution w d query k nonce hd hk hs] at hr
  have hw := congrArg Prod.snd (Except.ok.inj hr)
  dsimp only at hw
  rw [← hw]
  exact cExecution_other query other nonce k w hne

end Leanux.Spikes.Framing
