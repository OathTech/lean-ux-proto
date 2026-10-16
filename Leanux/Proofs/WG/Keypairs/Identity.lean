import Leanux.Proofs.WG.Keypairs.LifetimeMirror

/-! Lifetime identities projected from the current keypair store.
Deletion is absence from that store. A numeric slot may be reused, but a
previously allocated identity cannot return after it has disappeared. -/
namespace Leanux.Proofs.WG.Keypairs
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.CounterWindow

/-- The keypair store contains no object with this allocation identity. -/
def LifetimeAbsent (s : Snapshot) (stamp : Nat) : Prop :=
  ∀ i c, s.slots i = some c → c.stamp ≠ stamp

/-- Validator updates retain the allocation frontier; ordinary transitions
only keep it or advance it with an allocation. -/
theorem Evolution.frontier_mono (he : Evolution s h t g) :
    s.frontier ≤ t.frontier := by
  induction he with
  | refl => exact Nat.le_refl _
  | ordinary ho => exact ho.frontier_mono
  | validate => exact Nat.le_refl _
  | trans _ _ ih₁ ih₂ => exact Nat.le_trans ih₁ ih₂

/-- Every old identity in a final slot already occupied that slot initially.
The counter may have changed through successful or rejected validator calls. -/
theorem Evolution.old_identity (he : Evolution s h t g)
    (hc : t.slots i = some c) (hb : c.stamp ≤ s.frontier) :
    ∃ old, s.slots i = some old ∧ old.stamp = c.stamp := by
  induction he generalizing c with
  | refl => exact ⟨c, hc, rfl⟩
  | ordinary ho => exact ⟨c, ho.old_slot hc hb, rfl⟩
  | @validate saved s h j hsaved nonce =>
    by_cases hij : i = j
    · subst i
      simp [Leanux.Proofs.WG.Keypairs.validate] at hc
      subst c
      exact ⟨saved, hsaved, rfl⟩
    · exact ⟨c, by simpa [Leanux.Proofs.WG.Keypairs.validate, hij] using hc, rfl⟩
  | trans h₁ _ ih₁ ih₂ =>
    obtain ⟨mid, hmid, hstamp⟩ := ih₂ hc (Nat.le_trans hb h₁.frontier_mono)
    obtain ⟨old, hold, hstamp'⟩ := ih₁ hmid (by simpa [hstamp] using hb)
    exact ⟨old, hold, hstamp'.trans hstamp⟩

/-- An absent identity below the allocation frontier never reappears anywhere
in any finite evolution, including validator calls and slot reuse. -/
theorem Evolution.absent_preserved (he : Evolution s h t g)
    (stamp : Nat) (hb : stamp ≤ s.frontier) (ha : LifetimeAbsent s stamp) :
    LifetimeAbsent t stamp := by
  intro i c hc hstamp
  obtain ⟨old, hold, hid⟩ := he.old_identity hc (by simpa [hstamp] using hb)
  exact ha i old hold (hid.trans hstamp)

/-- An empty slot can later contain only an identity allocated after the
starting frontier. This permits slot reuse without identifying the objects. -/
theorem Evolution.empty_slot_fresh (he : Evolution s h t g)
    (hi : s.slots i = none) (hc : t.slots i = some c) :
    s.frontier < c.stamp := by
  by_cases hb : c.stamp ≤ s.frontier
  · obtain ⟨old, hold, _⟩ := he.old_identity hc hb
    simp [hi] at hold
  · omega

/-- Once a previously allocated identity is absent at an intermediate state,
all later evolution states remain free of it. The reachable-state invariant
supplies the original allocation bound, rather than assuming freshness. -/
theorem Evolution.released_absent (first : Evolution s h t g)
    (later : Evolution t g u k) (hi : Inv s h)
    (hc : s.slots i = some c) (ha : LifetimeAbsent t c.stamp) :
    LifetimeAbsent u c.stamp :=
  later.absent_preserved c.stamp
    (Nat.le_trans (hi.bounded i c hc) first.frontier_mono) ha

/-- A successful original getter returns exactly the current store object
and leaves both WG and Ambient unchanged, including its lifetime identity. -/
theorem getKeypair_current (i : KeypairId) (w w' : WGWorld)
    (ambient ambient' : Ambient) (k : Keypair)
    (hr : ((getKeypair i).run w).run ambient = .ok ((k, w'), ambient')) :
    w' = w ∧ ambient' = ambient ∧ (snapshot w).slots i = some (cell k) := by
  cases hd : w.dev with
  | none =>
    simp [getKeypair, getDev, hd, invariant, AmbientM.invariant] at hr
    cases hr
  | some d =>
    cases hk : d.keypairs[i]? with
    | none =>
      simp [getKeypair, getDev, hd, hk, invariant, AmbientM.invariant] at hr
      cases hr
    | some actual =>
      rw [getKeypair_run w ambient d i actual hd hk] at hr
      cases hr
      exact ⟨rfl, rfl, snapshot_lookup w d i k hd hk⟩

/-- Looking up a slot cannot resolve an allocation identity absent from the
current store, even when that slot has since been reused. -/
theorem getKeypair_absent_identity (i : KeypairId) (w w' : WGWorld)
    (ambient ambient' : Ambient)
    (k : Keypair) (stamp : Nat) (ha : LifetimeAbsent (snapshot w) stamp)
    (hr : ((getKeypair i).run w).run ambient = .ok ((k, w'), ambient')) : k.internalId ≠ stamp :=
  ha i (cell k) (getKeypair_current i w w' ambient ambient' k hr).2.2

end Leanux.Proofs.WG.Keypairs
