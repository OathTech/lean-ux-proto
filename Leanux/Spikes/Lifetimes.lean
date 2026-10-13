import Leanux.Spikes.Ghost

/-! A receive-state projection with explicit allocation lifetimes. Ordinary
steps can delete slots or allocate a fresh lifetime, but cannot alter a
surviving window. The history invariant is independent of mirror bookkeeping. -/
namespace Leanux.Spikes.Lifetimes
open Leanux Leanux.WG Leanux.Spikes.Window Leanux.Spikes.Ghost

@[ext] structure Cell where
  stamp : Nat
  counter : ReplayCounter

@[ext] structure Snapshot where
  frontier : Nat
  slots : Nat → Option Cell

def cell (k : Keypair) : Cell := ⟨k.internalId, k.receivingCounter⟩

def snapshot (w : World) : Snapshot :=
  ⟨w.k.keypairCounter, fun i => (w.k.wg.bind fun d => d.keypairs[i]?).map cell⟩

def Snapshot.put (s : Snapshot) (i : Nat) (v : Option Cell) : Snapshot :=
  { s with slots := fun j => if j = i then v else s.slots j }

def Snapshot.empty (s : Snapshot) : Snapshot := { s with slots := fun _ => none }

def Snapshot.fresh (s : Snapshot) (i : Nat) : Snapshot :=
  { frontier := s.frontier + 1
    slots := fun j => if j = i then some ⟨s.frontier + 1, {}⟩ else s.slots j }

@[simp] theorem put_frontier (s : Snapshot) (i : Nat) (v : Option Cell) :
    (s.put i v).frontier = s.frontier := rfl
@[simp] theorem put_here (s : Snapshot) (i : Nat) (v : Option Cell) :
    (s.put i v).slots i = v := by simp [Snapshot.put]
@[simp] theorem put_elsewhere (s : Snapshot) (i j : Nat) (v : Option Cell) (h : j ≠ i) :
    (s.put i v).slots j = s.slots j := by simp [Snapshot.put, h]

/-- All obligations needed when one validator appends an acceptance event. -/
structure Inv (s : Snapshot) (history : History) : Prop where
  bounded : ∀ i c, s.slots i = some c → c.stamp ≤ s.frontier
  shaped : ∀ i c, s.slots i = some c → c.counter.backtrack.size = 128
  unique : ∀ i j c d, s.slots i = some c → s.slots j = some d → c.stamp = d.stamp → i = j
  pastBounded : ∀ e ∈ history, e.keypair ≤ s.frontier
  nodup : history.Nodup
  remembers : ∀ i c, s.slots i = some c → ∀ e ∈ history,
    e.keypair = c.stamp → Remembers c.counter e.nonce

theorem inv_empty (frontier : Nat) : Inv ⟨frontier, fun _ => none⟩ [] := by
  constructor <;> simp

/-- Deletion and device teardown only remove active obligations. -/
theorem Inv.subset (h : Inv s history) (hf : s.frontier ≤ t.frontier)
    (hs : ∀ i c, t.slots i = some c → s.slots i = some c) : Inv t history := by
  exact ⟨fun i c hc => Nat.le_trans (h.bounded i c (hs i c hc)) hf,
    fun i c hc => h.shaped i c (hs i c hc),
    fun i j c d hc hd hid => h.unique i j c d (hs i c hc) (hs j d hd) hid,
    fun e he => Nat.le_trans (h.pastBounded e he) hf, h.nodup,
    fun i c hc e he hid => h.remembers i c (hs i c hc) e he hid⟩

theorem Inv.erase (h : Inv s history) (i : Nat) : Inv (s.put i none) history := by
  apply h.subset (t := s.put i none) (Nat.le_refl _)
  intro j c hc
  by_cases hj : j = i
  · subst j; simp at hc
  · simpa [hj] using hc

theorem Inv.empty (h : Inv s history) : Inv s.empty history := by
  apply h.subset (t := s.empty) (Nat.le_refl _)
  intro i c hc
  cases hc

theorem Inv.fresh (h : Inv s history) (i : Nat) : Inv (s.fresh i) history := by
  constructor
  · intro j c hc
    by_cases hj : j = i
    · simp [Snapshot.fresh, hj] at hc; subst c; exact Nat.le_refl _
    · simp [Snapshot.fresh, hj] at hc
      exact Nat.le_trans (h.bounded j c hc) (Nat.le_succ _)
  · intro j c hc
    by_cases hj : j = i
    · simp [Snapshot.fresh, hj] at hc; subst c; rfl
    · simp [Snapshot.fresh, hj] at hc
      exact h.shaped j c hc
  · intro j k c d hc hd hid
    by_cases hj : j = i <;> by_cases hk : k = i
    · exact hj.trans hk.symm
    · simp [Snapshot.fresh, hj] at hc; subst c
      simp [Snapshot.fresh, hk] at hd
      have := h.bounded k d hd
      dsimp at hid
      omega
    · simp [Snapshot.fresh, hk] at hd; subst d
      simp [Snapshot.fresh, hj] at hc
      have := h.bounded j c hc
      dsimp at hid
      omega
    · simp [Snapshot.fresh, hj] at hc
      simp [Snapshot.fresh, hk] at hd
      exact h.unique j k c d hc hd hid
  · intro e he
    exact Nat.le_trans (h.pastBounded e he) (Nat.le_succ _)
  · exact h.nodup
  · intro j c hc e he hid
    by_cases hj : j = i
    · simp [Snapshot.fresh, hj] at hc; subst c
      have := h.pastBounded e he
      dsimp at hid
      omega
    · simp [Snapshot.fresh, hj] at hc
      exact h.remembers j c hc e he hid

/-- A counter update preserves all old history if it preserves Remembers. -/
theorem Inv.replace (h : Inv s history) (hc : s.slots i = some c)
    (counter : ReplayCounter) (hs : counter.backtrack.size = 128)
    (hr : ∀ p, Remembers c.counter p → Remembers counter p) :
    Inv (s.put i (some ⟨c.stamp, counter⟩)) history := by
  constructor
  · intro j d hd
    by_cases hj : j = i
    · subst j; simp at hd; subst d; exact h.bounded i c hc
    · simp [hj] at hd; exact h.bounded j d hd
  · intro j d hd
    by_cases hj : j = i
    · subst j; simp at hd; subst d; exact hs
    · simp [hj] at hd; exact h.shaped j d hd
  · intro j k d e hd he hid
    by_cases hj : j = i <;> by_cases hk : k = i
    · exact hj.trans hk.symm
    · subst j; simp at hd; subst d
      simp [hk] at he
      exact h.unique i k c e hc he hid
    · subst k; simp at he; subst e
      simp [hj] at hd
      exact h.unique j i d c hd hc hid
    · simp [hj] at hd; simp [hk] at he
      exact h.unique j k d e hd he hid
  · exact h.pastBounded
  · exact h.nodup
  · intro j d hd e he hid
    by_cases hj : j = i
    · subst j; simp at hd; subst d
      exact hr e.nonce (h.remembers i c hc e he hid)
    · simp [hj] at hd
      exact h.remembers j d hd e he hid

theorem Inv.append (h : Inv s history) (e : AcceptedEvent)
    (hb : e.keypair ≤ s.frontier) (hn : e ∉ history)
    (hr : ∀ i c, s.slots i = some c → e.keypair = c.stamp → Remembers c.counter e.nonce) :
    Inv s (history ++ [e]) := by
  refine ⟨h.bounded, h.shaped, h.unique, ?_, ?_, ?_⟩
  · intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact h.pastBounded f hf
    · simpa using (List.mem_singleton.mp hf ▸ hb)
  · apply List.nodup_append.mpr
    refine ⟨h.nodup, by simp, ?_⟩
    intro a ha b hb hab
    have hbe := List.mem_singleton.mp hb
    subst b; subst a
    exact hn ha
  · intro i c hc f hf hid
    rcases List.mem_append.mp hf with hf | hf
    · exact h.remembers i c hc f hf hid
    · have := List.mem_singleton.mp hf
      subst f
      exact hr i c hc hid

def validate (s : Snapshot) (i : Nat) (c : Cell) (nonce : Nat) : Snapshot :=
  s.put i (some ⟨c.stamp, (step c.counter nonce).2⟩)

def logResult (history : History) (c : Cell) (nonce : Nat) : History :=
  if (step c.counter nonce).1 then history ++ [⟨c.stamp, nonce⟩] else history

/-- No duplicate lifetime/nonce can be appended by a valid window step. -/
theorem Inv.validate (h : Inv s history) (hc : s.slots i = some c) (nonce : Nat) :
    Inv (Lifetimes.validate s i c nonce) (logResult history c nonce) := by
  have hs := h.shaped i c hc
  have hp : Inv (Lifetimes.validate s i c nonce) history :=
    h.replace hc _ (by simpa using hs) (fun p => step_remembers c.counter nonce p hs)
  unfold logResult
  split
  · rename_i ha
    apply hp.append ⟨c.stamp, nonce⟩ (h.bounded i c hc)
    · intro he
      have hm := h.remembers i c hc ⟨c.stamp, nonce⟩ he rfl
      have hf := remembered_rejected c.counter nonce hm
      simp [hf] at ha
    · intro j d hd hid
      have hi : (Lifetimes.validate s i c nonce).slots i = some ⟨c.stamp, (step c.counter nonce).2⟩ := by
        simp [Lifetimes.validate]
      have hij := hp.unique i j _ d hi hd hid
      subst j
      rw [hi] at hd
      cases hd
      exact accepted_remembered c.counter nonce hs ha
  · exact hp

/-- Ordinary effects are atomic: the frontier increment and fresh insertion
belong to one allocation step, matching a complete keypairCreate call. -/
inductive Ordinary : Snapshot → Snapshot → Prop where
  | refl (s) : Ordinary s s
  | erase (s i) : Ordinary s (s.put i none)
  | empty (s) : Ordinary s s.empty
  | fresh (s i) : Ordinary s (s.fresh i)
  | trans : Ordinary s t → Ordinary t u → Ordinary s u

theorem Ordinary.frontier_mono (ho : Ordinary s t) : s.frontier ≤ t.frontier := by
  induction ho with
  | refl | erase | empty => exact Nat.le_refl _
  | fresh => exact Nat.le_succ _
  | trans _ _ ih₁ ih₂ => exact Nat.le_trans ih₁ ih₂

/-- An ordinary execution cannot replace or reintroduce any old lifetime. -/
theorem Ordinary.old_slot (ho : Ordinary s t) (hc : t.slots i = some c)
    (hb : c.stamp ≤ s.frontier) : s.slots i = some c := by
  induction ho with
  | refl => exact hc
  | erase s j =>
    by_cases hi : i = j
    · subst i; simp at hc
    · simpa [hi] using hc
  | empty => cases hc
  | fresh s j =>
    by_cases hi : i = j
    · simp [Snapshot.fresh, hi] at hc
      subst c; dsimp at hb; omega
    · simpa [Snapshot.fresh, hi] using hc
  | trans h₁ h₂ ih₁ ih₂ =>
    exact ih₁ (ih₂ hc (Nat.le_trans hb h₁.frontier_mono)) hb

theorem Ordinary.preserves (ho : Ordinary s t) (h : Inv s history) : Inv t history := by
  induction ho with
  | refl => exact h
  | erase s i => exact h.erase i
  | empty => exact h.empty
  | fresh s i => exact h.fresh i
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ h)

/-- A finite receive-state execution. Each validate constructor names its
actual slot; all other state changes belong to Ordinary. -/
inductive Evolution : Snapshot → History → Snapshot → History → Prop where
  | refl (s h) : Evolution s h s h
  | ordinary : Ordinary s t → Evolution s h t h
  | validate (hc : s.slots i = some c) (nonce : Nat) :
      Evolution s h (Lifetimes.validate s i c nonce) (logResult h c nonce)
  | trans : Evolution s h t g → Evolution t g u k → Evolution s h u k

theorem Evolution.preserves (he : Evolution s h t g) (hi : Inv s h) : Inv t g := by
  induction he with
  | refl => exact hi
  | ordinary ho => exact ho.preserves hi
  | validate hc n => exact hi.validate hc n
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ hi)

theorem Evolution.nodup (he : Evolution ⟨frontier, fun _ => none⟩ [] t history) :
    history.Nodup := (he.preserves (inv_empty frontier)).nodup

end Leanux.Spikes.Lifetimes
