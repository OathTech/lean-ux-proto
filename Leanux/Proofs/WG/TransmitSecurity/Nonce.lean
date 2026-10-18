import Leanux.Proofs.Logged.Basic

/-! Sending nonce allocations, including attempts abandoned before encryption.
The state is a projection of the real key store. The finite relation below is
support for source refinement, not a claim that every runner step refines it. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce
open Leanux Leanux.WG

@[ext] structure Cell where
  stamp : Nat
  next : Nat
  deriving DecidableEq

@[ext] structure View where
  frontier : Nat
  cells : KeypairId → Option Cell

def cell (k : Keypair) : Cell := ⟨k.internalId, k.sendingCounter⟩

def view (w : WGWorld) : View :=
  ⟨w.keypairCounter, fun id => (w.dev.bind fun d => d.keypairs[id]?).map cell⟩

@[ext] structure Allocation where
  stamp : Nat
  nonce : Nat
  deriving DecidableEq

def View.put (s : View) (id : KeypairId) (c : Option Cell) : View :=
  { s with cells := fun j => if j = id then c else s.cells j }

def View.fresh (s : View) (id : KeypairId) : View :=
  { frontier := s.frontier + 1
    cells := fun j => if j = id then some ⟨s.frontier + 1, 0⟩ else s.cells j }

structure Inv (s : View) (history : List Allocation) : Prop where
  bounded : ∀ id c, s.cells id = some c → c.stamp ≤ s.frontier
  unique : ∀ i j c d, s.cells i = some c → s.cells j = some d → c.stamp = d.stamp → i = j
  pastBounded : ∀ e ∈ history, e.stamp ≤ s.frontier
  nodup : history.Nodup
  ahead : ∀ id c, s.cells id = some c → ∀ e ∈ history, e.stamp = c.stamp → e.nonce < c.next

theorem initial (frontier : Nat) : Inv ⟨frontier, fun _ => none⟩ [] := by
  constructor <;> simp

theorem Inv.subset (h : Inv s history) (hf : s.frontier ≤ t.frontier)
    (hc : ∀ id c, t.cells id = some c → s.cells id = some c) : Inv t history := by
  exact ⟨fun id c he => Nat.le_trans (h.bounded id c (hc id c he)) hf,
    fun i j c d hi hj hs => h.unique i j c d (hc i c hi) (hc j d hj) hs,
    fun e he => Nat.le_trans (h.pastBounded e he) hf, h.nodup,
    fun id c he e hh hs => h.ahead id c (hc id c he) e hh hs⟩

theorem Inv.erase (h : Inv s history) (id : KeypairId) :
    Inv (s.put id none) history := by
  apply h.subset (t := s.put id none) (Nat.le_refl _)
  intro j c hc
  by_cases hj : j = id
  · simp [View.put, hj] at hc
  · simpa [View.put, hj] using hc

theorem Inv.fresh (h : Inv s history) (id : KeypairId) :
    Inv (s.fresh id) history := by
  constructor
  · intro j c hc
    by_cases hj : j = id
    · simp [View.fresh, hj] at hc; subst c; exact Nat.le_refl _
    · simp [View.fresh, hj] at hc
      exact Nat.le_trans (h.bounded j c hc) (Nat.le_succ _)
  · intro i j c d hi hj hs
    by_cases hi' : i = id <;> by_cases hj' : j = id
    · exact hi'.trans hj'.symm
    · simp [View.fresh, hi'] at hi; subst c
      simp [View.fresh, hj'] at hj
      have := h.bounded j d hj
      dsimp at hs; omega
    · simp [View.fresh, hj'] at hj; subst d
      simp [View.fresh, hi'] at hi
      have := h.bounded i c hi
      dsimp at hs; omega
    · simp [View.fresh, hi'] at hi
      simp [View.fresh, hj'] at hj
      exact h.unique i j c d hi hj hs
  · intro e he
    exact Nat.le_trans (h.pastBounded e he) (Nat.le_succ _)
  · exact h.nodup
  · intro j c hc e he hs
    by_cases hj : j = id
    · simp [View.fresh, hj] at hc; subst c
      have := h.pastBounded e he
      dsimp at hs; omega
    · simp [View.fresh, hj] at hc
      exact h.ahead j c hc e he hs

/-- Reserve the old counter before any bound check, allocation or queue result. -/
def reserve (s : View) (id : KeypairId) (c : Cell) : View :=
  s.put id (some {c with next := c.next + 1})

def allocation (c : Cell) : Allocation := ⟨c.stamp, c.next⟩

theorem Inv.reserve_preserves {id : KeypairId} (h : Inv s history) (hc : s.cells id = some c) :
    Inv (reserve s id c) (history ++ [allocation c]) := by
  have old : Inv (reserve s id c) history := by
    constructor
    · intro j d hd
      by_cases hj : j = id
      · simp [reserve, View.put, hj] at hd; subst d
        exact h.bounded id c hc
      · simp [reserve, View.put, hj] at hd
        exact h.bounded j d hd
    · intro i j d e hi hj hs
      by_cases hi' : i = id <;> by_cases hj' : j = id
      · exact hi'.trans hj'.symm
      · simp [reserve, View.put, hi'] at hi; subst d
        simp [reserve, View.put, hj'] at hj
        exact hi'.trans (h.unique id j c e hc hj hs)
      · simp [reserve, View.put, hj'] at hj; subst e
        simp [reserve, View.put, hi'] at hi
        exact (h.unique i id d c hi hc hs).trans hj'.symm
      · simp [reserve, View.put, hi'] at hi
        simp [reserve, View.put, hj'] at hj
        exact h.unique i j d e hi hj hs
    · exact h.pastBounded
    · exact h.nodup
    · intro j d hd e he hs
      by_cases hj : j = id
      · simp [reserve, View.put, hj] at hd; subst d
        exact Nat.lt_trans (h.ahead id c hc e he hs) (Nat.lt_succ_self _)
      · simp [reserve, View.put, hj] at hd
        exact h.ahead j d hd e he hs
  constructor
  · exact old.bounded
  · exact old.unique
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact h.pastBounded e he
    · have := List.mem_singleton.mp he
      subst e
      exact h.bounded id c hc
  · apply List.nodup_append.mpr
    refine ⟨h.nodup, by simp, ?_⟩
    intro e he f hf hef
    have hf := List.mem_singleton.mp hf
    subst f
    subst e
    have := h.ahead id c hc (allocation c) he rfl
    exact (Nat.lt_irrefl c.next) this
  · intro j d hd e he hs
    rcases List.mem_append.mp he with he | he
    · exact old.ahead j d hd e he hs
    · have := List.mem_singleton.mp he
      subst e
      have hi : (reserve s id c).cells id = some {c with next := c.next + 1} := by
        simp [reserve, View.put]
      have hij := old.unique id j _ d hi hd hs
      subst j
      rw [hi] at hd
      cases hd
      exact Nat.lt_succ_self _

/-- Nonce allocations remain recorded when a subsequent action refuses work. -/
theorem allocated_not_reusable {id : KeypairId} (h : Inv s history) (hc : s.cells id = some c)
    (he : allocation c ∈ history) : False := by
  exact (Nat.lt_irrefl c.next) (h.ahead id c hc (allocation c) he rfl)

end Leanux.Proofs.WG.TransmitSecurity.Nonce
