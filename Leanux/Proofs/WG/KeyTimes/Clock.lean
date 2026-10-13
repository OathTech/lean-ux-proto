import Leanux.Proofs.Framing.WGTime

/-! Exact original recorded age tests. The deadline is the signed 64-bit
addition and multiplication performed by the mirror, including wrap. -/
namespace Leanux.Proofs.WG.KeyTimes
open Leanux Leanux.WG Leanux.Proofs.WG.CounterWindow

def deadline (birthday : Int64) (seconds : Nat) : Int64 :=
  birthday + seconds.toInt64 * NSEC_PER_SEC64

theorem birthdateTest_run_iff (birthday : Int64) (seconds : Nat)
    (w v : World) (result : Bool × Int × Int) :
    (birthdateTest birthday seconds).run w = .ok (result, v) ↔
      ∃ now, (hiddenClock64 .birthdateExpired).run w = .ok (now, v) ∧
        result = (decide (deadline birthday seconds ≤ now),
          (deadline birthday seconds).toInt, now.toInt) := by
  unfold birthdateTest
  simp only [StateT.run_bind]
  cases h : (hiddenClock64 .birthdateExpired).run w with
  | error e => simp
  | ok out =>
    rcases out with ⟨now, u⟩
    change (Except.ok ((decide (deadline birthday seconds ≤ now),
      (deadline birthday seconds).toInt, now.toInt), u) : Except Stop _) = .ok (result, v) ↔ _
    constructor
    · intro he
      cases he
      exact ⟨now, rfl, rfl⟩
    · rintro ⟨n, hc, he⟩
      cases hc
      cases he
      rfl

theorem branchExpired_run_iff (d : Decision) (birthday : Int64) (seconds : Nat)
    (f : Bool → Bool) (w v : World) (outcome : Bool) :
    (branchExpired d birthday seconds f).run w = .ok (outcome, v) ↔
      ∃ now u, (hiddenClock64 .birthdateExpired).run w = .ok (now, u) ∧
        outcome = f (decide (deadline birthday seconds ≤ now)) ∧
        v = recordCmp u d outcome (deadline birthday seconds).toInt now.toInt := by
  unfold branchExpired birthdateTest
  simp only [StateT.run_bind]
  cases h : (hiddenClock64 .birthdateExpired).run w with
  | error e => simp
  | ok out =>
    rcases out with ⟨now, u⟩
    change (Except.ok (f (decide (deadline birthday seconds ≤ now)),
      recordCmp u d (f (decide (deadline birthday seconds ≤ now)))
        (deadline birthday seconds).toInt now.toInt) : Except Stop _) = .ok (outcome, v) ↔ _
    constructor
    · intro he
      cases he
      exact ⟨now, u, rfl, rfl, rfl⟩
    · rintro ⟨n, z, hc, ho, hv⟩
      cases hc
      subst outcome
      subst v
      rfl

theorem branchExpired_false (d : Decision) (birthday : Int64) (seconds : Nat)
    (w v : World) (h : (branchExpired d birthday seconds).run w = .ok (false, v)) :
    ∃ now u, (hiddenClock64 .birthdateExpired).run w = .ok (now, u) ∧
      ¬ deadline birthday seconds ≤ now ∧
      v = recordCmp u d false (deadline birthday seconds).toInt now.toInt := by
  obtain ⟨now, u, hc, ho, hv⟩ := (branchExpired_run_iff d birthday seconds id w v false).mp h
  exact ⟨now, u, hc, by simpa using ho.symm, hv⟩

end Leanux.Proofs.WG.KeyTimes
