import Leanux.Proofs.Framing.WGTime
import Leanux.Proofs.WG.CounterWindow.Refinement

/-! Exact recorded age tests on the actual WG/Ambient stack, including signed
64-bit wrap and the returned comparison operands. -/
namespace Leanux.Proofs.WG.KeyTimes
open Leanux Leanux.WG Leanux.Proofs.WG.CounterWindow

def deadline (birthday : Int64) (seconds : Nat) : Int64 :=
  birthday + seconds.toInt64 * NSEC_PER_SEC64

theorem birthdateTest_run_iff (birthday : Int64) (seconds : Nat)
    (w v : WGWorld) (a b : Ambient) (result : Bool × Int × Int) :
    ((birthdateTest birthday seconds).run w).run a = .ok ((result, v), b) ↔
      ∃ now, (((hiddenClock64 .birthdateExpired : WG.M Int64).run w).run a) =
          .ok ((now, v), b) ∧
        result = (decide (deadline birthday seconds ≤ now),
          (deadline birthday seconds).toInt, now.toInt) := by
  unfold birthdateTest
  simp only [StateT.run_bind]
  cases h : (((hiddenClock64 .birthdateExpired : WG.M Int64).run w).run a) with
  | error e =>
    change (Except.error e : Except Stop _) = .ok ((result, v), b) ↔ _
    simp
  | ok out =>
    rcases out with ⟨⟨now, u⟩, c⟩
    change (Except.ok (((decide (deadline birthday seconds ≤ now),
      (deadline birthday seconds).toInt, now.toInt), u), c) : Except Stop _) =
        .ok ((result, v), b) ↔ _
    constructor
    · intro he
      cases he
      exact ⟨now, rfl, rfl⟩
    · rintro ⟨n, hc, he⟩
      cases hc
      cases he
      rfl

theorem branchExpired_run_iff (d : Decision) (birthday : Int64) (seconds : Nat)
    (f : Bool → Bool) (w v : WGWorld) (a b : Ambient) (outcome : Bool) :
    ((branchExpired d birthday seconds f).run w).run a = .ok ((outcome, v), b) ↔
      ∃ now u c, (((hiddenClock64 .birthdateExpired : WG.M Int64).run w).run a) =
          .ok ((now, u), c) ∧
        outcome = f (decide (deadline birthday seconds ≤ now)) ∧
        v = u ∧ b = recordCmp c d outcome (deadline birthday seconds).toInt now.toInt := by
  unfold branchExpired birthdateTest
  simp only [StateT.run_bind]
  cases h : (((hiddenClock64 .birthdateExpired : WG.M Int64).run w).run a) with
  | error e =>
    change (Except.error e : Except Stop _) = .ok ((outcome, v), b) ↔ _
    simp
  | ok out =>
    rcases out with ⟨⟨now, u⟩, c⟩
    change (Except.ok ((f (decide (deadline birthday seconds ≤ now)), u),
      recordCmp c d (f (decide (deadline birthday seconds ≤ now)))
        (deadline birthday seconds).toInt now.toInt) : Except Stop _) = .ok ((outcome, v), b) ↔ _
    constructor
    · intro he
      cases he
      exact ⟨now, _, _, rfl, rfl, rfl, rfl⟩
    · rintro ⟨n, z, t, hc, ho, hv, hb⟩
      cases hc
      subst outcome
      subst v
      subst b
      rfl

theorem branchExpired_false (d : Decision) (birthday : Int64) (seconds : Nat)
    (w v : WGWorld) (a b : Ambient)
    (h : ((branchExpired d birthday seconds).run w).run a = .ok ((false, v), b)) :
    ∃ now u c, (((hiddenClock64 .birthdateExpired : WG.M Int64).run w).run a) =
        .ok ((now, u), c) ∧
      ¬ deadline birthday seconds ≤ now ∧
      v = u ∧ b = recordCmp c d false (deadline birthday seconds).toInt now.toInt := by
  obtain ⟨now, u, c, hc, ho, hv, hb⟩ :=
    (branchExpired_run_iff d birthday seconds id w v a b false).mp h
  exact ⟨now, u, c, hc, by simpa using ho.symm, hv, hb⟩

end Leanux.Proofs.WG.KeyTimes
