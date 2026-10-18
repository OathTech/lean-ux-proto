import Leanux.Proofs.WG.RetirementSecurity.Creation

/-! Finite sequences of actual native puts pay precisely the supplied
reference occurrences. This is a local source family: alignment with the
peer-slot clearing caller and RX/TX disposal callers is not assumed solved. -/
namespace Leanux.Proofs.WG.RetirementSecurity.Credits
open Leanux Leanux.WG Leanux.Proofs.Framing

def pay (pending : Ledger) (now : Bool) : WG.M Unit :=
  pending.forM fun allocation => keypairPut (some allocation.slot) now

theorem pay_cons (allocation : Allocation) (pending : Ledger) (now : Bool) :
    pay (allocation :: pending) now = (do
      keypairPut (some allocation.slot) now
      pay pending now) := by simp [pay,List.forM_cons]

theorem pay_exact (pending remaining : Ledger) (now : Bool) :
    Hoare (pay pending now) (Exact (pending ++ remaining)) (fun _ => Exact remaining) := by
  induction pending with
  | nil =>
    change Preserves (Exact remaining) (pure ())
    exact preserves_pure ()
  | cons allocation pending ih =>
    rw [pay_cons]
    have first : Hoare (keypairPut (some allocation.slot) now)
        (Exact (allocation :: pending ++ remaining)) (fun _ => Exact (pending ++ remaining)) := by
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w a result v b hi run
      cases result
      exact Exact.put hi now a b run
    exact hoare_bind _ _ first (fun _ => ih)

theorem pay_retains (pending : Ledger) (now : Bool) (initial : WGWorld) :
    Preserves (Retains initial) (pay pending now) := by
  induction pending with
  | nil => exact preserves_pure ()
  | cons allocation pending ih =>
    rw [pay_cons]
    exact preserves_bind (put_preserves (some allocation.slot) now initial) (fun _ => ih)

/-- A normal finite payment sequence cannot resurrect an allocation erased
by an earlier final payment. The statement concerns original put calls. -/
theorem pay_absent {id : KeypairId} (pending : Ledger) (now : Bool) (w v : WGWorld) (a b : Ambient)
    (absent : keyAt w id = none)
    (run : ((pay pending now).run w).run a = .ok (((),v),b)) : keyAt v id = none := by
  have kept := (hoare_iff_run_ambient _ _ _).mp (pay_retains pending now w)
    w a () v b (Retains.refl w) run
  cases found : keyAt v id with
  | none => rfl
  | some k =>
    obtain ⟨old,earlier,_⟩ := kept.keys id k found
    rw [absent] at earlier
    cases earlier

end Leanux.Proofs.WG.RetirementSecurity.Credits
