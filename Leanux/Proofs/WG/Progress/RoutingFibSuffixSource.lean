import Leanux.Proofs.WG.Progress.RoutingSuffixSource
import Leanux.Proofs.Framing.EnvOperations

/-! Normal-result hidden-record suffix retention through the original IPv4 FIB lookup. Proofs factor generated continuations without copying any operational loop. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.Proofs.Framing
theorem net_forIn {α β : Type} (records : List HiddenRecord) (xs : List α) (initial : β)
    (f : α→β→Net.M (ForInStep β)) (each : ∀x b,NetKeeps records (f x b)) :
    NetKeeps records (forIn xs initial f) := by
  induction xs generalizing initial with
  | nil => exact net_pure records _
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply net_bind records _ _ (each x initial)
    intro step
    cases step with
    | done b => exact net_pure records b
    | yield b => exact ih b

theorem net_set (records : List HiddenRecord) (s : Net.State) : NetKeeps records (set s) :=
  fun _=>preserves_pure _

theorem net_branch (records : List HiddenRecord) (decision : Decision) (value : Bool) :
    NetKeeps records (branch decision value) := by
  intro s
  apply (hoare_iff_run _ _ _).mpr
  intro a out b pre run
  cases run
  exact pre

theorem net_branchCmp (records : List HiddenRecord) (decision : Decision)
    (value : Bool) (left right : Int) :
    NetKeeps records (branchCmp decision value left right) := by
  intro s
  apply (hoare_iff_run _ _ _).mpr
  intro a out b pre run
  cases run
  exact pre

theorem net_invariant {α : Type} (records : List HiddenRecord) (message : String) :
    NetKeeps records (invariant message : Net.M α) := fun _=>ambient_stop _ _

theorem net_unsupported {α : Type} (records : List HiddenRecord) (message : String) :
    NetKeeps records (unsupported message : Net.M α) := by
  intro s
  apply (hoare_iff_run _ _ _).mpr
  intro a out b pre run
  cases run

theorem net_dite {α : Type} (records : List HiddenRecord) (p : Prop) [Decidable p]
    (yes : p→Net.M α) (no : (¬p)→Net.M α)
    (hy : ∀h,NetKeeps records (yes h)) (hn : ∀h,NetKeeps records (no h)) :
    NetKeeps records (if h:p then yes h else no h) := by
  split
  · exact hy _
  · exact hn _

theorem net_getTrie (records : List HiddenRecord) : NetKeeps records Net.Fib.getTrie := by
  unfold Net.Fib.getTrie
  exact net_bind records _ _ (net_getTable records) (fun _=>net_pure records _)

theorem net_modifyTable (records : List HiddenRecord) (f : Net.Fib.Table→Net.Fib.Table) :
    NetKeeps records (Net.Fib.modifyTable f) := by
  unfold Net.Fib.modifyTable
  apply net_bind records _ _ (net_get records)
  intro s
  split <;> exact net_set records _

theorem net_nodeAt (records : List HiddenRecord) (p : Net.Fib.Path) :
    NetKeeps records (Net.Fib.nodeAt p) := by
  unfold Net.Fib.nodeAt
  apply net_bind records _ _ (net_getTrie records)
  intro t
  split
  · exact net_pure records _
  · exact net_invariant records _

theorem net_setNode (records : List HiddenRecord) (p : Net.Fib.Path) (n : Option Net.Fib.KeyVector) :
    NetKeeps records (Net.Fib.setNode p n) := by
  unfold Net.Fib.setNode Net.Fib.setTrie
  exact net_bind records _ _ (net_getTrie records) (fun _=>net_modifyTable records _)
theorem net_goodNhc (records : List HiddenRecord) (fi : Net.Fib.FibInfo) (flow : Net.Fib.Flow) :
    NetKeeps records (Net.Fib.lookupGoodNhc fi flow) := by
  env_operation_source [Net.Fib.lookupGoodNhc]
    using [net_branch, net_branchCmp, net_pure, net_bind, net_ite]

theorem net_budget {α : Type} (records : List HiddenRecord) (message : String) :
    NetKeeps records (budgetExhausted message : Net.M α) := by
  intro s
  apply (hoare_iff_run _ _ _).mpr
  intro a out b pre run
  dsimp [budgetExhausted, AmbientM.budgetExhausted] at run
  split at run <;> cases run

theorem net_tableLookup (records : List HiddenRecord) (flow : Net.Fib.Flow) :
    NetKeeps records (Net.Fib.tableLookup flow) := by
  unfold Net.Fib.tableLookup
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | env_operation_fact net_getTrie
    | env_operation_fact net_getTable
    | env_operation_fact net_nodeAt
    | env_operation_fact net_setNode
    | env_operation_fact net_goodNhc
    | env_operation_fact net_branch
    | env_operation_fact net_branchCmp
    | env_operation_fact net_invariant
    | env_operation_fact net_budget
    | env_operation_fact net_pure
    | env_operation_fact net_bind
    | env_operation_fact net_forIn
    | env_operation_fact net_ite
    | env_operation_fact net_dite
    | env_operation_step

end Leanux.Proofs.WG.Progress.RecordSuffix
