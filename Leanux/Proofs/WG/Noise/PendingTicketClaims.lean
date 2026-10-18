import Leanux.Proofs.WG.Lifetimes.Store

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingTickets
open Leanux.Proofs.WG.Lifetimes

variable {Slot : Type}

/-- An allocation not left in a pending responder slot still advances the
same global allocation frontier. -/
def advance (s : Store Slot) : Store Slot :=
  {s with frontier := s.frontier + 1}

structure Inv (s : Store Slot) (confirmed : List Nat) : Prop where
  bounded : Bounded s
  unique : Unique s
  distinct : confirmed.Nodup
  past : ∀ stamp ∈ confirmed, stamp ≤ s.frontier
  absent : ∀ stamp ∈ confirmed, Absent s stamp

theorem Inv.retained {s t : Store Slot} {seen : List Nat}
    (hi : Inv s seen) (step : Retained s t) : Inv t seen := by
  refine ⟨step.bounded hi.bounded,step.unique hi.unique,hi.distinct,?_,?_⟩
  · intro stamp member
    rw [step.1]
    exact hi.past stamp member
  · intro stamp member
    exact step.absent (hi.absent stamp member)

theorem Inv.allocate [DecidableEq Slot] {s : Store Slot} {seen : List Nat} (hi : Inv s seen) (i : Slot) :
    Inv (s.allocate i) seen := by
  refine ⟨allocate_bounded s i hi.bounded,allocate_unique s i hi.bounded hi.unique,
    hi.distinct,?_,?_⟩
  · intro stamp member
    exact Nat.le_trans (hi.past stamp member) (Nat.le_succ _)
  · intro stamp member
    exact (allocate_transition s i).absent (hi.past stamp member) (hi.absent stamp member)

theorem Inv.advance {s : Store Slot} {seen : List Nat} (hi : Inv s seen) :
    Inv (advance s) seen := by
  refine ⟨?_,hi.unique,hi.distinct,?_,hi.absent⟩
  · intro i stamp resident
    exact Nat.le_trans (hi.bounded i stamp resident) (Nat.le_succ _)
  · intro stamp member
    exact Nat.le_trans (hi.past stamp member) (Nat.le_succ _)

theorem Inv.confirm [DecidableEq Slot] {s : Store Slot} {seen : List Nat}
    (hi : Inv s seen) (i : Slot) (stamp : Nat) (resident : s.slots i = some stamp) :
    Inv (s.put i none) (stamp :: seen) := by
  have fresh : stamp ∉ seen := fun member => hi.absent stamp member i resident
  refine ⟨erase_bounded s i hi.bounded,(erase_retained s i).unique hi.unique,
    List.nodup_cons.mpr ⟨fresh,hi.distinct⟩,?_,?_⟩
  · intro value member
    rcases List.mem_cons.mp member with rfl | old
    · exact hi.bounded i _ resident
    · exact hi.past value old
  · intro value member
    rcases List.mem_cons.mp member with rfl | old
    · exact hi.unique.erase_absent resident
    · exact (erase_retained s i).absent (hi.absent value old)

/-- Source obligations contain no confirmed history. Administrative removals
and recreation are retained steps. A new pending ticket is fresh allocation;
normal confirmation consumes the current pending ticket. -/
inductive Step [DecidableEq Slot] : Store Slot → Option Nat → Store Slot → Prop where
  | retained {s t} (effect : Retained s t) : Step s none t
  | allocated {s t} (i : Slot) (effect : Retained (s.allocate i) t) : Step s none t
  | unused {s t} (effect : Retained (advance s) t) : Step s none t
  | confirmed {s t} (i : Slot) (stamp : Nat) (resident : s.slots i = some stamp)
      (effect : Retained (s.put i none) t) : Step s (some stamp) t

def record (event : Option Nat) (seen : List Nat) : List Nat :=
  event.toList ++ seen

theorem Step.preserves [DecidableEq Slot] {s t : Store Slot} {event : Option Nat} {seen : List Nat}
    (step : Step s event t) (hi : Inv s seen) : Inv t (record event seen) := by
  cases step with
  | retained effect => exact hi.retained effect
  | allocated i effect => exact (hi.allocate i).retained effect
  | unused effect => exact hi.advance.retained effect
  | confirmed i stamp resident effect => exact (hi.confirm i stamp resident).retained effect

/-- Any finite reached prefix; the relation makes no assumption that an outer
execution will return normally after this prefix. -/
inductive Run [DecidableEq Slot] : Store Slot → List Nat → Store Slot → Prop where
  | nil (s) : Run s [] s
  | snoc {s t u events event} (prior : Run s events t) (step : Step t event u) :
      Run s (events ++ event.toList) u

theorem Run.preserves [DecidableEq Slot] {s t : Store Slot} {events seen : List Nat}
    (run : Run s events t) (hi : Inv s seen) : Inv t (events.reverse ++ seen) := by
  induction run with
  | nil => exact hi
  | @snoc middle finish history event prior step ih =>
    have next := step.preserves ih
    cases event <;> simpa [record,List.reverse_append,List.append_assoc] using next

theorem empty_initial (frontier : Nat) :
    Inv ({frontier,slots := fun _ : Slot => none} : Store Slot) [] := by
  refine ⟨?_,?_,List.nodup_nil,?_,?_⟩
  · intro i stamp impossible
    cases impossible
  · intro i j stamp impossible
    cases impossible
  · intro stamp impossible
    cases impossible
  · intro stamp impossible
    cases impossible

/-- Initialized pending tickets permit arbitrary actor interleaving and resets.
The source bridge must establish Run for the actual committed prefix. -/
theorem initialized_prefix_distinct [DecidableEq Slot] (frontier : Nat) {events : List Nat} {final : Store Slot}
    (run : Run {frontier,slots := fun _ => none} events final) :
    events.Nodup ∧
    (∀ stamp ∈ events, stamp ≤ final.frontier ∧ Absent final stamp) := by
  have result := run.preserves (empty_initial frontier)
  simp only [List.append_nil] at result
  refine ⟨(List.pairwise_reverse.mp result.distinct).imp (fun h => Ne.symm h),?_⟩
  intro stamp member
  have reverseMember : stamp ∈ events.reverse := List.mem_reverse.mpr member
  exact ⟨result.past stamp reverseMember,result.absent stamp reverseMember⟩

end Leanux.Proofs.WG.Noise.PendingTickets
