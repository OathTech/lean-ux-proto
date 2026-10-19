import Leanux.Proofs.WG.TimerDiscipline.SessionFrontierEffects
import Leanux.Proofs.WG.TimerDiscipline.SessionWheelSource

/-! Per-allocation enqueue accounting for normal session-derived hook exits.
Stopped hooks have no successor; give-up cleanup is a distinct arm cause. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
open Leanux Leanux.WG

def completedHookEnqueues (r : HookJournal.Receipt) : Nat :=
  match r.outcome with
  | .error _ => 0
  | .ok ((),after) => after.wg.timerEnqueues-r.before.wg.timerEnqueues

def Event.completedEnqueuesFor (e : Event) (serial : Nat) : Nat :=
  if e.derivedId==some serial then
    match e with
    | .session _ => 0
    | .hook r => completedHookEnqueues r
  else 0

def completedSessionEnqueues (h : List Event) (serial : Nat) : Nat :=
  (h.map (fun e=>e.completedEnqueuesFor serial)).sum

theorem SessionWheelFacts.enqueue_bound {s : SessionReceipt} {r : HookJournal.Receipt}
    (facts : SessionWheelFacts s r) : completedHookEnqueues r≤1 := by
  rcases facts with ⟨link,d,p,hd,hp,live,effect⟩
  cases outcome : r.outcome with
  | error stop => simp [completedHookEnqueues,outcome]
  | ok pair =>
    rcases pair with ⟨⟨⟩,after⟩
    simp only [outcome] at effect
    rcases effect with ⟨counter,effect⟩
    dsimp only [completedHookEnqueues]
    rw [outcome]
    dsimp only
    split at effect
    · rcases effect.2.1 with ⟨q,resident,stamp,armed,other,old | fresh⟩
      · rw [old.1];simp
      · rcases fresh with ⟨we,delta,rest⟩
        omega
    · rw [effect];simp

theorem enqueue_weight_bound (h : List Event) (facts : WheelHistoryFacts h)
    (serial : Nat) (e : Event) (member : e∈h) :
    e.completedEnqueuesFor serial≤if e.derivedId==some serial then 1 else 0 := by
  cases e with
  | session s => simp [Event.completedEnqueuesFor,Event.derivedId]
  | hook r =>
    cases kind : r.hook <;> simp only [Event.completedEnqueuesFor,Event.derivedId,kind]
    all_goals try simp
    split
    · obtain ⟨before,s,after,splitHistory,effect⟩:=facts r kind member
      exact effect.enqueue_bound
    · omega

theorem completedSessionEnqueues_le_occurrences (h : List Event) (facts : WheelHistoryFacts h)
    (serial : Nat) :
    completedSessionEnqueues h serial≤h.countP (fun e=>e.derivedId==some serial) := by
  have sumBound (xs : List Event)
      (bounds : ∀e∈xs,e.completedEnqueuesFor serial≤if e.derivedId==some serial then 1 else 0) :
      (xs.map (fun e=>e.completedEnqueuesFor serial)).sum≤xs.countP (fun e=>e.derivedId==some serial) := by
    induction xs with
    | nil => simp
    | cons e rest ih =>
      have head:=bounds e (by simp)
      have tail:=ih (fun x hx=>bounds x (by simp [hx]))
      simp only [List.map_cons,List.sum_cons,List.countP_cons]
      split <;> simp_all <;> omega
  exact sumBound h (enqueue_weight_bound h facts serial)

theorem completedSessionEnqueues_per_allocation (h : List Event) (facts : WheelHistoryFacts h)
    (paired : Paired h) (ordered : Ordered h) (serial : Nat) :
    completedSessionEnqueues h serial≤1 :=
  Nat.le_trans (completedSessionEnqueues_le_occurrences h facts serial) (ordered.derived_count paired serial)

end Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
