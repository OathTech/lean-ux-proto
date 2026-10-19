import Leanux.Proofs.WG.Queues.RingMap

/-! Finite journals execute the original guarded production and consumption.
Every offer, refusal and empty poll is retained. Physical retirement is not a
logical loss: admitted = consumed ++ live, consumed = retired ++ stale. -/
namespace Leanux.Proofs.WG.Queues.Ring.Journal
open Leanux Leanux.WG

inductive Command (α : Type) where
  | offer (x : α)
  | poll

inductive Event (α : Type) where
  | offered (x : α) (accepted : Bool)
  | polled (x : Option α)

def admitted (h : List (Event α)) : List α := h.filterMap fun e => match e with
  | .offered x true => some x
  | _ => none

def consumed (h : List (Event α)) : List α := h.filterMap fun e => match e with
  | .polled x => x
  | _ => none

def offered (h : List (Event α)) : List α := h.filterMap fun e => match e with
  | .offered x _ => some x
  | _ => none

def step (r : PtrRing α) : Command α → Event α × PtrRing α
  | .offer x => let (ok, r') := tryProduce r x; (.offered x ok, r')
  | .poll => let (x, r') := r.consume; (.polled x, r')

def run (r : PtrRing α) : List (Command α) → List (Event α) × PtrRing α
  | [] => ([], r)
  | c :: cs => let (e, r') := step r c
               let (es, r'') := run r' cs
               (e :: es, r'')

def Inv (n batch : Nat) (h : List (Event α)) (r : PtrRing α) : Prop :=
  ∃ t retired stale live, Bounds n t stale live ∧ r = ringOf n batch t stale live ∧
    admitted h = consumed h ++ live ∧ consumed h = retired ++ stale

theorem step_inv {h : List (Event α)} {r : PtrRing α} (hi : Inv n batch h r) (c : Command α) :
    Inv n batch (h ++ [(step r c).1]) (step r c).2 := by
  obtain ⟨t, retired, stale, live, hb, rfl, ha, hc⟩ := hi
  cases c with
  | offer x =>
    simp only [step, tryProduce_eq hb]
    by_cases he : stale.length + live.length = n
    · simp only [he, ↓reduceIte]
      refine ⟨t, retired, stale, live, hb, rfl, ?_, ?_⟩ <;>
        simpa [admitted, consumed] using (by assumption)
    · simp only [he, ↓reduceIte]
      refine ⟨t, retired, stale, live ++ [x], produce_bounds hb (by have := hb.2; omega) x, rfl, ?_, ?_⟩
      · simpa [admitted, consumed, List.append_assoc] using congrArg (fun xs => xs ++ [x]) ha
      · simpa [consumed] using hc
  | poll =>
    cases live with
    | nil =>
      simp only [step, consume_empty hb]
      refine ⟨t, retired, stale, [], hb, rfl, ?_, ?_⟩
      · simpa [admitted, consumed] using ha
      · simpa [admitted, consumed] using hc
    | cons x xs =>
      by_cases he : stale.length + 1 < batch ∧ t + (stale.length + 1) < n
      · simp only [step, consume_retain hb he.1 he.2]
        refine ⟨t, retired, stale ++ [x], xs, retain_bounds hb he.2, rfl, ?_, ?_⟩
        · simpa [admitted, consumed, List.append_assoc] using ha
        · simpa [consumed, List.append_assoc] using congrArg (fun xs => xs ++ [x]) hc
      · simp only [step, consume_retire (batch := batch) hb (by omega)]
        refine ⟨loc n t (stale.length + 1), retired ++ stale ++ [x], [], xs,
          retire_bounds hb, rfl, ?_, ?_⟩
        · simpa [admitted, consumed, List.append_assoc] using ha
        · simpa [consumed] using congrArg (fun xs => xs ++ [x]) hc

theorem run_inv {h : List (Event α)} {r : PtrRing α} (hi : Inv n batch h r) (cs : List (Command α)) :
    Inv n batch (h ++ (run r cs).1) (run r cs).2 := by
  induction cs generalizing h r with
  | nil => simpa [run] using hi
  | cons c cs ih =>
    have hs := ih (step_inv hi c)
    simpa [run, List.append_assoc] using hs

theorem initialized (hn : 0 < n) (cs : List (Command α)) :
    Inv n (PtrRing.init (α := α) n).batch (run (PtrRing.init n) cs).1
      (run (PtrRing.init n) cs).2 := by
  have hi : Inv n (PtrRing.init (α := α) n).batch [] (PtrRing.init n) :=
    ⟨0, [], [], [], by simp [Bounds, hn], init_eq hn, rfl, rfl⟩
  simpa using run_inv hi cs

theorem conservation (hn : 0 < n) (cs : List (Command α)) :
    admitted (run (PtrRing.init n) cs).1 =
      consumed (run (PtrRing.init n) cs).1 ++ (run (PtrRing.init n) cs).2.items ∧
    ∃ t retired stale live,
      Bounds n t stale live ∧
      (run (PtrRing.init n) cs).2 = ringOf n (PtrRing.init (α := α) n).batch t stale live ∧
      consumed (run (PtrRing.init n) cs).1 = retired ++ stale := by
  obtain ⟨t, retired, stale, live, hb, hr, ha, hc⟩ := initialized hn cs
  exact ⟨by rw [hr, items hb]; exact ha, t, retired, stale, live, hb, hr, hc⟩

def zeroEvent : Command α → Event α
  | .offer x => .offered x false
  | .poll => .polled none

theorem run_zero (r : PtrRing α) (hz : r.size = 0) (cs : List (Command α)) :
    run r cs = (cs.map zeroEvent, r) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases c with
    | offer x => simp [run, step, (zero_size r hz x).2.2.2.2.2, ih, zeroEvent]
    | poll =>
      have hc : r.consume = (none, r) := by simp [PtrRing.consume, PtrRing.peek, hz]
      simp [run, step, hc, ih, zeroEvent]

theorem zero_counts (cs : List (Command α)) :
    admitted (cs.map zeroEvent) = [] ∧ consumed (cs.map zeroEvent) = [] := by
  induction cs with
  | nil => simp [admitted, consumed]
  | cons c cs ih => cases c <;> simpa [zeroEvent, admitted, consumed] using ih

/-- Logical conservation also includes the zero-size ring, which admits and
consumes nothing. -/
theorem conservation_all (n : Nat) (cs : List (Command α)) :
    admitted (run (PtrRing.init n) cs).1 =
      consumed (run (PtrRing.init n) cs).1 ++ (run (PtrRing.init n) cs).2.items := by
  by_cases hn : 0 < n
  · exact (conservation hn cs).1
  · have hz : n = 0 := by omega
    subst n
    rw [run_zero _ (by rfl)]
    simp only [zero_counts cs, List.nil_append]
    simp [PtrRing.items, PtrRing.count, PtrRing.init]

def Command.map (f : α → β) : Command α → Command β
  | .offer x => .offer (f x)
  | .poll => .poll

def Event.map (f : α → β) : Event α → Event β
  | .offered x ok => .offered (f x) ok
  | .polled x => .polled (x.map f)

theorem step_map (f : α → β) (r : PtrRing α) (c : Command α) :
    step (mapRing f r) (c.map f) = ((step r c).1.map f, mapRing f (step r c).2) := by
  cases c <;> simp [step, Command.map, Event.map, tryProduce_map, consume_map]

theorem run_map (f : α → β) (r : PtrRing α) (cs : List (Command α)) :
    run (mapRing f r) (cs.map (Command.map f)) =
      ((run r cs).1.map (Event.map f), mapRing f (run r cs).2) := by
  induction cs generalizing r with
  | nil => rfl
  | cons c cs ih => simp [run, step_map, ih]

end Leanux.Proofs.WG.Queues.Ring.Journal
