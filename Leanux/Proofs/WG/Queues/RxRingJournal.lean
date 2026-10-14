import Leanux.Proofs.WG.Queues.RingOccurrences
import Leanux.Proofs.Logged.PrefixWorkers

/-! Source journals refine finite executions of the original ring operations.
On a Stop only the reached event prefix survives; no failed World is asserted.
The cell fixes the device interface index and physical ring; it does not
identify a fresh lifecycle epoch or distinguish resets. -/
namespace Leanux.Proofs.WG.Queues.RxRing
open Leanux Leanux.WG Leanux.Proofs.Logged
open Ring.Journal

abbrev Event := Ring.Journal.Event SkbId
abbrev Obs := PrefixM Event

def cell (w : World) : Option (Nat × PtrRing SkbId) :=
  w.k.wg.map fun d => (d.ifindex, d.decryptQueue)

def Refines (initial : PtrRing SkbId) (h : List Event) (r : PtrRing SkbId) : Prop :=
  ∃ cs, Ring.Journal.run initial cs = (h, r)

def Safe (initial : PtrRing SkbId) (h : List Event) : Prop := ∃ r, Refines initial h r

def Inv (deviceIndex : Nat) (initial : PtrRing SkbId) (h : List Event) (w : World) : Prop :=
  ∃ r, Refines initial h r ∧ cell w = some (deviceIndex, r)

theorem run_append (r : PtrRing α) (xs ys : List (Command α)) :
    Ring.Journal.run r (xs ++ ys) =
      let (h, s) := Ring.Journal.run r xs
      let (h', t) := Ring.Journal.run s ys
      (h ++ h', t) := by
  induction xs generalizing r with
  | nil => rfl
  | cons c cs ih => simp [Ring.Journal.run, ih, List.append_assoc]

theorem Refines.step (hr : Refines initial h r) (c : Command SkbId) :
    Refines initial (h ++ [(step r c).1]) (step r c).2 := by
  obtain ⟨cs, hc⟩ := hr
  exact ⟨cs ++ [c], by simp [run_append, hc, Ring.Journal.run]⟩

theorem Inv.safe (hi : Inv deviceIndex initial h w) : Safe initial h :=
  ⟨hi.choose, hi.choose_spec.1⟩

theorem initial_inv (hc : cell w = some (deviceIndex, initial)) : Inv deviceIndex initial [] w :=
  ⟨initial, ⟨[], rfl⟩, hc⟩

/-- Initialized physical conservation and an ordinal refinement. The positive
size clause retains the retired/stale/live representation; size zero still
has exact event erasure, conservation and distinct occurrence ordinals. -/
def Initialized (n : Nat) (h : List Event) (r : PtrRing SkbId) : Prop :=
    (0 < n → Ring.Journal.Inv n (PtrRing.init (α := SkbId) n).batch h r) ∧
    admitted h = consumed h ++ r.items ∧
    ∃ cs, Ring.Journal.run (PtrRing.init n) cs = (h, r) ∧
      let tagged := Ring.Journal.run (PtrRing.init n) (tagCommands 0 cs)
      tagged.1.map (Ring.Journal.Event.map Prod.snd) = h ∧
      Ring.mapRing Prod.snd tagged.2 = r ∧
      admitted tagged.1 = consumed tagged.1 ++ tagged.2.items ∧
      ((consumed tagged.1 ++ tagged.2.items).map Prod.fst).Nodup

/-- Initialized histories have a refinement with distinct occurrence
ordinals, even with repeated skb numbers and size zero. -/
theorem Refines.initialized (hr : Refines (PtrRing.init n) h r) : Initialized n h r := by
  obtain ⟨cs, hc⟩ := hr
  have conservation := conservation_all n cs
  rw [hc] at conservation
  refine ⟨?_, conservation, cs, hc, ?_⟩
  · intro hn
    have hi := Ring.Journal.initialized hn cs
    simpa only [hc] using hi
  · have he := tagged_initialized_erasure n 0 cs
    rw [hc] at he
    have ht := tagged_conservation n 0 cs
    exact ⟨(congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm, ht⟩

end Leanux.Proofs.WG.Queues.RxRing
