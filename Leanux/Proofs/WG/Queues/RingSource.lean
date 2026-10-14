import Leanux.Proofs.WG.Queues.RingOccurrences
import Leanux.Proofs.Logged.PrefixWorkers
import Leanux.Proofs.Framing.Projection
import Leanux.Proofs.Framing.KernelEffects
import Leanux.WG.Send

/-! Source journals refine finite executions of the original ring operations.
On a Stop only the reached event prefix survives; no failed World is asserted.
The cell fixes the device interface index and physical ring; it does not
identify a fresh lifecycle epoch or distinguish resets. -/
namespace Leanux.Proofs.WG.Queues.Ring.Source
open Leanux Leanux.WG Leanux.Proofs.Logged
open Ring.Journal
open Leanux.Proofs.Framing

variable {ι : Type}

def Refines (initial : PtrRing ι) (h : List (Ring.Journal.Event ι)) (r : PtrRing ι) : Prop :=
  ∃ cs, Ring.Journal.run initial cs = (h, r)

def Safe (initial : PtrRing ι) (h : List (Ring.Journal.Event ι)) : Prop := ∃ r, Refines initial h r

def Inv (cell : World → Option (Nat × PtrRing ι)) (deviceIndex : Nat) (initial : PtrRing ι) (h : List (Ring.Journal.Event ι)) (w : World) : Prop :=
  ∃ r, Refines initial h r ∧ cell w = some (deviceIndex, r)

theorem run_append (r : PtrRing α) (xs ys : List (Command α)) :
    Ring.Journal.run r (xs ++ ys) =
      let (h, s) := Ring.Journal.run r xs
      let (h', t) := Ring.Journal.run s ys
      (h ++ h', t) := by
  induction xs generalizing r with
  | nil => rfl
  | cons c cs ih => simp [Ring.Journal.run, ih, List.append_assoc]

theorem Refines.step (hr : Refines initial h r) (c : Command ι) :
    Refines initial (h ++ [(step r c).1]) (step r c).2 := by
  obtain ⟨cs, hc⟩ := hr
  exact ⟨cs ++ [c], by simp [run_append, hc, Ring.Journal.run]⟩

variable {cell : World → Option (Nat × PtrRing ι)}

theorem Inv.safe (hi : Inv cell deviceIndex initial h w) : Safe initial h :=
  ⟨hi.choose, hi.choose_spec.1⟩

theorem initial_inv (hc : cell w = some (deviceIndex, initial)) : Inv cell deviceIndex initial [] w :=
  ⟨initial, ⟨[], rfl⟩, hc⟩

/-- Initialized physical conservation and an ordinal refinement. The positive
size clause retains the retired/stale/live representation; size zero still
has exact event erasure, conservation and distinct occurrence ordinals. -/
def Initialized (n : Nat) (h : List (Ring.Journal.Event ι)) (r : PtrRing ι) : Prop :=
    (0 < n → Ring.Journal.Inv n (PtrRing.init (α := ι) n).batch h r) ∧
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


theorem lift_frame (ha : SameView cell a) :
    PrefixPreserves (Inv cell deviceIndex initial) (Safe initial) (liftPrefix a) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.safe)
  intro h w x v hi hr
  obtain ⟨r, hj, hc⟩ := hi
  exact ⟨r, hj, (ha w x v hr).trans hc⟩

def enqueue (source : M Int) (id : ι) : PrefixM (Ring.Journal.Event ι) Int := do
  let ret ← liftPrefix source
  if ret = 0 then emitPrefix (.offered id true)
  else if ret = -EPIPE then emitPrefix (.offered id false)
  return ret

theorem enqueue_erases (source : M Int) (id : ι) : ErasesPrefix (enqueue source id) source := by
  intro w h
  simp only [enqueue, runPrefix_bind, runPrefix_lift]
  cases hr : source.run w with
  | error e => rfl
  | ok result =>
    rcases result with ⟨ret, v⟩
    by_cases hz : ret = 0
    · simp only [hz, ↓reduceIte, runPrefix_bind, runPrefix_emit, runPrefix_pure]
    · simp only [hz, ↓reduceIte]
      by_cases hp : ret = -EPIPE <;>
        simp only [hp, ↓reduceIte, runPrefix_bind, runPrefix_emit, runPrefix_pure]

def EnqueueResult (before : Option (Nat × PtrRing ι)) (id : ι)
    (ret : Int) (after : Option (Nat × PtrRing ι)) : Prop :=
  (ret = 0 ∧ after = before.map (fun (e, r) => (e, r.produce id))) ∨
  (ret = -ENOSPC ∧ after = before) ∨
  (ret = -EPIPE ∧ after = before ∧ ∃ e r, before = some (e, r) ∧ r.full = true)

theorem enqueue_preserves (source : M Int) (id : ι)
    (hresult : ∀ w ret v, source.run w = .ok (ret, v) → EnqueueResult (cell w) id ret (cell v))
    (free : ∀ w v r, cell w = some (deviceIndex, r) → source.run w = .ok (0, v) → r.full = false) :
    PrefixPreserves (Inv cell deviceIndex initial) (Safe initial) (enqueue source id) := by
  intro w h hi
  obtain ⟨r, hj, hc⟩ := hi
  simp only [enqueue, runPrefix_bind, runPrefix_lift]
  cases hr : source.run w with
  | error e => exact ⟨[], by simp, ⟨r, hj⟩, True.intro⟩
  | ok result =>
    rcases result with ⟨ret, v⟩
    rcases hresult w ret v hr with ⟨rfl, ha⟩ | ⟨rfl, ha⟩ | ⟨rfl, ha, e, s, hb, hf⟩
    · have hf := free w v r hc hr
      have hn : Refines initial (h ++ [.offered id true]) (r.produce id) := by
        simpa [step, tryProduce, hf] using hj.step (.offer id)
      simp only [↓reduceIte, runPrefix_bind, runPrefix_emit, runPrefix_pure]
      exact ⟨[.offered id true], rfl, ⟨_, hn⟩, ⟨_, hn, by simpa [hc] using ha⟩⟩
    · simp only [ENOSPC, EPIPE, Int.reduceNeg, Int.reduceEq, ↓reduceIte, runPrefix_pure]
      exact ⟨[], by simp, ⟨r, hj⟩, ⟨r, hj, ha.trans hc⟩⟩
    · have he : (e, s) = (deviceIndex, r) := Option.some.inj (hb.symm.trans hc)
      have he' : s = r := congrArg Prod.snd he
      have hf' : r.full = true := he' ▸ hf
      have hn : Refines initial (h ++ [.offered id false]) r := by
        simpa [step, tryProduce, hf'] using hj.step (.offer id)
      simp only [EPIPE, Int.reduceNeg, Int.reduceEq, ↓reduceIte, runPrefix_bind,
        runPrefix_emit, runPrefix_pure]
      exact ⟨[.offered id false], rfl, ⟨r, hn⟩, ⟨r, hn, ha.trans hc⟩⟩

def poll (source : M (Option ι)) : PrefixM (Ring.Journal.Event ι) (Option ι) := do
  let out ← liftPrefix source
  emitPrefix (.polled out)
  return out

theorem poll_erases (source : M (Option ι)) : ErasesPrefix (poll source) source := by
  intro w h
  simp only [poll, runPrefix_bind, runPrefix_lift]
  cases hr : source.run w with
  | error e => rfl
  | ok result =>
    rcases result with ⟨out, v⟩
    simp [runPrefix_emit, runPrefix_pure]

theorem poll_preserves (source : M (Option ι))
    (hresult : ∀ w out v r, cell w = some (deviceIndex, r) → source.run w = .ok (out, v) →
      out = r.consume.1 ∧ cell v = some (deviceIndex, r.consume.2)) : PrefixPreserves (Inv cell deviceIndex initial) (Safe initial) (poll source) := by
  intro w h hi
  obtain ⟨r, hj, hc⟩ := hi
  simp only [poll, runPrefix_bind, runPrefix_lift]
  cases hr : source.run w with
  | error e => exact ⟨[], by simp, ⟨r, hj⟩, True.intro⟩
  | ok result =>
    rcases result with ⟨out, v⟩
    obtain ⟨ho, hv⟩ := hresult w out v r hc hr
    have hn : Refines initial (h ++ [.polled out]) r.consume.2 := by
      simpa [step, ho] using hj.step .poll
    simp only [runPrefix_bind, runPrefix_emit, runPrefix_pure]
    exact ⟨[.polled out], rfl, ⟨_, hn⟩, ⟨_, hn, hv⟩⟩

theorem from_initial {g : PrefixM (Ring.Journal.Event ι) α}
    (hg : PrefixPreserves (Inv cell deviceIndex (PtrRing.init n)) (Safe (PtrRing.init n)) g)
    (hc : cell w = some (deviceIndex, PtrRing.init n)) :
    Safe (PtrRing.init n) (runPrefix g w []).2 ∧
      match (runPrefix g w []).1 with
      | .error _ => True
      | .ok (_, v) => Inv cell deviceIndex (PtrRing.init n) (runPrefix g w []).2 v := by
  obtain ⟨_, _, hs, ho⟩ := hg w [] (initial_inv hc)
  exact ⟨hs, ho⟩

theorem initialized {g : PrefixM (Ring.Journal.Event ι) α}
    (hg : PrefixPreserves (Inv cell deviceIndex (PtrRing.init n)) (Safe (PtrRing.init n)) g)
    (hc : cell w = some (deviceIndex, PtrRing.init n)) :
    let out := runPrefix g w []
    ∃ r, Initialized n out.2 r ∧
      match out.1 with
      | .error _ => True
      | .ok (_, v) => cell v = some (deviceIndex, r) := by
  obtain ⟨safe, done⟩ := from_initial hg hc
  cases hout : (runPrefix g w []).1 with
  | error e =>
    obtain ⟨r, hj⟩ := safe
    exact ⟨r, hj.initialized, by simp [hout]⟩
  | ok result =>
    rcases result with ⟨x, v⟩
    simp only [hout] at done
    obtain ⟨r, hj, he⟩ := done
    exact ⟨r, hj.initialized, by simpa only [hout] using he⟩


end Leanux.Proofs.WG.Queues.Ring.Source
