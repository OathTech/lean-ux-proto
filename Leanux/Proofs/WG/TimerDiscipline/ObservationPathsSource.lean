import Leanux.Proofs.WG.TimerDiscipline.ObservationProductSource
import Leanux.Proofs.WG.TimerDiscipline.RecordedJitterFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2
variable {α β : Type}

/-- Two original reads with the actual between-read observation. -/
def clockJitterPath (clock jitter : HiddenSite) : Leanux.M (Option UInt64 × Product.Snapshot × Nat) := do
  let caller ← liftWG (callerJiffies clock)
  let afterRead ← Product.read
  let value ← liftWG (jitterBelowRekeyTimeout jitter)
  return (caller, afterRead, value)

def prefixClockPath (first : Leanux.M α) (clock : HiddenSite) : Leanux.M (α × Product.Snapshot × Option UInt64) := do
  let choice ← first
  let before ← Product.read
  let caller ← liftWG (callerJiffies clock)
  return (choice, before, caller)

def prefixClockJitterPath (first : Leanux.M α) (clock jitter : HiddenSite) :
    Leanux.M (α × Product.Snapshot × Option UInt64 × Product.Snapshot × Nat) := do
  let choice ← first
  let before ← Product.read
  let result ← clockJitterPath clock jitter
  return (choice, before, result)

/-- Inspect the tail at the actual post-first state, retaining even tail errors. -/
def prefixInspect (first : Leanux.M α) (tail : Leanux.M β) : Leanux.M (α × Product.Snapshot × Product.Outcome β) := do
  let choice ← first
  let middle ← Product.read
  let result ← Product.inspect tail
  return (choice, middle, result)

theorem clockJitterPath_run (clock jitter : HiddenSite) (w afterRead afterJitter : World)
    (caller : Option UInt64) (value : Nat)
    (hc : (liftWG (callerJiffies clock)).run w = .ok (caller, afterRead))
    (hj : (liftWG (jitterBelowRekeyTimeout jitter)).run afterRead = .ok (value, afterJitter)) :
    (clockJitterPath clock jitter).run w = .ok ((caller, Product.snapshot afterRead, value), afterJitter) := by
  simp only [clockJitterPath, StateT.run_bind, hc]
  change ((liftWG (jitterBelowRekeyTimeout jitter)).run afterRead >>= fun out =>
    Except.ok ((caller, Product.snapshot afterRead, out.1), out.2)) = _
  rw [hj]; rfl

theorem prefixClockPath_run (first : Leanux.M α) (clock : HiddenSite) (w before afterRead : World)
    (choice : α) (caller : Option UInt64)
    (hp : first.run w = .ok (choice, before))
    (hc : (liftWG (callerJiffies clock)).run before = .ok (caller, afterRead)) :
    (prefixClockPath first clock).run w = .ok ((choice, Product.snapshot before, caller), afterRead) := by
  simp only [prefixClockPath, StateT.run_bind, hp]
  change ((liftWG (callerJiffies clock)).run before >>= fun out =>
    Except.ok ((choice, Product.snapshot before, out.1), out.2)) = _
  rw [hc]; rfl

theorem prefixClockJitterPath_run (first : Leanux.M α) (clock jitter : HiddenSite)
    (w before afterRead afterJitter : World) (choice : α) (caller : Option UInt64) (value : Nat)
    (hp : first.run w = .ok (choice, before))
    (hc : (liftWG (callerJiffies clock)).run before = .ok (caller, afterRead))
    (hj : (liftWG (jitterBelowRekeyTimeout jitter)).run afterRead = .ok (value, afterJitter)) :
    (prefixClockJitterPath first clock jitter).run w =
      .ok ((choice, Product.snapshot before, caller, Product.snapshot afterRead, value), afterJitter) := by
  simp only [prefixClockJitterPath, StateT.run_bind, hp]
  change ((clockJitterPath clock jitter).run before >>= fun out =>
    Except.ok ((choice, Product.snapshot before, out.1), out.2)) = _
  rw [clockJitterPath_run clock jitter before afterRead afterJitter caller value hc hj]; rfl

theorem prefixInspect_run (first : Leanux.M α) (tail : Leanux.M β) (w middle : World) (choice : α)
    (hp : first.run w = .ok (choice, middle)) :
    (prefixInspect first tail).run w =
      .ok ((choice, Product.snapshot middle, Product.observeResult (tail.run middle)), middle) := by
  simp only [prefixInspect, StateT.run_bind, hp]; rfl

theorem prefixInspect_error (first : Leanux.M α) (tail : Leanux.M β) (w : World) (err : Stop)
    (hp : first.run w = .error err) :
    (prefixInspect first tail).run w = .error err := by
  simp only [prefixInspect, StateT.run_bind, hp]; rfl


/-- All tail observations here come from the single actual post-prefix state. -/
theorem prefixInspect_property (first : Leanux.M α) (tail : Leanux.M β) (w : World)
    (R : α → Product.Snapshot → Product.Outcome β → Prop)
    (proof : ∀ choice middle, first.run w = .ok (choice, middle) →
      R choice (Product.snapshot middle) (Product.observeResult (tail.run middle))) :
    ∀ choice middle result,
      Product.observeResult ((prefixInspect first tail).run w) = .ok ((choice, middle, result), middle) →
      R choice middle result := by
  intro choice middle result run
  cases hp : first.run w with
  | error e =>
    rw [prefixInspect_error first tail w e hp] at run
    cases run
  | ok pair =>
    obtain ⟨value, after⟩ := pair
    rw [observe_ok (prefixInspect_run first tail w after value hp)] at run
    obtain ⟨values1, _⟩ := Prod.mk.inj (Except.ok.inj run)
    obtain ⟨rfl, values2⟩ := Prod.mk.inj values1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj values2
    exact proof value after hp

end Leanux.Proofs.WG.TimerDiscipline
