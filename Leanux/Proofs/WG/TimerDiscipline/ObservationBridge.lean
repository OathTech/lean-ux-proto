import Leanux.Proofs.WG.TimerDiscipline.ObservationProductSource
import Leanux.Proofs.WG.TimerDiscipline.SourceClaims
import Leanux.Proofs.WG.Campaign2.Bridge
import Leanux.Proofs.WG.TimerDiscipline.View

/-! Source connection for projected timer observations. Every inspection starts
at the same concrete entry as the original action; every first internally
threads its actual state. No state is reconstructed from an observation. -/
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

/-- Two original reads with the actual between-read observation. -/
def clockJitterPath (clock jitter : HiddenSite) : M (Option UInt64 × Snapshot × Nat) := do
  let caller ← callerJiffies clock
  let afterRead ← Campaign2.read
  let value ← jitterBelowRekeyTimeout jitter
  return (caller, afterRead, value)

def prefixClockPath (first : M α) (clock : HiddenSite) : M (α × Snapshot × Option UInt64) := do
  let choice ← first
  let before ← Campaign2.read
  let caller ← callerJiffies clock
  return (choice, before, caller)

def prefixClockJitterPath (first : M α) (clock jitter : HiddenSite) :
    M (α × Snapshot × Option UInt64 × Snapshot × Nat) := do
  let choice ← first
  let before ← Campaign2.read
  let result ← clockJitterPath clock jitter
  return (choice, before, result)

/-- Inspect the tail at the actual post-first state, retaining even tail errors. -/
def prefixInspect (first : M α) (tail : M β) : M (α × Snapshot × Outcome β) := do
  let choice ← first
  let middle ← Campaign2.read
  let result ← Campaign2.inspect tail
  return (choice, middle, result)

theorem clockJitterPath_run (clock jitter : HiddenSite) (w afterRead afterJitter : World)
    (caller : Option UInt64) (value : Nat)
    (hc : (callerJiffies clock).run w = .ok (caller, afterRead))
    (hj : (jitterBelowRekeyTimeout jitter).run afterRead = .ok (value, afterJitter)) :
    (clockJitterPath clock jitter).run w = .ok ((caller, snapshot afterRead, value), afterJitter) := by
  simp only [clockJitterPath, StateT.run_bind, hc]
  change ((jitterBelowRekeyTimeout jitter).run afterRead >>= fun out =>
    Except.ok ((caller, snapshot afterRead, out.1), out.2)) = _
  rw [hj]; rfl

theorem prefixClockPath_run (first : M α) (clock : HiddenSite) (w before afterRead : World)
    (choice : α) (caller : Option UInt64)
    (hp : first.run w = .ok (choice, before))
    (hc : (callerJiffies clock).run before = .ok (caller, afterRead)) :
    (prefixClockPath first clock).run w = .ok ((choice, snapshot before, caller), afterRead) := by
  simp only [prefixClockPath, StateT.run_bind, hp]
  change ((callerJiffies clock).run before >>= fun out =>
    Except.ok ((choice, snapshot before, out.1), out.2)) = _
  rw [hc]; rfl

theorem prefixClockJitterPath_run (first : M α) (clock jitter : HiddenSite)
    (w before afterRead afterJitter : World) (choice : α) (caller : Option UInt64) (value : Nat)
    (hp : first.run w = .ok (choice, before))
    (hc : (callerJiffies clock).run before = .ok (caller, afterRead))
    (hj : (jitterBelowRekeyTimeout jitter).run afterRead = .ok (value, afterJitter)) :
    (prefixClockJitterPath first clock jitter).run w =
      .ok ((choice, snapshot before, caller, snapshot afterRead, value), afterJitter) := by
  simp only [prefixClockJitterPath, StateT.run_bind, hp]
  change ((clockJitterPath clock jitter).run before >>= fun out =>
    Except.ok ((choice, snapshot before, out.1), out.2)) = _
  rw [clockJitterPath_run clock jitter before afterRead afterJitter caller value hc hj]; rfl

theorem prefixInspect_run (first : M α) (tail : M β) (w middle : World) (choice : α)
    (hp : first.run w = .ok (choice, middle)) :
    (prefixInspect first tail).run w =
      .ok ((choice, snapshot middle, observeResult (tail.run middle)), middle) := by
  simp only [prefixInspect, StateT.run_bind, hp]; rfl

theorem prefixInspect_error (first : M α) (tail : M β) (w : World) (err : Stop)
    (hp : first.run w = .error err) :
    (prefixInspect first tail).run w = .error err := by
  simp only [prefixInspect, StateT.run_bind, hp]; rfl


/-- All tail observations here come from the single actual post-prefix state. -/
theorem prefixInspect_property (first : M α) (tail : M β) (w : World)
    (R : α → Snapshot → Outcome β → Prop)
    (proof : ∀ choice middle, first.run w = .ok (choice, middle) →
      R choice (snapshot middle) (observeResult (tail.run middle))) :
    ∀ choice middle result,
      observeResult ((prefixInspect first tail).run w) = .ok ((choice, middle, result), middle) →
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

def giveUpClockPath (pid : PeerId) :
    M (Bool × Snapshot × Bool × Snapshot × Option UInt64) := do
  let decision ← retransmitDecision pid
  let afterDecision ← Campaign2.read
  let result ← prefixClockPath (giveUpArmPrefix pid) .timerJiffiesRetransmitZeroKey
  return (decision, afterDecision, result)

def timerExecutionPath (worker : Worker) (horizon : UInt64) : M (PeerId × PeerTimer × Snapshot) := do
  let selected ← timerSelection worker horizon
  let beforeCallback ← Campaign2.read
  fireSelected worker selected.1 selected.2
  return (selected.1, selected.2, beforeCallback)

def initiationExecutionPath (pid : PeerId) : M (Bool × Snapshot) := do
  let reached ← initiationArmPrefix pid
  let beforeArm ← Campaign2.read
  if reached then timersHandshakeInitiated pid
  return (reached, beforeArm)

end Leanux.Proofs.WG.TimerDiscipline
