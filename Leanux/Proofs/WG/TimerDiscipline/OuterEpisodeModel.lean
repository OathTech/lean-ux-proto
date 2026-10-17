import Leanux.Env
import Leanux.Proofs.WG.Campaign2.Bridge
import Leanux.Proofs.WG.TimerDiscipline.Model

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env

abbrev TimerOuterControl := Bool × Option UInt64

structure OuterTimerChoice where
  worker : Worker
  pid : PeerId
  timer : PeerTimer
  wheel : WheelEntry

/-- Selection reads the actual current wheel, never a supplied unit list. -/
def outerTimerChoice (jPass : UInt64) (s : Campaign2.Product.Snapshot) : Option OuterTimerChoice := do
  let site ← s.ambient.hidden.bind fun rs => (rs.find? fun (r : HiddenRecord) => !HiddenSite.passive r.site).map HiddenRecord.site
  let worker ← timerSectionOf site
  if worker == .clearPeerWorker then none else do
    let d ← s.wg.device
    let (pid,timer,wheel) ← TimerWheel.nextDue d jPass
    return ⟨worker,pid,timer,wheel⟩

structure OuterTimerUnitReceipt where
  choice : OuterTimerChoice
  selected : Campaign2.Product.Snapshot

structure OuterTimerTurnReceipt where
  iteration : Nat
  before : Campaign2.Product.Snapshot
  control : TimerOuterControl
  result : ForInStep TimerOuterControl
  unit : Campaign2.Product.Outcome (Option OuterTimerUnitReceipt)
  after : Campaign2.Product.Snapshot

def OuterTimerTurnValid (jPass : UInt64) (r : OuterTimerTurnReceipt) : Prop :=
  match outerTimerChoice jPass r.before with
  | none => r.unit = .ok (none,r.before)
  | some choice => ∃ selected,
      r.unit = .ok (some ⟨choice,selected⟩,r.after) ∧
      r.result = .yield (true,some choice.wheel.bucketExpiry) ∧
      choice.worker.timer? = some choice.timer ∧
      selected.wg.device = r.before.wg.device ∧
      ∀identity attempts expiry,
        choice.timer = .retransmitHandshake →
        retryObservation selected.toSnapshot choice.pid = some (identity,attempts,expiry) →
        retryObservation r.after.toSnapshot choice.pid = some (identity,nextAttempts attempts,none)

/-- A chain of every executed turn. A done receipt is retained, and excludes
execution of the unused tail. No predicate asserts that fuel exhaustion means
there are no more due timers. -/
inductive OuterTimerChain (jPass : UInt64) : Campaign2.Product.Snapshot → TimerOuterControl →
    List Nat → List OuterTimerTurnReceipt → Campaign2.Product.Snapshot → TimerOuterControl → Prop
  | nil (entry : Campaign2.Product.Snapshot) (control : TimerOuterControl) :
      OuterTimerChain jPass entry control [] [] entry control
  | done (r : OuterTimerTurnReceipt) (rest : List Nat) (control : TimerOuterControl)
      (step : r.result = .done control) (valid : OuterTimerTurnValid jPass r) :
      OuterTimerChain jPass r.before r.control (r.iteration :: rest) [r] r.after control
  | yield (r : OuterTimerTurnReceipt) (rest : List Nat) (control finalControl : TimerOuterControl)
      (tail : List OuterTimerTurnReceipt) (final : Campaign2.Product.Snapshot)
      (step : r.result = .yield control) (valid : OuterTimerTurnValid jPass r)
      (chain : OuterTimerChain jPass r.after control rest tail final finalControl) :
      OuterTimerChain jPass r.before r.control (r.iteration :: rest) (r :: tail) final finalControl

structure OuterTimerEpisodeReceipt where
  start : Campaign2.Product.Snapshot
  budget : Option Nat
  turns : List OuterTimerTurnReceipt
  beforeFinish : Campaign2.Product.Snapshot
  control : TimerOuterControl
  finish : Option (Campaign2.Product.Outcome Bool)

def outerTimerReset (entry : Campaign2.Product.Snapshot) : Campaign2.Product.Snapshot :=
  {entry with wg := {entry.wg with queuedThisCall := []}}

def outerTimerBudget (entry : Campaign2.Product.Snapshot) : Nat :=
  match entry.ambient.hidden with
  | some records => records.length + 1
  | none => DOMAIN_FILTER_TURNS

/-- Every executed original loop turn, including a terminating turn, and the
actual unchanged finish. It makes no claim of global no-due or retry bounds. -/
def OuterTimerEpisodeValid (jPass : UInt64) (entry : Campaign2.Product.Snapshot)
    (receipt : OuterTimerEpisodeReceipt) (result : Bool) (final : Campaign2.Product.Snapshot) : Prop :=
  receipt.start = outerTimerReset entry ∧
  if receipt.start.wg.device.isNone then
    receipt.budget = none ∧ receipt.turns = [] ∧ receipt.beforeFinish = receipt.start ∧
    receipt.control = (false,none) ∧ receipt.finish = none ∧ result = false ∧ final = receipt.start
  else
    receipt.budget = some (outerTimerBudget receipt.start) ∧
    OuterTimerChain jPass receipt.start (false,none) (List.range' 0 (outerTimerBudget receipt.start))
      receipt.turns receipt.beforeFinish receipt.control ∧
    receipt.finish = some (.ok (result,final))


end Leanux.Proofs.WG.TimerDiscipline
