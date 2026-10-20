import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSchedulerIteration

import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedProductReadCanonical

/-! A proof-only source shape indexed by the original action. It has no
evaluator and introduces no new scheduler or ledger. Points will index the
fixed canonical shape, not an existential shape or bind-factor equation.
Copied-world consistency tests are a distinct native atom, never committed
iteration or NAPI callbacks. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Scheduler.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

abbrev History := List Event
abbrev Result (α : Type) := Except Stop (α × World)

inductive Native : {α : Type} → Leanux.M α → Type 1 where
  | reading (source : ProductRead.Shape body) : Native body
  | device : Native (liftWG getDev)
  | ambient : Native getAmbient
  | budget : Native recordBudget
  | occupancy (a : Activation) : Native (Env.Activation.occupancy a)
  | refills : Native Env.Activation.refills
  | pendingDevice (worker : Worker) (queued : Bool) : Native (Env.pendingDevice worker queued)
  | pending (next : Option Nat) : Native (Lifetimes.pendingNapi next)
  | work (a : Activation) : Native (Env.Activation.hasWork a)
  | trials (active : List Activation) : Native (active.filterM Env.Activation.consistent)
  | hiddenSite : Native peekHiddenSite
  | unit (worker : Worker) : Native (peekUnit worker)
  | resolve (worker : Worker) (unit : Nat) (peers : List PeerId) :
      Native (resolveUnit worker unit peers)
  | eraseWork (pid : PeerId) :
      Native (liftWG (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue.erase pid}))
  | start (worker : Worker) : Native (hidden (.sectionStart worker))
  | stop (worker : Worker) : Native (hidden (.sectionStop worker))
  | suspend (a : Activation) : Native (modifyAmbient fun s =>
      {s with suspended := s.suspended ++ [{a with iterations := a.iterations + 1}]})
  | resume (a : Activation) : Native (modifyAmbient fun s => {s with suspended := s.suspended.filter (· != a)})
  | invariant (message : String) : Native (Leanux.invariant message : Leanux.M Unit)
  | unsupported (message : String) : Native (Leanux.unsupported message : Leanux.M Unit)
  | exhausted (message : String) : Native (budgetExhausted message : Leanux.M Unit)

inductive Child : {α : Type} → PrefixM Event α → Type 1 where
  | iteration (a : Activation) : Child (Scheduler.iteration a)
  | napi : Child (Driver.softirqObserved hooks)

inductive Label where
  | run (a : Activation)
  | runIndex (a : Activation) (occupancy index : Nat)
  | dispatch (worker : Worker)
  | choose (stack : Option Worker)
  | schedule (stack : Option Worker)
  | scheduleIndex (stack : Option Worker) (budget index : Nat)

inductive Shape : {α : Type} → PrefixM Event α → Type 1 where
  | pure (value : α) : Shape (pure value)
  | native (token : Native action) : Shape (liftPrefix action)
  | child (token : Child action) : Shape action
  | bind {body : PrefixM Event α} {next : α → PrefixM Event β}
      (head : Shape body) (tail : ∀ value, Shape (next value)) : Shape (body >>= next)
  | marked (label : Label) (body : Shape action) : Shape action

/-- The finite original list is expanded only as a source witness. The
corresponding action remains the original forIn; done skips the whole suffix. -/
noncomputable def listShape (xs : List Nat) (initial : σ)
    (body : Nat → σ → PrefixM Event (ForInStep σ))
    (shapes : ∀ index acc, Shape (body index acc)) :
    Shape (forIn xs initial body) :=
  List.rec (motive := fun positions => ∀ acc, Shape (forIn positions acc body))
    (fun acc => .pure acc)
    (fun index rest ih acc =>
      (List.forIn_cons body index rest acc).symm ▸
        Shape.bind (shapes index acc) (fun decision => match decision with
          | .done final => .pure final
          | .yield next => ih next)) xs initial

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Scheduler.Points
