import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDispatchPointRunner

import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedProductReadCanonical

/-! Fixed service source syntax. Timers and delivery are expanded from the
original source; only the seven deeper callback families remain children.
No service operation is itself a child and no new evaluator is introduced. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Service.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal
abbrev History := List Event
abbrev Result (α : Type) := Except Stop (α × World)

inductive NativeKind : Type 1 where
  | wg | device | env | routing
  | ambient {α : Type} (body : AmbientM α)
  | ambientEdit (f : Ambient → Ambient)
  | envEdit (f : EnvWorld → EnvWorld)
  | reset | sentClear
  | pass (value : Option UInt64)
  | jiffies (value : UInt64)
  | delete (pid : PeerId) (timer : PeerTimer)
  | peek
  | timerWorker (timer : PeerTimer)
  | stepComplete (expiry : UInt64)
  | nothingDue (expiry : UInt64)
  | delivery (sent : List SentDatagram)

def NativeKind.Result : NativeKind → Type
  | .wg => WGWorld
  | .device => Device
  | .env => EnvWorld
  | .routing => Net.Routing
  | @ambient α _ => α
  | .peek => Option Nat
  | .timerWorker _ => Worker
  | _ => Unit

def NativeKind.action (kind : NativeKind) : PrefixM Event kind.Result := match kind with
  | .wg => liftPrefix getWG
  | .device => liftPrefix (liftWG getDev)
  | .env => liftPrefix getEnv
  | .routing => liftPrefix getRouting
  | .ambient body => liftPrefix (liftAmbient body)
  | .ambientEdit f => liftPrefix (modifyAmbient f)
  | .envEdit f => liftPrefix (modifyEnv f)
  | .reset => liftPrefix (modifyWG fun w => {w with queuedThisCall := []})
  | .sentClear => liftPrefix (modifyWG fun w => {w with sent := []})
  | .pass value => liftPrefix (modifyWG fun w => {w with timerPassStep := value})
  | .jiffies value => liftPrefix (modifyWG fun w => {w with jiffiesLast := some value})
  | .delete pid timer => liftPrefix (liftWG (delTimer pid timer))
  | .peek => liftPrefix Env.peekNextSite
  | .timerWorker timer => liftPrefix (Env.timerWorker timer)
  | .stepComplete expiry => liftPrefix (Env.requireStepComplete expiry)
  | .nothingDue expiry => liftPrefix (Env.requireNothingDue expiry)
  | .delivery sent => emitPrefix (Event.delivery sent)

inductive Native : {α : Type} → PrefixM Event α → Type 1 where
  | reading (source : ProductRead.Shape body) : Native (liftPrefix body)
  | kind (source : NativeKind) : Native source.action

inductive Family where
  | schedule (stack : Option Worker)
  | sends
  | sendWorker
  | clearWorker
  | timer (pid : PeerId) (timer : PeerTimer)
  | selected (device : Device) (bound : UInt64) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry)
  | finished (token : Nat)

def Family.Result : Family → Type
  | .selected .. => Nat
  | _ => Unit

def Family.action (family : Family) : PrefixM Event family.Result := match family with
  | .schedule stack => Driver.scheduleObserved hooks stack
  | .sends => Driver.sendWorkersObserved hooks
  | .sendWorker => Driver.sendWorkerObserved hooks
  | .clearWorker => Driver.clearWorkerObserved hooks
  | .timer pid t => liftWGObserver (Driver.timerObserved hooks pid t)
  | .selected device bound pid t entry => hooks.timerSelected device bound pid t entry
  | .finished token => hooks.timerFinished token

inductive Child : {α : Type} → PrefixM Event α → Type 1 where
  | family (source : Family) : Child source.action

inductive Label where
  | idle | advance | delivery | crypt
  | timers (bound : UInt64)
  | placeholders (bound : UInt64)
  | timerSection (worker : Worker)
  | range (start stop step : Nat)
  | index (value : Nat)
  | datagram (value : SentDatagram)

inductive Shape : {α : Type} → PrefixM Event α → Type 1 where
  | pure (value : α) : Shape (pure value)
  | native (token : Native action) : Shape action
  | child (token : Child action) : Shape action
  | bind {body : PrefixM Event α} {next : α → PrefixM Event β}
      (head : Shape body) (tail : ∀ value, Shape (next value)) : Shape (body >>= next)
  | marked (label : Label) (body : Shape action) : Shape action

noncomputable def listShape (xs : List ι) (initial : σ)
    (body : ι → σ → PrefixM Event (ForInStep σ))
    (shapes : ∀ value acc, Shape (body value acc)) : Shape (forIn xs initial body) :=
  List.rec (motive := fun values => ∀ acc, Shape (forIn values acc body))
    (fun acc => .pure acc)
    (fun value rest ih acc => (List.forIn_cons body value rest acc).symm ▸
      Shape.bind (shapes value acc) (fun decision => match decision with
        | .done final => .pure final
        | .yield next => ih next)) xs initial

noncomputable def rangeShape (range : Std.Legacy.Range) (initial : σ)
    (body : Nat → σ → PrefixM Event (ForInStep σ))
    (shapes : ∀ value acc, Shape (body value acc)) : Shape (forIn range initial body) := by
  apply Shape.marked (.range range.start range.stop range.step)
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact listShape _ _ _ (fun value acc => .marked (.index value) (shapes value acc))

/-- Lift laws expose the original native delivery loop without changing it. -/
theorem lift_bind (body : Leanux.M α) (next : α → Leanux.M β) :
    (liftPrefix (body >>= next) : PrefixM Event β) =
      (liftPrefix body >>= fun value => liftPrefix (next value)) := by
  funext w h
  change ((body >>= next).run w,h) = runPrefix (liftPrefix body >>= fun value => liftPrefix (next value)) w h
  rw [runPrefix_bind,runPrefix_lift]
  cases run : body.run w <;> simp only [StateT.run_bind,run,runPrefix_lift] <;> rfl

theorem lift_pure (value : α) :
    (liftPrefix (pure value : Leanux.M α) : PrefixM Event α) = pure value := rfl

theorem lift_list (xs : List ι) (initial : σ) (body : ι → σ → Leanux.M (ForInStep σ)) :
    (liftPrefix (forIn xs initial body) : PrefixM Event σ) =
      forIn xs initial (fun value acc => liftPrefix (body value acc)) := by
  induction xs generalizing initial with
  | nil => rfl
  | cons value rest ih =>
      simp only [List.forIn_cons,lift_bind]
      congr 1
      funext decision
      cases decision <;> simp only [lift_pure,ih]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Service.Points
