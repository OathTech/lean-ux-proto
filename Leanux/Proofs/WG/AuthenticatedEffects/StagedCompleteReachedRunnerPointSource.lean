import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedReturnFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerEndpoint
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRunnerSetupSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRunnerCleanupSource

/-! Fixed outer source witnesses. The World is the original runner's explicit
accumulator, not a reconstructed error state. The only effectful children are
native dispatch and the four named return-callback families. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Runner.Points
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal

abbrev History := List Event
abbrev Result (α : Type) := Except (Nat × Stop) α
abbrev State := RunnerOperation.State

inductive Child : {α : Type} → PrefixM Event α → Type 1 where
  | dispatch (call : Syscall) : Child (Driver.dispatchObserved hooks call)
  | sends : Child (Driver.sendWorkersObserved hooks)
  | idle : Child (Driver.idleTimersObserved hooks)
  | afterXmit : Child (Driver.afterXmitObserved hooks)
  | advance : Child (Driver.afterAdvanceObserved hooks)

/-- These are fixed native runner leaves. They never stand for an arbitrary
caller selected by extensional equality. Initialization and metadata guards
retain their original failure result and operation index. -/
inductive Native : {α : Type} → PrefixOuter Event α → Type 1 where
  | stored (index : Nat) (w : World) (source : PrefixStore.Shape body) :
      Native (runAtPrefix index w body)
  | prefill (count : Nat) (w : World) : Native (ConservationRunner.prefillWith count w pure)
  | boot (net foreign : Bool) (w : World) : Native (ConservationRunner.bootWith net foreign w pure)
  | enter (index : Nat) (w : World) (call : Syscall) :
      Native (runAtPrefix index w (SyscallSource.enter call))
  | prelude (index : Nat) (w : World) : Native (runAtPrefix index w ReturnSource.prelude)
  | routing (index : Nat) (w : World) (call : Syscall) :
      Native (runAtPrefix index w (ReturnSource.routing call))
  | route (index : Nat) (w : World) : Native (runAtPrefix index w (liftPrefix Env.routeIntoWg0))
  | cleanup (index : Nat) (w : World) : Native (runAtPrefix index w (liftPrefix Env.netnsCleanup))
  | skip (index : Nat) (w : World) : Native (runAtPrefix index w (liftPrefix (skipAmbient : Leanux.M Unit)))

inductive Label where
  | fixture
  | prepared (index : Nat) (op : Operation)
  | operation (index : Nat) (op : Operation)
  | callback (call : Syscall) (index : Nat)
  | afterCall (index : Nat) (op : Operation)
  | metadata (index : Nat)
  | finish

inductive Shape : {α : Type} → PrefixOuter Event α → Type 1 where
  | pure (value : α) : Shape (pure value)
  | stopped (reason : Nat × Stop) : Shape (throw reason : PrefixOuter Event α)
  | native (token : Native action) : Shape action
  | child (index : Nat) (w : World) (token : Child action) : Shape (runAtPrefix index w action)
  | bind {body : PrefixOuter Event α} {next : α → PrefixOuter Event β}
      (head : Shape body) (tail : ∀ value, Shape (next value)) : Shape (body >>= next)
  | marked (label : Label) (w : World) (body : Shape action) : Shape action

noncomputable def listShape (xs : List ι) (initial : σ)
    (body : ι → σ → PrefixOuter Event (ForInStep σ))
    (shapes : ∀ value acc, Shape (body value acc)) : Shape (forIn xs initial body) :=
  List.rec (motive := fun values => ∀ acc, Shape (forIn values acc body))
    (fun acc => .pure acc)
    (fun value rest ih acc => (List.forIn_cons body value rest acc).symm ▸
      Shape.bind (shapes value acc) (fun decision => match decision with
        | .done final => .pure final
        | .yield next => ih next)) xs initial

noncomputable def arrayShape (xs : Array ι) (initial : σ)
    (body : ι → σ → PrefixOuter Event (ForInStep σ))
    (shapes : ∀ value acc, Shape (body value acc)) : Shape (forIn xs initial body) := by
  rw [←Array.forIn_toList]
  exact listShape _ _ _ shapes

theorem runAt_bind (index : Nat) (w : World) (body : PrefixM Event α)
    (next : α → PrefixM Event β) :
    runAtPrefix index w (body >>= next) =
      (runAtPrefix index w body >>= fun out => runAtPrefix index out.2 (next out.1)) := by
  funext h
  change runPrefixOuter (runAtPrefix index w (body >>= next)) h =
    runPrefixOuter (runAtPrefix index w body >>= fun out=>runAtPrefix index out.2 (next out.1)) h
  simp only [runAtPrefix_run,runPrefix_bind,runPrefixOuter_bind]
  cases runPrefix body w h with
  | mk result history => cases result <;> rfl

theorem runAt_pure (index : Nat) (w : World) (value : α) :
    runAtPrefix index w (pure value : PrefixM Event α) = pure (value,w) := by
  funext h; rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Runner.Points
