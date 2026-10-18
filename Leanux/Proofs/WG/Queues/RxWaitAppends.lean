import Leanux.Proofs.WG.Queues.RxEnvTimersHistory

/-! The concrete return-to-user worker and timer observers append to every
incoming journal, including on Stop. No allocation or safety invariant is
needed to establish this observation property. -/
namespace Leanux.Proofs.WG.Queues.RxHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

elab "rx_append_head " name:ident : tactic => do
  let ty := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless ty.isAppOf ``Appends do Lean.throwError "not Appends"
  let args := ty.getAppArgs
  if args.isEmpty then Lean.throwError "missing action"
  let action := args.back!.consumeMData
  let .const actual _ := action.getAppFn | Lean.throwError "not a constant action"
  let expected := name.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    Lean.throwError "different action"

private theorem appends_discard {E α : Type} {a : PrefixM E α} (ha : Appends a) :
    Appends (discard a) := by
  change Appends (a >>= fun _ => pure ())
  exact Appends.bind ha (fun _ => Appends.pure ())

macro "rx_append_step" : tactic => `(tactic| first
  | (rx_append_head liftPrefix; exact Appends.lift _)
  | (rx_append_head Pure.pure; exact Appends.pure _)
  | (rx_append_head audit; exact Appends.focus _ _ _)
  | (rx_append_head mixed; exact Appends.focus _ _ _)
  | (rx_append_head focus; exact Appends.focus _ _ _)
  | (rx_append_head discard; apply appends_discard)
  | (rx_append_head Functor.mapConst; apply appends_discard)
  | (rx_append_head Bind.bind; apply Appends.bind)
  | (rx_append_head ForIn.forIn; first | apply Appends.range | apply Appends.forIn)
  | dsimp only
  | maintenance_intro
  | split)

private theorem runWorker_appends {E : Type} (worker : Worker) {body : PrefixM E Unit}
    (hb : Appends body) : Appends (runWorkerPrefix worker body) := by
  unfold runWorkerPrefix
  repeat' first | exact hb | rx_append_step

private theorem softirq_appends {E : Type} {scan : PrefixM E (List PeerId)}
    {poll : PeerId → Nat → PrefixM E Nat} (hs : Appends scan) (hp : ∀ pid budget, Appends (poll pid budget)) :
    Appends (RxNapi.softirqWith scan poll) := by
  unfold RxNapi.softirqWith
  repeat' first
    | exact hs
    | exact hp _ _
    | (rx_append_head runWorkerPrefix; apply runWorker_appends)
    | rx_append_step

private theorem irq_appends {E : Type} {scan : PrefixM E Bool} {softirq : PrefixM E Unit}
    (hs : Appends scan) (hi : Appends softirq) : Appends (RxNapi.irqExitWith scan softirq) := by
  unfold RxNapi.irqExitWith
  repeat' first | exact hs | exact hi | rx_append_step

theorem napiSoftirq_appends : Appends napiSoftirq :=
  softirq_appends (Appends.focus _ _ _) observePoll_appends

theorem napiIrqExit_appends : Appends napiIrqExit :=
  irq_appends (Appends.focus _ _ _) napiSoftirq_appends

private theorem workerIter_appends {E : Type} (worker : Worker) (pid : Option Nat)
    {step after : PrefixM E Bool} (hs : Appends step) (ha : Appends after) :
    Appends (workerIterPrefix worker pid step after) := by
  unfold workerIterPrefix
  repeat' first | exact hs | exact ha | rx_append_step

private theorem encryptIteration_appends : Appends encryptIteration := by
  unfold encryptIteration
  exact Appends.bind (Appends.focus _ _ _) (fun _ =>
    Appends.bind napiSoftirq_appends (fun _ => Appends.focus _ _ _))

private theorem decryptStep_appends : Appends decryptStep := by
  unfold decryptStep RxWorkers.decryptWith
  repeat' first
    | (rx_append_head napiSoftirq; exact napiSoftirq_appends)
    | (rx_append_head napiIrqExit; exact napiIrqExit_appends)
    | (rx_append_head prepare; exact Appends.focus _ _ _)
    | rx_append_step

private theorem decryptIteration_appends : Appends decryptIteration :=
  workerIter_appends _ _ decryptStep_appends
    (Appends.bind (Appends.lift _) (fun _ => Appends.lift _))

private theorem receiveIteration_appends : Appends Origins.HistoryAdapters.receiveIteration :=
  workerIter_appends _ _ (Appends.focus _ _ _) (Appends.lift _)

private theorem cryptAhead_appends (pid : PeerId) : Appends (cryptAhead pid) := by
  unfold cryptAhead
  repeat' first
    | (rx_append_head encryptIteration; exact encryptIteration_appends)
    | rx_append_step

private theorem activationIteration_appends (a : Activation) : Appends (activationIteration a) := by
  unfold activationIteration
  repeat' first
    | (rx_append_head encryptIteration; exact encryptIteration_appends)
    | (rx_append_head decryptIteration; exact decryptIteration_appends)
    | (rx_append_head receiveIteration; exact receiveIteration_appends)
    | (rx_append_head cryptAhead; exact cryptAhead_appends _)
    | rx_append_step

private theorem activationRun_appends (a : Activation) : Appends (activationRun a) := by
  unfold activationRun
  repeat' first
    | (rx_append_head activationIteration; exact activationIteration_appends _)
    | rx_append_step

private theorem dispatch_appends (worker : Worker) : Appends (dispatch worker) := by
  unfold dispatch
  repeat' first
    | (rx_append_head activationRun; exact activationRun_appends _)
    | rx_append_step

theorem schedule_appends (stack : Option Worker) : Appends (schedule stack) := by
  unfold schedule
  repeat' first
    | (rx_append_head dispatch; exact dispatch_appends _)
    | (rx_append_head activationRun; exact activationRun_appends _)
    | (rx_append_head napiSoftirq; exact napiSoftirq_appends)
    | rx_append_step

theorem runCryptWorkers_appends : Appends runCryptWorkers := by
  unfold runCryptWorkers
  exact Appends.bind (schedule_appends _) (fun _ => Appends.lift _)

theorem runSendWorkers_appends : Appends runSendWorkers := by
  unfold runSendWorkers
  repeat' first
    | (rx_append_head schedule; exact schedule_appends _)
    | rx_append_step

private theorem runTimers_appends (jHi : UInt64) : Appends (runTimers jHi) := by
  unfold runTimers
  repeat' first
    | (rx_append_head runCryptWorkers; exact runCryptWorkers_appends)
    | rx_append_step

private theorem runTimersPlaceholder_appends (jHi : UInt64) : Appends (runTimersPlaceholder jHi) := by
  unfold runTimersPlaceholder
  repeat' first
    | (rx_append_head runCryptWorkers; exact runCryptWorkers_appends)
    | (rx_append_head runSendWorkers; exact runSendWorkers_appends)
    | rx_append_step

theorem idleTimers_appends : Appends idleTimers := by
  unfold idleTimers discard
  repeat' first
    | (rx_append_head runTimers; exact runTimers_appends _)
    | (rx_append_head runTimersPlaceholder; exact runTimersPlaceholder_appends _)
    | rx_append_step

end Leanux.Proofs.WG.Queues.RxHistory
