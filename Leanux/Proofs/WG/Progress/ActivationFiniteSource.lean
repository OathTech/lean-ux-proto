import Leanux.Proofs.WG.Progress.PacketAllocationFiniteSource
import Leanux.Proofs.WG.Progress.ReceptionFiniteSource
import Leanux.Proofs.WG.TimerDiscipline.HookSchedulerReceiveSource
import Leanux.Proofs.WG.Progress.CookieControlSource
import Leanux.Proofs.WG.Progress.Dispatch

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.ActivationFinite
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.TimerDiscipline

/-- Concrete callbacks for the existing worker factories. Reception uses the
finite handshake evaluation; transmit and NAPI are the original bounded
packet/list computations and do not execute queued handshake work. -/
def callbacks : HookScheduler.Callbacks PUnit where
  transmit pid := liftPrefix (WG.txIter pid (Env.condResched .txWorker))
  receive := liftPrefix (liftWG HandshakeFinite.receiveStep)
  softirq := liftPrefix Env.napiSoftirq
  irq := liftPrefix Env.napiIrqExit

theorem callbacks_erases : HookScheduler.ErasureContracts callbacks := by
  constructor
  · intro pid
    exact erasesPrefix_lift _
  · change ErasesPrefix (liftPrefix (liftWG HandshakeFinite.receiveStep)) (liftWG WG.receiveStep)
    rw [HandshakeFinite.receiveStep_source]
    exact erasesPrefix_lift _
  · exact erasesPrefix_lift _
  · exact erasesPrefix_lift _

/-- Only reception reaches a nonstructural handshake evaluator. The other
worker arms retain the original bounded packet/NAPI computations; their
concrete allocation sites reduce through PacketAllocationFiniteSource. -/
def iteration (a : Activation) : Leanux.M IterResult :=
  match a.worker with
  | .receiveWorker => fun w => (runPrefix (HookScheduler.receive callbacks) w []).1
  | _ => Env.Activation.iter a

theorem iteration_source (a : Activation) :
    Env.Activation.iter a = iteration a := by
  cases worker : a.worker <;> simp only [iteration,worker]
  all_goals first
    | rfl
    | (funext w
       simp only [Env.Activation.iter,worker]
       change (workerIter .receiveWorker none (liftWG WG.receiveStep)
         (Env.condResched .receiveWorker)).run w = _
       exact (HookScheduler.receive_erases callbacks callbacks_erases w []).symm)

/-- The carried native activation factor captures occupancy and refills at
their actual reads. Every iteration and exhaustion outcome remains literal. -/
def run (a : Activation) : Leanux.M Unit := do
  let occupancy ← Env.Activation.occupancy a
  let refills ← Env.Activation.refills
  let state ← activationLoopSourceWith iteration (List.range' 0 (occupancy + refills + 1)) a
  activationFinishSource a occupancy refills state

theorem run_source (a : Activation) : Env.Activation.run a = run a := by
  rw [activation_run_source]
  unfold run activationLoopSource
  rw [funext iteration_source]

/-- The carried selection prefix retains pending empty device units; the
selected finite run follows the actual section-start read. -/
def dispatch (worker : Worker) : Leanux.M Bool := do
  let selected ← dispatchPrefix worker
  dispatchAfterPrefixWith run worker selected

theorem dispatch_source (worker : Worker) : Env.dispatch worker = dispatch worker := by
  rw [Progress.dispatch_source]
  unfold dispatch dispatchAfterPrefix
  rw [funext run_source]

end Leanux.Proofs.WG.Progress.ActivationFinite
