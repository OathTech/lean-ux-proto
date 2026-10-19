import Leanux.Proofs.WG.Progress.PacketAllocationFiniteSource
import Leanux.Proofs.WG.Progress.ReceptionFiniteSource
import Leanux.Proofs.WG.TimerDiscipline.HookSchedulerSource

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

/-- The existing worker-iteration factory, evaluated with concrete finite
callbacks. Erasing its empty journal preserves every original outcome. -/
def iteration (a : Activation) : Leanux.M IterResult :=
  fun w => (runPrefix (HookScheduler.iteration callbacks a) w []).1

theorem iteration_source (a : Activation) :
    Env.Activation.iter a = iteration a := by
  funext w
  exact (HookScheduler.iteration_erases callbacks callbacks_erases a w []).symm

/-- The existing occupancy-bounded activation factory. Exhaustion remains the
original invariant Stop; finite evaluation does not establish sufficient fuel. -/
def run (a : Activation) : Leanux.M Unit :=
  fun w => (runPrefix (HookScheduler.run callbacks a) w []).1

theorem run_source (a : Activation) : Env.Activation.run a = run a := by
  funext w
  exact (HookScheduler.run_erases callbacks callbacks_erases a w []).symm

/-- Actual worker selection and section entry from the existing dispatch
factory, followed by the same bounded activation evaluation. -/
def dispatch (worker : Worker) : Leanux.M Bool :=
  fun w => (runPrefix (HookScheduler.dispatch callbacks worker) w []).1

theorem dispatch_source (worker : Worker) : Env.dispatch worker = dispatch worker := by
  funext w
  exact (HookScheduler.dispatch_erases callbacks callbacks_erases worker w []).symm

end Leanux.Proofs.WG.Progress.ActivationFinite
