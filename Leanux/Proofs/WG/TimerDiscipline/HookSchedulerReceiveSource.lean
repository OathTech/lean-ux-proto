import Leanux.Env.Batch
import Leanux.Proofs.Logged.PrefixWorkers

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookScheduler
open Leanux Leanux.WG Leanux.Proofs.Logged
variable {E : Type}

structure Callbacks (E : Type) where
  transmit : PeerId → PrefixM E IterResult
  receive : PrefixM E Bool
  softirq : PrefixM E Unit
  irq : PrefixM E Unit

structure ErasureContracts (c : Callbacks E) : Prop where
  transmit : ∀ pid, ErasesPrefix (c.transmit pid) (txIter pid (Env.condResched .txWorker))
  receive : ErasesPrefix c.receive (liftWG WG.receiveStep)
  softirq : ErasesPrefix c.softirq Env.napiSoftirq
  irq : ErasesPrefix c.irq Env.napiIrqExit


def receive (c : Callbacks E) : PrefixM E IterResult :=
  workerIterPrefix .receiveWorker none c.receive (liftPrefix (Env.condResched .receiveWorker))


theorem receive_erases (c : Callbacks E) (h : ErasureContracts c) :
    ErasesPrefix (receive c)
      (workerIter .receiveWorker none (liftWG WG.receiveStep) (Env.condResched .receiveWorker)) :=
  workerIterPrefix_erases _ _ h.receive (erasesPrefix_lift _)


end Leanux.Proofs.WG.TimerDiscipline.HookScheduler
